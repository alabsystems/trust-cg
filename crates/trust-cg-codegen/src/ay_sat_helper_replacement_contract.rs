// trust-cg-codegen/ay_sat_helper_replacement_contract.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only artifact contract helpers for bounded ay SAT helper slices.
//!
//! This module binds the proof metadata, ABI/layout records, signature,
//! proof-policy, invalidation, and manifest shape for the bounded
//! `contains4_masked`, minimization keep/drop, and theory-dispatch assignment
//! helper replacements. It intentionally records non-promoting evidence only:
//! useful-native promotion and product release authority remain blocked on the
//! parent gates.

use std::collections::BTreeMap;

use crate::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, ArtifactSection, ArtifactSectionKind, ArtifactSymbol,
    DeterministicArtifactManifest, Endianness, FieldLayout, InvalidationKey, JitArtifactKind,
    LayoutManifest, ProofEvidenceSummary, ProofPolicy, RecordLayout, SymbolLayout,
    SymbolLookupContract, SymbolSignature, SymbolVisibility, TargetDescriptor,
    TargetOperatingSystem,
};
use crate::target::Target;

/// Stable schema tag for SAT helper replacement contract output.
pub const AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA: &str =
    "trust-cg.ay_sat_helper_replacement.artifact_contract.v1";

/// Stable numeric schema version for SAT helper replacement contracts.
pub const AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Stable proof-fact schema for SAT contains-helper replacement evidence.
pub const AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA: &str =
    "trust-cg.ay_sat_helper_replacement.proof_facts.v1";

/// Metadata key prefix for required SAT helper proof facts.
pub const AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_METADATA_PREFIX: &str = "ay_sat_helper.proof_fact.";

/// Canonical native payload digest bound to the contains-helper manifest evidence.
pub const AY_SAT_CONTAINS4_MASKED_NATIVE_PAYLOAD_SHA256: &str =
    "sha256:ay-sat-contains4-masked-native-payload";

/// Canonical proof-report digest bound to the contains-helper manifest evidence.
pub const AY_SAT_CONTAINS4_MASKED_PROOF_REPORT_SHA256: &str =
    "sha256:ay-sat-contains4-masked-proof-report";

/// Canonical native payload digest bound to the minimization manifest evidence.
pub const AY_SAT_MINIMIZE_KEEP_DROP_NATIVE_PAYLOAD_SHA256: &str =
    "sha256:ay-sat-minimize-keep-drop-native-payload";

/// Canonical proof-report digest bound to the minimization manifest evidence.
pub const AY_SAT_MINIMIZE_KEEP_DROP_PROOF_REPORT_SHA256: &str =
    "sha256:ay-sat-minimize-keep-drop-proof-report";

/// Canonical native payload digest bound to the theory-dispatch manifest evidence.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_NATIVE_PAYLOAD_SHA256: &str =
    "sha256:ay-sat-theory-dispatch-assignment-native-payload";

/// Canonical proof-report digest bound to the theory-dispatch manifest evidence.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_PROOF_REPORT_SHA256: &str =
    "sha256:ay-sat-theory-dispatch-assignment-proof-report";

/// Callable helper symbol named by the contract.
pub const AY_SAT_CONTAINS4_MASKED_SYMBOL: &str = "ay_sat_contains4_masked";

/// Artifact id for the canonical contains-helper manifest.
pub const AY_SAT_CONTAINS4_MASKED_ARTIFACT_ID: &str = "ay-sat-contains4-masked-helper";

/// Kernel metadata id.
pub const AY_SAT_HELPER_REPLACEMENT_KERNEL: &str = "ay_sat_contains4_masked";

/// Consumer metadata id.
pub const AY_SAT_HELPER_REPLACEMENT_CONSUMER: &str = "ay";

/// Domain metadata id.
pub const AY_SAT_HELPER_REPLACEMENT_DOMAIN: &str = "sat";

/// Proof family metadata id.
pub const AY_SAT_HELPER_REPLACEMENT_PROOF_FAMILY: &str = "ay-sat-helper-replacement";

/// Rust wrapper/layout identity for the LP64 contains helper.
pub const AY_SAT_CONTAINS4_MASKED_WRAPPER_IDENTITY: &str =
    "ay::sat::Contains4MaskedHelper::lp64:v1";

/// Reference oracle used by differential evidence.
pub const AY_SAT_CONTAINS4_MASKED_REFERENCE_ORACLE: &str =
    "rust_contains4_masked_and_contains_literal_reference";

/// Argument ABI record name.
pub const AY_SAT_CONTAINS4_MASKED_ARGS_RECORD: &str = "AYSatContains4MaskedArgsAbi";

/// Result ABI record name.
pub const AY_SAT_CONTAINS4_MASKED_RESULT_RECORD: &str = "AYSatContains4MaskedResultAbi";

/// Stable argument ABI metadata id.
pub const AY_SAT_CONTAINS4_MASKED_ARGS_ABI: &str = "ay_sat_contains4_masked_args_abi_v1";

/// Stable result ABI metadata id.
pub const AY_SAT_CONTAINS4_MASKED_RESULT_ABI: &str = "ay_sat_contains4_masked_result_abi_v1";

/// Source invalidation fingerprint for the canonical SAT helper contract.
pub const AY_SAT_CONTAINS4_MASKED_SOURCE_FINGERPRINT: &str = "ay:sat:contains4-masked:helper-v1";

/// Compiler/profile invalidation fingerprint for the canonical helper.
pub const AY_SAT_CONTAINS4_MASKED_COMPILER_FINGERPRINT: &str =
    "trust-cg:phase7:sat:contains4-masked:o2";

/// Default non-promoting generation for the pure contract fixture.
pub const AY_SAT_CONTAINS4_MASKED_DEFAULT_GENERATION: u64 = 801;

/// Canonical pre-product text size used by the manifest contract.
pub const AY_SAT_CONTAINS4_MASKED_TEXT_SIZE_BYTES: u64 = 192;

/// Argument ABI record size.
pub const AY_SAT_CONTAINS4_MASKED_ARGS_SIZE_BYTES: u64 = 24;

/// Result ABI record size.
pub const AY_SAT_CONTAINS4_MASKED_RESULT_SIZE_BYTES: u64 = 4;

/// Callable minimization classifier symbol named by the contract.
pub const AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL: &str = "ay_sat_minimize_keep_drop_classify";

/// Artifact id for the canonical minimization classifier manifest.
pub const AY_SAT_MINIMIZE_KEEP_DROP_ARTIFACT_ID: &str = "ay-sat-minimize-keep-drop-helper";

/// Kernel metadata id for the minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_KERNEL: &str = "ay_sat_minimize_keep_drop_classify";

/// Rust wrapper/layout identity for the LP64 minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_WRAPPER_IDENTITY: &str =
    "ay::sat::MinimizeKeepDropClassifier::lp64:v1";

/// Reference oracle used by minimization differential evidence.
pub const AY_SAT_MINIMIZE_KEEP_DROP_REFERENCE_ORACLE: &str =
    "rust_minimize_keep_drop_classification_reference";

/// Argument ABI record name for the minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD: &str = "AYSatMinimizeKeepDropArgsAbi";

/// Result ABI record name for the minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_RESULT_RECORD: &str = "AYSatMinimizeKeepDropResultAbi";

/// Stable argument ABI metadata id for the minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_ARGS_ABI: &str = "ay_sat_minimize_keep_drop_args_abi_v1";

/// Stable result ABI metadata id for the minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_RESULT_ABI: &str = "ay_sat_minimize_keep_drop_result_abi_v1";

/// Source invalidation fingerprint for the minimization classifier contract.
pub const AY_SAT_MINIMIZE_KEEP_DROP_SOURCE_FINGERPRINT: &str =
    "ay:sat:minimize-keep-drop:helper-v1";

/// Compiler/profile invalidation fingerprint for the minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_COMPILER_FINGERPRINT: &str =
    "trust-cg:phase7:sat:minimize-keep-drop:o2";

/// Default non-promoting generation for the minimization contract fixture.
pub const AY_SAT_MINIMIZE_KEEP_DROP_DEFAULT_GENERATION: u64 = 802;

/// Canonical pre-product text size used by the minimization manifest contract.
pub const AY_SAT_MINIMIZE_KEEP_DROP_TEXT_SIZE_BYTES: u64 = 224;

/// Argument ABI record size for the minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_ARGS_SIZE_BYTES: u64 = 28;

/// Result ABI record size for the minimization classifier.
pub const AY_SAT_MINIMIZE_KEEP_DROP_RESULT_SIZE_BYTES: u64 = 4;

/// Classification value: literal is redundant and can be dropped/skipped.
pub const AY_SAT_MINIMIZE_CLASSIFY_DROP: i32 = 0;

/// Classification value: literal must be kept and minimization aborts.
pub const AY_SAT_MINIMIZE_CLASSIFY_KEEP: i32 = 1;

/// Classification value: literal needs recursive redundancy checking.
pub const AY_SAT_MINIMIZE_CLASSIFY_CHECK: i32 = 2;

/// ay SAT minimize flag: poisoned/non-removable literal.
pub const AY_SAT_MINIMIZE_MIN_POISON_FLAG: i32 = 0x01;

/// ay SAT minimize flag: cached removable literal.
pub const AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG: i32 = 0x02;

/// ay SAT minimize flag: cached keep literal.
pub const AY_SAT_MINIMIZE_MIN_KEEP_FLAG: i32 = 0x08;

/// ay SAT reason sentinel for decision variables.
pub const AY_SAT_MINIMIZE_NO_REASON: i32 = -1;

/// Callable theory-dispatch assignment helper symbol named by the contract.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL: &str = "ay_sat_theory_dispatch_assignment";

/// Artifact id for the canonical theory-dispatch assignment manifest.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARTIFACT_ID: &str =
    "ay-sat-theory-dispatch-assignment-helper";

/// Kernel metadata id for the theory-dispatch assignment helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_KERNEL: &str = "ay_sat_theory_dispatch_assignment";

/// Rust wrapper/layout identity for the LP64 theory-dispatch helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_WRAPPER_IDENTITY: &str =
    "ay::sat::TheoryDispatchAssignmentHelper::lp64:v1";

/// Reference oracle used by theory-dispatch differential evidence.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_REFERENCE_ORACLE: &str =
    "local_private_theory_dispatch_dispatch_assignment_reference";

/// Argument ABI record name for the theory-dispatch helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_RECORD: &str =
    "AYSatTheoryDispatchAssignmentArgsAbi";

/// Result ABI record name for the theory-dispatch helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_RECORD: &str =
    "AYSatTheoryDispatchAssignmentResultAbi";

/// Stable argument ABI metadata id for the theory-dispatch helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_ABI: &str =
    "ay_sat_theory_dispatch_assignment_args_abi_v1";

/// Stable result ABI metadata id for the theory-dispatch helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_ABI: &str =
    "ay_sat_theory_dispatch_assignment_result_abi_v1";

/// Source invalidation fingerprint for the theory-dispatch helper contract.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SOURCE_FINGERPRINT: &str =
    "ay:sat:theory-dispatch-assignment:helper-v1";

/// Compiler/profile invalidation fingerprint for the theory-dispatch helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_COMPILER_FINGERPRINT: &str =
    "trust-cg:phase7:sat:theory-dispatch-assignment:o2";

/// Default non-promoting generation for the theory-dispatch contract fixture.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_DEFAULT_GENERATION: u64 = 803;

/// Canonical pre-product text size used by the theory-dispatch manifest contract.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_TEXT_SIZE_BYTES: u64 = 256;

/// Argument ABI record size for the theory-dispatch helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_SIZE_BYTES: u64 = 28;

/// Result ABI record size for the theory-dispatch helper.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_SIZE_BYTES: u64 = 8;

/// Dispatch status: variable is absent from the table and must be skipped.
pub const AY_SAT_THEORY_DISPATCH_STATUS_SKIP: i32 = 0;

/// Dispatch status: theory atom should be asserted immediately.
pub const AY_SAT_THEORY_DISPATCH_STATUS_ASSERT: i32 = 1;

/// Dispatch status: ITE-guarded atom is in an inactive branch and is deferred.
pub const AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE: i32 = 2;

/// Sentinel matching ay's `u32::MAX` no-ITE-guard encoding.
pub const AY_SAT_THEORY_DISPATCH_NO_ITE_COND_VAR: i32 = -1;

/// Guard flag: entry has an ITE condition guard.
pub const AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED: i32 = 0x01;

/// Guard flag: guarded entry belongs to the ITE then branch.
pub const AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH: i32 = 0x02;

/// Guard flag: condition assignment is currently known.
pub const AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED: i32 = 0x04;

/// Guard flag: condition assignment value is true.
pub const AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE: i32 = 0x08;

/// Low bits occupied by the packed theory-dispatch status.
pub const AY_SAT_THEORY_DISPATCH_RESULT_STATUS_MASK: u64 = 0x3;

/// Packed result bit carrying the normalized assignment value.
pub const AY_SAT_THEORY_DISPATCH_RESULT_VALUE_BIT: u64 = 1 << 2;

/// Packed result shift for the dispatched term id.
pub const AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT: u32 = 32;

/// Typed SAT helper replacement proof fact required by the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYSatHelperReplacementProofFact {
    /// Lane equality uses exact i32 literal identity.
    LaneEquality,
    /// Valid-mask bits gate each lane and upper mask bits are ignored.
    ValidMaskLaneBounds,
    /// Padded sentinel lanes are ignored when their valid-mask bit is clear.
    PaddedSentinelMasking,
    /// OR-folding chunk masks implements `contains_literal`.
    ContainsLiteralChunkFold,
    /// Helper, reference, and replay artifacts compare equal.
    ReplayComparison,
}

impl AYSatHelperReplacementProofFact {
    /// Return the stable lower-snake-case fact id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LaneEquality => "lane_equality",
            Self::ValidMaskLaneBounds => "valid_mask_lane_bounds",
            Self::PaddedSentinelMasking => "padded_sentinel_masking",
            Self::ContainsLiteralChunkFold => "contains_literal_chunk_fold",
            Self::ReplayComparison => "replay_comparison",
        }
    }

    /// Return the stable proof-evidence metadata key for this fact.
    pub fn metadata_key(self) -> String {
        format!(
            "{AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_METADATA_PREFIX}{}",
            self.as_str()
        )
    }
}

/// One required SAT helper proof-fact metadata binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYSatHelperReplacementProofFactRequirement {
    /// Required proof fact.
    pub fact: AYSatHelperReplacementProofFact,
    /// Stable lemma or checker id expected from proof evidence.
    pub lemma_id: &'static str,
}

/// Required SAT helper proof facts in canonical metadata order.
pub const AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_REQUIREMENTS:
    [AYSatHelperReplacementProofFactRequirement; 5] = [
    AYSatHelperReplacementProofFactRequirement {
        fact: AYSatHelperReplacementProofFact::LaneEquality,
        lemma_id: "ay_sat_helper.contains4_lane_equality_i32",
    },
    AYSatHelperReplacementProofFactRequirement {
        fact: AYSatHelperReplacementProofFact::ValidMaskLaneBounds,
        lemma_id: "ay_sat_helper.contains4_valid_mask_lane_bounds",
    },
    AYSatHelperReplacementProofFactRequirement {
        fact: AYSatHelperReplacementProofFact::PaddedSentinelMasking,
        lemma_id: "ay_sat_helper.contains4_padded_sentinel_masking",
    },
    AYSatHelperReplacementProofFactRequirement {
        fact: AYSatHelperReplacementProofFact::ContainsLiteralChunkFold,
        lemma_id: "ay_sat_helper.contains_literal_chunk_or_fold",
    },
    AYSatHelperReplacementProofFactRequirement {
        fact: AYSatHelperReplacementProofFact::ReplayComparison,
        lemma_id: "trust_cg_ay_sat_helper.replay_helper_reference_equal",
    },
];

/// Return the stable comma-separated required proof fact ids.
pub fn ay_sat_helper_replacement_required_fact_csv() -> String {
    AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_REQUIREMENTS
        .iter()
        .map(|requirement| requirement.fact.as_str())
        .collect::<Vec<_>>()
        .join(",")
}

/// Insert canonical SAT helper proof-fact metadata.
pub fn insert_ay_sat_helper_replacement_proof_fact_metadata(
    metadata: &mut BTreeMap<String, String>,
) {
    metadata.insert(
        "proof_fact_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "required_proof_facts".to_owned(),
        ay_sat_helper_replacement_required_fact_csv(),
    );
    for requirement in AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_REQUIREMENTS {
        metadata.insert(
            requirement.fact.metadata_key(),
            requirement.lemma_id.to_owned(),
        );
    }
}

/// Return true when a metadata map carries the canonical required facts.
pub fn ay_sat_helper_replacement_proof_fact_metadata_matches(
    metadata: &BTreeMap<String, String>,
) -> bool {
    metadata.get("proof_fact_schema").map(String::as_str)
        == Some(AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA)
        && metadata.get("required_proof_facts").map(String::as_str)
            == Some(ay_sat_helper_replacement_required_fact_csv().as_str())
        && AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_REQUIREMENTS
            .iter()
            .all(|requirement| {
                metadata
                    .get(&requirement.fact.metadata_key())
                    .map(String::as_str)
                    == Some(requirement.lemma_id)
            })
}

/// Typed SAT minimization helper proof fact required by the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYSatMinimizeKeepDropProofFact {
    /// Level-zero literals are redundant and classify as drop.
    LevelZeroDrop,
    /// Cached removable/keep flags classify as drop without recursion.
    CachedDropFlags,
    /// Cached poison flags classify as keep/abort.
    PoisonKeepAbort,
    /// Current decision-level and decision-variable literals classify as keep.
    DecisionKeepAbort,
    /// Seen-count and trail-position guards preserve early abort semantics.
    ReasonTrailGuards,
    /// Helper, reference, and replay artifacts compare equal.
    ReplayComparison,
}

impl AYSatMinimizeKeepDropProofFact {
    /// Return the stable lower-snake-case fact id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LevelZeroDrop => "level_zero_drop",
            Self::CachedDropFlags => "cached_drop_flags",
            Self::PoisonKeepAbort => "poison_keep_abort",
            Self::DecisionKeepAbort => "decision_keep_abort",
            Self::ReasonTrailGuards => "reason_trail_guards",
            Self::ReplayComparison => "replay_comparison",
        }
    }

    /// Return the stable proof-evidence metadata key for this fact.
    pub fn metadata_key(self) -> String {
        format!(
            "{AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_METADATA_PREFIX}minimize.{}",
            self.as_str()
        )
    }
}

/// One required SAT minimization helper proof-fact metadata binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYSatMinimizeKeepDropProofFactRequirement {
    /// Required proof fact.
    pub fact: AYSatMinimizeKeepDropProofFact,
    /// Stable lemma or checker id expected from proof evidence.
    pub lemma_id: &'static str,
}

/// Required SAT minimization helper proof facts in canonical metadata order.
pub const AY_SAT_MINIMIZE_KEEP_DROP_PROOF_FACT_REQUIREMENTS:
    [AYSatMinimizeKeepDropProofFactRequirement; 6] = [
    AYSatMinimizeKeepDropProofFactRequirement {
        fact: AYSatMinimizeKeepDropProofFact::LevelZeroDrop,
        lemma_id: "ay_sat_helper.minimize_level_zero_drop",
    },
    AYSatMinimizeKeepDropProofFactRequirement {
        fact: AYSatMinimizeKeepDropProofFact::CachedDropFlags,
        lemma_id: "ay_sat_helper.minimize_cached_removable_or_keep_drop",
    },
    AYSatMinimizeKeepDropProofFactRequirement {
        fact: AYSatMinimizeKeepDropProofFact::PoisonKeepAbort,
        lemma_id: "ay_sat_helper.minimize_poison_keep_abort",
    },
    AYSatMinimizeKeepDropProofFactRequirement {
        fact: AYSatMinimizeKeepDropProofFact::DecisionKeepAbort,
        lemma_id: "ay_sat_helper.minimize_decision_keep_abort",
    },
    AYSatMinimizeKeepDropProofFactRequirement {
        fact: AYSatMinimizeKeepDropProofFact::ReasonTrailGuards,
        lemma_id: "ay_sat_helper.minimize_reason_trail_guards",
    },
    AYSatMinimizeKeepDropProofFactRequirement {
        fact: AYSatMinimizeKeepDropProofFact::ReplayComparison,
        lemma_id: "trust_cg_ay_sat_helper.minimize_replay_reference_equal",
    },
];

/// Return the stable comma-separated required minimization proof fact ids.
pub fn ay_sat_minimize_keep_drop_required_fact_csv() -> String {
    AY_SAT_MINIMIZE_KEEP_DROP_PROOF_FACT_REQUIREMENTS
        .iter()
        .map(|requirement| requirement.fact.as_str())
        .collect::<Vec<_>>()
        .join(",")
}

/// Insert canonical SAT minimization proof-fact metadata.
pub fn insert_ay_sat_minimize_keep_drop_proof_fact_metadata(
    metadata: &mut BTreeMap<String, String>,
) {
    metadata.insert(
        "proof_fact_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "required_proof_facts".to_owned(),
        ay_sat_minimize_keep_drop_required_fact_csv(),
    );
    for requirement in AY_SAT_MINIMIZE_KEEP_DROP_PROOF_FACT_REQUIREMENTS {
        metadata.insert(
            requirement.fact.metadata_key(),
            requirement.lemma_id.to_owned(),
        );
    }
}

/// Return true when a metadata map carries the required minimization facts.
pub fn ay_sat_minimize_keep_drop_proof_fact_metadata_matches(
    metadata: &BTreeMap<String, String>,
) -> bool {
    metadata.get("proof_fact_schema").map(String::as_str)
        == Some(AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA)
        && metadata.get("required_proof_facts").map(String::as_str)
            == Some(ay_sat_minimize_keep_drop_required_fact_csv().as_str())
        && AY_SAT_MINIMIZE_KEEP_DROP_PROOF_FACT_REQUIREMENTS
            .iter()
            .all(|requirement| {
                metadata
                    .get(&requirement.fact.metadata_key())
                    .map(String::as_str)
                    == Some(requirement.lemma_id)
            })
}

/// Typed SAT theory-dispatch helper proof fact required by the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYSatTheoryDispatchProofFact {
    /// Out-of-bounds or absent table entries classify as skip.
    TableLookupBounds,
    /// Present entries preserve the table-provided theory term id.
    EntryTermPassthrough,
    /// Assignment truth values are normalized to bool and preserved.
    AssignmentValuePassthrough,
    /// Assigned ITE conditions selecting the opposite branch classify as defer.
    IteInactiveBranchDeferral,
    /// Unassigned ITE conditions assert normally.
    IteUnassignedConditionAssert,
    /// Level-zero ITE assignments assert normally even for inactive branches.
    LevelZeroAssert,
    /// Helper, reference, and replay artifacts compare equal.
    ReplayComparison,
}

impl AYSatTheoryDispatchProofFact {
    /// Return the stable lower-snake-case fact id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TableLookupBounds => "table_lookup_bounds",
            Self::EntryTermPassthrough => "entry_term_passthrough",
            Self::AssignmentValuePassthrough => "assignment_value_passthrough",
            Self::IteInactiveBranchDeferral => "ite_inactive_branch_deferral",
            Self::IteUnassignedConditionAssert => "ite_unassigned_condition_assert",
            Self::LevelZeroAssert => "level_zero_assert",
            Self::ReplayComparison => "replay_comparison",
        }
    }

    /// Return the stable proof-evidence metadata key for this fact.
    pub fn metadata_key(self) -> String {
        format!(
            "{AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_METADATA_PREFIX}theory_dispatch.{}",
            self.as_str()
        )
    }
}

/// One required SAT theory-dispatch helper proof-fact metadata binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYSatTheoryDispatchProofFactRequirement {
    /// Required proof fact.
    pub fact: AYSatTheoryDispatchProofFact,
    /// Stable lemma or checker id expected from proof evidence.
    pub lemma_id: &'static str,
}

/// Required SAT theory-dispatch helper proof facts in canonical metadata order.
pub const AY_SAT_THEORY_DISPATCH_ASSIGNMENT_PROOF_FACT_REQUIREMENTS:
    [AYSatTheoryDispatchProofFactRequirement; 7] = [
    AYSatTheoryDispatchProofFactRequirement {
        fact: AYSatTheoryDispatchProofFact::TableLookupBounds,
        lemma_id: "ay_sat_helper.theory_dispatch_table_lookup_bounds",
    },
    AYSatTheoryDispatchProofFactRequirement {
        fact: AYSatTheoryDispatchProofFact::EntryTermPassthrough,
        lemma_id: "ay_sat_helper.theory_dispatch_entry_term_passthrough",
    },
    AYSatTheoryDispatchProofFactRequirement {
        fact: AYSatTheoryDispatchProofFact::AssignmentValuePassthrough,
        lemma_id: "ay_sat_helper.theory_dispatch_assignment_value_passthrough",
    },
    AYSatTheoryDispatchProofFactRequirement {
        fact: AYSatTheoryDispatchProofFact::IteInactiveBranchDeferral,
        lemma_id: "ay_sat_helper.theory_dispatch_ite_inactive_branch_deferral",
    },
    AYSatTheoryDispatchProofFactRequirement {
        fact: AYSatTheoryDispatchProofFact::IteUnassignedConditionAssert,
        lemma_id: "ay_sat_helper.theory_dispatch_ite_unassigned_condition_assert",
    },
    AYSatTheoryDispatchProofFactRequirement {
        fact: AYSatTheoryDispatchProofFact::LevelZeroAssert,
        lemma_id: "ay_sat_helper.theory_dispatch_level_zero_assert",
    },
    AYSatTheoryDispatchProofFactRequirement {
        fact: AYSatTheoryDispatchProofFact::ReplayComparison,
        lemma_id: "trust_cg_ay_sat_helper.theory_dispatch_replay_reference_equal",
    },
];

/// Return the stable comma-separated required theory-dispatch proof fact ids.
pub fn ay_sat_theory_dispatch_assignment_required_fact_csv() -> String {
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_PROOF_FACT_REQUIREMENTS
        .iter()
        .map(|requirement| requirement.fact.as_str())
        .collect::<Vec<_>>()
        .join(",")
}

/// Insert canonical SAT theory-dispatch proof-fact metadata.
pub fn insert_ay_sat_theory_dispatch_assignment_proof_fact_metadata(
    metadata: &mut BTreeMap<String, String>,
) {
    metadata.insert(
        "proof_fact_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "required_proof_facts".to_owned(),
        ay_sat_theory_dispatch_assignment_required_fact_csv(),
    );
    for requirement in AY_SAT_THEORY_DISPATCH_ASSIGNMENT_PROOF_FACT_REQUIREMENTS {
        metadata.insert(
            requirement.fact.metadata_key(),
            requirement.lemma_id.to_owned(),
        );
    }
}

/// Return true when a metadata map carries the required theory-dispatch facts.
pub fn ay_sat_theory_dispatch_assignment_proof_fact_metadata_matches(
    metadata: &BTreeMap<String, String>,
) -> bool {
    metadata.get("proof_fact_schema").map(String::as_str)
        == Some(AY_SAT_HELPER_REPLACEMENT_PROOF_FACT_SCHEMA)
        && metadata.get("required_proof_facts").map(String::as_str)
            == Some(ay_sat_theory_dispatch_assignment_required_fact_csv().as_str())
        && AY_SAT_THEORY_DISPATCH_ASSIGNMENT_PROOF_FACT_REQUIREMENTS
            .iter()
            .all(|requirement| {
                metadata
                    .get(&requirement.fact.metadata_key())
                    .map(String::as_str)
                    == Some(requirement.lemma_id)
            })
}

/// Build the canonical `extern "C"` masked contains4 helper signature.
pub fn ay_sat_contains4_masked_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
        ],
        vec![AbiValue::new(AbiValueKind::I32)],
    )
}

/// Build the host-OS AArch64 target descriptor for this contract.
pub fn ay_sat_contains4_masked_aarch64_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::Aarch64, target_os_descriptor())
        .with_cpu("aarch64-ay-test")
        .with_features(["fp", "simd"])
}

/// Build the canonical AAPCS64/LP64 ABI descriptor for this contract.
pub fn ay_sat_contains4_masked_aarch64_abi() -> AbiDescriptor {
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-sat-contains4-aapcs64-lp64".to_owned();
    abi
}

/// Build the argument ABI record layout.
pub fn ay_sat_contains4_masked_args_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_SAT_CONTAINS4_MASKED_ARGS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_SAT_CONTAINS4_MASKED_ARGS_SIZE_BYTES,
        alignment_bytes: 4,
        fields: vec![
            field("lane0", 0, 4, 4),
            field("lane1", 4, 4, 4),
            field("lane2", 8, 4, 4),
            field("lane3", 12, 4, 4),
            field("literal", 16, 4, 4),
            field("valid_mask", 20, 4, 4),
        ],
    }
}

/// Build the result ABI record layout.
pub fn ay_sat_contains4_masked_result_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_SAT_CONTAINS4_MASKED_RESULT_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_SAT_CONTAINS4_MASKED_RESULT_SIZE_BYTES,
        alignment_bytes: 4,
        fields: vec![field("match_mask", 0, 4, 4)],
    }
}

/// Build the canonical LP64 layout manifest.
pub fn ay_sat_contains4_masked_layout() -> LayoutManifest {
    ay_sat_contains4_masked_layout_with_text_size(16, AY_SAT_CONTAINS4_MASKED_TEXT_SIZE_BYTES)
}

/// Build an LP64 layout manifest with caller-specified stack alignment and text size.
pub fn ay_sat_contains4_masked_layout_with_text_size(
    stack_alignment_bytes: u16,
    text_size_bytes: u64,
) -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, stack_alignment_bytes);
    layout.wrapper_identity = Some(AY_SAT_CONTAINS4_MASKED_WRAPPER_IDENTITY.to_owned());
    layout
        .records
        .push(ay_sat_contains4_masked_args_record_layout());
    layout
        .records
        .push(ay_sat_contains4_masked_result_record_layout());
    layout.symbols.push(SymbolLayout {
        name: AY_SAT_CONTAINS4_MASKED_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
    });
    insert_ay_sat_helper_replacement_layout_metadata(&mut layout.metadata);
    layout
}

/// Build the non-promoting proof policy for SAT helper replacement artifacts.
///
/// The manifest remains compile-service compatible for this pre-product slice;
/// proof evidence is still required by the symbol lookup contract and native
/// install-gate packet.
pub fn ay_sat_contains4_masked_proof_policy() -> ProofPolicy {
    ProofPolicy::disabled()
}

/// Build the default invalidation key for the canonical AArch64 contract.
pub fn ay_sat_contains4_masked_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    ay_sat_contains4_masked_invalidation_with_generation(
        target,
        abi,
        layout,
        proof_policy,
        AY_SAT_CONTAINS4_MASKED_DEFAULT_GENERATION,
    )
}

/// Build an invalidation key for a caller-specified generation.
pub fn ay_sat_contains4_masked_invalidation_with_generation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
    generation: u64,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        AY_SAT_CONTAINS4_MASKED_SOURCE_FINGERPRINT,
        AY_SAT_CONTAINS4_MASKED_COMPILER_FINGERPRINT,
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        generation,
    );
    insert_ay_sat_helper_replacement_invalidation_metadata(&mut invalidation.extra);
    invalidation
}

/// Build the canonical non-promoting AArch64 artifact manifest.
pub fn ay_sat_contains4_masked_manifest() -> DeterministicArtifactManifest {
    ay_sat_contains4_masked_manifest_with_generation(AY_SAT_CONTAINS4_MASKED_DEFAULT_GENERATION)
}

/// Build the canonical AArch64 artifact manifest for a caller-specified generation.
pub fn ay_sat_contains4_masked_manifest_with_generation(
    generation: u64,
) -> DeterministicArtifactManifest {
    let target = ay_sat_contains4_masked_aarch64_target();
    let abi = ay_sat_contains4_masked_aarch64_abi();
    let layout = ay_sat_contains4_masked_layout();
    let proof_policy = ay_sat_contains4_masked_proof_policy();
    ay_sat_contains4_masked_manifest_for_parts(
        target,
        abi,
        layout,
        proof_policy,
        generation,
        AY_SAT_CONTAINS4_MASKED_TEXT_SIZE_BYTES,
    )
}

/// Build a manifest from explicit contract parts.
pub fn ay_sat_contains4_masked_manifest_for_parts(
    target: TargetDescriptor,
    abi: AbiDescriptor,
    layout: LayoutManifest,
    proof_policy: ProofPolicy,
    generation: u64,
    text_size_bytes: u64,
) -> DeterministicArtifactManifest {
    let text_size_bytes = ay_sat_contains4_masked_layout_text_size_bytes(&layout, text_size_bytes);
    let invalidation = ay_sat_contains4_masked_invalidation_with_generation(
        &target,
        &abi,
        &layout,
        &proof_policy,
        generation,
    );
    let mut manifest = DeterministicArtifactManifest::new(
        AY_SAT_CONTAINS4_MASKED_ARTIFACT_ID,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: AY_SAT_CONTAINS4_MASKED_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_sat_contains4_masked_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
        checksum: None,
    });
    insert_ay_sat_helper_replacement_manifest_metadata(&mut manifest.metadata);
    manifest
}

fn ay_sat_contains4_masked_layout_text_size_bytes(layout: &LayoutManifest, fallback: u64) -> u64 {
    layout
        .symbols
        .iter()
        .find(|symbol| symbol.name == AY_SAT_CONTAINS4_MASKED_SYMBOL && symbol.section == ".text")
        .map(|symbol| symbol.size_bytes)
        .unwrap_or(fallback)
}

/// Build verified proof-evidence summary bound to a SAT helper manifest.
pub fn ay_sat_contains4_masked_verified_proof_evidence(
    verifier: impl Into<String>,
    manifest: &DeterministicArtifactManifest,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        verifier,
        manifest,
        AY_SAT_CONTAINS4_MASKED_NATIVE_PAYLOAD_SHA256,
        AY_SAT_CONTAINS4_MASKED_PROOF_REPORT_SHA256,
    );
    insert_ay_sat_helper_replacement_evidence_metadata(&mut evidence.metadata);
    evidence
}

/// Build the symbol lookup contract for the SAT contains-helper symbol.
pub fn ay_sat_contains4_masked_symbol_lookup_contract(
    manifest: &DeterministicArtifactManifest,
    proof_evidence: ProofEvidenceSummary,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        AY_SAT_CONTAINS4_MASKED_SYMBOL,
        ay_sat_contains4_masked_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_required_proof_evidence()
    .with_proof_evidence(proof_evidence)
}

/// Build the canonical `extern "C"` minimization keep/drop classifier signature.
pub fn ay_sat_minimize_keep_drop_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
        ],
        vec![AbiValue::new(AbiValueKind::I32)],
    )
}

/// Build the host-OS AArch64 target descriptor for the minimization contract.
pub fn ay_sat_minimize_keep_drop_aarch64_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::Aarch64, target_os_descriptor())
        .with_cpu("aarch64-ay-test")
        .with_features(["fp", "simd"])
}

/// Build the canonical AAPCS64/LP64 ABI descriptor for this contract.
pub fn ay_sat_minimize_keep_drop_aarch64_abi() -> AbiDescriptor {
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-sat-minimize-classify-aapcs64-lp64".to_owned();
    abi
}

/// Build the minimization argument ABI record layout.
pub fn ay_sat_minimize_keep_drop_args_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_SAT_MINIMIZE_KEEP_DROP_ARGS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_SAT_MINIMIZE_KEEP_DROP_ARGS_SIZE_BYTES,
        alignment_bytes: 4,
        fields: vec![
            field("var_level", 0, 4, 4),
            field("trail_pos", 4, 4, 4),
            field("reason", 8, 4, 4),
            field("min_flags", 12, 4, 4),
            field("level_seen_count", 16, 4, 4),
            field("level_seen_trail", 20, 4, 4),
            field("decision_level", 24, 4, 4),
        ],
    }
}

/// Build the minimization result ABI record layout.
pub fn ay_sat_minimize_keep_drop_result_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_SAT_MINIMIZE_KEEP_DROP_RESULT_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_SAT_MINIMIZE_KEEP_DROP_RESULT_SIZE_BYTES,
        alignment_bytes: 4,
        fields: vec![field("classification", 0, 4, 4)],
    }
}

/// Build the canonical LP64 minimization layout manifest.
pub fn ay_sat_minimize_keep_drop_layout() -> LayoutManifest {
    ay_sat_minimize_keep_drop_layout_with_text_size(16, AY_SAT_MINIMIZE_KEEP_DROP_TEXT_SIZE_BYTES)
}

/// Build an LP64 minimization layout with caller-specified stack/text sizes.
pub fn ay_sat_minimize_keep_drop_layout_with_text_size(
    stack_alignment_bytes: u16,
    text_size_bytes: u64,
) -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, stack_alignment_bytes);
    layout.wrapper_identity = Some(AY_SAT_MINIMIZE_KEEP_DROP_WRAPPER_IDENTITY.to_owned());
    layout
        .records
        .push(ay_sat_minimize_keep_drop_args_record_layout());
    layout
        .records
        .push(ay_sat_minimize_keep_drop_result_record_layout());
    layout.symbols.push(SymbolLayout {
        name: AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
    });
    insert_ay_sat_minimize_keep_drop_layout_metadata(&mut layout.metadata);
    layout
}

/// Build the non-promoting proof policy for minimization helper artifacts.
pub fn ay_sat_minimize_keep_drop_proof_policy() -> ProofPolicy {
    ProofPolicy::disabled()
}

/// Build the default invalidation key for the canonical minimization contract.
pub fn ay_sat_minimize_keep_drop_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    ay_sat_minimize_keep_drop_invalidation_with_generation(
        target,
        abi,
        layout,
        proof_policy,
        AY_SAT_MINIMIZE_KEEP_DROP_DEFAULT_GENERATION,
    )
}

/// Build an invalidation key for a caller-specified minimization generation.
pub fn ay_sat_minimize_keep_drop_invalidation_with_generation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
    generation: u64,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        AY_SAT_MINIMIZE_KEEP_DROP_SOURCE_FINGERPRINT,
        AY_SAT_MINIMIZE_KEEP_DROP_COMPILER_FINGERPRINT,
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        generation,
    );
    insert_ay_sat_minimize_keep_drop_invalidation_metadata(&mut invalidation.extra);
    invalidation
}

/// Build the canonical non-promoting AArch64 minimization artifact manifest.
pub fn ay_sat_minimize_keep_drop_manifest() -> DeterministicArtifactManifest {
    ay_sat_minimize_keep_drop_manifest_with_generation(AY_SAT_MINIMIZE_KEEP_DROP_DEFAULT_GENERATION)
}

/// Build the canonical minimization manifest for a caller-specified generation.
pub fn ay_sat_minimize_keep_drop_manifest_with_generation(
    generation: u64,
) -> DeterministicArtifactManifest {
    let target = ay_sat_minimize_keep_drop_aarch64_target();
    let abi = ay_sat_minimize_keep_drop_aarch64_abi();
    let layout = ay_sat_minimize_keep_drop_layout();
    let proof_policy = ay_sat_minimize_keep_drop_proof_policy();
    ay_sat_minimize_keep_drop_manifest_for_parts(
        target,
        abi,
        layout,
        proof_policy,
        generation,
        AY_SAT_MINIMIZE_KEEP_DROP_TEXT_SIZE_BYTES,
    )
}

/// Build a minimization manifest from explicit contract parts.
pub fn ay_sat_minimize_keep_drop_manifest_for_parts(
    target: TargetDescriptor,
    abi: AbiDescriptor,
    layout: LayoutManifest,
    proof_policy: ProofPolicy,
    generation: u64,
    text_size_bytes: u64,
) -> DeterministicArtifactManifest {
    let text_size_bytes =
        ay_sat_minimize_keep_drop_layout_text_size_bytes(&layout, text_size_bytes);
    let invalidation = ay_sat_minimize_keep_drop_invalidation_with_generation(
        &target,
        &abi,
        &layout,
        &proof_policy,
        generation,
    );
    let mut manifest = DeterministicArtifactManifest::new(
        AY_SAT_MINIMIZE_KEEP_DROP_ARTIFACT_ID,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_sat_minimize_keep_drop_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
        checksum: None,
    });
    insert_ay_sat_minimize_keep_drop_manifest_metadata(&mut manifest.metadata);
    manifest
}

fn ay_sat_minimize_keep_drop_layout_text_size_bytes(layout: &LayoutManifest, fallback: u64) -> u64 {
    layout
        .symbols
        .iter()
        .find(|symbol| symbol.name == AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL && symbol.section == ".text")
        .map(|symbol| symbol.size_bytes)
        .unwrap_or(fallback)
}

/// Build verified proof-evidence summary bound to a minimization manifest.
pub fn ay_sat_minimize_keep_drop_verified_proof_evidence(
    verifier: impl Into<String>,
    manifest: &DeterministicArtifactManifest,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        verifier,
        manifest,
        AY_SAT_MINIMIZE_KEEP_DROP_NATIVE_PAYLOAD_SHA256,
        AY_SAT_MINIMIZE_KEEP_DROP_PROOF_REPORT_SHA256,
    );
    insert_ay_sat_minimize_keep_drop_evidence_metadata(&mut evidence.metadata);
    evidence
}

/// Build the symbol lookup contract for the minimization classifier symbol.
pub fn ay_sat_minimize_keep_drop_symbol_lookup_contract(
    manifest: &DeterministicArtifactManifest,
    proof_evidence: ProofEvidenceSummary,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL,
        ay_sat_minimize_keep_drop_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_required_proof_evidence()
    .with_proof_evidence(proof_evidence)
}

/// Build the canonical `extern "C"` theory-dispatch assignment signature.
pub fn ay_sat_theory_dispatch_assignment_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
            AbiValue::new(AbiValueKind::I32),
        ],
        vec![AbiValue::new(AbiValueKind::I64)],
    )
}

/// Build the host-OS AArch64 target descriptor for the theory-dispatch contract.
pub fn ay_sat_theory_dispatch_assignment_aarch64_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::Aarch64, target_os_descriptor())
        .with_cpu("aarch64-ay-test")
        .with_features(["fp", "simd"])
}

/// Build the canonical AAPCS64/LP64 ABI descriptor for this contract.
pub fn ay_sat_theory_dispatch_assignment_aarch64_abi() -> AbiDescriptor {
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-sat-theory-dispatch-aapcs64-lp64".to_owned();
    abi
}

/// Build the theory-dispatch argument ABI record layout.
pub fn ay_sat_theory_dispatch_assignment_args_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_SIZE_BYTES,
        alignment_bytes: 4,
        fields: vec![
            field("var_id", 0, 4, 4),
            field("table_len", 4, 4, 4),
            field("entry_present", 8, 4, 4),
            field("term_id", 12, 4, 4),
            field("assignment_value", 16, 4, 4),
            field("guard_flags", 20, 4, 4),
            field("decision_level", 24, 4, 4),
        ],
    }
}

/// Build the theory-dispatch packed result ABI record layout.
pub fn ay_sat_theory_dispatch_assignment_result_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_SIZE_BYTES,
        alignment_bytes: 8,
        fields: vec![field("packed_result", 0, 8, 8)],
    }
}

/// Build the canonical LP64 theory-dispatch layout manifest.
pub fn ay_sat_theory_dispatch_assignment_layout() -> LayoutManifest {
    ay_sat_theory_dispatch_assignment_layout_with_text_size(
        16,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_TEXT_SIZE_BYTES,
    )
}

/// Build an LP64 theory-dispatch layout with caller-specified stack/text sizes.
pub fn ay_sat_theory_dispatch_assignment_layout_with_text_size(
    stack_alignment_bytes: u16,
    text_size_bytes: u64,
) -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, stack_alignment_bytes);
    layout.wrapper_identity = Some(AY_SAT_THEORY_DISPATCH_ASSIGNMENT_WRAPPER_IDENTITY.to_owned());
    layout
        .records
        .push(ay_sat_theory_dispatch_assignment_args_record_layout());
    layout
        .records
        .push(ay_sat_theory_dispatch_assignment_result_record_layout());
    layout.symbols.push(SymbolLayout {
        name: AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
    });
    insert_ay_sat_theory_dispatch_assignment_layout_metadata(&mut layout.metadata);
    layout
}

/// Build the non-promoting proof policy for theory-dispatch helper artifacts.
///
/// The native install gate and typed symbol contract still require explicit
/// proof evidence for this child slice; the manifest policy remains disabled so
/// this helper cannot promote product status through compile-service policy.
pub fn ay_sat_theory_dispatch_assignment_proof_policy() -> ProofPolicy {
    ProofPolicy::disabled()
}

/// Build the default invalidation key for the canonical theory-dispatch contract.
pub fn ay_sat_theory_dispatch_assignment_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    ay_sat_theory_dispatch_assignment_invalidation_with_generation(
        target,
        abi,
        layout,
        proof_policy,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_DEFAULT_GENERATION,
    )
}

/// Build an invalidation key for a caller-specified theory-dispatch generation.
pub fn ay_sat_theory_dispatch_assignment_invalidation_with_generation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
    generation: u64,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SOURCE_FINGERPRINT,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_COMPILER_FINGERPRINT,
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        generation,
    );
    insert_ay_sat_theory_dispatch_assignment_invalidation_metadata(&mut invalidation.extra);
    invalidation
}

/// Build the canonical non-promoting AArch64 theory-dispatch artifact manifest.
pub fn ay_sat_theory_dispatch_assignment_manifest() -> DeterministicArtifactManifest {
    ay_sat_theory_dispatch_assignment_manifest_with_generation(
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_DEFAULT_GENERATION,
    )
}

/// Build the canonical theory-dispatch manifest for a caller-specified generation.
pub fn ay_sat_theory_dispatch_assignment_manifest_with_generation(
    generation: u64,
) -> DeterministicArtifactManifest {
    let target = ay_sat_theory_dispatch_assignment_aarch64_target();
    let abi = ay_sat_theory_dispatch_assignment_aarch64_abi();
    let layout = ay_sat_theory_dispatch_assignment_layout();
    let proof_policy = ay_sat_theory_dispatch_assignment_proof_policy();
    ay_sat_theory_dispatch_assignment_manifest_for_parts(
        target,
        abi,
        layout,
        proof_policy,
        generation,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_TEXT_SIZE_BYTES,
    )
}

/// Build a theory-dispatch manifest from explicit contract parts.
pub fn ay_sat_theory_dispatch_assignment_manifest_for_parts(
    target: TargetDescriptor,
    abi: AbiDescriptor,
    layout: LayoutManifest,
    proof_policy: ProofPolicy,
    generation: u64,
    text_size_bytes: u64,
) -> DeterministicArtifactManifest {
    let text_size_bytes =
        ay_sat_theory_dispatch_assignment_layout_text_size_bytes(&layout, text_size_bytes);
    let invalidation = ay_sat_theory_dispatch_assignment_invalidation_with_generation(
        &target,
        &abi,
        &layout,
        &proof_policy,
        generation,
    );
    let mut manifest = DeterministicArtifactManifest::new(
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARTIFACT_ID,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_sat_theory_dispatch_assignment_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: text_size_bytes,
        alignment_bytes: 16,
        checksum: None,
    });
    insert_ay_sat_theory_dispatch_assignment_manifest_metadata(&mut manifest.metadata);
    manifest
}

fn ay_sat_theory_dispatch_assignment_layout_text_size_bytes(
    layout: &LayoutManifest,
    fallback: u64,
) -> u64 {
    layout
        .symbols
        .iter()
        .find(|symbol| {
            symbol.name == AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL && symbol.section == ".text"
        })
        .map(|symbol| symbol.size_bytes)
        .unwrap_or(fallback)
}

/// Build verified proof-evidence summary bound to a theory-dispatch manifest.
pub fn ay_sat_theory_dispatch_assignment_verified_proof_evidence(
    verifier: impl Into<String>,
    manifest: &DeterministicArtifactManifest,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        verifier,
        manifest,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_NATIVE_PAYLOAD_SHA256,
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_PROOF_REPORT_SHA256,
    );
    insert_ay_sat_theory_dispatch_assignment_evidence_metadata(&mut evidence.metadata);
    evidence
}

/// Build the symbol lookup contract for the theory-dispatch assignment symbol.
pub fn ay_sat_theory_dispatch_assignment_symbol_lookup_contract(
    manifest: &DeterministicArtifactManifest,
    proof_evidence: ProofEvidenceSummary,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL,
        ay_sat_theory_dispatch_assignment_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_required_proof_evidence()
    .with_proof_evidence(proof_evidence)
}

fn target_os_descriptor() -> TargetOperatingSystem {
    if cfg!(target_os = "macos") {
        TargetOperatingSystem::Macos
    } else if cfg!(target_os = "linux") {
        TargetOperatingSystem::Linux
    } else {
        TargetOperatingSystem::Unknown
    }
}

fn insert_ay_sat_helper_replacement_layout_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_KERNEL.to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_CONTAINS4_MASKED_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_CONTAINS4_MASKED_RESULT_ABI.to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_CONTAINS4_MASKED_REFERENCE_ORACLE.to_owned(),
    );
    insert_ay_sat_helper_replacement_proof_fact_metadata(metadata);
}

fn insert_ay_sat_helper_replacement_manifest_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "consumer".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_CONSUMER.to_owned(),
    );
    metadata.insert(
        "domain".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_DOMAIN.to_owned(),
    );
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_KERNEL.to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_CONTAINS4_MASKED_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_CONTAINS4_MASKED_RESULT_ABI.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema_version".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA_VERSION.to_string(),
    );
    metadata.insert(
        "native_install".to_owned(),
        "helper_callable_gate_only".to_owned(),
    );
    metadata.insert("useful_native".to_owned(), "0".to_owned());
    metadata.insert(
        "promotion_disposition".to_owned(),
        "non_promoting_manifest_backed_helper_replacement".to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_CONTAINS4_MASKED_REFERENCE_ORACLE.to_owned(),
    );
    metadata.insert(
        "native_payload_sha256".to_owned(),
        AY_SAT_CONTAINS4_MASKED_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
    insert_ay_sat_helper_replacement_proof_fact_metadata(metadata);
}

fn insert_ay_sat_helper_replacement_evidence_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_KERNEL.to_owned(),
    );
    metadata.insert(
        "proof_family".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_PROOF_FAMILY.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_CONTAINS4_MASKED_REFERENCE_ORACLE.to_owned(),
    );
    insert_ay_sat_helper_replacement_proof_fact_metadata(metadata);
}

fn insert_ay_sat_helper_replacement_invalidation_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "helper_semantics".to_owned(),
        "contains4_masked_i32_lane_mask".to_owned(),
    );
    metadata.insert(
        "contains_literal_fold".to_owned(),
        "or_nonzero_chunk_masks".to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_CONTAINS4_MASKED_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_CONTAINS4_MASKED_RESULT_ABI.to_owned(),
    );
    metadata.insert("useful_native".to_owned(), "0".to_owned());
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_CONTAINS4_MASKED_REFERENCE_ORACLE.to_owned(),
    );
}

fn insert_ay_sat_minimize_keep_drop_layout_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_KERNEL.to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_RESULT_ABI.to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_REFERENCE_ORACLE.to_owned(),
    );
    metadata.insert(
        "classification_values".to_owned(),
        "drop=0,keep=1,check=2".to_owned(),
    );
    insert_ay_sat_minimize_keep_drop_proof_fact_metadata(metadata);
}

fn insert_ay_sat_minimize_keep_drop_manifest_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "consumer".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_CONSUMER.to_owned(),
    );
    metadata.insert(
        "domain".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_DOMAIN.to_owned(),
    );
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_KERNEL.to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_RESULT_ABI.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema_version".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA_VERSION.to_string(),
    );
    metadata.insert(
        "native_install".to_owned(),
        "helper_callable_gate_only".to_owned(),
    );
    metadata.insert("useful_native".to_owned(), "0".to_owned());
    metadata.insert(
        "promotion_disposition".to_owned(),
        "non_promoting_manifest_backed_helper_replacement".to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_REFERENCE_ORACLE.to_owned(),
    );
    metadata.insert(
        "classification_values".to_owned(),
        "drop=0,keep=1,check=2".to_owned(),
    );
    metadata.insert(
        "native_payload_sha256".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
    insert_ay_sat_minimize_keep_drop_proof_fact_metadata(metadata);
}

fn insert_ay_sat_minimize_keep_drop_evidence_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_KERNEL.to_owned(),
    );
    metadata.insert(
        "proof_family".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_PROOF_FAMILY.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_REFERENCE_ORACLE.to_owned(),
    );
    metadata.insert(
        "classification_values".to_owned(),
        "drop=0,keep=1,check=2".to_owned(),
    );
    insert_ay_sat_minimize_keep_drop_proof_fact_metadata(metadata);
}

fn insert_ay_sat_minimize_keep_drop_invalidation_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.insert(
        "helper_semantics".to_owned(),
        "minimize_keep_drop_literal_classification".to_owned(),
    );
    metadata.insert(
        "cached_flag_bits".to_owned(),
        "poison=0x01,removable=0x02,keep=0x08".to_owned(),
    );
    metadata.insert(
        "reason_sentinel".to_owned(),
        "u32::MAX/no_reason".to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_RESULT_ABI.to_owned(),
    );
    metadata.insert("useful_native".to_owned(), "0".to_owned());
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_MINIMIZE_KEEP_DROP_REFERENCE_ORACLE.to_owned(),
    );
}

fn insert_ay_sat_theory_dispatch_assignment_layout_metadata(
    metadata: &mut BTreeMap<String, String>,
) {
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_KERNEL.to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_ABI.to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_REFERENCE_ORACLE.to_owned(),
    );
    metadata.insert(
        "status_values".to_owned(),
        "skip=0,assert=1,defer_ite=2".to_owned(),
    );
    metadata.insert(
        "guard_flags".to_owned(),
        "ite_guarded=0x01,then_branch=0x02,cond_assigned=0x04,cond_value=0x08".to_owned(),
    );
    metadata.insert(
        "result_encoding".to_owned(),
        "status:bits0_1,value:bit2,term_id:bits32_63".to_owned(),
    );
    insert_ay_sat_theory_dispatch_assignment_proof_fact_metadata(metadata);
}

fn insert_ay_sat_theory_dispatch_assignment_manifest_metadata(
    metadata: &mut BTreeMap<String, String>,
) {
    metadata.insert(
        "consumer".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_CONSUMER.to_owned(),
    );
    metadata.insert(
        "domain".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_DOMAIN.to_owned(),
    );
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_KERNEL.to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_ABI.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema_version".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA_VERSION.to_string(),
    );
    metadata.insert(
        "native_install".to_owned(),
        "helper_callable_gate_only".to_owned(),
    );
    metadata.insert("useful_native".to_owned(), "0".to_owned());
    metadata.insert(
        "promotion_disposition".to_owned(),
        "non_promoting_manifest_backed_helper_replacement".to_owned(),
    );
    metadata.insert(
        "product_promotion_scope".to_owned(),
        "does_not_unblock_665_product_promotion_or_public_ay_repin".to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_REFERENCE_ORACLE.to_owned(),
    );
    metadata.insert(
        "reference_provenance".to_owned(),
        "local_private_reference_only".to_owned(),
    );
    metadata.insert(
        "status_values".to_owned(),
        "skip=0,assert=1,defer_ite=2".to_owned(),
    );
    metadata.insert(
        "guard_flags".to_owned(),
        "ite_guarded=0x01,then_branch=0x02,cond_assigned=0x04,cond_value=0x08".to_owned(),
    );
    metadata.insert(
        "result_encoding".to_owned(),
        "status:bits0_1,value:bit2,term_id:bits32_63".to_owned(),
    );
    metadata.insert(
        "native_payload_sha256".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
    insert_ay_sat_theory_dispatch_assignment_proof_fact_metadata(metadata);
}

fn insert_ay_sat_theory_dispatch_assignment_evidence_metadata(
    metadata: &mut BTreeMap<String, String>,
) {
    metadata.insert(
        "kernel".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_KERNEL.to_owned(),
    );
    metadata.insert(
        "proof_family".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_PROOF_FAMILY.to_owned(),
    );
    metadata.insert(
        "artifact_contract_schema".to_owned(),
        AY_SAT_HELPER_REPLACEMENT_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
    );
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_REFERENCE_ORACLE.to_owned(),
    );
    metadata.insert(
        "reference_provenance".to_owned(),
        "local_private_reference_only".to_owned(),
    );
    metadata.insert(
        "status_values".to_owned(),
        "skip=0,assert=1,defer_ite=2".to_owned(),
    );
    metadata.insert(
        "guard_flags".to_owned(),
        "ite_guarded=0x01,then_branch=0x02,cond_assigned=0x04,cond_value=0x08".to_owned(),
    );
    insert_ay_sat_theory_dispatch_assignment_proof_fact_metadata(metadata);
}

fn insert_ay_sat_theory_dispatch_assignment_invalidation_metadata(
    metadata: &mut BTreeMap<String, String>,
) {
    metadata.insert(
        "helper_semantics".to_owned(),
        "theory_dispatch_lookup_assignment".to_owned(),
    );
    metadata.insert(
        "ite_relevancy".to_owned(),
        "defer_assigned_inactive_branch_only_when_decision_level_gt_zero".to_owned(),
    );
    metadata.insert("no_ite_guard_sentinel".to_owned(), "u32::MAX".to_owned());
    metadata.insert(
        "bool_encoding".to_owned(),
        "zero_false_nonzero_true".to_owned(),
    );
    metadata.insert(
        "guard_flags".to_owned(),
        "ite_guarded=0x01,then_branch=0x02,cond_assigned=0x04,cond_value=0x08".to_owned(),
    );
    metadata.insert(
        "args_abi".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_ARGS_ABI.to_owned(),
    );
    metadata.insert(
        "result_abi".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_RESULT_ABI.to_owned(),
    );
    metadata.insert("useful_native".to_owned(), "0".to_owned());
    metadata.insert(
        "reference_oracle".to_owned(),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_REFERENCE_ORACLE.to_owned(),
    );
}

fn field(name: &str, offset_bytes: u64, size_bytes: u64, alignment_bytes: u32) -> FieldLayout {
    FieldLayout {
        name: name.to_owned(),
        offset_bytes,
        size_bytes,
        alignment_bytes,
    }
}
