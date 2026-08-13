// trust-cg-codegen/ty_reducer_evidence.rs - Phase 4 TY reducer evidence packets
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Deterministic Phase 4 evidence packets for Trust Codegen-local TY O3 reducers.
//!
//! These packets describe reducer evidence that already runs inside Trust Codegen and
//! bind bounded downstream TY replay metadata that has been accepted elsewhere.
//! The accepted replay rows remain non-promoting until final Phase 9 blockers
//! close through their own packet.

use std::collections::BTreeSet;

use serde_json::{Value, json};

use crate::jit_diagnostics::sha256_hex;

/// Stable schema tag for local TY reducer evidence packets.
pub const TY_REDUCER_EVIDENCE_PACKET_SCHEMA: &str = "trust-cg.phase4.ty_reducer_evidence/v2";

/// Current schema version for local TY reducer evidence packets.
pub const TY_REDUCER_EVIDENCE_PACKET_SCHEMA_VERSION: u32 = 2;

/// Manifest metadata key for the reducer evidence packet schema.
pub const TY_REDUCER_EVIDENCE_SCHEMA_METADATA_KEY: &str = "ty.local_reducer_evidence.schema";

/// Manifest metadata key for the reducer evidence packet schema version.
pub const TY_REDUCER_EVIDENCE_SCHEMA_VERSION_METADATA_KEY: &str =
    "ty.local_reducer_evidence.schema_version";

/// Manifest metadata key for the reducer evidence packet hash.
pub const TY_REDUCER_EVIDENCE_PACKET_SHA256_METADATA_KEY: &str =
    "ty.local_reducer_evidence.packet_sha256";

/// Manifest metadata key for the sorted reducer family coverage list.
pub const TY_REDUCER_EVIDENCE_FAMILIES_METADATA_KEY: &str = "ty.local_reducer_evidence.families";

/// Reducer families required before TY native-fused product readiness can bind local evidence.
pub const TY_REDUCER_REQUIRED_EVIDENCE_FAMILIES: &[&str] = &[
    "minimal_parent_loop",
    "no_action_body_parent_loop",
    "mcl_shaped_native_fused_parent_loop",
    "callback_abi_call_clobber",
    "edge_copy_block_arg",
    "o3_materialized_helper_return",
];

/// Bounded downstream replay family carried as accepted input, not local reducer coverage.
pub const TY_REDUCER_REQUEST_REPLAY_FAMILY: &str = "request_1_1_downstream_replay";

/// Accepted downstream issue refs that make the replay row reusable input.
pub const TY_REDUCER_ACCEPTED_DOWNSTREAM_REFS: &[&str] = &["#671", "#729", "#730", "#667"];

/// Non-promoting final blockers for public/source publication.
pub const TY_REDUCER_PUBLIC_SOURCE_BLOCKER_REFS: &[&str] = &["#719", "#779"];

/// Non-promoting final blockers for release packet closure.
pub const TY_REDUCER_RELEASE_PACKET_BLOCKER_REFS: &[&str] = &["#664", "#667", "#730"];

/// Trust Codegen revision accepted by downstream TY evidence.
pub const TY_REDUCER_TRUST_CG_ACCEPTED_REVISION: &str = "dde709e0c56a29a0839e6c789c7ba591f3b1c2d0";

/// Focused TY pin cited by accepted Request__1_1/MCL evidence comments.
pub const TY_REDUCER_TY_FOCUSED_PIN: &str = "baa2a7230";

/// TY commit recorded inside accepted three-spec replay metadata.
pub const TY_REDUCER_TY_THREE_SPEC_REPLAY_METADATA_PIN: &str =
    "b2467ae55068cecf0558265b19209e9c73d1c875";

/// Deterministic packet containing one row per reducer family/case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyReducerEvidencePacket {
    /// Trust Codegen issue that requested this packet.
    pub issue: u64,
    /// Parent reducer corpus issue.
    pub parent_issue: u64,
    /// Accepted downstream issue refs whose TY replay artifacts are reusable input.
    pub accepted_downstream_issue_refs: Vec<String>,
    /// Final public-source blockers that keep this packet non-promoting.
    pub public_source_blocker_issue_refs: Vec<String>,
    /// Final release-packet blockers that keep this packet non-promoting.
    pub release_packet_blocker_issue_refs: Vec<String>,
    /// Trust Codegen revision accepted by downstream TY evidence.
    pub trust_cg_accepted_revision: String,
    /// Focused TY pin cited by accepted Request__1_1/MCL evidence comments.
    pub ty_focused_pin: String,
    /// TY commit recorded inside accepted three-spec replay metadata.
    pub ty_three_spec_replay_metadata_pin: String,
    /// Human-readable boundary between accepted replay input and final promotion.
    pub downstream_boundary: String,
    /// Human-readable boundary for remaining non-promoting final blockers.
    pub final_blocker_boundary: String,
    /// Evidence rows. JSON rendering sorts these rows deterministically.
    pub rows: Vec<TyReducerEvidenceRow>,
}

impl TyReducerEvidencePacket {
    /// Build a packet for issue #693's local Phase 4 reducer evidence.
    pub fn phase4_local(rows: impl IntoIterator<Item = TyReducerEvidenceRow>) -> Self {
        Self {
            issue: 693,
            parent_issue: 662,
            accepted_downstream_issue_refs: refs_to_strings(TY_REDUCER_ACCEPTED_DOWNSTREAM_REFS),
            public_source_blocker_issue_refs: refs_to_strings(
                TY_REDUCER_PUBLIC_SOURCE_BLOCKER_REFS,
            ),
            release_packet_blocker_issue_refs: refs_to_strings(
                TY_REDUCER_RELEASE_PACKET_BLOCKER_REFS,
            ),
            trust_cg_accepted_revision: TY_REDUCER_TRUST_CG_ACCEPTED_REVISION.to_owned(),
            ty_focused_pin: TY_REDUCER_TY_FOCUSED_PIN.to_owned(),
            ty_three_spec_replay_metadata_pin: TY_REDUCER_TY_THREE_SPEC_REPLAY_METADATA_PIN
                .to_owned(),
            downstream_boundary: concat!(
                "accepted TY replay evidence is bounded reusable input; ",
                "it does not promote final TY native-fused release readiness"
            )
            .to_owned(),
            final_blocker_boundary: concat!(
                "final readiness remains non-promoting until public-source ",
                "and release-packet blockers close through their own review"
            )
            .to_owned(),
            rows: rows.into_iter().collect(),
        }
    }

    /// Convert to deterministic JSON. Rows are ordered by reducer family, case,
    /// command, and target tuple.
    pub fn to_json_value(&self) -> Value {
        let mut rows = self.rows.clone();
        rows.sort_by(|left, right| {
            (
                left.reducer_family.as_str(),
                left.case_name.as_str(),
                left.command.as_str(),
                left.target_tuple.as_str(),
            )
                .cmp(&(
                    right.reducer_family.as_str(),
                    right.case_name.as_str(),
                    right.command.as_str(),
                    right.target_tuple.as_str(),
                ))
        });

        let accepted_downstream_issue_refs =
            unique_ordered_strings(&self.accepted_downstream_issue_refs);
        let public_source_blocker_issue_refs =
            unique_ordered_strings(&self.public_source_blocker_issue_refs);
        let release_packet_blocker_issue_refs =
            unique_ordered_strings(&self.release_packet_blocker_issue_refs);
        let mut final_blocker_issue_refs = public_source_blocker_issue_refs.clone();
        final_blocker_issue_refs.extend(release_packet_blocker_issue_refs.clone());
        final_blocker_issue_refs = unique_ordered_strings(&final_blocker_issue_refs);

        json!({
            "schema": TY_REDUCER_EVIDENCE_PACKET_SCHEMA,
            "schema_version": TY_REDUCER_EVIDENCE_PACKET_SCHEMA_VERSION,
            "issue": self.issue,
            "parent_issue": self.parent_issue,
            "consumer": "ty",
            "evidence_scope": "trust-cg-local-o1-o3-reducer-with-bounded-ty-replay",
            "bounded_downstream_replay": {
                "request_replay_family": TY_REDUCER_REQUEST_REPLAY_FAMILY,
                "disposition": "accepted_bounded_input",
                "accepted_issue_refs": accepted_downstream_issue_refs,
                "source_locks": {
                    "trust-cg": {
                        "revision": self.trust_cg_accepted_revision,
                        "role": "accepted_aarch64_execute_allocation_fix",
                    },
                    "ty_focused": {
                        "pin": self.ty_focused_pin,
                        "role": "focused_request_1_1_mcl_replay_evidence",
                    },
                    "ty_three_spec_replay_metadata": {
                        "pin": self.ty_three_spec_replay_metadata_pin,
                        "role": "three_spec_replay_metadata_ty_git_commit",
                    },
                },
                "boundary": self.downstream_boundary,
            },
            "non_promoting_final_blockers": {
                "product_promotion_allowed": false,
                "public_source_issue_refs": public_source_blocker_issue_refs,
                "release_packet_issue_refs": release_packet_blocker_issue_refs,
                "issue_refs": final_blocker_issue_refs,
                "boundary": self.final_blocker_boundary,
            },
            "rows": rows.into_iter().map(|row| row.to_json_value()).collect::<Vec<_>>(),
        })
    }

    /// Convert to deterministic pretty JSON with a trailing newline.
    pub fn to_pretty_json(&self) -> Result<String, serde_json::Error> {
        let mut output = serde_json::to_string_pretty(&self.to_json_value())?;
        output.push('\n');
        Ok(output)
    }

    /// Try to return the stable hash of the canonical packet JSON.
    pub fn try_canonical_packet_sha256(&self) -> Result<String, serde_json::Error> {
        let bytes = serde_json::to_vec(&self.to_json_value())?;
        Ok(format!("sha256:{}", sha256_hex(&bytes)))
    }

    /// Return the stable hash of the canonical packet JSON.
    pub fn canonical_packet_sha256(&self) -> String {
        match self.try_canonical_packet_sha256() {
            Ok(packet_sha256) => packet_sha256,
            Err(_) => {
                let mut bytes = Vec::new();
                append_canonical_json_value(&mut bytes, &self.to_json_value());
                format!("sha256:{}", sha256_hex(&bytes))
            }
        }
    }

    /// Return a deterministic coverage summary for the standard product-readiness families.
    pub fn coverage_summary(
        &self,
    ) -> Result<TyReducerEvidenceCoverageSummary, TyReducerEvidenceCoverageError> {
        self.coverage_summary_for_expected_families(TY_REDUCER_REQUIRED_EVIDENCE_FAMILIES)
    }

    /// Return a deterministic coverage summary requiring every expected family to be green.
    pub fn coverage_summary_for_expected_families(
        &self,
        expected_families: &[&str],
    ) -> Result<TyReducerEvidenceCoverageSummary, TyReducerEvidenceCoverageError> {
        let expected = expected_families.iter().copied().collect::<BTreeSet<_>>();
        let mut green_families = BTreeSet::new();

        for row in &self.rows {
            if !expected.contains(row.reducer_family.as_str()) {
                continue;
            }
            if row.status != TyReducerEvidenceStatus::GreenReducerEvidence {
                return Err(TyReducerEvidenceCoverageError::NonGreenReducerEvidence {
                    reducer_family: row.reducer_family.clone(),
                });
            }
            green_families.insert(row.reducer_family.clone());
        }

        for family in expected_families {
            if !green_families.contains(*family) {
                return Err(TyReducerEvidenceCoverageError::MissingReducerFamily {
                    reducer_family: (*family).to_owned(),
                });
            }
        }

        Ok(TyReducerEvidenceCoverageSummary {
            schema: TY_REDUCER_EVIDENCE_PACKET_SCHEMA.to_owned(),
            schema_version: TY_REDUCER_EVIDENCE_PACKET_SCHEMA_VERSION,
            packet_sha256: self.canonical_packet_sha256(),
            reducer_families: green_families.into_iter().collect(),
        })
    }
}

/// Deterministic reducer evidence coverage bound into native-fused readiness packets.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyReducerEvidenceCoverageSummary {
    pub schema: String,
    pub schema_version: u32,
    pub packet_sha256: String,
    pub reducer_families: Vec<String>,
}

impl TyReducerEvidenceCoverageSummary {
    /// Return sorted `key=value` manifest metadata bindings for this summary.
    pub fn metadata_bindings(&self) -> Vec<(String, String)> {
        vec![
            (
                TY_REDUCER_EVIDENCE_SCHEMA_METADATA_KEY.to_owned(),
                self.schema.clone(),
            ),
            (
                TY_REDUCER_EVIDENCE_SCHEMA_VERSION_METADATA_KEY.to_owned(),
                self.schema_version.to_string(),
            ),
            (
                TY_REDUCER_EVIDENCE_PACKET_SHA256_METADATA_KEY.to_owned(),
                self.packet_sha256.clone(),
            ),
            (
                TY_REDUCER_EVIDENCE_FAMILIES_METADATA_KEY.to_owned(),
                self.reducer_families.join(","),
            ),
        ]
    }
}

/// Typed reason a reducer packet cannot summarize local product-readiness coverage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TyReducerEvidenceCoverageError {
    MissingReducerFamily { reducer_family: String },
    NonGreenReducerEvidence { reducer_family: String },
}

/// One reducer evidence row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyReducerEvidenceRow {
    pub command: String,
    pub target_tuple: String,
    pub trust_cg_revision: String,
    pub opt_level: String,
    pub reducer_family: String,
    pub case_name: String,
    pub parent_digest: String,
    pub state_count: u64,
    pub generated_count: u64,
    pub fingerprint_digest: Option<String>,
    pub callback_observations: Vec<TyReducerCallbackObservation>,
    pub status: TyReducerEvidenceStatus,
    pub issue_refs: Vec<String>,
}

impl TyReducerEvidenceRow {
    /// Convert to deterministic JSON. Callback observations and issue refs are
    /// sorted so caller insertion order cannot perturb packet bytes.
    pub fn to_json_value(&self) -> Value {
        let mut callbacks = self.callback_observations.clone();
        callbacks.sort();
        let mut issue_refs = self.issue_refs.clone();
        issue_refs.sort();
        issue_refs.dedup();

        json!({
            "command": self.command,
            "target_tuple": self.target_tuple,
            "trust_cg_revision": self.trust_cg_revision,
            "opt_level": self.opt_level,
            "reducer_family": self.reducer_family,
            "case_name": self.case_name,
            "parent_digest": self.parent_digest,
            "state_count": self.state_count,
            "generated_count": self.generated_count,
            "fingerprint_digest": self.fingerprint_digest,
            "callback_observations": callbacks
                .into_iter()
                .map(|callback| callback.to_json_value())
                .collect::<Vec<_>>(),
            "status": self.status.to_json_value(),
            "issue_refs": issue_refs,
        })
    }
}

/// Stable callback observation captured by reducers that exercise callouts.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct TyReducerCallbackObservation {
    pub name: String,
    pub calls: u64,
    pub digest: String,
}

impl TyReducerCallbackObservation {
    pub fn to_json_value(&self) -> Value {
        json!({
            "name": self.name,
            "calls": self.calls,
            "digest": self.digest,
        })
    }
}

/// Reducer row status with an explicit downstream distinction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TyReducerEvidenceStatus {
    GreenReducerEvidence,
    AcceptedDownstreamRequestReplay { evidence: String },
}

impl TyReducerEvidenceStatus {
    fn to_json_value(&self) -> Value {
        match self {
            Self::GreenReducerEvidence => json!({
                "kind": "green_reducer_evidence",
            }),
            Self::AcceptedDownstreamRequestReplay { evidence } => json!({
                "kind": "accepted_downstream_request_replay",
                "evidence": evidence,
            }),
        }
    }
}

fn refs_to_strings(refs: &[&str]) -> Vec<String> {
    refs.iter()
        .map(|issue_ref| (*issue_ref).to_owned())
        .collect()
}

fn unique_ordered_strings(strings: &[String]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut ordered = Vec::new();

    for string in strings {
        if seen.insert(string.clone()) {
            ordered.push(string.clone());
        }
    }

    ordered
}

fn append_canonical_json_value(output: &mut Vec<u8>, value: &Value) {
    match value {
        Value::Null => output.extend_from_slice(b"null"),
        Value::Bool(true) => output.extend_from_slice(b"true"),
        Value::Bool(false) => output.extend_from_slice(b"false"),
        Value::Number(number) => output.extend_from_slice(number.to_string().as_bytes()),
        Value::String(string) => append_canonical_json_string(output, string),
        Value::Array(values) => {
            output.push(b'[');
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    output.push(b',');
                }
                append_canonical_json_value(output, value);
            }
            output.push(b']');
        }
        Value::Object(fields) => {
            output.push(b'{');
            for (index, (key, value)) in fields.iter().enumerate() {
                if index > 0 {
                    output.push(b',');
                }
                append_canonical_json_string(output, key);
                output.push(b':');
                append_canonical_json_value(output, value);
            }
            output.push(b'}');
        }
    }
}

fn append_canonical_json_string(output: &mut Vec<u8>, string: &str) {
    output.push(b'"');
    for character in string.chars() {
        match character {
            '"' => output.extend_from_slice(br#"\""#),
            '\\' => output.extend_from_slice(br#"\\"#),
            '\u{08}' => output.extend_from_slice(br#"\b"#),
            '\u{0c}' => output.extend_from_slice(br#"\f"#),
            '\n' => output.extend_from_slice(br#"\n"#),
            '\r' => output.extend_from_slice(br#"\r"#),
            '\t' => output.extend_from_slice(br#"\t"#),
            '\u{00}'..='\u{1f}' => {
                output.extend_from_slice(b"\\u00");
                output.push(hex_digit((character as u8) >> 4));
                output.push(hex_digit((character as u8) & 0x0f));
            }
            _ => {
                let mut buffer = [0; 4];
                output.extend_from_slice(character.encode_utf8(&mut buffer).as_bytes());
            }
        }
    }
    output.push(b'"');
}

fn hex_digit(nibble: u8) -> u8 {
    match nibble {
        0..=9 => b'0' + nibble,
        10..=15 => b'a' + (nibble - 10),
        _ => b'0',
    }
}

#[cfg(test)]
mod tests {
    use super::{
        TyReducerEvidencePacket, TyReducerEvidenceRow, TyReducerEvidenceStatus,
        append_canonical_json_value,
    };

    fn row(reducer_family: &str, case_name: &str) -> TyReducerEvidenceRow {
        TyReducerEvidenceRow {
            command: "cargo test -p trust-cg-codegen --test ty_reducer_evidence_packet".to_owned(),
            target_tuple: "aarch64-apple-darwin".to_owned(),
            trust_cg_revision: "trust-cg-test-revision".to_owned(),
            opt_level: "O1/O3".to_owned(),
            reducer_family: reducer_family.to_owned(),
            case_name: case_name.to_owned(),
            parent_digest: "trust-cg-stable128:test-parent".to_owned(),
            state_count: 1,
            generated_count: 1,
            fingerprint_digest: Some("trust-cg-stable128:test-fingerprint".to_owned()),
            callback_observations: Vec::new(),
            status: TyReducerEvidenceStatus::GreenReducerEvidence,
            issue_refs: vec!["#699".to_owned(), "#693".to_owned()],
        }
    }

    #[test]
    fn canonical_packet_hash_uses_fallible_serialization_without_changing_identity() {
        let packet = TyReducerEvidencePacket::phase4_local([
            row("minimal_parent_loop", "a"),
            row("callback_abi_call_clobber", "b"),
        ]);

        let fallible_packet_sha256 = packet.try_canonical_packet_sha256();

        assert!(fallible_packet_sha256.is_ok());
        assert_eq!(
            fallible_packet_sha256.unwrap_or_default(),
            packet.canonical_packet_sha256()
        );
    }

    #[test]
    fn fallback_canonical_json_matches_serde_json_canonical_bytes() {
        let value = serde_json::json!({
            "string_edges": [
                "quote \"",
                "backslash \\",
                "backspace \u{0008}",
                "form_feed \u{000c}",
                "carriage_return \r",
                "tab \t",
                "newline \n",
                "unit_separator \u{001f}",
                "non_ascii café 雪",
            ],
            "scalar_array": [null, true, false, 0, -17, 42, 3.5],
            "nested": {
                "object": {
                    "array": [
                        {"key": "value"},
                        {"number": 128, "bool": true},
                    ],
                },
            },
        });
        let serde_bytes = serde_json::to_vec(&value);
        assert!(serde_bytes.is_ok());
        let serde_bytes = serde_bytes.unwrap_or_default();
        let mut fallback_bytes = Vec::new();

        append_canonical_json_value(&mut fallback_bytes, &value);

        assert_eq!(fallback_bytes, serde_bytes);
    }
}
