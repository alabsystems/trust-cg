// trust-cg-verify/aarch64_backend_proof_report.rs - AArch64 backend proof-family report
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Metadata-only AArch64 backend proof-family report.
//!
//! This report is deliberately non-installable. It binds the first AArch64
//! backend proof-family inventory slices for the `aarch64-apple-darwin` target
//! without authorizing native product promotion.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtSort;

/// Stable schema tag for AArch64 backend proof-family reports.
pub const AARCH64_BACKEND_PROOF_FAMILY_REPORT_SCHEMA: &str =
    "trust-cg.aarch64.backend_proof_family_report/v1";

/// Target triple covered by this metadata-only report.
pub const AARCH64_BACKEND_PROOF_TARGET: &str = "aarch64-apple-darwin";

/// Obligation set named by this metadata-only backend proof-family report.
pub const AARCH64_BACKEND_PROOF_OBLIGATION_SET: &str =
    "aarch64-ldp-lse-scheduler-switch-address-mode-frame-call-lowering-regalloc-v1";

/// Stable policy id for the non-installable metadata-only disposition.
pub const AARCH64_BACKEND_PROOF_POLICY_ID: &str =
    "trust-cg.aarch64.backend_proof_family_report.metadata_only_non_installable.v1";

/// Stable schema tag for per-obligation evidence hashes.
pub const AARCH64_BACKEND_PROOF_OBLIGATION_HASH_SCHEMA: &str =
    "trust-cg.aarch64.backend_proof_obligation_hash_payload/v1";

/// Top-level AArch64 backend proof-family report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64BackendProofFamilyReport {
    /// Stable schema tag.
    pub schema: String,
    /// Target triple covered by all rows.
    pub target: String,
    /// Stable obligation-set id.
    pub obligation_set: String,
    /// Product/install policy for this report.
    pub policy: Aarch64BackendProofPolicy,
    /// Stable ordered proof/evidence rows.
    pub rows: Vec<Aarch64BackendProofRow>,
    /// `sha256:<lowercase-hex>` digest of the canonical report payload.
    pub report_hash: String,
}

impl Aarch64BackendProofFamilyReport {
    /// Build a report from rows, sorting rows into canonical order and hashing
    /// the resulting metadata payload.
    pub fn from_rows(mut rows: Vec<Aarch64BackendProofRow>) -> Self {
        rows.sort_by_key(Aarch64BackendProofRow::stable_sort_key);

        let mut report = Self {
            schema: AARCH64_BACKEND_PROOF_FAMILY_REPORT_SCHEMA.to_string(),
            target: AARCH64_BACKEND_PROOF_TARGET.to_string(),
            obligation_set: AARCH64_BACKEND_PROOF_OBLIGATION_SET.to_string(),
            policy: Aarch64BackendProofPolicy::metadata_only_non_installable(),
            rows,
            report_hash: String::new(),
        };
        report.report_hash = report.compute_report_hash();
        report
    }

    /// Recompute the stable report hash from the current report payload.
    ///
    /// The `report_hash` field itself is excluded, so callers can mutate a copy
    /// and compare this value with the original hash.
    pub fn compute_report_hash(&self) -> String {
        let payload = Aarch64BackendProofFamilyReportHashPayload {
            schema: &self.schema,
            target: &self.target,
            obligation_set: &self.obligation_set,
            policy: &self.policy,
            rows: &self.rows,
        };
        let canonical = serde_json::to_vec(&payload)
            .expect("AArch64 backend proof report hash payload should serialize");
        sha256_prefixed(&canonical)
    }
}

#[derive(Debug, Serialize)]
struct Aarch64BackendProofFamilyReportHashPayload<'a> {
    schema: &'a str,
    target: &'a str,
    obligation_set: &'a str,
    policy: &'a Aarch64BackendProofPolicy,
    rows: &'a [Aarch64BackendProofRow],
}

/// Non-installable policy carried by the report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64BackendProofPolicy {
    /// Stable policy identifier.
    pub policy_id: String,
    /// This report contains metadata only.
    pub metadata_only: bool,
    /// The report must not be converted into an installable native artifact.
    pub installable: bool,
    /// Product/native promotion is outside this report's authority.
    pub product_promotion_allowed: bool,
    /// Stable disposition string for consumers and dashboards.
    pub disposition: String,
    /// Human-readable policy reason.
    pub reason: String,
}

impl Aarch64BackendProofPolicy {
    /// Return the required non-installable metadata-only policy.
    pub fn metadata_only_non_installable() -> Self {
        Self {
            policy_id: AARCH64_BACKEND_PROOF_POLICY_ID.to_string(),
            metadata_only: true,
            installable: false,
            product_promotion_allowed: false,
            disposition: "metadata_only_non_installable".to_string(),
            reason: "proof-family inventory only; no native artifact or install authority"
                .to_string(),
        }
    }
}

/// Proof-family bucket for one report row.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Aarch64BackendProofFamily {
    /// Load-pair memory proof obligations from `memory_proofs::all_ldp_proofs()`.
    Ldp,
    /// AArch64 atomic/LSE proof obligations plus explicit contract/test evidence.
    Lse,
    /// Instruction scheduler proof obligations from `scheduler_proofs::all_scheduler_proofs()`.
    Scheduler,
    /// Switch lowering proof obligations from `switch_proofs::all_switch_proofs()`.
    Switch,
    /// Address-mode proof obligations from `addr_mode_proofs::all_addr_mode_proofs()`.
    AddressMode,
    /// Frame-layout proof obligations from `frame_proofs::all_frame_proofs()`.
    Frame,
    /// Call-lowering proof obligations from `call_lowering_proofs::all_call_lowering_proofs()`.
    CallLowering,
    /// Register-allocation proof obligations from `regalloc_proofs::all_regalloc_proofs()`.
    RegAlloc,
}

impl Aarch64BackendProofFamily {
    /// Stable lower-snake-case family id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ldp => "ldp",
            Self::Lse => "lse",
            Self::Scheduler => "scheduler",
            Self::Switch => "switch",
            Self::AddressMode => "address_mode",
            Self::Frame => "frame",
            Self::CallLowering => "call_lowering",
            Self::RegAlloc => "regalloc",
        }
    }

    const fn stable_sort_ordinal(self) -> u8 {
        match self {
            Self::Ldp => 0,
            Self::Lse => 1,
            Self::Scheduler => 2,
            Self::Switch => 3,
            Self::AddressMode => 4,
            Self::Frame => 5,
            Self::CallLowering => 6,
            Self::RegAlloc => 7,
        }
    }
}

/// Evidence type named by one report row.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Aarch64BackendProofEvidenceKind {
    /// A concrete `ProofObligation` sourced from an existing proof aggregator.
    ProofObligation,
    /// A named semantic/architectural contract.
    Contract,
    /// A named test that exercises the contract or proof family.
    Test,
}

impl Aarch64BackendProofEvidenceKind {
    /// Stable lower-snake-case evidence-kind id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProofObligation => "proof_obligation",
            Self::Contract => "contract",
            Self::Test => "test",
        }
    }
}

/// One metadata row in the AArch64 backend proof-family report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64BackendProofRow {
    /// Stable row id.
    pub row_id: String,
    /// Proof-family bucket.
    pub family: Aarch64BackendProofFamily,
    /// Source inventory or explicit evidence source.
    pub source: String,
    /// Evidence type.
    pub evidence_kind: Aarch64BackendProofEvidenceKind,
    /// Proof obligation name, contract id, or test id.
    pub evidence_id: String,
    /// `sha256:<lowercase-hex>` digest over this row's source evidence metadata.
    pub evidence_hash: String,
    /// Coarse translation-validation category when the source is a proof obligation.
    pub transval_check_kind: Option<String>,
    /// Input bit widths in declaration order for proof-obligation rows.
    pub input_widths: Vec<u32>,
    /// Floating-point input widths in declaration order for proof-obligation rows.
    pub fp_input_widths: Vec<Aarch64BackendFpInputWidth>,
    /// Number of preconditions in the source proof obligation.
    pub precondition_count: usize,
    /// Result sort of the source equivalence expression.
    pub result_sort: String,
    /// Row-level copy of the report's target triple.
    pub target: String,
    /// Row-level metadata-only marker.
    pub metadata_only: bool,
    /// Row-level installability marker.
    pub installable: bool,
}

impl Aarch64BackendProofRow {
    /// Stable sort key used by report construction and tests.
    pub fn stable_sort_key(&self) -> String {
        format!(
            "{:02}|{}|{}|{}|{}",
            self.family.stable_sort_ordinal(),
            self.family.as_str(),
            self.evidence_kind.as_str(),
            self.row_id,
            self.evidence_id
        )
    }
}

/// Floating-point input width tuple recorded for completeness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aarch64BackendFpInputWidth {
    /// Symbol name.
    pub name: String,
    /// Floating-point exponent bits.
    pub exponent_bits: u32,
    /// Floating-point significand bits.
    pub significand_bits: u32,
}

/// Build the metadata-only AArch64 backend proof-family report.
pub fn build_aarch64_backend_proof_family_report() -> Aarch64BackendProofFamilyReport {
    let mut rows = Vec::new();

    rows.extend(proof_rows(
        Aarch64BackendProofFamily::Ldp,
        "memory_proofs::all_ldp_proofs()",
        crate::memory_proofs::all_ldp_proofs(),
    ));
    rows.extend(proof_rows(
        Aarch64BackendProofFamily::Lse,
        "atomic_proofs::all_atomic_proofs()",
        crate::atomic_proofs::all_atomic_proofs(),
    ));
    rows.extend(explicit_lse_evidence_rows());
    rows.extend(proof_rows(
        Aarch64BackendProofFamily::Scheduler,
        "scheduler_proofs::all_scheduler_proofs()",
        crate::scheduler_proofs::all_scheduler_proofs(),
    ));
    rows.extend(proof_rows(
        Aarch64BackendProofFamily::Switch,
        "switch_proofs::all_switch_proofs()",
        crate::switch_proofs::all_switch_proofs(),
    ));
    rows.extend(proof_rows(
        Aarch64BackendProofFamily::AddressMode,
        "addr_mode_proofs::all_addr_mode_proofs()",
        crate::addr_mode_proofs::all_addr_mode_proofs(),
    ));
    rows.extend(proof_rows(
        Aarch64BackendProofFamily::Frame,
        "frame_proofs::all_frame_proofs()",
        crate::frame_proofs::all_frame_proofs(),
    ));
    rows.extend(proof_rows(
        Aarch64BackendProofFamily::CallLowering,
        "call_lowering_proofs::all_call_lowering_proofs()",
        crate::call_lowering_proofs::all_call_lowering_proofs(),
    ));
    rows.extend(proof_rows(
        Aarch64BackendProofFamily::RegAlloc,
        "regalloc_proofs::all_regalloc_proofs()",
        crate::regalloc_proofs::all_regalloc_proofs(),
    ));

    Aarch64BackendProofFamilyReport::from_rows(rows)
}

fn proof_rows(
    family: Aarch64BackendProofFamily,
    source: &str,
    proofs: Vec<ProofObligation>,
) -> Vec<Aarch64BackendProofRow> {
    proofs
        .into_iter()
        .map(|obligation| proof_row(family, source, obligation))
        .collect()
}

fn proof_row(
    family: Aarch64BackendProofFamily,
    source: &str,
    obligation: ProofObligation,
) -> Aarch64BackendProofRow {
    let evidence_id = obligation.name.clone();
    let row_id = format!("{}:{}", family.as_str(), stable_slug(&evidence_id));
    let evidence_hash = proof_obligation_hash(source, family, &obligation);
    let input_widths = obligation.inputs.iter().map(|(_, width)| *width).collect();
    let fp_input_widths = obligation
        .fp_inputs
        .iter()
        .map(
            |(name, exponent_bits, significand_bits)| Aarch64BackendFpInputWidth {
                name: name.clone(),
                exponent_bits: *exponent_bits,
                significand_bits: *significand_bits,
            },
        )
        .collect();
    let precondition_count = obligation.preconditions.len();
    let result_sort = result_sort_label(&obligation.trust_ir_expr.sort());
    let transval_check_kind = obligation.category.map(|category| category.to_string());

    Aarch64BackendProofRow {
        row_id,
        family,
        source: source.to_string(),
        evidence_kind: Aarch64BackendProofEvidenceKind::ProofObligation,
        evidence_id,
        evidence_hash,
        transval_check_kind,
        input_widths,
        fp_input_widths,
        precondition_count,
        result_sort,
        target: AARCH64_BACKEND_PROOF_TARGET.to_string(),
        metadata_only: true,
        installable: false,
    }
}

fn explicit_lse_evidence_rows() -> Vec<Aarch64BackendProofRow> {
    vec![
        explicit_lse_row(
            "lse:atomic-dataflow-architecture-contract",
            Aarch64BackendProofEvidenceKind::Contract,
            "aarch64_lse_atomic_dataflow_contract_v1",
            "atomic_proofs.rs: module-level LSE ordering/data-flow contract",
            "AArch64 LSE atomic proofs cover data-flow equivalence; acquire/release ordering is an architecture-level contract",
        ),
        explicit_lse_row(
            "lse:atomic-proof-suite-test",
            Aarch64BackendProofEvidenceKind::Test,
            "atomic_proofs::tests::test_all_atomic_proofs_valid",
            "atomic_proofs.rs: all_atomic_proofs() evaluation test",
            "Focused test evidence that the atomic/LSE proof inventory is evaluated by trust-cg-verify",
        ),
    ]
}

fn explicit_lse_row(
    row_id: &str,
    evidence_kind: Aarch64BackendProofEvidenceKind,
    evidence_id: &str,
    source: &str,
    summary: &str,
) -> Aarch64BackendProofRow {
    let hash_material = format!(
        "family={}|kind={}|row_id={}|source={}|evidence_id={}|summary={}",
        Aarch64BackendProofFamily::Lse.as_str(),
        evidence_kind.as_str(),
        row_id,
        source,
        evidence_id,
        summary
    );

    Aarch64BackendProofRow {
        row_id: row_id.to_string(),
        family: Aarch64BackendProofFamily::Lse,
        source: source.to_string(),
        evidence_kind,
        evidence_id: evidence_id.to_string(),
        evidence_hash: sha256_prefixed(hash_material.as_bytes()),
        transval_check_kind: None,
        input_widths: Vec::new(),
        fp_input_widths: Vec::new(),
        precondition_count: 0,
        result_sort: "metadata".to_string(),
        target: AARCH64_BACKEND_PROOF_TARGET.to_string(),
        metadata_only: true,
        installable: false,
    }
}

fn proof_obligation_hash(
    source: &str,
    family: Aarch64BackendProofFamily,
    obligation: &ProofObligation,
) -> String {
    let payload = ProofObligationHashPayload {
        schema: AARCH64_BACKEND_PROOF_OBLIGATION_HASH_SCHEMA,
        family: family.as_str(),
        source,
        name: &obligation.name,
        category: obligation.category.map(|category| category.to_string()),
        inputs: &obligation.inputs,
        fp_inputs: &obligation.fp_inputs,
        preconditions_smt2: obligation
            .preconditions
            .iter()
            .map(|expr| expr.to_smt2_expr())
            .collect(),
        trust_ir_expr_smt2: obligation.trust_ir_expr.to_smt2_expr(),
        aarch64_expr_smt2: obligation.aarch64_expr.to_smt2_expr(),
        negated_equivalence_smt2: obligation.negated_equivalence().to_smt2_expr(),
    };
    let canonical =
        serde_json::to_vec(&payload).expect("proof-obligation hash payload should serialize");
    sha256_prefixed(&canonical)
}

#[derive(Debug, Serialize)]
struct ProofObligationHashPayload<'a> {
    schema: &'static str,
    family: &'static str,
    source: &'a str,
    name: &'a str,
    category: Option<String>,
    inputs: &'a [(String, u32)],
    fp_inputs: &'a [(String, u32, u32)],
    preconditions_smt2: Vec<String>,
    trust_ir_expr_smt2: String,
    aarch64_expr_smt2: String,
    negated_equivalence_smt2: String,
}

fn result_sort_label(sort: &SmtSort) -> String {
    match sort {
        SmtSort::Bool => "bool".to_string(),
        SmtSort::BitVec(width) => format!("bv{width}"),
        SmtSort::FloatingPoint(exponent_bits, significand_bits) => {
            format!("fp{exponent_bits}_{significand_bits}")
        }
        SmtSort::Array(index, value) => {
            format!(
                "array({},{})",
                result_sort_label(index),
                result_sort_label(value)
            )
        }
    }
}

fn stable_slug(raw: &str) -> String {
    let mut slug = String::new();
    let mut last_was_separator = false;

    for byte in raw.bytes() {
        let ch = byte as char;
        if ch.is_ascii_alphanumeric() {
            slug.push(ch.to_ascii_lowercase());
            last_was_separator = false;
        } else if !last_was_separator {
            slug.push('_');
            last_was_separator = true;
        }
    }

    let trimmed = slug.trim_matches('_');
    if trimmed.is_empty() {
        "row".to_string()
    } else {
        trimmed.to_string()
    }
}

fn sha256_prefixed(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity("sha256:".len() + digest.len() * 2);
    out.push_str("sha256:");
    for byte in digest {
        out.push(hex_digit(byte >> 4));
        out.push(hex_digit(byte & 0x0f));
    }
    out
}

fn hex_digit(nibble: u8) -> char {
    match nibble {
        0..=9 => (b'0' + nibble) as char,
        10..=15 => (b'a' + (nibble - 10)) as char,
        _ => unreachable!("nibble is masked to four bits"),
    }
}
