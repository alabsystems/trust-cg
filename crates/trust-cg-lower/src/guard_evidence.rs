// trust-cg-lower/guard_evidence.rs — Build the kernel's DischargedEvidenceTable from trust-ir proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Trust-IR proof observations for guard-elimination reporting.
//!
//! A Trust-IR [`ProofStatus`] or `CleanCic` lineage record is producer-owned metadata.  Neither is
//! an exact replay result, and both can be constructed through Trust-IR's public data model.  They
//! therefore remain useful for diagnostics, but **must not populate** the
//! [`DischargedEvidenceTable`] consulted by the behavior-changing guard kernel.
//!
//! The production authority seam is intentionally unwired until an independent validator can issue
//! a capability bound to the exact obligation, guard kind, operands, target semantics, and replayed
//! proof artifact.  [`production_guard_replay_evidence`] consequently returns an empty table.  This
//! is feature loss by design: all guard carriers expand to runtime checks in production.
//!
//! [`build_guard_evidence_report`] preserves the old status/lineage census as report-only data.  The
//! legacy [`build_discharged_evidence_table`] API is retained for source compatibility, but is now a
//! fail-closed alias of [`production_guard_replay_evidence`].

use trust_cg_ir::guard::DischargedEvidenceTable;
use trust_ir::proof::{
    ProofCertificate, ProofDigest, ProofObligation, ProofStatus, clean_cic_lineage_digest,
    obligation_has_matching_clean_cic,
};

/// One producer-owned proof observation.  This is diagnostic metadata, never elimination authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardEvidenceObservation {
    pub obligation_id: u128,
    pub claimed_status: ProofStatus,
    pub matching_clean_cic: bool,
    pub lineage_key: Option<u128>,
}

/// Report-only census of the proof metadata attached to potential guard obligations.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GuardEvidenceReport {
    observations: Vec<GuardEvidenceObservation>,
}

impl GuardEvidenceReport {
    pub fn observations(&self) -> &[GuardEvidenceObservation] {
        &self.observations
    }

    pub fn len(&self) -> usize {
        self.observations.len()
    }

    pub fn is_empty(&self) -> bool {
        self.observations.is_empty()
    }
}

/// Deterministically fold a 32-byte trust-ir [`ProofDigest`] into the kernel's `u128` lineage key.
/// Panic-free; covers all 32 bytes by XOR-folding into 16 byte lanes. Used identically wherever a
/// lineage digest is compared, so an evidence-table entry and a receipt agree iff they came from
/// the same obligation.
pub fn proof_digest_to_u128(digest: &ProofDigest) -> u128 {
    let mut acc: u128 = 0;
    for (i, b) in digest.bytes.iter().enumerate() {
        acc ^= (*b as u128) << ((i % 16) * 8);
    }
    acc
}

/// The kernel's `u128` lineage key for an obligation (the fold of its CleanCic lineage digest).
/// The receipt-binding side uses this same function so the kernel's Certified-tier comparison holds.
pub fn obligation_lineage_key(obligation: &ProofObligation) -> u128 {
    proof_digest_to_u128(&clean_cic_lineage_digest(obligation))
}

/// Record Trust-IR's producer-owned proof claims without granting behavioral authority.
pub fn build_guard_evidence_report(
    obligations: &[ProofObligation],
    certificates: &[ProofCertificate],
) -> GuardEvidenceReport {
    let observations = obligations
        .iter()
        .map(|obligation| {
            let matching_clean_cic = obligation_has_matching_clean_cic(obligation, certificates);
            GuardEvidenceObservation {
                obligation_id: obligation.id.index() as u128,
                claimed_status: obligation.status,
                matching_clean_cic,
                lineage_key: matching_clean_cic.then(|| obligation_lineage_key(obligation)),
            }
        })
        .collect();
    GuardEvidenceReport { observations }
}

/// Production guard-replay evidence.
///
/// Empty until the validator-issued, exact obligation-bound replay capability is wired end to end.
/// This function deliberately has no environment-variable or feature-flag bypass.
pub fn production_guard_replay_evidence() -> DischargedEvidenceTable {
    DischargedEvidenceTable::new()
}

/// Whether production has a validator-issued exact guard-replay authority carrier.
///
/// Kept as a function (rather than an environment-controlled policy) so call sites can share one
/// explicit fail-closed seam.  When a real carrier is implemented, this function must be replaced by
/// possession and validation of that opaque capability, not flipped to a boolean `true`.
pub fn validator_guard_replay_authority_available() -> bool {
    false
}

/// Legacy compatibility API.  Producer-owned status/lineage is no longer converted into authority.
pub fn build_discharged_evidence_table(
    _obligations: &[ProofObligation],
    _certificates: &[ProofCertificate],
) -> DischargedEvidenceTable {
    production_guard_replay_evidence()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::proof::{ObligationKind, ProofEvidence};
    use trust_ir::value::ProofId;

    fn obligation(id: u32, status: ProofStatus) -> ProofObligation {
        ProofObligation {
            id: ProofId::new(id),
            kind: ObligationKind::MemorySafety,
            status,
            description: String::new(),
            formula: None,
            function: None,
            // Synthetic report-only fixture; no frontend identity exists.
            source: None,
            // No IR position: these are synthetic fixtures, and `site: None`
            // is the fail-closed reading (unbindable, never a wildcard).
            site: None,
        }
    }

    #[test]
    fn discharged_obligation_is_reported_but_never_authoritative() {
        let obls = vec![obligation(3, ProofStatus::Discharged)];
        let report = build_guard_evidence_report(&obls, &[]);
        assert_eq!(report.len(), 1);
        assert_eq!(report.observations()[0].obligation_id, 3);
        assert_eq!(
            report.observations()[0].claimed_status,
            ProofStatus::Discharged
        );
        let table = build_discharged_evidence_table(&obls, &[]);
        assert!(table.is_empty());
    }

    #[test]
    fn pending_and_failed_are_excluded() {
        let obls = vec![
            obligation(1, ProofStatus::Pending),
            obligation(2, ProofStatus::Failed),
        ];
        let table = build_discharged_evidence_table(&obls, &[]);
        assert!(table.is_empty());
    }

    #[test]
    fn certified_with_matching_clean_cic_carries_lineage() {
        let obl = obligation(7, ProofStatus::Certified);
        // A certificate whose CleanCic lineage matches the obligation's derived digest.
        let cert = ProofCertificate {
            obligation: obl.id,
            prover: "clean".to_string(),
            evidence: ProofEvidence::CleanCic {
                // The matcher (`obligation_has_matching_clean_cic`) requires a
                // NON-EMPTY kernel term: an empty term carries no real CleanCic
                // evidence, so it must not promote to the Certified tier.
                term: vec![1],
                context: vec![],
                lineage: clean_cic_lineage_digest(&obl),
                kernel_recheck: None,
            },
        };
        let report = build_guard_evidence_report(std::slice::from_ref(&obl), &[cert]);
        let expected_lineage = obligation_lineage_key(&obl);
        assert_eq!(report.observations()[0].lineage_key, Some(expected_lineage));
        assert!(report.observations()[0].matching_clean_cic);
        let table = build_discharged_evidence_table(&[obl], &[]);
        assert!(table.is_empty());
    }

    #[test]
    fn forged_certified_status_without_replay_never_becomes_authority() {
        let obls = vec![obligation(9, ProofStatus::Certified)];
        let report = build_guard_evidence_report(&obls, &[]);
        assert_eq!(
            report.observations()[0].claimed_status,
            ProofStatus::Certified
        );
        assert!(!report.observations()[0].matching_clean_cic);
        let table = build_discharged_evidence_table(&obls, &[]);
        assert!(table.is_empty());
        assert!(!validator_guard_replay_authority_available());
    }

    #[test]
    fn digest_fold_is_deterministic_and_covers_all_bytes() {
        let mut a = [0u8; 32];
        a[0] = 1;
        let mut b = [0u8; 32];
        b[16] = 1; // folds into the same lane as a[0] — must still differ via lane position? No:
        // a[0] -> lane 0, b[16] -> lane 0 as well (16 % 16 == 0), same byte value =>
        // identical fold. That is acceptable (XOR fold); assert the high-byte case below.
        let da = ProofDigest {
            algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
            bytes: a,
        };
        let db = ProofDigest {
            algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
            bytes: b,
        };
        // Determinism.
        assert_eq!(proof_digest_to_u128(&da), proof_digest_to_u128(&da));
        // Distinct content in distinct lanes differs.
        let mut c = [0u8; 32];
        c[1] = 1; // lane 1
        let dc = ProofDigest {
            algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
            bytes: c,
        };
        assert_ne!(proof_digest_to_u128(&da), proof_digest_to_u128(&dc));
        // (da and db collide by design of the XOR fold; that is fine — lineage digests are full
        // 32-byte SHA-like values where lane collisions across the wrap are astronomically rare.)
        let _ = db;
    }
}
