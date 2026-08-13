// trust-cg-verify/tests/aarch64_backend_proof_report.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeSet;

use trust_cg_verify::aarch64_backend_proof_report::{
    AARCH64_BACKEND_PROOF_FAMILY_REPORT_SCHEMA, AARCH64_BACKEND_PROOF_OBLIGATION_SET,
    AARCH64_BACKEND_PROOF_TARGET, Aarch64BackendProofEvidenceKind, Aarch64BackendProofFamily,
    Aarch64BackendProofFamilyReport, Aarch64BackendProofRow,
    build_aarch64_backend_proof_family_report,
};
use trust_cg_verify::smt_bv_batch::{
    AARCH64_SMT_BV_BATCH_PROOF_CONSUMPTION_SCHEMA, AARCH64_SMT_BV_BATCH_PROOF_CONSUMPTION_VERSION,
    SmtBvAarch64ProofConsumptionReport, SmtBvAarch64ProofRecord, SmtBvBatchStatus, SmtBvOutcome,
    build_aarch64_smt_bv_batch_proof_consumption_report,
};

fn assert_sha256_prefixed_lowercase(value: &str) {
    let digest = value
        .strip_prefix("sha256:")
        .expect("hash should use sha256: prefix");
    assert_eq!(digest.len(), 64, "sha256 digest should be 64 hex chars");
    assert!(
        digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "sha256 digest should be lowercase hex: {value}"
    );
}

fn smt_bv_batch_consumable_rows(
    report: &Aarch64BackendProofFamilyReport,
) -> Vec<&Aarch64BackendProofRow> {
    report
        .rows
        .iter()
        .filter(|row| {
            row.evidence_kind == Aarch64BackendProofEvidenceKind::ProofObligation
                && row.fp_input_widths.is_empty()
                && row
                    .result_sort
                    .strip_prefix("bv")
                    .and_then(|width| width.parse::<u32>().ok())
                    .is_some_and(|width| width > 0)
                && row.input_widths.iter().all(|width| *width > 0)
        })
        .collect()
}

fn consumed_region<'a>(
    consumption: &'a SmtBvAarch64ProofConsumptionReport,
    row: &Aarch64BackendProofRow,
) -> &'a trust_cg_verify::smt_bv_batch::SmtBvAarch64RegionStatus {
    consumption
        .regions
        .iter()
        .find(|region| region.region_id == row.row_id)
        .expect("consumption report should contain source row")
}

#[test]
fn report_has_required_schema_target_policy_and_row_counts() {
    let report = build_aarch64_backend_proof_family_report();

    assert_eq!(report.schema, AARCH64_BACKEND_PROOF_FAMILY_REPORT_SCHEMA);
    assert_eq!(report.target, AARCH64_BACKEND_PROOF_TARGET);
    assert_eq!(report.obligation_set, AARCH64_BACKEND_PROOF_OBLIGATION_SET);
    assert_eq!(
        report.obligation_set,
        "aarch64-ldp-lse-scheduler-switch-address-mode-frame-call-lowering-regalloc-v1"
    );
    assert!(report.policy.metadata_only);
    assert!(!report.policy.installable);
    assert!(!report.policy.product_promotion_allowed);
    assert_eq!(report.policy.disposition, "metadata_only_non_installable");

    let ldp_count = trust_cg_verify::memory_proofs::all_ldp_proofs().len();
    let atomic_count = trust_cg_verify::atomic_proofs::all_atomic_proofs().len();
    let scheduler_count = trust_cg_verify::scheduler_proofs::all_scheduler_proofs().len();
    let switch_count = trust_cg_verify::switch_proofs::all_switch_proofs().len();
    let addr_mode_count = trust_cg_verify::addr_mode_proofs::all_addr_mode_proofs().len();
    let frame_count = trust_cg_verify::frame_proofs::all_frame_proofs().len();
    let call_lowering_count =
        trust_cg_verify::call_lowering_proofs::all_call_lowering_proofs().len();
    let regalloc_count = trust_cg_verify::regalloc_proofs::all_regalloc_proofs().len();
    // #62: degenerate X==X proofs retracted across atomic (16 old-value + 3 fence),
    // scheduler (6), addr_mode (8), frame (12), call_lowering (98), regalloc (12).
    // call_lowering = 5 structural + 2 memory-model aggregate placement proofs
    // (scalar-pair eightbyte + 4xF32 HFA lane) = 7.
    assert_eq!(ldp_count, 3);
    assert_eq!(atomic_count, 36);
    assert_eq!(scheduler_count, 24);
    assert_eq!(switch_count, 9);
    assert_eq!(addr_mode_count, 10);
    assert_eq!(frame_count, 18);
    assert_eq!(call_lowering_count, 7);
    assert_eq!(regalloc_count, 31);
    assert_eq!(
        report.rows.len(),
        ldp_count
            + atomic_count
            + scheduler_count
            + switch_count
            + addr_mode_count
            + frame_count
            + call_lowering_count
            + regalloc_count
            + 2
    );

    assert_eq!(
        report
            .rows
            .iter()
            .filter(|row| row.family == Aarch64BackendProofFamily::Ldp)
            .count(),
        ldp_count
    );
    assert_eq!(
        report
            .rows
            .iter()
            .filter(|row| row.family == Aarch64BackendProofFamily::Scheduler)
            .count(),
        scheduler_count
    );
    assert_eq!(
        report
            .rows
            .iter()
            .filter(|row| row.family == Aarch64BackendProofFamily::Switch)
            .count(),
        switch_count
    );
    assert_eq!(
        report
            .rows
            .iter()
            .filter(|row| row.family == Aarch64BackendProofFamily::AddressMode)
            .count(),
        addr_mode_count
    );
    assert_eq!(
        report
            .rows
            .iter()
            .filter(|row| row.family == Aarch64BackendProofFamily::Frame)
            .count(),
        frame_count
    );
    assert_eq!(
        report
            .rows
            .iter()
            .filter(|row| row.family == Aarch64BackendProofFamily::CallLowering)
            .count(),
        call_lowering_count
    );
    assert_eq!(
        report
            .rows
            .iter()
            .filter(|row| row.family == Aarch64BackendProofFamily::RegAlloc)
            .count(),
        regalloc_count
    );
    assert_eq!(
        report
            .rows
            .iter()
            .filter(|row| row.family == Aarch64BackendProofFamily::Lse)
            .count(),
        atomic_count + 2
    );
}

#[test]
fn report_rows_are_metadata_only_non_installable_and_stably_ordered() {
    let report = build_aarch64_backend_proof_family_report();

    let keys: Vec<String> = report
        .rows
        .iter()
        .map(|row| row.stable_sort_key())
        .collect();
    let mut sorted_keys = keys.clone();
    sorted_keys.sort();
    assert_eq!(keys, sorted_keys, "report rows should be in stable order");

    let mut family_order = Vec::new();
    for row in &report.rows {
        if family_order.last().copied() != Some(row.family) {
            family_order.push(row.family);
        }
    }
    assert_eq!(
        family_order,
        vec![
            Aarch64BackendProofFamily::Ldp,
            Aarch64BackendProofFamily::Lse,
            Aarch64BackendProofFamily::Scheduler,
            Aarch64BackendProofFamily::Switch,
            Aarch64BackendProofFamily::AddressMode,
            Aarch64BackendProofFamily::Frame,
            Aarch64BackendProofFamily::CallLowering,
            Aarch64BackendProofFamily::RegAlloc,
        ]
    );

    let mut row_ids = BTreeSet::new();
    for row in &report.rows {
        assert_eq!(row.target, AARCH64_BACKEND_PROOF_TARGET);
        assert!(row.metadata_only);
        assert!(!row.installable);
        assert!(row_ids.insert(row.row_id.clone()), "duplicate row id");
        assert_sha256_prefixed_lowercase(&row.evidence_hash);
    }
}

#[test]
fn report_contains_all_backend_proof_obligation_rows() {
    let report = build_aarch64_backend_proof_family_report();

    let ldp_names: BTreeSet<String> = trust_cg_verify::memory_proofs::all_ldp_proofs()
        .into_iter()
        .map(|proof| proof.name)
        .collect();
    let atomic_names: BTreeSet<String> = trust_cg_verify::atomic_proofs::all_atomic_proofs()
        .into_iter()
        .map(|proof| proof.name)
        .collect();
    let scheduler_names: BTreeSet<String> =
        trust_cg_verify::scheduler_proofs::all_scheduler_proofs()
            .into_iter()
            .map(|proof| proof.name)
            .collect();
    let switch_names: BTreeSet<String> = trust_cg_verify::switch_proofs::all_switch_proofs()
        .into_iter()
        .map(|proof| proof.name)
        .collect();
    let addr_mode_names: BTreeSet<String> =
        trust_cg_verify::addr_mode_proofs::all_addr_mode_proofs()
            .into_iter()
            .map(|proof| proof.name)
            .collect();
    let frame_proofs = trust_cg_verify::frame_proofs::all_frame_proofs();
    let frame_transval_check_kinds: Vec<String> = frame_proofs
        .iter()
        .map(|proof| {
            proof
                .category
                .expect("frame proofs should carry a TransvalCheckKind")
                .to_string()
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    assert_eq!(frame_transval_check_kinds, vec!["regalloc".to_string()]);
    let frame_transval_check_kind = frame_transval_check_kinds[0].as_str();
    let frame_names: BTreeSet<String> = frame_proofs.into_iter().map(|proof| proof.name).collect();
    let call_lowering_proofs = trust_cg_verify::call_lowering_proofs::all_call_lowering_proofs();
    let call_lowering_transval_check_kinds: Vec<String> = call_lowering_proofs
        .iter()
        .map(|proof| {
            proof
                .category
                .expect("call-lowering proofs should carry a TransvalCheckKind")
                .to_string()
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    assert_eq!(
        call_lowering_transval_check_kinds,
        vec!["instruction_lowering".to_string()]
    );
    let call_lowering_transval_check_kind = call_lowering_transval_check_kinds[0].as_str();
    let call_lowering_names: BTreeSet<String> = call_lowering_proofs
        .into_iter()
        .map(|proof| proof.name)
        .collect();
    let regalloc_proofs = trust_cg_verify::regalloc_proofs::all_regalloc_proofs();
    let regalloc_transval_check_kinds: Vec<String> = regalloc_proofs
        .iter()
        .map(|proof| {
            proof
                .category
                .expect("regalloc proofs should carry a TransvalCheckKind")
                .to_string()
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    assert_eq!(regalloc_transval_check_kinds, vec!["regalloc".to_string()]);
    let regalloc_transval_check_kind = regalloc_transval_check_kinds[0].as_str();
    let regalloc_names: BTreeSet<String> = regalloc_proofs
        .into_iter()
        .map(|proof| proof.name)
        .collect();

    let report_ldp_names: BTreeSet<String> = report
        .rows
        .iter()
        .filter(|row| row.family == Aarch64BackendProofFamily::Ldp)
        .map(|row| {
            assert_eq!(
                row.evidence_kind,
                Aarch64BackendProofEvidenceKind::ProofObligation
            );
            assert_eq!(row.source, "memory_proofs::all_ldp_proofs()");
            assert_eq!(row.transval_check_kind.as_deref(), Some("memory"));
            row.evidence_id.clone()
        })
        .collect();
    let report_lse_proof_names: BTreeSet<String> = report
        .rows
        .iter()
        .filter(|row| {
            row.family == Aarch64BackendProofFamily::Lse
                && row.evidence_kind == Aarch64BackendProofEvidenceKind::ProofObligation
        })
        .map(|row| {
            assert_eq!(row.source, "atomic_proofs::all_atomic_proofs()");
            assert_eq!(row.transval_check_kind.as_deref(), Some("memory"));
            row.evidence_id.clone()
        })
        .collect();
    let report_scheduler_names: BTreeSet<String> = report
        .rows
        .iter()
        .filter(|row| row.family == Aarch64BackendProofFamily::Scheduler)
        .map(|row| {
            assert_eq!(
                row.evidence_kind,
                Aarch64BackendProofEvidenceKind::ProofObligation
            );
            assert_eq!(row.source, "scheduler_proofs::all_scheduler_proofs()");
            assert_eq!(
                row.transval_check_kind.as_deref(),
                Some("instruction_lowering")
            );
            row.evidence_id.clone()
        })
        .collect();
    let report_switch_names: BTreeSet<String> = report
        .rows
        .iter()
        .filter(|row| row.family == Aarch64BackendProofFamily::Switch)
        .map(|row| {
            assert_eq!(
                row.evidence_kind,
                Aarch64BackendProofEvidenceKind::ProofObligation
            );
            assert_eq!(row.source, "switch_proofs::all_switch_proofs()");
            assert_eq!(row.transval_check_kind.as_deref(), Some("control_flow"));
            row.evidence_id.clone()
        })
        .collect();
    let report_addr_mode_names: BTreeSet<String> = report
        .rows
        .iter()
        .filter(|row| row.family == Aarch64BackendProofFamily::AddressMode)
        .map(|row| {
            assert_eq!(
                row.evidence_kind,
                Aarch64BackendProofEvidenceKind::ProofObligation
            );
            assert_eq!(row.source, "addr_mode_proofs::all_addr_mode_proofs()");
            assert_eq!(
                row.transval_check_kind.as_deref(),
                Some("instruction_lowering")
            );
            row.evidence_id.clone()
        })
        .collect();
    let report_frame_names: BTreeSet<String> = report
        .rows
        .iter()
        .filter(|row| row.family == Aarch64BackendProofFamily::Frame)
        .map(|row| {
            assert_eq!(
                row.evidence_kind,
                Aarch64BackendProofEvidenceKind::ProofObligation
            );
            assert_eq!(row.source, "frame_proofs::all_frame_proofs()");
            assert_eq!(
                row.transval_check_kind.as_deref(),
                Some(frame_transval_check_kind)
            );
            row.evidence_id.clone()
        })
        .collect();
    let report_call_lowering_names: BTreeSet<String> = report
        .rows
        .iter()
        .filter(|row| row.family == Aarch64BackendProofFamily::CallLowering)
        .map(|row| {
            assert_eq!(
                row.evidence_kind,
                Aarch64BackendProofEvidenceKind::ProofObligation
            );
            assert_eq!(
                row.source,
                "call_lowering_proofs::all_call_lowering_proofs()"
            );
            assert_eq!(
                row.transval_check_kind.as_deref(),
                Some(call_lowering_transval_check_kind)
            );
            row.evidence_id.clone()
        })
        .collect();
    let report_regalloc_names: BTreeSet<String> = report
        .rows
        .iter()
        .filter(|row| row.family == Aarch64BackendProofFamily::RegAlloc)
        .map(|row| {
            assert_eq!(
                row.evidence_kind,
                Aarch64BackendProofEvidenceKind::ProofObligation
            );
            assert_eq!(row.source, "regalloc_proofs::all_regalloc_proofs()");
            assert_eq!(
                row.transval_check_kind.as_deref(),
                Some(regalloc_transval_check_kind)
            );
            row.evidence_id.clone()
        })
        .collect();

    assert_eq!(report_ldp_names, ldp_names);
    assert_eq!(report_lse_proof_names, atomic_names);
    assert_eq!(report_scheduler_names, scheduler_names);
    assert_eq!(report_switch_names, switch_names);
    assert_eq!(report_addr_mode_names, addr_mode_names);
    assert_eq!(report_frame_names, frame_names);
    assert_eq!(report_call_lowering_names, call_lowering_names);
    assert_eq!(report_regalloc_names, regalloc_names);
}

#[test]
fn report_contains_explicit_lse_contract_and_test_evidence_rows() {
    let report = build_aarch64_backend_proof_family_report();
    let lse_rows: Vec<_> = report
        .rows
        .iter()
        .filter(|row| {
            row.family == Aarch64BackendProofFamily::Lse
                && row.evidence_kind != Aarch64BackendProofEvidenceKind::ProofObligation
        })
        .collect();

    assert_eq!(lse_rows.len(), 2);
    assert!(lse_rows.iter().any(|row| {
        row.evidence_kind == Aarch64BackendProofEvidenceKind::Contract
            && row.evidence_id == "aarch64_lse_atomic_dataflow_contract_v1"
    }));
    assert!(lse_rows.iter().any(|row| {
        row.evidence_kind == Aarch64BackendProofEvidenceKind::Test
            && row.evidence_id == "atomic_proofs::tests::test_all_atomic_proofs_valid"
    }));

    for row in lse_rows {
        assert_eq!(row.result_sort, "metadata");
        assert!(row.transval_check_kind.is_none());
        assert!(row.input_widths.is_empty());
        assert!(row.fp_input_widths.is_empty());
    }
}

#[test]
fn report_hash_is_stable_lowercase_sha256_and_mutation_sensitive() {
    let report = build_aarch64_backend_proof_family_report();
    let rebuilt = build_aarch64_backend_proof_family_report();

    assert_eq!(report.report_hash, report.compute_report_hash());
    assert_eq!(report.report_hash, rebuilt.report_hash);
    assert_sha256_prefixed_lowercase(&report.report_hash);

    let mut mutated = report.clone();
    mutated.rows[0].evidence_id.push_str("_mutated");
    assert_ne!(report.report_hash, mutated.compute_report_hash());

    let json = serde_json::to_value(&report).expect("report should serialize to JSON");
    assert_eq!(json["schema"], AARCH64_BACKEND_PROOF_FAMILY_REPORT_SCHEMA);
    assert_eq!(json["report_hash"], report.report_hash);
}

#[test]
fn smt_bv_batch_consumes_aarch64_backend_report_metadata_only() {
    let report = build_aarch64_backend_proof_family_report();
    let rows = smt_bv_batch_consumable_rows(&report);
    assert!(
        rows.len() >= 5,
        "AArch64 report should expose SMT BV proof rows for batch consumption"
    );

    let records = vec![
        SmtBvAarch64ProofRecord::from_report_row(
            &report,
            rows[0],
            SmtBvOutcome::status(SmtBvBatchStatus::Verified),
        )
        .with_proof_cache_key("ay-cache:verified"),
        SmtBvAarch64ProofRecord::from_report_row(
            &report,
            rows[1],
            SmtBvOutcome::refuted(vec![("x".to_string(), 0x2a)]),
        )
        .with_proof_cache_key("ay-cache:refuted"),
        SmtBvAarch64ProofRecord::from_report_row(
            &report,
            rows[2],
            SmtBvOutcome::unknown("solver returned unknown"),
        )
        .with_proof_cache_key("ay-cache:unknown"),
        SmtBvAarch64ProofRecord::from_report_row(
            &report,
            rows[3],
            SmtBvOutcome::status(SmtBvBatchStatus::Timeout),
        )
        .with_proof_cache_key("ay-cache:timeout"),
        SmtBvAarch64ProofRecord::from_report_row(
            &report,
            rows[4],
            SmtBvOutcome::internal_error("solver transport failed"),
        )
        .with_proof_cache_key("ay-cache:internal-error"),
    ];

    let consumption = build_aarch64_smt_bv_batch_proof_consumption_report(&report, &records);

    assert_eq!(
        consumption.schema,
        AARCH64_SMT_BV_BATCH_PROOF_CONSUMPTION_SCHEMA
    );
    assert_eq!(
        consumption.schema_version,
        AARCH64_SMT_BV_BATCH_PROOF_CONSUMPTION_VERSION
    );
    assert_eq!(
        consumption.source_report_schema,
        AARCH64_BACKEND_PROOF_FAMILY_REPORT_SCHEMA
    );
    assert_eq!(consumption.source_report_hash, report.report_hash);
    assert_eq!(consumption.target, AARCH64_BACKEND_PROOF_TARGET);
    assert_eq!(
        consumption.obligation_set,
        AARCH64_BACKEND_PROOF_OBLIGATION_SET
    );
    assert!(consumption.metadata_only);
    assert!(!consumption.installable);
    assert!(!consumption.product_promotion_allowed);
    assert_eq!(consumption.promotion_policy.promotion_status, "blocked");
    assert_eq!(consumption.promotion_policy.install_status, "blocked");
    assert_eq!(
        consumption.promotion_policy.blocked_by,
        vec!["#660".to_string(), "#664".to_string()]
    );
    assert_eq!(consumption.regions.len(), report.rows.len());
    assert_eq!(consumption.status_counts.total(), report.rows.len());

    assert_eq!(
        consumed_region(&consumption, rows[0]).status,
        SmtBvBatchStatus::Verified
    );
    let refuted = consumed_region(&consumption, rows[1]);
    assert_eq!(refuted.status, SmtBvBatchStatus::Refuted);
    assert_eq!(
        refuted.outcome.counterexample,
        vec![("x".to_string(), 0x2a)]
    );
    assert_eq!(
        consumed_region(&consumption, rows[2]).status,
        SmtBvBatchStatus::Unknown
    );
    assert_eq!(
        consumed_region(&consumption, rows[3]).status,
        SmtBvBatchStatus::Timeout
    );
    assert_eq!(
        consumed_region(&consumption, rows[4]).status,
        SmtBvBatchStatus::InternalError
    );

    let unsupported_metadata = consumption
        .regions
        .iter()
        .find(|region| region.evidence_kind != Aarch64BackendProofEvidenceKind::ProofObligation)
        .expect("report should include explicit metadata evidence rows");
    assert_eq!(unsupported_metadata.status, SmtBvBatchStatus::Unsupported);
    assert!(
        unsupported_metadata
            .outcome
            .detail
            .as_deref()
            .expect("unsupported rows should explain why")
            .contains("metadata-only")
    );

    for status in SmtBvBatchStatus::vocabulary() {
        assert!(
            consumption.status_vocabulary.contains(&status),
            "status vocabulary should include {}",
            status.as_str()
        );
    }
    assert_eq!(consumption.status_counts.verified, 1);
    assert_eq!(consumption.status_counts.refuted, 1);
    assert!(consumption.status_counts.unsupported >= 1);
    assert!(consumption.status_counts.unknown >= 1);
    assert_eq!(consumption.status_counts.timeout, 1);
    assert_eq!(consumption.status_counts.internal_error, 1);

    let json = serde_json::to_value(&consumption).expect("consumption report should serialize");
    assert_eq!(json["metadata_only"], true);
    assert_eq!(json["installable"], false);
    assert_eq!(json["product_promotion_allowed"], false);
    assert_eq!(json["status_vocabulary"][6], "internal_error");
}

#[test]
fn smt_bv_batch_consumption_marks_stale_proof_cache() {
    let report = build_aarch64_backend_proof_family_report();
    let rows = smt_bv_batch_consumable_rows(&report);
    let row = rows[0];
    let mut stale_record = SmtBvAarch64ProofRecord::from_report_row(
        &report,
        row,
        SmtBvOutcome::status(SmtBvBatchStatus::Verified),
    )
    .with_proof_cache_key("ay-cache:stale");
    stale_record.evidence_hash =
        "sha256:0000000000000000000000000000000000000000000000000000000000000000".to_string();

    let consumption = build_aarch64_smt_bv_batch_proof_consumption_report(&report, &[stale_record]);
    let region = consumed_region(&consumption, row);

    assert_eq!(region.status, SmtBvBatchStatus::StaleCache);
    assert_eq!(region.proof_cache_key.as_deref(), Some("ay-cache:stale"));
    assert!(
        region
            .outcome
            .detail
            .as_deref()
            .expect("stale cache should explain why")
            .contains("evidence hash")
    );
    assert_eq!(consumption.status_counts.stale_cache, 1);
}
