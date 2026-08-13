// trust-cg-codegen/tests/jit_diagnostics.rs - JIT diagnostics replay metadata
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use serde_json::{Value, json};
use trust_cg_codegen::{
    JIT_CRASH_REPORT_SCHEMA, JIT_CRASH_REPORT_SCHEMA_VERSION, JIT_REPLAY_SCHEMA,
    JIT_REPLAY_SCHEMA_VERSION, JitCodeRange, JitCrashKind, JitCrashReportMetadata, JitPcMapEntry,
    JitReplayReportMetadata, JitSymbolLabel, JitTrapStatusBlock, JitTrapStatusKind,
    ProofOptimizationCertificateCitation, ProofOptimizationConsumedFactCitation,
};

fn shuffled_report(reverse: bool) -> JitReplayReportMetadata {
    let symbols = vec![
        JitSymbolLabel::new("compute", JitCodeRange::new(16, 48)).with_aliases([
            "_compute",
            "compute_alias",
            "_compute",
        ]),
        JitSymbolLabel::new("init", JitCodeRange::new(0, 16)).with_aliases(["init_alias", "_init"]),
    ];
    let pc_map = vec![
        JitPcMapEntry::new(28, "compute", 12)
            .with_machine_inst_index(3)
            .with_source_label("Next")
            .with_trust_ir_op("iadd"),
        JitPcMapEntry::new(4, "init", 4)
            .with_machine_inst_index(1)
            .with_source_label("Init")
            .with_trust_ir_op("call"),
        JitPcMapEntry::new(20, "compute", 4)
            .with_machine_inst_index(2)
            .with_source_label("Next")
            .with_trust_ir_op("icmp"),
    ];
    let statuses = vec![
        JitTrapStatusBlock::new(20, JitTrapStatusKind::NativeTrap, "execute")
            .with_symbol("compute")
            .with_pc_offset(28)
            .with_message("trap block 7"),
        JitTrapStatusBlock::new(10, JitTrapStatusKind::VerifierRejected, "verify")
            .with_symbol("init")
            .with_message("proof obligation failed"),
    ];

    let mut report = JitReplayReportMetadata::new(48);
    report.artifact_id = Some("trust-cg-stable128:0123456789abcdef".to_string());
    report.target = Some("aarch64-apple-darwin".to_string());
    report.entry_symbol = Some("init".to_string());
    report
        .properties
        .insert("frontend".to_string(), "ty".to_string());
    report
        .properties
        .insert("replay_seed".to_string(), "0x1234".to_string());

    if reverse {
        report.symbols = symbols.into_iter().rev().collect();
        report.pc_map = pc_map.into_iter().rev().collect();
        report.statuses = statuses.into_iter().rev().collect();
    } else {
        report.symbols = symbols;
        report.pc_map = pc_map;
        report.statuses = statuses;
    }

    report
}

fn proof_opt_citation(
    function_name: &str,
    certificate_id: &str,
) -> ProofOptimizationCertificateCitation {
    ProofOptimizationCertificateCitation {
        function_name: function_name.to_owned(),
        certificate_id: certificate_id.to_owned(),
        proof_hash: "00000000000000000000000000000002".to_owned(),
        validation_hash: "00000000000000000000000000000003".to_owned(),
        source_region_hash: "00000000000000000000000000000004".to_owned(),
        target_region_hash: "00000000000000000000000000000005".to_owned(),
        transform_name: "proof-opts.no-overflow".to_owned(),
        transform_version: 1,
        admission: "proof-annotation+proof-facts".to_owned(),
        kind: "CheckedToUnchecked".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: vec![ProofOptimizationConsumedFactCitation {
            name: "NoUndef".to_owned(),
            payload: None,
        }],
    }
}

#[test]
fn replay_report_pretty_json_is_canonical_from_shuffled_inputs() {
    let left = shuffled_report(false).to_pretty_json();
    let right = shuffled_report(true).to_pretty_json();

    assert_eq!(left, right);
    assert!(left.ends_with('\n'));

    let parsed: Value = serde_json::from_str(&left).expect("report JSON should parse");
    assert_eq!(parsed["schema"], JIT_REPLAY_SCHEMA);
    assert_eq!(parsed["schema_version"], JIT_REPLAY_SCHEMA_VERSION);
    assert_eq!(parsed["producer"], "trust-cg-codegen");
    assert_eq!(parsed["code_size"], 48);

    assert_eq!(parsed["symbols"][0]["name"], "init");
    assert_eq!(parsed["symbols"][0]["range"]["start_offset"], 0);
    assert_eq!(parsed["symbols"][0]["range"]["end_offset"], 16);
    assert_eq!(
        parsed["symbols"][0]["aliases"],
        json!(["_init", "init_alias"])
    );
    assert_eq!(parsed["symbols"][1]["name"], "compute");
    assert_eq!(
        parsed["symbols"][1]["aliases"],
        json!(["_compute", "compute_alias"])
    );

    let pc_offsets: Vec<_> = parsed["pc_map"]
        .as_array()
        .expect("pc_map should be an array")
        .iter()
        .map(|entry| entry["pc_offset"].as_u64().expect("pc_offset is u64"))
        .collect();
    assert_eq!(pc_offsets, vec![4, 20, 28]);

    let status_sequences: Vec<_> = parsed["statuses"]
        .as_array()
        .expect("statuses should be an array")
        .iter()
        .map(|entry| entry["sequence"].as_u64().expect("sequence is u64"))
        .collect();
    assert_eq!(status_sequences, vec![10, 20]);
    assert_eq!(parsed["statuses"][0]["kind"], "verifier_rejected");
    assert_eq!(parsed["statuses"][1]["kind"], "native_trap");

    assert_eq!(parsed["properties"]["frontend"], "ty");
    assert_eq!(parsed["properties"]["replay_seed"], "0x1234");
}

#[test]
fn replay_report_json_carries_proof_optimization_certificate_citations() {
    let mut report = JitReplayReportMetadata::new(16);
    report.proof_optimization_certificates = vec![
        proof_opt_citation("f_b", "0000000000000000000000000000000b"),
        proof_opt_citation("f_a", "0000000000000000000000000000000a"),
    ];

    let json = report.to_json_value();
    let citations = json["proof_optimization_certificates"]
        .as_array()
        .expect("replay metadata should serialize proof optimization citations");
    assert_eq!(citations.len(), 2);
    assert_eq!(citations[0]["function_name"].as_str(), Some("f_a"));
    assert_eq!(
        citations[0]["certificate_id"].as_str(),
        Some("0000000000000000000000000000000a")
    );
    assert_eq!(
        citations[0]["proof_hash"].as_str(),
        Some("00000000000000000000000000000002")
    );
    assert_eq!(
        citations[0]["validation_hash"].as_str(),
        Some("00000000000000000000000000000003")
    );
}

#[test]
fn replay_report_from_symbol_entries_builds_ranges_code_size_and_pc_map() {
    let report = JitReplayReportMetadata::from_symbol_entries([
        ("tail", 40, 8),
        ("entry", 0, 16),
        ("middle", 16, 12),
    ]);

    assert_eq!(report.code_size, 48);
    assert_eq!(report.pc_map.len(), 3);
    assert!(report.statuses.is_empty());

    let parsed = report.to_json_value();
    assert_eq!(parsed["schema"], JIT_REPLAY_SCHEMA);
    assert_eq!(parsed["schema_version"], JIT_REPLAY_SCHEMA_VERSION);
    assert_eq!(parsed["producer"], "trust-cg-codegen");
    assert_eq!(parsed["code_size"], 48);

    let symbols = parsed["symbols"]
        .as_array()
        .expect("symbols should be an array");
    assert_eq!(symbols.len(), 3);

    assert_eq!(symbols[0]["name"], "entry");
    assert_eq!(symbols[0]["range"]["start_offset"], 0);
    assert_eq!(symbols[0]["range"]["end_offset"], 16);
    assert_eq!(symbols[0]["range"]["byte_len"], 16);

    assert_eq!(symbols[1]["name"], "middle");
    assert_eq!(symbols[1]["range"]["start_offset"], 16);
    assert_eq!(symbols[1]["range"]["end_offset"], 28);
    assert_eq!(symbols[1]["range"]["byte_len"], 12);

    assert_eq!(symbols[2]["name"], "tail");
    assert_eq!(symbols[2]["range"]["start_offset"], 40);
    assert_eq!(symbols[2]["range"]["end_offset"], 48);
    assert_eq!(symbols[2]["range"]["byte_len"], 8);

    let pc_map = parsed["pc_map"]
        .as_array()
        .expect("pc_map should be an array");
    let expected_pc_map = json!([
        {
            "machine_inst_index": null,
            "pc_offset": 0,
            "source_label": null,
            "symbol": "entry",
            "symbol_offset": 0,
            "trust_ir_op": null,
        },
        {
            "machine_inst_index": null,
            "pc_offset": 16,
            "source_label": null,
            "symbol": "middle",
            "symbol_offset": 0,
            "trust_ir_op": null,
        },
        {
            "machine_inst_index": null,
            "pc_offset": 40,
            "source_label": null,
            "symbol": "tail",
            "symbol_offset": 0,
            "trust_ir_op": null,
        },
    ]);
    assert_eq!(
        pc_map,
        expected_pc_map
            .as_array()
            .expect("expected pc_map should be an array")
    );
}

#[test]
fn trap_status_kind_wire_names_are_stable() {
    let kinds = [
        (JitTrapStatusKind::Ok, "ok"),
        (JitTrapStatusKind::VerifierRejected, "verifier_rejected"),
        (JitTrapStatusKind::ReplayMismatch, "replay_mismatch"),
        (JitTrapStatusKind::NativeTrap, "native_trap"),
        (JitTrapStatusKind::HostSignal, "host_signal"),
        (JitTrapStatusKind::Panic, "panic"),
        (JitTrapStatusKind::Timeout, "timeout"),
        (JitTrapStatusKind::InternalError, "internal_error"),
        (JitTrapStatusKind::Unknown, "unknown"),
    ];

    for (kind, expected) in kinds {
        assert_eq!(kind.as_str(), expected);
        assert_eq!(kind.to_string(), expected);
    }
}

#[test]
fn phase3_status_matrix_replay_fixture_rows_are_non_promoting() {
    struct StatusMatrixRow {
        name: &'static str,
        kind: JitTrapStatusKind,
        stage: &'static str,
        failure_category: &'static str,
        failure_code: &'static str,
        install_disposition: &'static str,
        native_disposition: &'static str,
    }

    let rows = [
        StatusMatrixRow {
            name: "bounds",
            kind: JitTrapStatusKind::VerifierRejected,
            stage: "verify",
            failure_category: "bounds",
            failure_code: "bounds_check_rejected",
            install_disposition: "rejected",
            native_disposition: "reject",
        },
        StatusMatrixRow {
            name: "overflow",
            kind: JitTrapStatusKind::VerifierRejected,
            stage: "verify",
            failure_category: "overflow",
            failure_code: "checked_overflow_rejected",
            install_disposition: "rejected",
            native_disposition: "reject",
        },
        StatusMatrixRow {
            name: "stale-generation",
            kind: JitTrapStatusKind::ReplayMismatch,
            stage: "replay",
            failure_category: "stale",
            failure_code: "stale_generation",
            install_disposition: "replay_only",
            native_disposition: "stale",
        },
        StatusMatrixRow {
            name: "verifier-failure",
            kind: JitTrapStatusKind::VerifierRejected,
            stage: "verify",
            failure_category: "verifier",
            failure_code: "verifier_rejected",
            install_disposition: "rejected",
            native_disposition: "reject",
        },
        StatusMatrixRow {
            name: "timeout",
            kind: JitTrapStatusKind::Timeout,
            stage: "proof",
            failure_category: "timeout",
            failure_code: "proof_timeout",
            install_disposition: "replay_only",
            native_disposition: "deopt",
        },
        StatusMatrixRow {
            name: "native-trap",
            kind: JitTrapStatusKind::NativeTrap,
            stage: "execute",
            failure_category: "native_trap",
            failure_code: "native_trap",
            install_disposition: "replay_only",
            native_disposition: "fallback",
        },
        StatusMatrixRow {
            name: "host-signal",
            kind: JitTrapStatusKind::HostSignal,
            stage: "execute",
            failure_category: "host_signal",
            failure_code: "host_signal",
            install_disposition: "replay_only",
            native_disposition: "fallback",
        },
        StatusMatrixRow {
            name: "internal-error",
            kind: JitTrapStatusKind::InternalError,
            stage: "compile",
            failure_category: "internal_error",
            failure_code: "internal_error",
            install_disposition: "rejected",
            native_disposition: "internal_error",
        },
    ];

    let mut fixture_kinds = Vec::with_capacity(rows.len());
    let mut fixture_codes = Vec::with_capacity(rows.len());

    for (sequence, row) in rows.iter().enumerate() {
        let mut report = JitReplayReportMetadata::from_symbol_entries([
            ("entry", 0, 16),
            ("status_handler", 16, 16),
        ]);
        report.artifact_id = Some(format!("phase3-status-matrix-{}", row.name));
        report.target = Some("fixture-target".to_owned());
        report.entry_symbol = Some("entry".to_owned());
        report
            .properties
            .insert("epic".to_owned(), "#657".to_owned());
        report
            .properties
            .insert("parent_issue".to_owned(), "#661".to_owned());
        report
            .properties
            .insert("fixture_issue".to_owned(), "#710".to_owned());
        report
            .properties
            .insert("verifier_issue".to_owned(), "#704".to_owned());
        report
            .properties
            .insert("trap_issue".to_owned(), "#692".to_owned());
        report.properties.insert(
            "failure_category".to_owned(),
            row.failure_category.to_owned(),
        );
        report
            .properties
            .insert("failure_code".to_owned(), row.failure_code.to_owned());
        report.properties.insert(
            "install_disposition".to_owned(),
            row.install_disposition.to_owned(),
        );
        report.properties.insert(
            "native_disposition".to_owned(),
            row.native_disposition.to_owned(),
        );
        report.properties.insert(
            "promotion_disposition".to_owned(),
            "non_promoting".to_owned(),
        );
        report
            .properties
            .insert("useful_native_eligible".to_owned(), "false".to_owned());
        report
            .properties
            .insert("useful_native_count".to_owned(), "0".to_owned());
        report.statuses.push(
            JitTrapStatusBlock::new(sequence as u64, row.kind, row.stage)
                .with_symbol("status_handler")
                .with_pc_offset(16)
                .with_message(row.failure_code),
        );

        let json = report.to_json_value();
        assert_eq!(
            json["statuses"][0]["kind"],
            row.kind.as_str(),
            "{}",
            row.name
        );
        assert_eq!(
            json["properties"]["failure_category"], row.failure_category,
            "{}",
            row.name
        );
        assert_eq!(
            json["properties"]["failure_code"], row.failure_code,
            "{}",
            row.name
        );
        assert_ne!(
            json["properties"]["install_disposition"], "installable",
            "{}",
            row.name
        );
        assert_eq!(
            json["properties"]["promotion_disposition"], "non_promoting",
            "{}",
            row.name
        );
        assert_eq!(
            json["properties"]["useful_native_eligible"], "false",
            "{}",
            row.name
        );
        assert_eq!(
            json["properties"]["useful_native_count"], "0",
            "{}",
            row.name
        );

        fixture_kinds.push(
            json["statuses"][0]["kind"]
                .as_str()
                .expect("fixture status kind should be a string")
                .to_owned(),
        );
        fixture_codes.push(
            json["properties"]["failure_code"]
                .as_str()
                .expect("fixture failure code should be a string")
                .to_owned(),
        );
    }

    assert_eq!(
        fixture_kinds,
        vec![
            "verifier_rejected",
            "verifier_rejected",
            "replay_mismatch",
            "verifier_rejected",
            "timeout",
            "native_trap",
            "host_signal",
            "internal_error",
        ]
    );
    assert_eq!(
        fixture_codes,
        vec![
            "bounds_check_rejected",
            "checked_overflow_rejected",
            "stale_generation",
            "verifier_rejected",
            "proof_timeout",
            "native_trap",
            "host_signal",
            "internal_error",
        ]
    );
}

#[test]
fn code_ranges_are_half_open_and_report_stable_json() {
    let range = JitCodeRange::new(8, 24);

    assert!(range.is_valid());
    assert_eq!(range.byte_len(), 16);
    assert!(!range.contains(7));
    assert!(range.contains(8));
    assert!(range.contains(23));
    assert!(!range.contains(24));
    assert_eq!(
        range.to_json_value(),
        json!({
            "byte_len": 16,
            "end_offset": 24,
            "start_offset": 8,
            "valid": true,
        })
    );
}

#[test]
fn crash_report_pretty_json_is_canonical_and_preserves_routing_identity() {
    let mut left_replay = shuffled_report(false);
    left_replay.properties.insert(
        "artifact_manifest_checksum".to_string(),
        "manifest-sha256:1111".to_string(),
    );
    left_replay.properties.insert(
        "native_payload_sha256".to_string(),
        "payload-sha256:2222".to_string(),
    );
    left_replay.properties.insert(
        "reducer_input_hash".to_string(),
        "reducer-sha256:3333".to_string(),
    );
    left_replay.properties.insert(
        "source_lock_hash".to_string(),
        "lock-sha256:4444".to_string(),
    );

    let mut right_replay = left_replay.clone();
    right_replay.symbols.reverse();
    right_replay.pc_map.reverse();
    right_replay.statuses.reverse();

    let left = JitCrashReportMetadata::new(
        JitCrashKind::HostSignal,
        "jit-runtime",
        "execute",
        left_replay,
    )
    .with_location(Some(0x1000_001c), Some(28))
    .with_signal("SIGSEGV")
    .with_message("segmentation fault")
    .to_pretty_json();
    let right = JitCrashReportMetadata::new(
        JitCrashKind::HostSignal,
        "jit-runtime",
        "execute",
        right_replay,
    )
    .with_location(Some(0x1000_001c), Some(28))
    .with_signal("SIGSEGV")
    .with_message("segmentation fault")
    .to_pretty_json();

    assert_eq!(left, right);
    assert!(left.ends_with('\n'));

    let parsed: Value = serde_json::from_str(&left).expect("crash JSON should parse");
    assert_eq!(parsed["schema"], JIT_CRASH_REPORT_SCHEMA);
    assert_eq!(parsed["schema_version"], JIT_CRASH_REPORT_SCHEMA_VERSION);
    assert_eq!(parsed["producer"], "trust-cg-codegen");
    assert_eq!(parsed["kind"], "host_signal");
    assert_eq!(parsed["status"], "host_signal");
    assert_eq!(parsed["component"], "jit-runtime");
    assert_eq!(parsed["stage"], "execute");
    assert_eq!(parsed["signal"], "SIGSEGV");
    assert_eq!(parsed["message"], "segmentation fault");

    assert_eq!(
        parsed["replay_metadata"]["properties"]["artifact_manifest_checksum"],
        "manifest-sha256:1111"
    );
    assert_eq!(
        parsed["replay_metadata"]["properties"]["native_payload_sha256"],
        "payload-sha256:2222"
    );
    assert_eq!(
        parsed["replay_metadata"]["properties"]["reducer_input_hash"],
        "reducer-sha256:3333"
    );
    assert_eq!(
        parsed["replay_metadata"]["properties"]["source_lock_hash"],
        "lock-sha256:4444"
    );
}

#[test]
fn crash_report_classification_wire_names_are_stable() {
    let kinds = [
        (JitCrashKind::NativeTrap, "native_trap"),
        (JitCrashKind::HostSignal, "host_signal"),
        (JitCrashKind::Panic, "panic"),
        (JitCrashKind::Unknown, "unknown"),
    ];

    for (kind, expected) in kinds {
        let parsed =
            JitCrashReportMetadata::new(kind, "jit-runtime", "execute", shuffled_report(false))
                .to_json_value();
        assert_eq!(kind.as_str(), expected);
        assert_eq!(kind.to_string(), expected);
        assert_eq!(parsed["kind"], expected);
        assert_eq!(parsed["status"], expected);
    }

    let panic_report = JitCrashReportMetadata::new(
        JitCrashKind::Panic,
        "jit-runtime",
        "compile",
        shuffled_report(false),
    )
    .with_panic("assertion failed")
    .to_json_value();
    assert_eq!(panic_report["panic"], "assertion failed");
}

#[test]
fn crash_report_resolves_code_offset_to_symbol_and_pc_map() {
    let report = JitCrashReportMetadata::new(
        JitCrashKind::NativeTrap,
        "jit-runtime",
        "execute",
        shuffled_report(true),
    )
    .with_location(Some(0x2000_0014), Some(20))
    .to_json_value();

    assert_eq!(report["kind"], "native_trap");
    assert_eq!(report["status"], "native_trap");
    assert_eq!(report["location"]["host_pc"], 0x2000_0014_u64);
    assert_eq!(report["location"]["code_offset"], 20);
    assert_eq!(report["location"]["symbol"], "compute");
    assert_eq!(report["location"]["symbol_offset"], 4);
    assert_eq!(report["location"]["symbol_range"]["start_offset"], 16);
    assert_eq!(report["location"]["symbol_range"]["end_offset"], 48);
    assert_eq!(report["location"]["pc_map_entry"]["pc_offset"], 20);
    assert_eq!(report["location"]["pc_map_entry"]["source_label"], "Next");
    assert_eq!(report["location"]["pc_map_entry"]["trust_ir_op"], "icmp");
    assert_eq!(report["location"]["diagnostics"], json!([]));
}

#[test]
fn crash_report_records_missing_pc_and_missing_symbol_diagnostics() {
    let missing_pc = JitCrashReportMetadata::new(
        JitCrashKind::HostSignal,
        "jit-runtime",
        "execute",
        shuffled_report(false),
    )
    .to_json_value();
    assert_eq!(
        missing_pc["location"]["diagnostics"],
        json!(["missing_code_offset"])
    );

    let missing_symbol = JitCrashReportMetadata::new(
        JitCrashKind::HostSignal,
        "jit-runtime",
        "execute",
        shuffled_report(false),
    )
    .with_location(Some(0x2000_0040), Some(64))
    .to_json_value();
    assert_eq!(
        missing_symbol["location"]["diagnostics"],
        json!(["missing_symbol_for_code_offset"])
    );
    assert_eq!(missing_symbol["location"]["symbol"], Value::Null);
    assert_eq!(
        missing_symbol["location"]["pc_map_entry"]["symbol"],
        "compute"
    );
}

#[test]
fn crash_report_records_missing_pc_map_entry_diagnostic() {
    let mut replay = shuffled_report(false);
    replay.pc_map.clear();

    let report =
        JitCrashReportMetadata::new(JitCrashKind::HostSignal, "jit-runtime", "execute", replay)
            .with_location(Some(0x2000_0014), Some(20))
            .to_json_value();

    assert_eq!(report["location"]["symbol"], "compute");
    assert_eq!(report["location"]["pc_map_entry"], Value::Null);
    assert_eq!(
        report["location"]["diagnostics"],
        json!(["missing_pc_map_entry_for_code_offset"])
    );
}
