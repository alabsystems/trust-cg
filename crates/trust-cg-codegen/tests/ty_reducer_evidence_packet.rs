use trust_cg_codegen::ty_reducer_evidence::{
    TY_REDUCER_ACCEPTED_DOWNSTREAM_REFS, TY_REDUCER_PUBLIC_SOURCE_BLOCKER_REFS,
    TY_REDUCER_RELEASE_PACKET_BLOCKER_REFS, TY_REDUCER_REQUEST_REPLAY_FAMILY,
    TY_REDUCER_REQUIRED_EVIDENCE_FAMILIES, TY_REDUCER_TRUST_CG_ACCEPTED_REVISION,
    TY_REDUCER_TY_FOCUSED_PIN, TY_REDUCER_TY_THREE_SPEC_REPLAY_METADATA_PIN,
};
use trust_cg_codegen::{
    TyReducerCallbackObservation, TyReducerEvidencePacket, TyReducerEvidenceRow,
    TyReducerEvidenceStatus,
};

#[allow(clippy::too_many_arguments)] // Arguments mirror one persisted reducer-evidence row.
fn row(
    reducer_family: &str,
    case_name: &str,
    command: &str,
    state_count: u64,
    generated_count: u64,
    parent_digest: &str,
    fingerprint_digest: Option<&str>,
    callback_observations: Vec<TyReducerCallbackObservation>,
) -> TyReducerEvidenceRow {
    TyReducerEvidenceRow {
        command: command.to_owned(),
        target_tuple: "aarch64-apple-darwin".to_owned(),
        trust_cg_revision: "trust-cg-test-revision".to_owned(),
        opt_level: "O1/O3".to_owned(),
        reducer_family: reducer_family.to_owned(),
        case_name: case_name.to_owned(),
        parent_digest: parent_digest.to_owned(),
        state_count,
        generated_count,
        fingerprint_digest: fingerprint_digest.map(str::to_owned),
        callback_observations,
        status: TyReducerEvidenceStatus::GreenReducerEvidence,
        issue_refs: vec!["#662".to_owned(), "#693".to_owned()],
    }
}

fn accepted_replay_row() -> TyReducerEvidenceRow {
    TyReducerEvidenceRow {
        command: "TY accepted focused Request__1_1 replay plus three-spec smoke metadata"
            .to_owned(),
        target_tuple: "aarch64-apple-darwin".to_owned(),
        trust_cg_revision: TY_REDUCER_TRUST_CG_ACCEPTED_REVISION.to_owned(),
        opt_level: "O3".to_owned(),
        reducer_family: TY_REDUCER_REQUEST_REPLAY_FAMILY.to_owned(),
        case_name: "accepted_bounded_artifact".to_owned(),
        parent_digest: "trust-cg-stable128:request-1-1-accepted-replay".to_owned(),
        state_count: 4,
        generated_count: 3,
        fingerprint_digest: Some("trust-cg-stable128:request-1-1-replay-metadata".to_owned()),
        callback_observations: vec![],
        status: TyReducerEvidenceStatus::AcceptedDownstreamRequestReplay {
            evidence: "#671/#729 accepted TY replay; #730/#667 keep it bounded input".to_owned(),
        },
        issue_refs: vec![
            TY_REDUCER_ACCEPTED_DOWNSTREAM_REFS[0].to_owned(),
            TY_REDUCER_ACCEPTED_DOWNSTREAM_REFS[1].to_owned(),
            TY_REDUCER_ACCEPTED_DOWNSTREAM_REFS[2].to_owned(),
            TY_REDUCER_ACCEPTED_DOWNSTREAM_REFS[3].to_owned(),
        ],
    }
}

fn phase4_packet() -> TyReducerEvidencePacket {
    TyReducerEvidencePacket::phase4_local([
        row(
            "callback_abi_call_clobber",
            "parents_2_5_11",
            "cargo test -p trust-cg-codegen --test ty_callback_abi_call_clobber -- ty_indirect_callback_abi_and_call_clobbers_match_o1_o3 ty_callback_live_values_force_aarch64_callee_save_frame_o1_o3",
            3,
            3,
            "trust-cg-stable128:callback-abi-parent-2-5-11",
            Some("trust-cg-stable128:callback-abi-fingerprint-2-5-11"),
            vec![
                TyReducerCallbackObservation {
                    name: "host_ty_callback_abi_clobber".to_owned(),
                    calls: 3,
                    digest: "trust-cg-stable128:callback-abi-args-2-5-11".to_owned(),
                },
                TyReducerCallbackObservation {
                    name: "aarch64_call_volatile_gprs_x0_x17".to_owned(),
                    calls: 3,
                    digest: "trust-cg-stable128:callback-abi-clobber-x0-x17".to_owned(),
                },
                TyReducerCallbackObservation {
                    name: "aarch64_fpr_callee_saved_d8_d15_lower64".to_owned(),
                    calls: 3,
                    digest: "trust-cg-stable128:callback-abi-8-f64-live-across-d8-d15-lower64"
                        .to_owned(),
                },
            ],
        ),
        row(
            "edge_copy_block_arg",
            "parents_2_5_8_13",
            "cargo test -p trust-cg-codegen --test ty_edge_copy_loop_call -- ty_edge_copy_loop_call_block_args_match_o1_o3",
            4,
            4,
            "trust-cg-stable128:edge-copy-parent-2-5-8-13",
            Some("trust-cg-stable128:edge-copy-fingerprint-2-5-8-13"),
            vec![TyReducerCallbackObservation {
                name: "host_ty_edge_copy_call".to_owned(),
                calls: 4,
                digest: "trust-cg-stable128:edge-copy-callback-2-5-8-13".to_owned(),
            }],
        ),
        row(
            "mcl_shaped_native_fused_parent_loop",
            "mixed",
            "cargo test -p trust-cg-codegen --test ty_mcl_fused_parent_loop -- ty_mcl_fused_parent_loop_o1_o3_match_reference",
            5,
            7,
            "trust-cg-stable128:mcl-parent-mixed",
            Some("trust-cg-stable128:mcl-fingerprint-mixed"),
            vec![
                TyReducerCallbackObservation {
                    name: "action1".to_owned(),
                    calls: 2,
                    digest: "trust-cg-stable128:mcl-callback-action1".to_owned(),
                },
                TyReducerCallbackObservation {
                    name: "action0".to_owned(),
                    calls: 3,
                    digest: "trust-cg-stable128:mcl-callback-action0".to_owned(),
                },
            ],
        ),
        row(
            "no_action_body_parent_loop",
            "non_empty",
            "cargo test -p trust-cg-codegen --test ty_native_bfs_no_action_parent_loop -- native_bfs_no_action_parent_loop_o1_o3_status_summaries_match",
            4,
            0,
            "trust-cg-stable128:no-action-parent-non-empty",
            Some("trust-cg-stable128:no-action-fingerprint-non-empty"),
            vec![],
        ),
        row(
            "minimal_parent_loop",
            "duplicate_parent",
            "cargo test -p trust-cg-codegen --test ty_bfs_minimal_o1_o3_summary -- ty_bfs_minimal_parent_loop_o1_o3_status_summary_matches_reference",
            2,
            2,
            "trust-cg-stable128:minimal-parent-duplicate",
            Some("trust-cg-stable128:minimal-fingerprint-duplicate"),
            vec![],
        ),
        row(
            "o3_materialized_helper_return",
            "retbuf_later_clobber",
            "cargo test -p trust-cg-codegen --test o3_ty_materialized_return -- ty_materialized_retbuf_returns_survive_later_clobber_o1_o3",
            0,
            0,
            "trust-cg-stable128:materialized-helper-return-retbuf",
            Some("trust-cg-stable128:materialized-helper-return-fingerprint"),
            vec![],
        ),
        accepted_replay_row(),
    ])
}

#[test]
fn phase4_ty_o3_reducer_packet_json_is_stable_and_sorted() {
    let packet = phase4_packet();
    let value = packet.to_json_value();
    let pretty = packet
        .to_pretty_json()
        .expect("packet JSON should serialize deterministically");
    let reordered = TyReducerEvidencePacket::phase4_local([
        accepted_replay_row(),
        packet.rows[5].clone(),
        packet.rows[3].clone(),
        packet.rows[1].clone(),
        packet.rows[4].clone(),
        packet.rows[0].clone(),
        packet.rows[2].clone(),
    ]);

    assert_eq!(pretty, serde_json::to_string_pretty(&value).unwrap() + "\n");
    assert_eq!(
        pretty,
        reordered
            .to_pretty_json()
            .expect("reordered packet JSON should serialize deterministically")
    );
    assert_eq!(value["schema"], "trust-cg.phase4.ty_reducer_evidence/v2");
    let stale_blocked_section = ["blocked", "_downstream"].concat();
    assert!(value.get(&stale_blocked_section).is_none());
    assert_eq!(
        value["bounded_downstream_replay"]["request_replay_family"],
        TY_REDUCER_REQUEST_REPLAY_FAMILY
    );
    assert_eq!(
        value["bounded_downstream_replay"]["disposition"],
        "accepted_bounded_input"
    );
    assert_eq!(
        value["bounded_downstream_replay"]["accepted_issue_refs"],
        serde_json::json!(TY_REDUCER_ACCEPTED_DOWNSTREAM_REFS)
    );
    assert_eq!(
        value["bounded_downstream_replay"]["source_locks"]["trust-cg"]["revision"],
        TY_REDUCER_TRUST_CG_ACCEPTED_REVISION
    );
    assert_eq!(
        value["bounded_downstream_replay"]["source_locks"]["ty_focused"]["pin"],
        TY_REDUCER_TY_FOCUSED_PIN
    );
    assert_eq!(
        value["bounded_downstream_replay"]["source_locks"]["ty_three_spec_replay_metadata"]["pin"],
        TY_REDUCER_TY_THREE_SPEC_REPLAY_METADATA_PIN
    );
    assert_eq!(
        value["non_promoting_final_blockers"]["public_source_issue_refs"],
        serde_json::json!(TY_REDUCER_PUBLIC_SOURCE_BLOCKER_REFS)
    );
    assert_eq!(
        value["non_promoting_final_blockers"]["release_packet_issue_refs"],
        serde_json::json!(TY_REDUCER_RELEASE_PACKET_BLOCKER_REFS)
    );
    assert_eq!(
        value["non_promoting_final_blockers"]["product_promotion_allowed"],
        false
    );
    assert_eq!(
        value["rows"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["reducer_family"].as_str().unwrap())
            .collect::<Vec<_>>(),
        vec![
            "callback_abi_call_clobber",
            "edge_copy_block_arg",
            "mcl_shaped_native_fused_parent_loop",
            "minimal_parent_loop",
            "no_action_body_parent_loop",
            "o3_materialized_helper_return",
            TY_REDUCER_REQUEST_REPLAY_FAMILY,
        ]
    );
    assert_eq!(
        value["rows"][6]["status"]["kind"],
        "accepted_downstream_request_replay"
    );
    assert_eq!(
        value["rows"][0]["callback_observations"][0]["name"],
        "aarch64_call_volatile_gprs_x0_x17"
    );
    assert_eq!(
        value["rows"][0]["callback_observations"][1]["name"],
        "aarch64_fpr_callee_saved_d8_d15_lower64"
    );
    assert_eq!(
        value["rows"][2]["callback_observations"][0]["name"],
        "action0"
    );
    assert!(
        pretty.contains(
            "\"command\": \"cargo test -p trust-cg-codegen --test ty_mcl_fused_parent_loop"
        )
    );
    let stale_blocked_kind = ["blocked", "_downstream_request", "_replay"].concat();
    let stale_downstream_ref = ["alabsystems/ty", "#4383"].concat();
    assert!(!pretty.contains(&stale_blocked_kind));
    assert!(!pretty.contains(&stale_downstream_ref));
    assert!(pretty.contains("callback-abi-8-f64-live-across-d8-d15-lower64"));
    assert!(pretty.contains("\"trust_cg_revision\": \"trust-cg-test-revision\""));
}

#[test]
fn phase4_ty_o3_reducer_packet_hash_and_coverage_summary_are_stable() {
    let packet = phase4_packet();
    let reordered = TyReducerEvidencePacket::phase4_local([
        accepted_replay_row(),
        packet.rows[5].clone(),
        packet.rows[3].clone(),
        packet.rows[1].clone(),
        packet.rows[4].clone(),
        packet.rows[0].clone(),
        packet.rows[2].clone(),
    ]);
    let summary = packet
        .coverage_summary()
        .expect("required reducer families should summarize");

    assert_eq!(
        packet.canonical_packet_sha256(),
        reordered.canonical_packet_sha256()
    );
    assert!(summary.packet_sha256.starts_with("sha256:"));
    assert_eq!(summary.packet_sha256, packet.canonical_packet_sha256());
    assert_eq!(
        summary.reducer_families,
        vec![
            "callback_abi_call_clobber",
            "edge_copy_block_arg",
            "mcl_shaped_native_fused_parent_loop",
            "minimal_parent_loop",
            "no_action_body_parent_loop",
            "o3_materialized_helper_return",
        ]
    );
    assert_eq!(
        summary.metadata_bindings()[3].1,
        summary.reducer_families.join(",")
    );
    assert_eq!(
        TY_REDUCER_REQUIRED_EVIDENCE_FAMILIES.len(),
        summary.reducer_families.len()
    );
}

#[test]
fn phase4_ty_o3_reducer_coverage_requires_expected_green_families() {
    let mut missing_family = phase4_packet();
    missing_family
        .rows
        .retain(|row| row.reducer_family != "edge_copy_block_arg");
    assert!(missing_family.coverage_summary().is_err());

    let mut non_green = phase4_packet();
    non_green.rows[4].status = TyReducerEvidenceStatus::AcceptedDownstreamRequestReplay {
        evidence: "local reducer row is not green".to_owned(),
    };
    assert!(non_green.coverage_summary().is_err());
}
