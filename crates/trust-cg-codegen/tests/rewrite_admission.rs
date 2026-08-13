use trust_cg_codegen::rewrite_admission::{
    TinyBlockSuperoptCertificateIdentity, TinyBlockSuperoptCostModel,
    TinyBlockSuperoptCounterexampleModel, TinyBlockSuperoptCounterexampleReducerRejection,
    TinyBlockSuperoptRewriteAdmissionRecord, TinyBlockSuperoptRewriteIdentity,
    TinyBlockSuperoptRewriteRejection,
};
use trust_cg_codegen::{
    ProofGuidedAdmissionEvidence, ProofOptimizationCertificateCitation,
    ProofOptimizationConsumedFactCitation, RewriteAdmissionDisposition, RewriteAdmissionRecord,
    RewriteAdmissionRejection,
};

const TINY_ORIGINAL_HASH: &str =
    "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const TINY_REPLACEMENT_HASH: &str =
    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const TINY_CERTIFICATE_HASH: &str =
    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
const TINY_COUNTEREXAMPLE_HASH: &str =
    "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";

fn citation(function_name: &str) -> ProofOptimizationCertificateCitation {
    ProofOptimizationCertificateCitation {
        function_name: function_name.to_owned(),
        certificate_id: "cert-ay-lra-sparse-001".to_owned(),
        proof_hash: "proof-ay-lra-sparse-001".to_owned(),
        validation_hash: "validation-ay-lra-sparse-001".to_owned(),
        source_region_hash: "source-region-ay-lra-sparse-001".to_owned(),
        target_region_hash: "target-region-ay-lra-sparse-001".to_owned(),
        transform_name: "ay.lra.sparse_substitute".to_owned(),
        transform_version: 1,
        admission: "proof-annotation+proof-facts".to_owned(),
        kind: "SparseSubstitute".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: vec![ProofOptimizationConsumedFactCitation {
            name: "ay_lra_sparse_basis".to_owned(),
            payload: Some("fixture-row-7".to_owned()),
        }],
    }
}

fn complete_evidence() -> ProofGuidedAdmissionEvidence {
    ProofGuidedAdmissionEvidence::new(
        "sha256:manifest-ay-lra-sparse-001",
        "ay_lra_sparse_status_contract:v1:guarded_deopt",
        "sha256:replay-root-ay-lra-sparse-001",
        "trust-cg.proof_guided.ay_lra_sparse.useful_native_applications",
        0,
        "trust-cg.proof_guided.disable.ay_lra_sparse",
    )
}

fn tiny_original() -> TinyBlockSuperoptRewriteIdentity {
    TinyBlockSuperoptRewriteIdentity::new("ay.tiny.orig.block42.v1", TINY_ORIGINAL_HASH)
}

fn tiny_replacement() -> TinyBlockSuperoptRewriteIdentity {
    TinyBlockSuperoptRewriteIdentity::new("ay.tiny.repl.block42.v1", TINY_REPLACEMENT_HASH)
}

fn tiny_certificate() -> TinyBlockSuperoptCertificateIdentity {
    TinyBlockSuperoptCertificateIdentity::new(
        "ay.tiny.cert.block42.equiv.v1",
        TINY_CERTIFICATE_HASH,
    )
}

fn tiny_counterexample() -> TinyBlockSuperoptCounterexampleModel {
    TinyBlockSuperoptCounterexampleModel::new(
        "ay.tiny.counterexample.block42.model7",
        TINY_COUNTEREXAMPLE_HASH,
    )
}

fn record_with(citation: ProofOptimizationCertificateCitation) -> RewriteAdmissionRecord {
    RewriteAdmissionRecord::from_complete_evidence(
        citation,
        "aarch64",
        19,
        11,
        Some("validation-ay-lra-sparse-001".to_owned()),
        complete_evidence(),
    )
}

#[test]
fn tiny_block_superopt_verified_certificate_non_worse_admits() {
    let record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(7, 7),
        Some(tiny_certificate()),
        None,
    );

    assert_eq!(
        record.disposition,
        RewriteAdmissionDisposition::AdmitNonPromoting
    );
    assert_eq!(record.rejection, None);
    assert_eq!(record.diagnostic_reason, None);
    assert!(!record.product_install_authority);
    assert!(!record.grants_product_install_authority());
    record
        .validate()
        .expect("certificate-bound non-worse tiny block admits");
    assert_eq!(record.to_json_value()["cost_model"]["delta_cycles"], 0);
    assert_eq!(
        record.to_json_value()["certificate"]["identity"],
        "ay.tiny.cert.block42.equiv.v1"
    );

    let same_record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(7, 7),
        Some(tiny_certificate()),
        None,
    );
    assert_eq!(record.stable_json(), same_record.stable_json());
    assert_eq!(record.record_checksum, same_record.record_checksum);
}

#[test]
fn tiny_block_superopt_missing_certificate_rejects_fail_closed() {
    let record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(9, 4),
        None,
        None,
    );

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(TinyBlockSuperoptRewriteRejection::MissingCertificateIdentity)
    );
    assert_eq!(
        record.diagnostic_reason.as_deref(),
        Some("missing_certificate_identity")
    );
    assert_eq!(
        record.validate(),
        Err(TinyBlockSuperoptRewriteRejection::MissingCertificateIdentity)
    );
    assert_eq!(
        record.to_json_value()["certificate"],
        serde_json::Value::Null
    );
    assert!(!record.product_install_authority);
    assert!(!record.grants_product_install_authority());
}

#[test]
fn tiny_block_superopt_counterexample_rejects_with_stable_identity() {
    let record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(9, 4),
        Some(tiny_certificate()),
        Some(tiny_counterexample()),
    );

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(TinyBlockSuperoptRewriteRejection::CounterexampleModel)
    );
    assert_eq!(
        record.diagnostic_reason.as_deref(),
        Some("counterexample_model")
    );
    assert_eq!(
        record.validate(),
        Err(TinyBlockSuperoptRewriteRejection::CounterexampleModel)
    );
    assert_eq!(
        record.to_json_value()["counterexample_model"]["identity"],
        "ay.tiny.counterexample.block42.model7"
    );
    assert_eq!(
        record.to_json_value()["counterexample_model"]["sha256"],
        TINY_COUNTEREXAMPLE_HASH
    );
    assert_eq!(
        record.to_json_value()["diagnostic_reason"],
        "counterexample_model"
    );
}

#[test]
fn tiny_block_superopt_counterexample_reducer_record_is_stable() {
    let admission = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(9, 4),
        Some(tiny_certificate()),
        Some(tiny_counterexample()),
    );

    assert_eq!(
        admission.validate(),
        Err(TinyBlockSuperoptRewriteRejection::CounterexampleModel)
    );

    let reducer = admission
        .counterexample_reducer_record(Some(
            "requires_add_no_unsigned_wrap_precondition".to_owned(),
        ))
        .expect("counterexample reducer materialization should validate")
        .expect("counterexample-bearing rejection should emit reducer input");

    reducer
        .validate()
        .expect("counterexample reducer record validates");
    assert_eq!(
        reducer.rejection_reason,
        TinyBlockSuperoptRewriteRejection::CounterexampleModel
    );
    assert_eq!(reducer.original, tiny_original());
    assert_eq!(reducer.replacement, tiny_replacement());
    assert_eq!(reducer.counterexample_model, tiny_counterexample());
    assert_eq!(
        reducer.required_precondition_gap.as_deref(),
        Some("requires_add_no_unsigned_wrap_precondition")
    );
    assert_eq!(
        reducer.source_admission_record_checksum,
        admission.record_checksum
    );
    assert!(reducer.local_compiler_evidence_only);
    assert!(!reducer.publish_product_artifact);
    assert!(!reducer.activate_product);
    assert!(!reducer.product_install_authority);
    assert!(!reducer.grants_product_install_authority());

    let value = reducer.to_json_value();
    assert_eq!(value["rejection_reason"], "counterexample_model");
    assert_eq!(
        value["counterexample_model"]["sha256"],
        TINY_COUNTEREXAMPLE_HASH
    );
    assert_eq!(
        value["required_precondition_gap"],
        "requires_add_no_unsigned_wrap_precondition"
    );
    assert_eq!(
        value["source_admission_record_checksum"],
        admission.record_checksum
    );
    assert_eq!(value["publish_product_artifact"], false);
    assert_eq!(value["activate_product"], false);
    assert_eq!(value["product_install_authority"], false);

    let same_reducer = admission
        .counterexample_reducer_record(Some(
            "requires_add_no_unsigned_wrap_precondition".to_owned(),
        ))
        .expect("counterexample reducer materialization should validate")
        .expect("counterexample-bearing rejection should emit reducer input");
    assert_eq!(reducer.stable_json(), same_reducer.stable_json());
    assert_eq!(reducer.record_checksum, same_reducer.record_checksum);
}

#[test]
fn tiny_block_superopt_reducer_record_rejects_missing_model() {
    let record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(4, 9),
        Some(tiny_certificate()),
        None,
    );

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(TinyBlockSuperoptRewriteRejection::CostRegression)
    );
    assert_eq!(
        record.counterexample_reducer_record(None),
        Err(TinyBlockSuperoptCounterexampleReducerRejection::MissingCounterexampleModel)
    );
    assert_eq!(
        serde_json::to_string(
            &TinyBlockSuperoptCounterexampleReducerRejection::MissingCounterexampleModel
        )
        .expect("reducer rejection serializes"),
        "\"missing_counterexample_model\""
    );
}

#[test]
fn tiny_block_superopt_verified_candidate_produces_no_reducer_record() {
    let record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(7, 7),
        Some(tiny_certificate()),
        None,
    );

    record
        .validate()
        .expect("verified non-worse candidate validates");
    assert_eq!(
        record
            .counterexample_reducer_record(None)
            .expect("verified candidate reducer check should succeed"),
        None
    );
}

#[test]
fn tiny_block_superopt_malformed_certificate_identity_rejects_fail_closed() {
    let mut certificate = tiny_certificate();
    certificate.identity = "ay tiny cert with whitespace".to_owned();

    let record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(9, 4),
        Some(certificate),
        None,
    );

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(TinyBlockSuperoptRewriteRejection::MalformedCertificateIdentity)
    );
    assert_eq!(
        record.diagnostic_reason.as_deref(),
        Some("malformed_certificate_identity")
    );
    assert_eq!(
        record.validate(),
        Err(TinyBlockSuperoptRewriteRejection::MalformedCertificateIdentity)
    );
}

#[test]
fn tiny_block_superopt_cost_regression_rejects() {
    let record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(4, 9),
        Some(tiny_certificate()),
        None,
    );

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(TinyBlockSuperoptRewriteRejection::CostRegression)
    );
    assert_eq!(record.diagnostic_reason.as_deref(), Some("cost_regression"));
    assert_eq!(
        record.validate(),
        Err(TinyBlockSuperoptRewriteRejection::CostRegression)
    );
    assert_eq!(record.to_json_value()["cost_model"]["delta_cycles"], 5);
}

#[test]
fn tiny_block_superopt_kill_switch_blocks_non_promoting_admission() {
    let record = TinyBlockSuperoptRewriteAdmissionRecord::from_candidate_with_admission_enabled(
        tiny_original(),
        tiny_replacement(),
        TinyBlockSuperoptCostModel::new(9, 4),
        Some(tiny_certificate()),
        None,
        false,
    );

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(TinyBlockSuperoptRewriteRejection::AdmissionDisabled)
    );
    assert_eq!(
        record.diagnostic_reason.as_deref(),
        Some("admission_disabled")
    );
    assert_eq!(
        record.validate(),
        Err(TinyBlockSuperoptRewriteRejection::AdmissionDisabled)
    );
    assert_eq!(record.to_json_value()["admission_enabled"], false);
    assert!(!record.product_install_authority);
    assert!(!record.grants_product_install_authority());
}

#[test]
fn ay_lra_sparse_non_promoting_lower_cost_admits() {
    let record = record_with(citation("ay_lra_sparse"));

    assert_eq!(
        record.disposition,
        RewriteAdmissionDisposition::AdmitNonPromoting
    );
    assert_eq!(record.rejection, None);
    assert!(!record.product_install_authority);
    assert!(!record.grants_product_install_authority());
    record
        .validate()
        .expect("lower-cost aarch64 proof should admit");
    assert_eq!(
        record.to_json_value()["complete_evidence"]["manifest_hash"],
        "sha256:manifest-ay-lra-sparse-001"
    );
    assert_eq!(
        record.to_json_value()["complete_evidence"]["telemetry_useful_native_applications"],
        0
    );
}

#[test]
fn incomplete_complete_evidence_rejects_before_non_promoting_admit() {
    let record = RewriteAdmissionRecord::from_certificate_citation(
        citation("ay_lra_sparse"),
        "aarch64",
        19,
        11,
        Some("validation-ay-lra-sparse-001".to_owned()),
    );

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(RewriteAdmissionRejection::MissingManifestHash)
    );
    assert_eq!(
        record.validate(),
        Err(RewriteAdmissionRejection::MissingManifestHash)
    );
    assert!(!record.product_install_authority);
    assert!(!record.grants_product_install_authority());
}

#[test]
fn missing_consumed_proof_fact_rejects_otherwise_valid_lower_cost_aarch64() {
    let mut cert = citation("ay_lra_sparse");
    cert.consumed_facts.clear();

    let record = record_with(cert);

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(RewriteAdmissionRejection::MissingConsumedProofFact)
    );
    assert_eq!(
        record.validate(),
        Err(RewriteAdmissionRejection::MissingConsumedProofFact)
    );
    assert_eq!(
        record.to_json_value()["rejection"],
        "missing_consumed_proof_fact"
    );
    assert_eq!(
        serde_json::to_string(&RewriteAdmissionRejection::MissingConsumedProofFact)
            .expect("rejection serializes"),
        "\"missing_consumed_proof_fact\""
    );
    assert!(!record.product_install_authority);
    assert!(!record.grants_product_install_authority());
}

#[test]
fn rejected_certificate_status_rejects() {
    let mut cert = citation("ay_lra_sparse");
    cert.status = "rejected".to_owned();

    let record = record_with(cert);

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(RewriteAdmissionRejection::RejectedCertificateEvidence)
    );
    assert_eq!(
        record.validate(),
        Err(RewriteAdmissionRejection::RejectedCertificateEvidence)
    );
    assert_eq!(
        record.to_json_value()["rejection"],
        "rejected_certificate_evidence"
    );
    assert_eq!(
        serde_json::to_string(&RewriteAdmissionRejection::RejectedCertificateEvidence)
            .expect("rejection serializes"),
        "\"rejected_certificate_evidence\""
    );
    assert!(!record.product_install_authority);
    assert!(!record.grants_product_install_authority());
}

#[test]
#[allow(clippy::type_complexity)] // Cases pair a mutation callback with a field label.
fn rejected_certificate_fields_reject() {
    let field_cases: [(&str, fn(&mut ProofOptimizationCertificateCitation)); 3] = [
        ("rejection_code", |cert| {
            cert.rejection_code = Some("proof_fact_failed".to_owned());
        }),
        ("rejection_fact", |cert| {
            cert.rejection_fact = Some("ay_lra_sparse_basis".to_owned());
        }),
        ("rejection_detail", |cert| {
            cert.rejection_detail = Some("solver rejected sparse basis".to_owned());
        }),
    ];

    for (field_name, apply_rejected_field) in field_cases {
        let mut cert = citation("ay_lra_sparse");
        apply_rejected_field(&mut cert);

        let record = record_with(cert);

        assert_eq!(
            record.disposition,
            RewriteAdmissionDisposition::Reject,
            "{field_name} should reject"
        );
        assert_eq!(
            record.rejection,
            Some(RewriteAdmissionRejection::RejectedCertificateEvidence),
            "{field_name} should use rejected certificate evidence"
        );
        assert_eq!(
            record.validate(),
            Err(RewriteAdmissionRejection::RejectedCertificateEvidence),
            "{field_name} should fail validation"
        );
        assert_eq!(
            record.to_json_value()["rejection"],
            "rejected_certificate_evidence"
        );
        assert!(!record.product_install_authority);
        assert!(!record.grants_product_install_authority());
    }
}

#[test]
fn ty_native_fused_certificate_binding_is_preserved() {
    let mut cert = citation("ty_native_fused_parent_loop");
    cert.certificate_id = "ty-native-fused-cert".to_owned();
    cert.proof_hash = "ty-native-fused-proof".to_owned();
    cert.validation_hash = "ty-native-fused-validation".to_owned();
    cert.source_region_hash = "ty-native-fused-source".to_owned();
    cert.target_region_hash = "ty-native-fused-target".to_owned();
    cert.transform_name = "ty.native_fused.parent_loop".to_owned();
    cert.consumed_facts
        .push(ProofOptimizationConsumedFactCitation {
            name: "ty_native_fused_callback_layout".to_owned(),
            payload: Some("layout-v1".to_owned()),
        });

    let record = RewriteAdmissionRecord::from_complete_evidence(
        cert.clone(),
        "aarch64",
        101,
        73,
        Some("ty-native-fused-validation".to_owned()),
        ProofGuidedAdmissionEvidence::new(
            "sha256:manifest-ty-native-fused-001",
            "ty_native_fused_parent_loop_status_contract:v1:guarded_deopt",
            "sha256:replay-root-ty-native-fused-001",
            "trust-cg.proof_guided.ty_native_fused.useful_native_applications",
            0,
            "trust-cg.proof_guided.disable.ty_native_fused_parent_loop",
        ),
    );

    assert_eq!(record.certificate, cert);
    assert_eq!(
        record.to_json_value()["certificate"]["certificate_id"],
        "ty-native-fused-cert"
    );
    assert_eq!(
        record.to_json_value()["certificate"]["consumed_facts"][1]["name"],
        "ty_native_fused_callback_layout"
    );
    record.validate().expect("ty binding should validate");
}

#[test]
fn missing_identity_rejects() {
    let mut cert = citation("ay_lra_sparse");
    cert.proof_hash.clear();

    let record = record_with(cert);

    assert_eq!(record.disposition, RewriteAdmissionDisposition::Reject);
    assert_eq!(
        record.rejection,
        Some(RewriteAdmissionRejection::MissingCertificateIdentity)
    );
    assert_eq!(
        record.validate(),
        Err(RewriteAdmissionRejection::MissingCertificateIdentity)
    );
}

#[test]
fn validation_hash_mismatch_rejects() {
    let record = RewriteAdmissionRecord::from_complete_evidence(
        citation("ay_lra_sparse"),
        "aarch64",
        19,
        11,
        Some("other-validation".to_owned()),
        complete_evidence(),
    );

    assert_eq!(
        record.rejection,
        Some(RewriteAdmissionRejection::ValidationHashMismatch)
    );
    assert_eq!(
        record.validate(),
        Err(RewriteAdmissionRejection::ValidationHashMismatch)
    );
}

#[test]
#[allow(clippy::type_complexity)] // Cases bind a mutation callback to its typed rejection.
fn complete_evidence_negative_cases_are_typed_and_fail_closed() {
    let cases: [(
        &str,
        fn(&mut ProofGuidedAdmissionEvidence),
        RewriteAdmissionRejection,
    ); 5] = [
        (
            "manifest_hash",
            |evidence| evidence.manifest_hash.clear(),
            RewriteAdmissionRejection::MissingManifestHash,
        ),
        (
            "runtime_status_contract",
            |evidence| evidence.runtime_status_contract.clear(),
            RewriteAdmissionRejection::MissingRuntimeStatusContract,
        ),
        (
            "replay_artifact_root",
            |evidence| evidence.replay_artifact_root.clear(),
            RewriteAdmissionRejection::MissingReplayArtifactRoot,
        ),
        (
            "telemetry_useful_native_counter",
            |evidence| evidence.telemetry_useful_native_applications = None,
            RewriteAdmissionRejection::MissingTelemetryUsefulNativeCounter,
        ),
        (
            "rollback_disable_knob",
            |evidence| evidence.rollback_disable_knob.clear(),
            RewriteAdmissionRejection::MissingRollbackDisableKnob,
        ),
    ];

    for (field_name, mutate, expected) in cases {
        let mut evidence = complete_evidence();
        mutate(&mut evidence);

        let record = RewriteAdmissionRecord::from_complete_evidence(
            citation("ay_lra_sparse"),
            "aarch64",
            19,
            11,
            Some("validation-ay-lra-sparse-001".to_owned()),
            evidence,
        );

        assert_eq!(
            record.disposition,
            RewriteAdmissionDisposition::Reject,
            "{field_name} should reject"
        );
        assert_eq!(record.rejection, Some(expected), "{field_name}");
        assert_eq!(record.validate(), Err(expected), "{field_name}");
        assert_eq!(record.to_json_value()["rejection"], expected.as_str());
        assert!(!record.product_install_authority);
        assert!(!record.grants_product_install_authority());
    }
}

#[test]
fn non_aarch64_rejects() {
    let record = RewriteAdmissionRecord::from_complete_evidence(
        citation("ay_lra_sparse"),
        "x86_64",
        19,
        11,
        Some("validation-ay-lra-sparse-001".to_owned()),
        complete_evidence(),
    );

    assert_eq!(
        record.rejection,
        Some(RewriteAdmissionRejection::UnsupportedTargetArch)
    );
    assert_eq!(
        record.validate(),
        Err(RewriteAdmissionRejection::UnsupportedTargetArch)
    );
}

#[test]
fn unprofitable_and_equal_cost_reject() {
    for target_cost_cycles in [19, 20] {
        let record = RewriteAdmissionRecord::from_complete_evidence(
            citation("ay_lra_sparse"),
            "aarch64",
            19,
            target_cost_cycles,
            Some("validation-ay-lra-sparse-001".to_owned()),
            complete_evidence(),
        );

        assert_eq!(
            record.rejection,
            Some(RewriteAdmissionRejection::UnprofitableCost)
        );
        assert_eq!(
            record.validate(),
            Err(RewriteAdmissionRejection::UnprofitableCost)
        );
    }
}

#[test]
fn checksum_is_deterministic_and_sensitive() {
    let first = record_with(citation("ay_lra_sparse"));
    let second = record_with(citation("ay_lra_sparse"));
    let changed = RewriteAdmissionRecord::from_complete_evidence(
        citation("ay_lra_sparse"),
        "aarch64",
        19,
        10,
        Some("validation-ay-lra-sparse-001".to_owned()),
        complete_evidence(),
    );

    assert_eq!(first.stable_json(), second.stable_json());
    assert_eq!(first.record_checksum, second.record_checksum);
    assert_ne!(first.record_checksum, changed.record_checksum);
    assert!(first.record_checksum.starts_with("sha256:"));
}

#[test]
fn validate_rejects_tampered_checksum() {
    let mut record = record_with(citation("ay_lra_sparse"));
    record.record_checksum = "sha256:tampered".to_owned();

    assert_eq!(
        record.validate(),
        Err(RewriteAdmissionRejection::ChecksumMismatch)
    );
}

#[test]
fn duplicate_source_location_identity_does_not_collapse_distinct_regions() {
    let mut first = citation("duplicate_source_loc");
    first.source_region_hash = "trust_ir-origin-0".to_owned();
    first.certificate_id = "cert-origin-0".to_owned();

    let mut second = citation("duplicate_source_loc");
    second.source_region_hash = "trust_ir-origin-1".to_owned();
    second.certificate_id = "cert-origin-1".to_owned();

    let first = RewriteAdmissionRecord::from_complete_evidence(
        first,
        "aarch64",
        19,
        11,
        Some("validation-ay-lra-sparse-001".to_owned()),
        complete_evidence(),
    );
    let second = RewriteAdmissionRecord::from_complete_evidence(
        second,
        "aarch64",
        19,
        11,
        Some("validation-ay-lra-sparse-001".to_owned()),
        complete_evidence(),
    );

    assert_eq!(
        first.certificate.function_name,
        second.certificate.function_name
    );
    assert_ne!(
        first.certificate.source_region_hash,
        second.certificate.source_region_hash
    );
    assert_ne!(first.record_checksum, second.record_checksum);
    first
        .validate()
        .expect("first duplicate source loc validates");
    second
        .validate()
        .expect("second duplicate source loc validates");
}
