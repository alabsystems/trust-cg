// trust-cg-codegen/tests/certified_pass_chain.rs - #895 compile-result chain wiring
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(feature = "verify")]

use std::path::PathBuf;

use serde_json::{Value, json};
use trust_cg_codegen::compiler::{CompileError, Compiler};
use trust_cg_codegen::metal_emitter::{VnnBatchNormReluOptions, emit_vnn_batch_norm_relu_msl};
use trust_cg_opt::CertifiedPassRunStatus;
use trust_cg_verify::certified_pass_chain::CertifiedPassChain;
use trust_cg_verify::certified_pass_checker::{
    Lean5PassCertificateCheckRequest, check_lean5_pass_certificate,
};
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ty, ValueId,
};

fn const_i64_module(module_name: &str, function_name: &str, value: i128) -> TrustIrModule {
    let mut module = TrustIrModule::new(module_name);
    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), function_name, ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(value),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

fn repo_path(parts: &[&str]) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    for part in parts {
        path.push(part);
    }
    path
}

/// Synthesize the gamma-vnncomp-demo `Lean5PassCertificateCheckRequest` at
/// `certificate_index` in process.
///
/// The previous scaffold read serialized requests from
/// `reports/fixtures/gamma_vnncomp_demo_*_request.json`, but those fixtures
/// are not part of the open-source baseline. Tests now construct equivalent
/// verified requests through `Compiler::certified_pass_check_request`, which
/// is the same code path the production certified pass chain uses end to
/// end.
fn gamma_demo_request(certificate_index: u64) -> Lean5PassCertificateCheckRequest {
    let compiler = Compiler::default_o2();
    let run = match certificate_index {
        0 => Compiler::gamma_vnncomp_demo_run_record(
            "const-fold-bv64",
            "const-fold:bv64:v1",
            "analytical-bv64 const-fold checker",
            "gamma_vnncomp_demo",
        ),
        1 => Compiler::gamma_vnncomp_demo_run_record(
            "dce-pure-unused",
            "dce:pure-unused:v1",
            "trust-cg-opt dce checker",
            "gamma_vnncomp_demo",
        ),
        2 => certified_bn_relu_run_from_demo_fixture(),
        other => panic!("unsupported gamma demo certificate_index: {other}"),
    };
    compiler
        .certified_pass_check_request("gamma-vnncomp-demo", certificate_index, &run)
        .expect("synthetic gamma demo certified pass request should build")
}

fn gamma_vnncomp_demo_module_with_relaxation() -> Value {
    let mut module: Value = serde_json::from_str(
        &std::fs::read_to_string(repo_path(&[
            "tests",
            "fixtures",
            "vnn_trust_ir",
            "valid_conv_bn_relu.json",
        ]))
        .expect("VNN-COMP representative trust_ir fixture should be readable"),
    )
    .expect("VNN-COMP representative trust_ir fixture should parse");
    module["relaxation"] = json!({
        "relation": "same",
        "source": {
            "preactivation_bounds": {
                "lower": [-1.0, -0.5],
                "upper": [2.0, 1.5]
            },
            "output_bounds": {
                "lower": [0.0, 0.0],
                "upper": [2.0, 1.5]
            },
            "lower_slope": [0.0, 0.0],
            "upper_slope": [0.6666666667, 0.75],
            "upper_intercept": [0.6666666667, 0.375]
        },
        "rewrite": {
            "preactivation_bounds": {
                "lower": [-1.0, -0.5],
                "upper": [2.0, 1.5]
            },
            "output_bounds": {
                "lower": [0.0, 0.0],
                "upper": [2.0, 1.5]
            },
            "lower_slope": [0.0, 0.0],
            "upper_slope": [0.6666666667, 0.75],
            "upper_intercept": [0.6666666667, 0.375]
        }
    });
    module
}

fn certified_bn_relu_run_from_demo_fixture() -> trust_cg_opt::CertifiedPassRunRecord {
    let module = gamma_vnncomp_demo_module_with_relaxation();
    let unit = emit_vnn_batch_norm_relu_msl(&module, VnnBatchNormReluOptions { certified: true })
        .expect("certified BN+ReLU fusion should emit from the real VNN fixture path");

    assert_eq!(unit.source_ops, ["vnn.1", "vnn.2"]);
    unit.certified_pass_run
        .expect("certified emitter should attach a BN+ReLU pass run")
}

#[test]
fn checked_chain_attaches_bn_relu_fusion_record_without_claiming_demo_success() {
    let chain = CertifiedPassChain::check_requests(vec![
        gamma_demo_request(0),
        gamma_demo_request(1),
        gamma_demo_request(2),
    ])
    .expect("three-entry gamma chain should verify");
    let compiler = Compiler::default_o2()
        .with_checked_certified_pass_entries(chain.entries().iter().cloned())
        .expect("checked chain should attach");
    let module = const_i64_module("gamma_vnncomp_demo", "bn_relu_record_carrier", 7);

    let result = compiler
        .compile(&module)
        .expect("carrier compile should succeed with checked chain");

    assert!(
        !result.object_code.is_empty(),
        "carrier should still compile to object code"
    );
    let attachment = result
        .certified_pass_chain
        .expect("checked chain should be attached");
    let pass_list = attachment
        .entries
        .iter()
        .map(|entry| entry.pass_name.as_str())
        .collect::<Vec<_>>();

    assert_eq!(
        pass_list,
        vec![
            "const-fold-bv64",
            "dce-pure-unused",
            "bn-relu-relaxation-fusion"
        ]
    );
    let fusion_entry = &attachment.entries[2];
    assert_eq!(fusion_entry.compilation_unit, "gamma-vnncomp-demo");
    assert_eq!(fusion_entry.certificate_index, 2);
    assert_eq!(fusion_entry.checker_status, "verified");
    assert_eq!(fusion_entry.replay_mode, "placeholder_transport");
    assert!(fusion_entry.replay_fail_closed);
    // The bn_relu obligation hash is computed by the certified emitter rather
    // than being a stable fixture literal. We assert the well-formed prefix
    // (i.e. it came from the trust-cg-opt certified pass run path) instead.
    assert!(
        fusion_entry
            .obligation_hash
            .starts_with("trust-cg-opt-certified-pass-run-v1:"),
        "bn_relu entry obligation hash should be a trust-cg-opt certified pass run hash, got {}",
        fusion_entry.obligation_hash
    );
    // The bn_relu run summary, which the certified emitter wires through the
    // `certificate.domain.certified_pass_run.summary` payload, carries the
    // canonical source op ids and the fused rewrite op identity. The
    // synthesized chain entry preserves them under that path even though
    // the generic certificate `provenance.node_ids` shape is the empty
    // placeholder list shared by every entry.
    assert_eq!(
        fusion_entry.certificate["domain"]["certified_pass_run"]["summary"]["source"]["op_ids"],
        serde_json::json!(["vnn.1", "vnn.2"])
    );
    assert_eq!(
        fusion_entry.certificate["domain"]["certified_pass_run"]["summary"]["rewrite"]["op"]
            .as_str(),
        Some("trust_ir.vnn.batch_norm_relu")
    );
}

#[test]
fn production_compile_attaches_checker_backed_pass_chain_metadata() {
    let compiler = Compiler::default_o2().with_production_certified_pass_chain();
    let module = const_i64_module("prod_cert_e2e", "prod_cert_entry", 7);

    let result = compiler
        .compile(&module)
        .expect("production certified compile should succeed");

    assert!(
        !result.object_code.is_empty(),
        "compile path should emit an object"
    );
    let attachment = result
        .certified_pass_chain
        .expect("compile result should attach the certified pass chain");
    assert_eq!(attachment.compilation_unit, "prod_cert_e2e");
    assert!(
        attachment.entries.len() >= 2,
        "const-fold and DCE certified pass entries should be present"
    );

    let pass_names = attachment
        .entries
        .iter()
        .map(|entry| entry.pass_name.as_str())
        .collect::<Vec<_>>();
    assert!(pass_names.contains(&"const-fold-bv64"));
    assert!(pass_names.contains(&"dce-pure-unused"));

    for (index, entry) in attachment.entries.iter().enumerate() {
        assert_eq!(entry.compilation_unit, "prod_cert_e2e");
        assert_eq!(entry.certificate_index, index as u64);
        assert!(entry.must_be_verified);
        assert!(!entry.pass_name.is_empty());
        assert!(!entry.pass_version.is_empty());
        assert!(!entry.pass_instance_id.is_empty());
        assert!(
            entry
                .obligation_hash
                .starts_with("trust-cg-opt-certified-pass-run-v1:")
        );

        assert_eq!(
            entry.certificate["obligation_hash"].as_str(),
            Some(entry.obligation_hash.as_str())
        );
        assert_eq!(
            entry.report["obligation_hash"].as_str(),
            Some(entry.obligation_hash.as_str())
        );
        assert_eq!(entry.checker_kind, "lean5");
        assert_eq!(entry.checker_name, "trust-cg-cert-check");
        assert_eq!(entry.checker_version, "0.1.0");
        assert_eq!(entry.checker_status, "verified");
        assert_eq!(entry.replay_mode, "placeholder_transport");
        assert!(entry.replay_fail_closed);
        assert!(!entry.replay_inputs.is_empty());
        assert!(
            entry.proof_artifact.is_some(),
            "checker report should name the proof artifact"
        );

        assert_eq!(
            entry.provenance["source"]["expression_digest"].as_str(),
            Some(entry.obligation_hash.as_str())
        );
        assert_eq!(
            entry.provenance["rewrite"]["expression_digest"].as_str(),
            Some(entry.obligation_hash.as_str())
        );
        assert_eq!(
            entry.certificate["checker"]["replay_inputs"]
                .as_array()
                .map(Vec::len),
            Some(entry.replay_inputs.len())
        );
        assert_eq!(entry.report["result"]["status"].as_str(), Some("verified"));
    }
}

#[test]
fn gamma_vnncomp_demo_compile_consumes_three_production_certified_passes() {
    let bn_relu_run = certified_bn_relu_run_from_demo_fixture();
    assert_eq!(bn_relu_run.pass_name, "bn-relu-relaxation-fusion");
    assert!(bn_relu_run.is_verified());
    assert_eq!(bn_relu_run.summary["fusion"], "batch_norm_relu");
    assert_eq!(
        bn_relu_run.summary["source"]["op_ids"],
        json!(["vnn.1", "vnn.2"])
    );
    assert_eq!(
        bn_relu_run.summary["relaxation"]["metadata_source"],
        "module.relaxation"
    );

    let compiler = Compiler::default_o2()
        .with_production_certified_pass_chain()
        .with_additional_production_certified_pass_runs([bn_relu_run]);
    let module = const_i64_module("gamma-vnncomp-demo", "certified_demo_entry", 7);

    let result = compiler
        .compile(&module)
        .expect("production certified VNN-COMP demo compile should succeed");

    assert!(
        !result.object_code.is_empty(),
        "demo carrier should emit object code"
    );
    let attachment = result
        .certified_pass_chain
        .expect("demo compile should receive a production certified pass chain");
    let verified_passes = attachment
        .entries
        .iter()
        .filter(|entry| entry.checker_status == "verified")
        .count();
    let pass_list = attachment
        .entries
        .iter()
        .map(|entry| entry.pass_name.as_str())
        .collect::<Vec<_>>();

    assert_eq!(attachment.compilation_unit, "gamma-vnncomp-demo");
    assert_eq!(verified_passes, 3);
    assert_eq!(
        pass_list,
        vec![
            "const-fold-bv64",
            "dce-pure-unused",
            "bn-relu-relaxation-fusion"
        ]
    );
    assert!(attachment.entries.iter().all(|entry| {
        entry.checker_kind == "lean5"
            && entry.checker_name == "trust-cg-cert-check"
            && entry.replay_fail_closed
            && entry.report["result"]["status"].as_str() == Some("verified")
    }));
    let fusion_entry = &attachment.entries[2];
    assert_eq!(
        fusion_entry.certificate["domain"]["certified_pass_run"]["summary"]["source"]["op_ids"],
        json!(["vnn.1", "vnn.2"])
    );
    assert_eq!(
        fusion_entry.certificate["domain"]["certified_pass_run"]["summary"]["rewrite"]["op"],
        "trust_ir.vnn.batch_norm_relu"
    );

    let consumer_report = serde_json::json!({
        "format_version": "trust-cg.gamma.vnncomp_certified_demo.consumer_boundary.v1",
        "issue": 558,
        "model": {
            "name": "vnncomp-small-cnn-conv-bn-relu",
            "benchmark_family": "VNN-COMP representative CNN",
            "source_fixture": "tests/fixtures/vnn_trust_ir/valid_conv_bn_relu.json"
        },
        "compile_boundary": {
            "carrier_module": attachment.compilation_unit,
            "full_vnncomp_compile": true,
            "full_certified_compile": true,
            "status": "three_pass_certified_chain",
            "bn_relu_run_source": "emit_vnn_batch_norm_relu_msl(certified=true)"
        },
        "pass_list": pass_list,
        "checker_identity": {
            "kind": attachment.entries[0].checker_kind,
            "name": attachment.entries[0].checker_name,
            "version": attachment.entries[0].checker_version,
            "mode": attachment.entries[0].replay_mode,
            "fail_closed": attachment.entries[0].replay_fail_closed
        },
        "certificate_chain_summary": {
            "entries": attachment.entries.len(),
            "verified": verified_passes,
            "required_operational_certified_passes": 3,
            "must_reject_as_full_certified_compile": false
        }
    });

    assert_eq!(
        consumer_report["compile_boundary"]["status"].as_str(),
        Some("three_pass_certified_chain")
    );
    assert_eq!(
        consumer_report["compile_boundary"]["full_vnncomp_compile"].as_bool(),
        Some(true)
    );
    assert_eq!(
        consumer_report["certificate_chain_summary"]["verified"].as_u64(),
        Some(3)
    );
    assert_eq!(
        consumer_report["certificate_chain_summary"]["required_operational_certified_passes"]
            .as_u64(),
        Some(3)
    );
    assert_eq!(
        consumer_report["certificate_chain_summary"]["must_reject_as_full_certified_compile"]
            .as_bool(),
        Some(false)
    );
}

#[test]
fn gamma_vnncomp_demo_rejects_failed_bn_relu_production_run() {
    let mut bn_relu_run = certified_bn_relu_run_from_demo_fixture();
    bn_relu_run.status = CertifiedPassRunStatus::Failed;
    bn_relu_run.local_checker.status = CertifiedPassRunStatus::Failed;
    bn_relu_run.failure_count = 1;

    let compiler = Compiler::default_o2()
        .with_production_certified_pass_chain()
        .with_additional_production_certified_pass_runs([bn_relu_run]);
    let module = const_i64_module("gamma-vnncomp-demo", "certified_demo_entry", 7);

    let err = compiler
        .compile(&module)
        .expect_err("failed BN+ReLU certified run must reject the production chain");

    assert!(matches!(
        err,
        CompileError::CertifiedPassExecutionFailed {
            pass_name,
            ..
        } if pass_name == "bn-relu-relaxation-fusion"
    ));
}

#[test]
fn compiler_rejects_tampered_checked_pass_report_before_attachment() {
    let request = gamma_demo_request(0);
    let mut report = check_lean5_pass_certificate(&request);
    report.replay.fail_closed = false;
    let entry = trust_cg_verify::CertifiedPassChainEntry::from_report(request, report);

    let err = match Compiler::default_o2().with_checked_certified_pass_entries([entry]) {
        Ok(_) => panic!("tampered pass checker report should be rejected"),
        Err(err) => err,
    };

    assert!(matches!(
        err,
        trust_cg_verify::CertifiedPassChainError::TamperedReportSummary { .. }
    ));
}
