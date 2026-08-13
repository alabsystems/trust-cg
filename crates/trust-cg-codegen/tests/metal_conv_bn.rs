use serde_json::{Value, json};
use trust_cg_codegen::metal_emitter::{
    CONV_BATCH_NORM_FUSION, GPU_METAL_MSL_TARGET, GpuFusionUnsupportedReason,
    emit_vnn_conv_batch_norm_certified_fusion,
};
use trust_cg_verify::certified_pass_chain::CertifiedPassChain;
use trust_cg_verify::certified_pass_checker::{
    CheckerArtifactRef, Lean5CheckerMode, Lean5CheckerPolicy, Lean5PassCertificateCheckRequest,
    PlaceholderTransportEvidence,
};

fn conv_module_json() -> Value {
    json!({
        "version": 1,
        "dialect": "trust_ir.vnn",
        "entry": "conv_bn",
        "tensors": {
            "%input": {"shape": [1, 2, 1, 1], "dtype": "f32", "layout": "nchw", "role": "input"},
            "%conv0": {"shape": [1, 2, 1, 1], "dtype": "f32", "layout": "nchw", "role": "activation"},
            "%bn0": {"shape": [1, 2, 1, 1], "dtype": "f32", "layout": "nchw", "role": "output"}
        },
        "initializers": {
            "conv.weight": {
                "shape": [2, 1, 1, 1],
                "dtype": "f32",
                "layout": "oihw",
                "values": [3.0, -2.0]
            },
            "bn.scale": {
                "shape": [2],
                "dtype": "f32",
                "layout": "vector",
                "values": [2.0, -4.0]
            },
            "bn.bias": {
                "shape": [2],
                "dtype": "f32",
                "layout": "vector",
                "values": [0.5, -1.0]
            },
            "bn.mean": {
                "shape": [2],
                "dtype": "f32",
                "layout": "vector",
                "values": [1.0, -2.0]
            },
            "bn.var": {
                "shape": [2],
                "dtype": "f32",
                "layout": "vector",
                "values": [3.0, 15.0]
            }
        },
        "ops": [
            {
                "id": "vnn.0",
                "op": "trust_ir.vnn.conv2d",
                "inputs": ["%input"],
                "outputs": ["%conv0"],
                "weights": ["conv.weight"],
                "attrs": {"kernel_shape": [1, 1], "strides": [1, 1], "pads": [0, 0, 0, 0], "dilations": [1, 1], "groups": 1},
                "provenance": {
                    "gamma_layer_id": "layer.0",
                    "gamma_layer_type": "Conv2d",
                    "onnx_node_name": "Conv_0",
                    "onnx_op_type": "Conv",
                    "onnx_outputs": ["conv0"]
                }
            },
            {
                "id": "vnn.1",
                "op": "trust_ir.vnn.batch_norm",
                "inputs": ["%conv0"],
                "outputs": ["%bn0"],
                "weights": ["bn.scale", "bn.bias", "bn.mean", "bn.var"],
                "attrs": {"epsilon": 1.0},
                "provenance": {
                    "gamma_layer_id": "layer.1",
                    "gamma_layer_type": "BatchNorm",
                    "onnx_node_name": "BatchNormalization_1",
                    "onnx_op_type": "BatchNormalization",
                    "onnx_outputs": ["bn0"]
                }
            }
        ]
    })
}

fn linear_module_json() -> Value {
    let mut module = conv_module_json();
    module["entry"] = json!("linear_bn");
    module["tensors"]["%input"]["shape"] = json!([1, 2]);
    module["tensors"]["%input"]["layout"] = json!("nc");
    module["tensors"]["%conv0"]["shape"] = json!([1, 2]);
    module["tensors"]["%conv0"]["layout"] = json!("nc");
    module["tensors"]["%bn0"]["shape"] = json!([1, 2]);
    module["tensors"]["%bn0"]["layout"] = json!("nc");
    module["initializers"]["conv.weight"]["shape"] = json!([2, 2]);
    module["initializers"]["conv.weight"]["layout"] = json!("oi");
    module["initializers"]["conv.weight"]["values"] = json!([1.0, 2.0, 3.0, 4.0]);
    module["initializers"]["linear.bias"] = json!({
        "shape": [2],
        "dtype": "f32",
        "layout": "vector",
        "values": [10.0, -10.0]
    });
    module["ops"][0]["op"] = json!("trust_ir.vnn.linear");
    module["ops"][0]["weights"] = json!(["conv.weight", "linear.bias"]);
    module
}

fn fixture_module_json() -> Value {
    serde_json::from_str(include_str!(
        "../../../tests/fixtures/vnn_trust_ir/valid_conv_bn_relu.json"
    ))
    .expect("VNN fixture should parse")
}

fn expect_reason(mut module: Value, reason: GpuFusionUnsupportedReason) {
    let err =
        emit_vnn_conv_batch_norm_certified_fusion(&module).expect_err("candidate must fail closed");
    assert_eq!(err.code, "gpu.fusion.unsupported");
    assert_eq!(err.phase, "select_gpu_fusion");
    assert_eq!(err.fusion, CONV_BATCH_NORM_FUSION);
    assert_eq!(err.target, GPU_METAL_MSL_TARGET);
    assert_eq!(err.reason, reason);
    assert!(!err.source_ops.is_empty());
    module["ops"] = json!([]);
}

fn request_for_run(run: &trust_cg_opt::CertifiedPassRunRecord) -> Lean5PassCertificateCheckRequest {
    let proof_artifact = CheckerArtifactRef {
        kind: "lean_module".to_string(),
        uri: "builtin://trust-cg-codegen/conv-bn-fusion/placeholder-lean5".to_string(),
        digest: "sha256:conv-bn-placeholder".to_string(),
        media_type: Some("text/plain".to_string()),
        placeholder_transport: Some(PlaceholderTransportEvidence {
            accepted: true,
            note: "Transport check for #556 Conv+BN certified fusion run record.".to_string(),
        }),
    };
    let canonical_obligation = CheckerArtifactRef {
        kind: "canonical_obligation".to_string(),
        uri: "trust-cg-codegen://certified-pass-run/conv-bn.json".to_string(),
        digest: "sha256:conv-bn-run-record".to_string(),
        media_type: Some("application/json".to_string()),
        placeholder_transport: None,
    };
    let artifacts = vec![canonical_obligation, proof_artifact];
    let certificate_artifacts = serde_json::to_value(&artifacts).unwrap();

    Lean5PassCertificateCheckRequest {
        format_version: "trust-cg.lean5_pass_check.request.v1".to_string(),
        certificate: json!({
            "format_version": "trust-cg.certified_pass.v1",
            "pass": {
                "name": run.pass_name,
                "version": run.pass_version.to_string(),
                "instance_id": run.pass_instance_id,
                "pipeline_ordinal": 1
            },
            "provenance": {
                "source": {"program_id": "trust_ir://before-conv-bn", "expression_digest": run.obligation_hash},
                "rewrite": {"program_id": "trust_ir://after-conv-bn", "expression_digest": run.obligation_hash}
            },
            "contract": {
                "mode": "local_pass_certificate_summary",
                "semantic_policy": {"source": "trust-cg-codegen certified fusion", "fail_closed": true}
            },
            "domain": {
                "kind": "vnn-trust_ir",
                "certified_pass_run": run
            },
            "obligation_hash": run.obligation_hash,
            "checker": {
                "kind": "lean5",
                "name": "trust-cg-cert-check",
                "version": "0.1.0",
                "proof_family": "gamma-conv-bn-fusion-affine-v1",
                "replay_inputs": certificate_artifacts
            },
            "result": {
                "status": "verified",
                "local_checker": run.local_checker,
                "certificate_count": run.certificate_count,
                "failure_count": run.failure_count
            },
            "artifacts": {"refs": certificate_artifacts},
            "chain": {
                "compilation_unit": "gamma-conv-bn",
                "certificate_index": 0,
                "must_be_verified": true
            }
        }),
        obligation_hash: run.obligation_hash.clone(),
        policy: Lean5CheckerPolicy {
            checker: "lean5".to_string(),
            mode: Lean5CheckerMode::PlaceholderTransport,
            timeout_ms: 1000,
            fail_closed: true,
            expected_lean_version: Some("Lean 5.0.0-placeholder".to_string()),
            lean5_binary: None,
        },
        artifacts,
    }
}

#[test]
fn certified_conv_bn_emits_affine_fold_run_record() {
    let unit = emit_vnn_conv_batch_norm_certified_fusion(&conv_module_json()).unwrap();
    let run = &unit.certified_pass_run;

    assert_eq!(unit.fusion, CONV_BATCH_NORM_FUSION);
    assert_eq!(unit.source_ops, ["vnn.0", "vnn.1"]);
    assert_eq!(unit.fused_gamma_layer_ids, ["layer.0", "layer.1"]);
    assert!(run.is_verified());
    assert_eq!(run.pass_name, "conv-bn-fusion");
    assert_eq!(
        run.summary["source"]["op_kinds"],
        json!(["trust_ir.vnn.conv2d", "trust_ir.vnn.batch_norm"])
    );
    assert_eq!(run.summary["rewrite"]["op"], "trust_ir.vnn.conv2d");
    assert_eq!(
        run.summary["rewrite"]["fused_weight"]["values"],
        json!([3.0, 2.0])
    );
    assert_eq!(
        run.summary["rewrite"]["fused_bias"]["values"],
        json!([-0.5, -3.0])
    );
}

#[test]
fn certified_linear_bn_accepts_bias_and_positive_scale() {
    let unit = emit_vnn_conv_batch_norm_certified_fusion(&linear_module_json()).unwrap();
    let run = &unit.certified_pass_run;

    assert!(run.is_verified());
    assert_eq!(
        run.summary["source"]["op_kinds"],
        json!(["trust_ir.vnn.linear", "trust_ir.vnn.batch_norm"])
    );
    assert_eq!(run.summary["rewrite"]["op"], "trust_ir.vnn.linear");
    assert_eq!(
        run.summary["rewrite"]["fused_weight"]["values"],
        json!([1.0, 2.0, -3.0, -4.0])
    );
    assert_eq!(
        run.summary["rewrite"]["fused_bias"]["values"],
        json!([9.5, 7.0])
    );
}

#[test]
fn certified_conv_bn_fixture_emits_derived_initializer_record() {
    let unit = emit_vnn_conv_batch_norm_certified_fusion(&fixture_module_json()).unwrap();
    let run = &unit.certified_pass_run;

    assert!(run.is_verified());
    assert_eq!(unit.source_ops, ["vnn.0", "vnn.1"]);
    assert_eq!(
        run.summary["rewrite"]["fused_weight"]["kind"],
        "derived_initializer"
    );
    assert_eq!(
        run.summary["parameters"]["batch_norm"]["weights"]["scale"]["sha256"],
        "2222222222222222222222222222222222222222222222222222222222222222"
    );
}

#[test]
fn certified_conv_bn_run_record_checks_through_certificate_chain() {
    let unit = emit_vnn_conv_batch_norm_certified_fusion(&conv_module_json()).unwrap();
    let chain = CertifiedPassChain::check_requests([request_for_run(&unit.certified_pass_run)])
        .expect("Conv+BN run record should verify through checker-chain transport");

    assert_eq!(chain.compilation_unit(), "gamma-conv-bn");
    assert_eq!(chain.entries().len(), 1);
    assert_eq!(
        chain.entries()[0].request.certificate["domain"]["certified_pass_run"]["pass_name"],
        "conv-bn-fusion"
    );
}

#[test]
fn certified_conv_bn_rejects_training_mode() {
    let mut module = conv_module_json();
    module["ops"][1]["attrs"]["training_mode"] = json!(true);
    expect_reason(module, GpuFusionUnsupportedReason::TrainingModeBatchNorm);
}

#[test]
fn certified_conv_bn_rejects_layout_mismatch() {
    let mut module = conv_module_json();
    module["tensors"]["%input"]["layout"] = json!("nhwc");
    expect_reason(module, GpuFusionUnsupportedReason::UnsupportedLayout);
}

#[test]
fn certified_conv_bn_rejects_channel_shape_mismatch() {
    let mut module = conv_module_json();
    module["initializers"]["bn.scale"]["shape"] = json!([3]);
    module["initializers"]["bn.scale"]["values"] = json!([1.0, 1.0, 1.0]);
    expect_reason(module, GpuFusionUnsupportedReason::ShapeMismatch);
}

#[test]
fn certified_conv_bn_rejects_multiple_consumers() {
    let mut module = conv_module_json();
    module["ops"].as_array_mut().unwrap().push(json!({
        "id": "vnn.extra",
        "op": "trust_ir.vnn.relu",
        "inputs": ["%conv0"],
        "outputs": ["%extra"],
        "attrs": {}
    }));
    expect_reason(module, GpuFusionUnsupportedReason::MultipleConsumers);
}
