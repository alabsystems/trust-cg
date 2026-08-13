use serde_json::{Value, json};
use trust_cg_codegen::metal_emitter::{
    BATCH_NORM_RELU_FUSION, GPU_METAL_MSL_TARGET, GpuFusionUnsupportedReason,
    VnnBatchNormReluOptions, emit_vnn_batch_norm_relu_msl,
};
use trust_cg_opt::CertifiedPassRunStatus;

fn valid_module_json() -> Value {
    json!({
        "version": 1,
        "dialect": "trust_ir.vnn",
        "entry": "bn_relu",
        "tensors": {
            "%input": {
                "shape": [1, 2, 3, 4],
                "dtype": "f32",
                "layout": "nchw",
                "role": "input"
            },
            "%bn0": {
                "shape": [1, 2, 3, 4],
                "dtype": "f32",
                "layout": "nchw",
                "role": "activation"
            },
            "%relu0": {
                "shape": [1, 2, 3, 4],
                "dtype": "f32",
                "layout": "nchw",
                "role": "output"
            }
        },
        "initializers": {
            "bn.scale": {
                "shape": [2],
                "dtype": "f32",
                "layout": "vector",
                "storage": {"kind": "external", "name": "bn.scale"},
                "sha256": "00"
            },
            "bn.bias": {
                "shape": [2],
                "dtype": "f32",
                "layout": "vector",
                "storage": {"kind": "external", "name": "bn.bias"},
                "sha256": "00"
            },
            "bn.mean": {
                "shape": [2],
                "dtype": "f32",
                "layout": "vector",
                "storage": {"kind": "external", "name": "bn.mean"},
                "sha256": "00"
            },
            "bn.var": {
                "shape": [2],
                "dtype": "f32",
                "layout": "vector",
                "storage": {"kind": "external", "name": "bn.var"},
                "sha256": "00"
            }
        },
        "ops": [
            {
                "id": "vnn.0",
                "op": "trust_ir.vnn.batch_norm",
                "inputs": ["%input"],
                "outputs": ["%bn0"],
                "weights": ["bn.scale", "bn.bias", "bn.mean", "bn.var"],
                "attrs": {"epsilon": 0.00001},
                "provenance": {
                    "gamma_layer_id": "layer.0",
                    "gamma_layer_type": "BatchNorm",
                    "onnx_node_name": "BatchNormalization_0",
                    "onnx_op_type": "BatchNormalization",
                    "onnx_outputs": ["bn0"]
                }
            },
            {
                "id": "vnn.1",
                "op": "trust_ir.vnn.relu",
                "inputs": ["%bn0"],
                "outputs": ["%relu0"],
                "weights": [],
                "attrs": {},
                "provenance": {
                    "gamma_layer_id": "layer.1",
                    "gamma_layer_type": "ReLU",
                    "onnx_node_name": "Relu_1",
                    "onnx_op_type": "Relu",
                    "onnx_outputs": ["relu0"]
                }
            }
        ],
        "edges": [
            {
                "from": "%bn0",
                "to": "vnn.1",
                "from_layer": "layer.0",
                "to_layer": "layer.1",
                "onnx_tensor": "bn0"
            }
        ]
    })
}

fn op_mut<'a>(module: &'a mut Value, op_name: &str) -> &'a mut Value {
    module["ops"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|op| op["op"] == op_name)
        .unwrap()
}

fn expect_reason(mut module: Value, reason: GpuFusionUnsupportedReason) {
    let err = emit_vnn_batch_norm_relu_msl(&module, VnnBatchNormReluOptions::default())
        .expect_err("candidate must fail closed");
    assert_eq!(err.code, "gpu.fusion.unsupported");
    assert_eq!(err.phase, "select_gpu_fusion");
    assert_eq!(err.fusion, BATCH_NORM_RELU_FUSION);
    assert_eq!(err.target, GPU_METAL_MSL_TARGET);
    assert_eq!(err.reason, reason);
    assert!(!err.source_ops.is_empty());
    module["ops"] = json!([]);
}

fn install_relu_relaxation_metadata(module: &mut Value) {
    op_mut(module, "trust_ir.vnn.relu")["attrs"]["relaxation"] = json!({
        "relation": "same",
        "kind": "relu_triangle",
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
    });
}

#[test]
fn emits_bn_relu_f32_nchw_msl_compile_unit() {
    let module = valid_module_json();
    let unit = emit_vnn_batch_norm_relu_msl(&module, VnnBatchNormReluOptions::default()).unwrap();

    assert_eq!(unit.fusion, BATCH_NORM_RELU_FUSION);
    assert_eq!(unit.target, GPU_METAL_MSL_TARGET);
    assert_eq!(unit.source_ops, ["vnn.0", "vnn.1"]);
    assert_eq!(unit.input_tensor, "%input");
    assert_eq!(unit.preactivation_tensor, "%bn0");
    assert_eq!(unit.output_tensor, "%relu0");
    assert_eq!(unit.fused_gamma_layer_ids, ["layer.0", "layer.1"]);
    assert!(unit.certified_pass_run.is_none());
    assert_eq!(
        unit.source_provenance[0].onnx_node_name,
        "BatchNormalization_0"
    );
    assert_eq!(unit.source_provenance[1].onnx_node_name, "Relu_1");
    assert_eq!(unit.element_count, 24);
    assert_eq!(unit.dispatch.grid_size.width, 256);
    assert_eq!(unit.dispatch.threadgroup_size.width, 256);

    assert!(unit.kernel_name.contains("batch_norm_relu"));
    assert!(unit.source.contains("kernel void trust_cg_batch_norm_relu"));
    assert!(unit.source.contains("const device float* input"));
    assert!(unit.source.contains("const device float* scale"));
    assert!(unit.source.contains("constant float& epsilon"));
    assert!(unit.source.contains("uint channel = (tid / HW) % C;"));
    assert!(unit.source.contains("sqrt(variance[channel] + epsilon)"));
    assert!(unit.source.contains("output[tid] = max(y, 0.0f);"));
    assert!(unit.source.contains("Source ops: vnn.0 -> vnn.1"));
    assert!(
        unit.source
            .contains("Fused gamma layer IDs: layer.0, layer.1")
    );
}

#[test]
fn rejects_unsupported_dtype_without_scalar_fallback() {
    let mut module = valid_module_json();
    module["tensors"]["%input"]["dtype"] = json!("f16");
    expect_reason(module, GpuFusionUnsupportedReason::UnsupportedDtype);
}

#[test]
fn rejects_unsupported_layout_without_scalar_fallback() {
    let mut module = valid_module_json();
    module["tensors"]["%input"]["layout"] = json!("nhwc");
    expect_reason(module, GpuFusionUnsupportedReason::UnsupportedLayout);
}

#[test]
fn rejects_dynamic_shape_without_scalar_fallback() {
    let mut module = valid_module_json();
    module["tensors"]["%input"]["shape"] = json!([1, "C", 3, 4]);
    expect_reason(module, GpuFusionUnsupportedReason::DynamicShape);
}

#[test]
fn rejects_shape_mismatch_without_scalar_fallback() {
    let mut module = valid_module_json();
    module["initializers"]["bn.scale"]["shape"] = json!([3]);
    expect_reason(module, GpuFusionUnsupportedReason::ShapeMismatch);
}

#[test]
fn rejects_missing_initializer_without_scalar_fallback() {
    let mut module = valid_module_json();
    module["initializers"]
        .as_object_mut()
        .unwrap()
        .remove("bn.scale");
    expect_reason(module, GpuFusionUnsupportedReason::MissingInitializer);
}

#[test]
fn rejects_training_mode_batch_norm_without_scalar_fallback() {
    let mut module = valid_module_json();
    op_mut(&mut module, "trust_ir.vnn.batch_norm")["attrs"]["training_mode"] = json!(1);
    expect_reason(module, GpuFusionUnsupportedReason::TrainingModeBatchNorm);
}

#[test]
fn rejects_multiple_consumers_without_scalar_fallback() {
    let mut module = valid_module_json();
    module["tensors"]["%relu1"] = json!({
        "shape": [1, 2, 3, 4],
        "dtype": "f32",
        "layout": "nchw",
        "role": "activation"
    });
    module["ops"].as_array_mut().unwrap().push(json!({
        "id": "vnn.extra",
        "op": "trust_ir.vnn.relu",
        "inputs": ["%bn0"],
        "outputs": ["%relu1"],
        "weights": [],
        "attrs": {},
        "provenance": {
            "gamma_layer_id": "layer.extra",
            "gamma_layer_type": "ReLU",
            "onnx_node_name": "Relu_extra",
            "onnx_op_type": "Relu",
            "onnx_outputs": ["relu1"]
        }
    }));
    expect_reason(module, GpuFusionUnsupportedReason::MultipleConsumers);
}

#[test]
fn certified_mode_rejects_missing_relaxation_metadata() {
    let module = valid_module_json();
    let err = emit_vnn_batch_norm_relu_msl(&module, VnnBatchNormReluOptions { certified: true })
        .expect_err("certified mode must require #557 relaxation metadata");
    assert_eq!(
        err.reason,
        GpuFusionUnsupportedReason::MissingRelaxationMetadata
    );
}

#[test]
fn certified_mode_emits_bn_relu_pass_run_from_real_emitter() {
    let mut module = valid_module_json();
    install_relu_relaxation_metadata(&mut module);

    let unit = emit_vnn_batch_norm_relu_msl(&module, VnnBatchNormReluOptions { certified: true })
        .expect("certified BN+ReLU fusion should emit with relaxation metadata");
    let run = unit
        .certified_pass_run
        .as_ref()
        .expect("certified mode should attach a pass run record");

    assert_eq!(run.format_version, "trust-cg.opt.certified_pass_run.v1");
    assert_eq!(run.pass_name, "bn-relu-relaxation-fusion");
    assert_eq!(run.pass_version, 1);
    assert_eq!(
        run.pass_instance_id,
        "bn-relu-relaxation-fusion:vnn.0+vnn.1:v1"
    );
    assert_eq!(run.function_name, "bn_relu");
    assert!(run.changed);
    assert_eq!(run.status, CertifiedPassRunStatus::Verified);
    assert_eq!(run.local_checker.status, CertifiedPassRunStatus::Verified);
    assert_eq!(run.certificate_count, 1);
    assert_eq!(run.failure_count, 0);
    assert!(run.is_verified());
    assert!(
        run.obligation_hash
            .starts_with("trust-cg-opt-certified-pass-run-v1:")
    );
    assert_eq!(run.summary["fusion"], BATCH_NORM_RELU_FUSION);
    assert_eq!(run.summary["source"]["op_ids"], json!(["vnn.0", "vnn.1"]));
    assert_eq!(run.summary["source"]["preactivation_tensor"], "%bn0");
    assert_eq!(run.summary["rewrite"]["op"], "trust_ir.vnn.batch_norm_relu");
    assert_eq!(run.summary["rewrite"]["kernel_name"], unit.kernel_name);
    assert_eq!(run.summary["batch_norm"]["axis"], 1);
    assert_eq!(
        run.summary["batch_norm"]["weights"]["scale"]["sha256"],
        "00"
    );
    assert_eq!(
        run.summary["relaxation"]["metadata_source"],
        "relu.attrs.relaxation"
    );
    assert_eq!(run.summary["relaxation"]["relation"], "same");
    assert_eq!(
        run.summary["certification"]["proof_family"],
        "gamma-bn-relu-fusion-relaxation-v1"
    );
}
