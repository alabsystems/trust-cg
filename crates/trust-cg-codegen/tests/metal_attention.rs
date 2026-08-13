use serde_json::{Value, json};
use trust_cg_codegen::metal_emitter::{
    ATTENTION_QK_SOFTMAX_V_FUSION, GPU_METAL_MSL_TARGET, GpuFusionUnsupportedReason,
    VnnFusedAttentionOptions, emit_vnn_fused_attention_msl,
};

fn valid_attention_module_json() -> Value {
    json!({
        "version": 1,
        "dialect": "trust_ir.vnn",
        "entry": "attention",
        "tensors": {
            "%hidden": {
                "shape": [1, 4, 8],
                "dtype": "f32",
                "layout": "nld",
                "role": "input"
            },
            "%q": {
                "shape": [1, 4, 8],
                "dtype": "f32",
                "layout": "nld",
                "role": "activation"
            },
            "%k": {
                "shape": [1, 4, 8],
                "dtype": "f32",
                "layout": "nld",
                "role": "activation"
            },
            "%v": {
                "shape": [1, 4, 8],
                "dtype": "f32",
                "layout": "nld",
                "role": "activation"
            },
            "%kt": {
                "shape": [1, 8, 4],
                "dtype": "f32",
                "layout": "strided",
                "role": "activation"
            },
            "%scores": {
                "shape": [1, 4, 4],
                "dtype": "f32",
                "layout": "nld",
                "role": "activation"
            },
            "%scaled_scores": {
                "shape": [1, 4, 4],
                "dtype": "f32",
                "layout": "nld",
                "role": "activation"
            },
            "%prob": {
                "shape": [1, 4, 4],
                "dtype": "f32",
                "layout": "nld",
                "role": "activation"
            },
            "%ctx": {
                "shape": [1, 4, 8],
                "dtype": "f32",
                "layout": "nld",
                "role": "output"
            }
        },
        "initializers": {
            "q.weight": {
                "shape": [8, 8],
                "dtype": "f32",
                "layout": "oi",
                "values": [0.1]
            },
            "k.weight": {
                "shape": [8, 8],
                "dtype": "f32",
                "layout": "oi",
                "values": [0.1]
            },
            "v.weight": {
                "shape": [8, 8],
                "dtype": "f32",
                "layout": "oi",
                "values": [0.1]
            },
            "inv_sqrt_d": {
                "shape": [],
                "dtype": "f32",
                "layout": "scalar",
                "values": [0.3535533905932738]
            }
        },
        "ops": [
            {
                "id": "vnn.q",
                "op": "trust_ir.vnn.linear",
                "inputs": ["%hidden"],
                "outputs": ["%q"],
                "weights": ["q.weight"],
                "attrs": {"source_op": "MatMul"},
                "provenance": {
                    "gamma_layer_id": "layer.q",
                    "gamma_layer_type": "Linear",
                    "onnx_node_name": "Q_0",
                    "onnx_op_type": "MatMul",
                    "onnx_outputs": ["q"]
                }
            },
            {
                "id": "vnn.k",
                "op": "trust_ir.vnn.linear",
                "inputs": ["%hidden"],
                "outputs": ["%k"],
                "weights": ["k.weight"],
                "attrs": {"source_op": "MatMul"},
                "provenance": {
                    "gamma_layer_id": "layer.k",
                    "gamma_layer_type": "Linear",
                    "onnx_node_name": "K_1",
                    "onnx_op_type": "MatMul",
                    "onnx_outputs": ["k"]
                }
            },
            {
                "id": "vnn.v",
                "op": "trust_ir.vnn.linear",
                "inputs": ["%hidden"],
                "outputs": ["%v"],
                "weights": ["v.weight"],
                "attrs": {"source_op": "MatMul"},
                "provenance": {
                    "gamma_layer_id": "layer.v",
                    "gamma_layer_type": "Linear",
                    "onnx_node_name": "V_2",
                    "onnx_op_type": "MatMul",
                    "onnx_outputs": ["v"]
                }
            },
            {
                "id": "vnn.transpose",
                "op": "trust_ir.vnn.transpose",
                "inputs": ["%k"],
                "outputs": ["%kt"],
                "weights": [],
                "attrs": {"perm": [0, 2, 1]},
                "provenance": {
                    "gamma_layer_id": "layer.transpose",
                    "gamma_layer_type": "Transpose",
                    "onnx_node_name": "Transpose_3",
                    "onnx_op_type": "Transpose",
                    "onnx_outputs": ["kt"]
                }
            },
            {
                "id": "vnn.scores",
                "op": "trust_ir.vnn.matmul",
                "inputs": ["%q", "%kt"],
                "outputs": ["%scores"],
                "weights": [],
                "attrs": {},
                "provenance": {
                    "gamma_layer_id": "layer.scores",
                    "gamma_layer_type": "MatMul",
                    "onnx_node_name": "Scores_4",
                    "onnx_op_type": "MatMul",
                    "onnx_outputs": ["scores"]
                }
            },
            {
                "id": "vnn.scale",
                "op": "trust_ir.vnn.scale",
                "inputs": ["%scores"],
                "outputs": ["%scaled_scores"],
                "weights": ["inv_sqrt_d"],
                "attrs": {"scale_initializer": "inv_sqrt_d"},
                "provenance": {
                    "gamma_layer_id": "layer.scale",
                    "gamma_layer_type": "Scale",
                    "onnx_node_name": "Scale_5",
                    "onnx_op_type": "Mul",
                    "onnx_outputs": ["scaled_scores"]
                }
            },
            {
                "id": "vnn.softmax",
                "op": "trust_ir.vnn.softmax",
                "inputs": ["%scaled_scores"],
                "outputs": ["%prob"],
                "weights": [],
                "attrs": {"axis": -1},
                "provenance": {
                    "gamma_layer_id": "layer.softmax",
                    "gamma_layer_type": "Softmax",
                    "onnx_node_name": "Softmax_6",
                    "onnx_op_type": "Softmax",
                    "onnx_outputs": ["prob"]
                }
            },
            {
                "id": "vnn.context",
                "op": "trust_ir.vnn.matmul",
                "inputs": ["%prob", "%v"],
                "outputs": ["%ctx"],
                "weights": [],
                "attrs": {},
                "provenance": {
                    "gamma_layer_id": "layer.context",
                    "gamma_layer_type": "MatMul",
                    "onnx_node_name": "Context_7",
                    "onnx_op_type": "MatMul",
                    "onnx_outputs": ["ctx"]
                }
            }
        ]
    })
}

fn expect_reason(module: Value, reason: GpuFusionUnsupportedReason) {
    let err = emit_vnn_fused_attention_msl(&module, VnnFusedAttentionOptions::default())
        .expect_err("candidate must fail closed");
    assert_eq!(err.code, "gpu.fusion.unsupported");
    assert_eq!(err.phase, "select_gpu_fusion");
    assert_eq!(err.fusion, ATTENTION_QK_SOFTMAX_V_FUSION);
    assert_eq!(err.target, GPU_METAL_MSL_TARGET);
    assert_eq!(err.reason, reason);
}

#[test]
fn emits_attention_qk_softmax_v_f32_nld_msl_compile_unit() {
    let module = valid_attention_module_json();
    let unit = emit_vnn_fused_attention_msl(&module, VnnFusedAttentionOptions::default()).unwrap();

    assert_eq!(unit.fusion, ATTENTION_QK_SOFTMAX_V_FUSION);
    assert_eq!(unit.target, GPU_METAL_MSL_TARGET);
    assert_eq!(
        unit.source_ops,
        [
            "vnn.q",
            "vnn.k",
            "vnn.v",
            "vnn.transpose",
            "vnn.scores",
            "vnn.scale",
            "vnn.softmax",
            "vnn.context",
        ]
    );
    assert_eq!(unit.query_tensor, "%q");
    assert_eq!(unit.key_tensor, "%k");
    assert_eq!(unit.value_tensor, "%v");
    assert_eq!(unit.scores_tensor, "%scores");
    assert_eq!(unit.probability_tensor, "%prob");
    assert_eq!(unit.output_tensor, "%ctx");
    assert_eq!(
        unit.fused_gamma_layer_ids,
        [
            "layer.q",
            "layer.k",
            "layer.v",
            "layer.transpose",
            "layer.scores",
            "layer.scale",
            "layer.softmax",
            "layer.context",
        ]
    );
    assert_eq!(unit.batch, 1);
    assert_eq!(unit.sequence, 4);
    assert_eq!(unit.head_dim, 8);
    assert_eq!(unit.output_element_count, 32);
    assert_eq!(unit.dispatch.grid_size.width, 8);
    assert_eq!(unit.dispatch.grid_size.height, 8);
    assert_eq!(unit.dispatch.threadgroup_size.width, 8);
    assert_eq!(unit.dispatch.threadgroup_size.height, 8);

    assert!(unit.kernel_name.contains("attention_qk_softmax_v"));
    assert!(
        unit.source
            .contains("kernel void trust_cg_attention_qk_softmax_v")
    );
    assert!(unit.source.contains("const device float* query"));
    assert!(unit.source.contains("const device float* key"));
    assert!(unit.source.contains("const device float* value"));
    assert!(unit.source.contains("constant float& scale"));
    assert!(unit.source.contains("const uint S = 4u;"));
    assert!(unit.source.contains("const uint D = 8u;"));
    assert!(
        unit.source
            .contains("if (row >= B * S || dim >= D) return;")
    );
    assert!(
        unit.source
            .contains("max_score = max(max_score, dot * scale);")
    );
    assert!(
        unit.source
            .contains("float weight = exp((dot * scale) - max_score);")
    );
    assert!(unit.source.contains("acc += weight * value[k_base + dim];"));
    assert!(unit.source.contains("output[q_base + dim] = acc / denom;"));
    assert!(
        unit.source
            .contains("Source ops: vnn.q -> vnn.k -> vnn.v -> vnn.transpose")
    );
}

#[test]
fn fused_attention_reference_matches_naive_softmax_matmul() {
    let q = vec![0.2, -0.1, 0.4, 0.3];
    let k = vec![0.5, 0.25, -0.2, 0.6];
    let v = vec![1.0, -1.0, 0.5, 2.0];
    let scale = std::f32::consts::FRAC_1_SQRT_2;

    let fused = fused_attention_reference(&q, &k, &v, 1, 2, 2, scale);
    let naive = naive_attention_reference(&q, &k, &v, 1, 2, 2, scale);

    for (actual, expected) in fused.iter().zip(naive.iter()) {
        assert!(
            (actual - expected).abs() <= 1.0e-6,
            "actual={actual} expected={expected}"
        );
    }
}

#[test]
fn rejects_unsupported_attention_dtype_without_partial_kernel() {
    let mut module = valid_attention_module_json();
    module["tensors"]["%q"]["dtype"] = json!("f16");
    expect_reason(module, GpuFusionUnsupportedReason::UnsupportedDtype);
}

#[test]
fn rejects_unsupported_attention_layout_without_partial_kernel() {
    let mut module = valid_attention_module_json();
    module["tensors"]["%q"]["layout"] = json!("strided");
    expect_reason(module, GpuFusionUnsupportedReason::UnsupportedLayout);
}

#[test]
fn rejects_dynamic_attention_shape_without_partial_kernel() {
    let mut module = valid_attention_module_json();
    module["tensors"]["%q"]["shape"] = json!([1, "S", 8]);
    expect_reason(module, GpuFusionUnsupportedReason::DynamicShape);
}

#[test]
fn rejects_non_last_softmax_axis_without_partial_kernel() {
    let mut module = valid_attention_module_json();
    module["ops"][6]["attrs"]["axis"] = json!(1);
    expect_reason(module, GpuFusionUnsupportedReason::UnsupportedSoftmaxAxis);
}

#[test]
fn rejects_missing_transpose_metadata_without_partial_kernel() {
    let mut module = valid_attention_module_json();
    module["ops"][3]["attrs"]["perm"] = json!([0, 1, 2]);
    expect_reason(module, GpuFusionUnsupportedReason::MissingTransposeMetadata);
}

#[test]
fn rejects_attention_mask_without_partial_kernel() {
    let mut module = valid_attention_module_json();
    module["tensors"]["%masked_scores"] = json!({
        "shape": [1, 4, 4],
        "dtype": "f32",
        "layout": "nld",
        "role": "activation"
    });
    module["ops"].as_array_mut().unwrap().insert(
        5,
        json!({
            "id": "vnn.mask",
            "op": "trust_ir.vnn.add",
            "inputs": ["%scores", "%mask"],
            "outputs": ["%masked_scores"],
            "weights": [],
            "attrs": {},
            "provenance": {
                "gamma_layer_id": "layer.mask",
                "gamma_layer_type": "Add",
                "onnx_node_name": "Mask_5",
                "onnx_op_type": "Add",
                "onnx_outputs": ["masked_scores"]
            }
        }),
    );
    module["ops"][6]["inputs"] = json!(["%masked_scores"]);
    expect_reason(module, GpuFusionUnsupportedReason::UnsupportedAttentionMask);
}

#[test]
fn rejects_multiple_attention_consumers_without_partial_kernel() {
    let mut module = valid_attention_module_json();
    module["tensors"]["%prob_alias"] = json!({
        "shape": [1, 4, 4],
        "dtype": "f32",
        "layout": "nld",
        "role": "activation"
    });
    module["ops"].as_array_mut().unwrap().push(json!({
        "id": "vnn.extra",
        "op": "trust_ir.vnn.relu",
        "inputs": ["%prob"],
        "outputs": ["%prob_alias"],
        "weights": [],
        "attrs": {},
        "provenance": {
            "gamma_layer_id": "layer.extra",
            "gamma_layer_type": "ReLU",
            "onnx_node_name": "Relu_extra",
            "onnx_op_type": "Relu",
            "onnx_outputs": ["prob_alias"]
        }
    }));
    expect_reason(module, GpuFusionUnsupportedReason::MultipleConsumers);
}

fn fused_attention_reference(
    query: &[f32],
    key: &[f32],
    value: &[f32],
    batch: usize,
    sequence: usize,
    dim: usize,
    scale: f32,
) -> Vec<f32> {
    let mut output = vec![0.0; batch * sequence * dim];
    for b in 0..batch {
        for q_pos in 0..sequence {
            for d in 0..dim {
                let base = b * sequence * dim;
                let q_base = base + q_pos * dim;
                let mut max_score = f32::NEG_INFINITY;
                for k_pos in 0..sequence {
                    let k_base = base + k_pos * dim;
                    let dot = (0..dim)
                        .map(|kk| query[q_base + kk] * key[k_base + kk])
                        .sum::<f32>();
                    max_score = max_score.max(dot * scale);
                }

                let mut denom = 0.0;
                let mut acc = 0.0;
                for k_pos in 0..sequence {
                    let k_base = base + k_pos * dim;
                    let dot = (0..dim)
                        .map(|kk| query[q_base + kk] * key[k_base + kk])
                        .sum::<f32>();
                    let weight = ((dot * scale) - max_score).exp();
                    denom += weight;
                    acc += weight * value[k_base + d];
                }
                output[q_base + d] = acc / denom;
            }
        }
    }
    output
}

fn naive_attention_reference(
    query: &[f32],
    key: &[f32],
    value: &[f32],
    batch: usize,
    sequence: usize,
    dim: usize,
    scale: f32,
) -> Vec<f32> {
    let mut output = vec![0.0; batch * sequence * dim];
    let mut scores = vec![0.0; batch * sequence * sequence];
    for b in 0..batch {
        for q_pos in 0..sequence {
            for k_pos in 0..sequence {
                let base = b * sequence * dim;
                let q_base = base + q_pos * dim;
                let k_base = base + k_pos * dim;
                let dot = (0..dim)
                    .map(|kk| query[q_base + kk] * key[k_base + kk])
                    .sum::<f32>();
                scores[(b * sequence + q_pos) * sequence + k_pos] = dot * scale;
            }
        }
    }

    for b in 0..batch {
        for q_pos in 0..sequence {
            let row_base = (b * sequence + q_pos) * sequence;
            let row = &mut scores[row_base..row_base + sequence];
            let max_score = row.iter().copied().fold(f32::NEG_INFINITY, f32::max);
            let denom = row
                .iter_mut()
                .map(|score| {
                    *score = (*score - max_score).exp();
                    *score
                })
                .sum::<f32>();
            for score in row.iter_mut() {
                *score /= denom;
            }
            for d in 0..dim {
                let mut acc = 0.0;
                for (k_pos, &weight) in row.iter().enumerate() {
                    let base = b * sequence * dim;
                    let k_base = base + k_pos * dim;
                    acc += weight * value[k_base + d];
                }
                output[b * sequence * dim + q_pos * dim + d] = acc;
            }
        }
    }
    output
}
