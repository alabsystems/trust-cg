// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use serde_json::{Value, json};
use trust_cg_onnx_import::{
    AttentionFusionOptions, AttentionFusionUnsupportedReason, Error, GraphFixture, TensorRole,
    VNN_DIALECT, VNN_OP_PREFIX, VnnOp, VnnProvenance, attention_fusion_report,
    attention_fusion_report_for_graph_fixture, import_graph_fixture_str,
    import_onnx_model_proto_bytes, import_path,
};

// ---------------------------------------------------------------------------
// FORMAT FIREWALL enforcement.
//
// The `trust_ir.vnn` dialect label and the `trust_ir.vnn.*` op names asserted
// throughout this file are HISTORICAL and denote no TrustIr artifact: this
// crate has no `trust-ir` dependency and emits no TrustIr. The 2026-09-01
// decision was to KEEP the strings (they are a pinned output contract that
// roughly 1300 lines of assertions below match byte-for-byte) and document them
// unmissably instead of churning the wire format. The test below is the
// enforcing half of that decision: it pins both labels AND checks the premise
// the documentation rests on, so the claim cannot quietly become false.
// ---------------------------------------------------------------------------

/// The four dependencies the crate-level FORMAT FIREWALL section enumerates.
const DOCUMENTED_DEPENDENCIES: [&str; 4] = ["serde", "serde_json", "sha2", "thiserror"];

#[test]
fn vnn_labels_are_pinned_and_this_crate_emits_no_trustir() {
    // 1. The emitted labels are a pinned output contract. Renaming them is a
    //    wire-format break, not a cleanup — see the crate docs for the decision.
    assert_eq!(VNN_DIALECT, "trust_ir.vnn");
    assert_eq!(VNN_OP_PREFIX, "trust_ir.vnn.");
    assert_eq!(VNN_OP_PREFIX, format!("{VNN_DIALECT}."));

    // 2. Every fixture this importer accepts emits exactly those labels.
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut imported = 0usize;
    let mut entries = std::fs::read_dir(&fixtures)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        // Rejection fixtures (e.g. dynamic_shape) are expected to fail; they
        // emit no module and so carry no label to check.
        let Ok(module) = import_path(&path) else {
            continue;
        };
        imported += 1;
        assert_eq!(
            module.dialect,
            VNN_DIALECT,
            "{} emitted an unpinned dialect label",
            path.display()
        );
        for op in &module.ops {
            assert!(
                op.op.starts_with(VNN_OP_PREFIX),
                "{} emitted op `{}` outside the pinned `{VNN_OP_PREFIX}` vocabulary",
                path.display(),
                op.op
            );
        }
    }
    assert!(
        imported >= 8,
        "expected the fixture corpus to import; only {imported} module(s) did, so the \
         label check above proved nothing"
    );

    // 3. The premise the FORMAT FIREWALL rests on: this crate depends on no
    //    part of trust-ir, so the `trust_ir.` prefix above cannot denote a
    //    TrustIr artifact. If this fails, the crate documentation has become
    //    FALSE and the naming decision must be re-taken — do not delete this
    //    assertion to make a new dependency land.
    let manifest_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let manifest = std::fs::read_to_string(&manifest_path).unwrap();
    let mut section = String::new();
    let mut declared = Vec::new();
    let mut trust_ir_deps = Vec::new();
    for raw in manifest.lines() {
        // Comments must be stripped before matching: the manifest deliberately
        // MENTIONS trust-ir in prose (the `trust-cg-onnx-to-vnn-trust-ir`
        // rename note), and prose is not a dependency. No `#` appears inside a
        // quoted value in this manifest, so a plain split is exact here.
        let line = match raw.find('#') {
            Some(index) => &raw[..index],
            None => raw,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = line
            .strip_prefix('[')
            .and_then(|rest| rest.strip_suffix(']'))
        {
            section = header.trim().to_string();
            continue;
        }
        if !section.ends_with("dependencies") {
            continue;
        }
        let key = line
            .split('=')
            .next()
            .unwrap_or_default()
            .trim()
            .trim_matches('"')
            .to_string();
        if line.contains("trust-ir") || line.contains("trust_ir") {
            trust_ir_deps.push(format!("[{section}] {line}"));
        }
        declared.push(key);
    }
    assert!(
        trust_ir_deps.is_empty(),
        "trust-cg-onnx-import declared a trust-ir dependency: {trust_ir_deps:?}\n\
         The crate-level FORMAT FIREWALL states this crate has NO trust-ir dependency \
         and that its `trust_ir.vnn` labels denote no TrustIr artifact. Adding one \
         makes that documentation false. Re-open the naming decision (keep-and-document \
         vs. rename + regenerate goldens) instead of relaxing this check."
    );

    declared.sort();
    let mut expected = DOCUMENTED_DEPENDENCIES.to_vec();
    expected.sort_unstable();
    assert_eq!(
        declared, expected,
        "the crate-level FORMAT FIREWALL enumerates this crate's ENTIRE dependency \
         list; update that sentence in src/lib.rs (and DOCUMENTED_DEPENDENCIES here) to \
         match, after confirming the new dependency does not reach trust-ir"
    );
}

#[test]
fn imports_single_conv2d_fixture() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/single_conv2d.onnx.json")).unwrap();
    assert_eq!(module.dialect, "trust_ir.vnn");
    assert_eq!(module.ops.len(), 1);
    assert_eq!(module.ops[0].op, "trust_ir.vnn.conv2d");
    assert_eq!(module.ops[0].weights, ["conv.weight", "conv.bias"]);
    assert_eq!(module.ops[0].provenance.gamma_layer_id, "layer.0");
    assert_eq!(module.ops[0].provenance.gamma_layer_type, "Conv2d");
    assert!(module.initializers["conv.weight"].sha256.len() == 64);
}

#[test]
fn imports_conv_relu_maxpool_with_edges() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/conv_relu_maxpool.onnx.json")).unwrap();
    let op_names = module
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        op_names,
        [
            "trust_ir.vnn.conv2d",
            "trust_ir.vnn.relu",
            "trust_ir.vnn.max_pool2d"
        ]
    );
    assert_eq!(module.edges.len(), 2);
    assert_eq!(module.edges[0].from_layer, "layer.0");
    assert_eq!(module.edges[0].to_layer, "layer.1");
}

#[test]
fn imports_cnn_with_flatten_and_gemm() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/cnn_with_flatten.onnx.json")).unwrap();
    let last = module.ops.last().unwrap();
    assert_eq!(last.op, "trust_ir.vnn.linear");
    assert_eq!(last.provenance.onnx_op_type, "Gemm");
    assert_eq!(module.tensors["%logits"].role, TensorRole::Output);
}

#[test]
fn imports_matmul_as_linear_add_mlp() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/matmul_add_mlp.onnx.json")).unwrap();
    assert_eq!(module.ops[0].op, "trust_ir.vnn.linear");
    assert_eq!(
        module.ops[0].attrs["source_op"],
        Value::String("MatMul".to_string())
    );
    assert_eq!(module.ops[1].op, "trust_ir.vnn.add");
}

#[test]
fn imports_transformer_attention_subset() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/transformer_attention.onnx.json")).unwrap();
    let op_names = module
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        op_names,
        [
            "trust_ir.vnn.linear",
            "trust_ir.vnn.linear",
            "trust_ir.vnn.linear",
            "trust_ir.vnn.transpose",
            "trust_ir.vnn.matmul",
            "trust_ir.vnn.scale",
            "trust_ir.vnn.softmax",
            "trust_ir.vnn.matmul",
            "trust_ir.vnn.add",
            "trust_ir.vnn.layer_norm"
        ]
    );
    assert_eq!(
        module.ops[3].attrs["perm"],
        Value::Array(vec![0.into(), 2.into(), 1.into()])
    );
    assert_eq!(module.ops[4].attrs["m"], Value::from(4));
    assert_eq!(module.ops[4].attrs["k"], Value::from(8));
    assert_eq!(module.ops[4].attrs["n"], Value::from(4));
    assert_eq!(
        module.ops[5].attrs["scale_initializer"],
        Value::String("inv_sqrt_d".to_string())
    );
    assert_eq!(module.ops[6].attrs["axis"], Value::from(-1));
    assert_eq!(
        module.ops[8].attrs["kind"],
        Value::String("residual".to_string())
    );
    assert_eq!(module.ops[9].weights, ["ln.weight", "ln.bias"]);
    assert_eq!(module.ops[9].attrs["epsilon"], Value::from(0.000001));
    assert_eq!(module.ops[9].provenance.onnx_op_type, "LayerNormalization");
}

#[test]
fn reports_transformer_attention_fusion_eligible() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/transformer_attention.onnx.json")).unwrap();
    let report = attention_fusion_report(&module, AttentionFusionOptions::default());
    assert!(report.eligible, "{report:?}");
    assert!(report.diagnostics.is_empty());
    assert_eq!(report.candidates.len(), 1);
    let candidate = &report.candidates[0];
    assert_eq!(candidate.batch, 1);
    assert_eq!(candidate.sequence, 4);
    assert_eq!(candidate.head_count, 1);
    assert_eq!(candidate.head_dim, 8);
    assert_eq!(candidate.hidden_dim, 8);
    assert_eq!(candidate.scale, Some(0.3535533905932738));
    assert!(candidate.source_ops.contains(&"Q_0".to_string()));
    assert!(candidate.source_ops.contains(&"Context_7".to_string()));
}

#[test]
fn rejects_attention_mask_between_scale_and_softmax() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["tensors"].as_array_mut().unwrap().push(
        json!({ "name": "masked_scores", "shape": [1, 4, 4], "dtype": "f32", "layout": "nld" }),
    );
    fixture["initializers"]
        .as_array_mut()
        .unwrap()
        .push(json!({ "name": "attention_mask", "shape": [1, 4, 4], "dtype": "f32", "layout": "strided", "values": [0.0] }));
    let nodes = fixture["nodes"].as_array_mut().unwrap();
    nodes.insert(
        6,
        json!({
            "name": "Mask_6",
            "op_type": "Add",
            "inputs": ["scaled_scores", "attention_mask"],
            "outputs": ["masked_scores"]
        }),
    );
    nodes[7]["inputs"] = json!(["masked_scores"]);

    let module = import_graph_fixture_str(&fixture.to_string()).unwrap();
    assert_attention_rejects(
        &module,
        AttentionFusionUnsupportedReason::UnsupportedAttentionMask,
    );
}

#[test]
fn rejects_attention_dropout() {
    let mut module =
        import_graph_fixture_str(include_str!("fixtures/transformer_attention.onnx.json")).unwrap();
    module.ops.push(VnnOp {
        id: "vnn.10".to_string(),
        op: "trust_ir.vnn.dropout".to_string(),
        inputs: vec!["%prob".to_string()],
        outputs: vec!["%prob_after_dropout".to_string()],
        weights: vec![],
        attrs: Default::default(),
        provenance: VnnProvenance {
            gamma_layer_id: "layer.10".to_string(),
            gamma_layer_type: "Dropout".to_string(),
            onnx_node_name: "Dropout_6b".to_string(),
            onnx_op_type: "Dropout".to_string(),
            onnx_outputs: vec!["prob_after_dropout".to_string()],
        },
    });

    assert_attention_rejects(
        &module,
        AttentionFusionUnsupportedReason::UnsupportedDropout,
    );
}

#[test]
fn rejects_attention_dynamic_sequence_length_preflight() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["inputs"][0]["shape"] = json!([1, -1, 8]);
    let graph: GraphFixture = serde_json::from_value(fixture).unwrap();
    let report =
        attention_fusion_report_for_graph_fixture(&graph, AttentionFusionOptions::default());
    assert!(!report.eligible);
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason == AttentionFusionUnsupportedReason::DynamicShape),
        "{report:?}"
    );
}

#[test]
fn rejects_attention_gather_data_dependent_indexing_preflight() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["initializers"].as_array_mut().unwrap().push(
        json!({ "name": "gather_index", "shape": [1], "dtype": "i64", "layout": "vector", "values": [0] }),
    );
    fixture["tensors"].as_array_mut().unwrap().push(
        json!({ "name": "gathered_hidden", "shape": [1, 4, 8], "dtype": "f32", "layout": "nld" }),
    );
    fixture["nodes"].as_array_mut().unwrap().push(json!({
        "name": "Gather_unsupported",
        "op_type": "Gather",
        "inputs": ["hidden", "gather_index"],
        "outputs": ["gathered_hidden"],
        "attributes": { "axis": 1 }
    }));

    assert_attention_fixture_rejects(
        fixture,
        AttentionFusionUnsupportedReason::DataDependentIndexing,
        "Gather_unsupported",
    );
}

#[test]
fn rejects_attention_scatter_data_dependent_indexing_preflight() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["initializers"].as_array_mut().unwrap().push(
        json!({ "name": "scatter_index", "shape": [1], "dtype": "i64", "layout": "vector", "values": [0] }),
    );
    fixture["tensors"].as_array_mut().unwrap().push(
        json!({ "name": "scattered_hidden", "shape": [1, 4, 8], "dtype": "f32", "layout": "nld" }),
    );
    fixture["nodes"].as_array_mut().unwrap().push(json!({
        "name": "Scatter_unsupported",
        "op_type": "Scatter",
        "inputs": ["hidden", "scatter_index", "hidden"],
        "outputs": ["scattered_hidden"],
        "attributes": { "axis": 1 }
    }));

    assert_attention_fixture_rejects(
        fixture,
        AttentionFusionUnsupportedReason::DataDependentIndexing,
        "Scatter_unsupported",
    );
}

#[test]
fn rejects_attention_unsupported_dtype() {
    let mut fixture = transformer_attention_fixture_value();
    for group in ["inputs", "tensors", "initializers"] {
        for tensor in fixture[group].as_array_mut().unwrap() {
            if tensor["dtype"] == "f32" {
                tensor["dtype"] = json!("f16");
            }
        }
    }
    let module = import_graph_fixture_str(&fixture.to_string()).unwrap();
    assert_attention_rejects(&module, AttentionFusionUnsupportedReason::UnsupportedDtype);
}

#[test]
fn rejects_attention_missing_transpose_metadata() {
    let mut module =
        import_graph_fixture_str(include_str!("fixtures/transformer_attention.onnx.json")).unwrap();
    module.ops[3].attrs.remove("perm");
    assert_attention_rejects(
        &module,
        AttentionFusionUnsupportedReason::MissingTransposeMetadata,
    );
}

#[test]
fn rejects_attention_reshape_missing_static_target_shape_metadata() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["tensors"]
        .as_array_mut()
        .unwrap()
        .push(json!({ "name": "q_reshaped", "shape": [1, 4, 8], "dtype": "f32", "layout": "nld" }));
    fixture["initializers"].as_array_mut().unwrap().push(
        json!({ "name": "q_target_shape", "shape": [3], "dtype": "i64", "layout": "vector", "values": [1, 4, 8] }),
    );
    let nodes = fixture["nodes"].as_array_mut().unwrap();
    nodes.insert(
        1,
        json!({
            "name": "Reshape_Q",
            "op_type": "Reshape",
            "inputs": ["q", "q_target_shape"],
            "outputs": ["q_reshaped"]
        }),
    );
    nodes[5]["inputs"][0] = json!("q_reshaped");

    let mut module = import_graph_fixture_str(&fixture.to_string()).unwrap();
    let reshape = module
        .ops
        .iter_mut()
        .find(|op| op.provenance.onnx_node_name == "Reshape_Q")
        .unwrap();
    reshape.attrs.remove("target_shape");

    assert_attention_rejects(
        &module,
        AttentionFusionUnsupportedReason::MissingStaticShapeMetadata,
    );
}

#[test]
fn rejects_attention_reshape_missing_static_metadata_preflight() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["tensors"]
        .as_array_mut()
        .unwrap()
        .push(json!({ "name": "q_reshaped", "shape": [1, 4, 8], "dtype": "f32", "layout": "nld" }));
    fixture["initializers"].as_array_mut().unwrap().push(
        json!({ "name": "q_dynamic_shape", "shape": [3], "dtype": "i64", "layout": "vector" }),
    );
    fixture["nodes"].as_array_mut().unwrap().insert(
        1,
        json!({
            "name": "Reshape_missing_shape_values",
            "op_type": "Reshape",
            "inputs": ["q", "q_dynamic_shape"],
            "outputs": ["q_reshaped"]
        }),
    );

    assert_attention_fixture_rejects(
        fixture,
        AttentionFusionUnsupportedReason::MissingStaticShapeMetadata,
        "Reshape_missing_shape_values",
    );
}

#[test]
fn rejects_attention_split_missing_static_metadata_preflight() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["tensors"].as_array_mut().unwrap().extend([
        json!({ "name": "q_head0", "shape": [1, 2, 8], "dtype": "f32", "layout": "nld" }),
        json!({ "name": "q_head1", "shape": [1, 2, 8], "dtype": "f32", "layout": "nld" }),
    ]);
    fixture["nodes"].as_array_mut().unwrap().push(json!({
        "name": "Split_missing_sizes",
        "op_type": "Split",
        "inputs": ["q"],
        "outputs": ["q_head0", "q_head1"],
        "attributes": { "axis": 1 }
    }));

    assert_attention_fixture_rejects(
        fixture,
        AttentionFusionUnsupportedReason::MissingStaticShapeMetadata,
        "Split_missing_sizes",
    );
}

#[test]
fn rejects_attention_concat_missing_static_metadata_preflight() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["tensors"]
        .as_array_mut()
        .unwrap()
        .push(json!({ "name": "concat_qk", "shape": [1, 4, 16], "dtype": "f32", "layout": "nld" }));
    fixture["nodes"].as_array_mut().unwrap().push(json!({
        "name": "Concat_missing_axis",
        "op_type": "Concat",
        "inputs": ["q", "k"],
        "outputs": ["concat_qk"]
    }));

    assert_attention_fixture_rejects(
        fixture,
        AttentionFusionUnsupportedReason::MissingStaticShapeMetadata,
        "Concat_missing_axis",
    );
}

#[test]
fn rejects_attention_non_last_axis_softmax() {
    let mut fixture = transformer_attention_fixture_value();
    fixture["nodes"][6]["attributes"]["axis"] = json!(1);
    let module = import_graph_fixture_str(&fixture.to_string()).unwrap();
    assert_attention_rejects(
        &module,
        AttentionFusionUnsupportedReason::UnsupportedSoftmaxAxis,
    );
}

#[test]
fn rejects_certified_attention_without_relaxation_policy() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/transformer_attention.onnx.json")).unwrap();
    let report = attention_fusion_report(
        &module,
        AttentionFusionOptions {
            certified: true,
            relaxation_policy: None,
            checker_obligation_schema: None,
        },
    );
    assert!(!report.eligible);
    assert!(report.candidates.is_empty());
    assert!(
        report.diagnostics.iter().any(|diagnostic| {
            diagnostic.reason == AttentionFusionUnsupportedReason::MissingRelaxationMetadata
        }),
        "{report:?}"
    );
}

#[test]
fn rejects_certified_attention_without_checker_obligation_schema() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/transformer_attention.onnx.json")).unwrap();
    let report = attention_fusion_report(
        &module,
        AttentionFusionOptions {
            certified: true,
            relaxation_policy: Some("softmax-relaxation-v1".to_string()),
            checker_obligation_schema: None,
        },
    );
    assert!(!report.eligible);
    assert!(report.candidates.is_empty());
    assert!(
        report.diagnostics.iter().any(|diagnostic| {
            diagnostic.reason == AttentionFusionUnsupportedReason::MissingRelaxationMetadata
        }),
        "{report:?}"
    );
}

#[test]
fn allows_certified_attention_with_relaxation_policy_and_checker_schema() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/transformer_attention.onnx.json")).unwrap();
    let report = attention_fusion_report(
        &module,
        AttentionFusionOptions {
            certified: true,
            relaxation_policy: Some("softmax-relaxation-v1".to_string()),
            checker_obligation_schema: Some("attention-softmax-obligations-v1".to_string()),
        },
    );
    assert!(report.eligible, "{report:?}");
    assert_eq!(
        report.candidates[0].relaxation_policy.as_deref(),
        Some("softmax-relaxation-v1")
    );
    assert_eq!(
        report.candidates[0].checker_obligation_schema.as_deref(),
        Some("attention-softmax-obligations-v1")
    );
}

#[test]
fn imports_transformer_block_fixture() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/transformer_block.onnx.json")).unwrap();
    let op_names = module
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        op_names,
        [
            "trust_ir.vnn.layer_norm",
            "trust_ir.vnn.linear",
            "trust_ir.vnn.add",
            "trust_ir.vnn.linear",
            "trust_ir.vnn.add"
        ]
    );
    assert_eq!(module.tensors["%block_out"].role, TensorRole::Output);
    assert_eq!(
        module.ops[0].provenance.gamma_layer_type,
        "LayerNorm".to_string()
    );
    assert_eq!(
        module.ops[2].attrs["kind"],
        Value::String("bias".to_string())
    );
    assert_eq!(
        module.ops[4].attrs["kind"],
        Value::String("residual".to_string())
    );
}

#[test]
fn imports_remaining_cnn_mvp_ops() {
    let module =
        import_graph_fixture_str(include_str!("fixtures/cnn_structural_ops.onnx.json")).unwrap();
    let op_names = module
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        op_names,
        [
            "trust_ir.vnn.batch_norm",
            "trust_ir.vnn.avg_pool2d",
            "trust_ir.vnn.avg_pool2d",
            "trust_ir.vnn.transpose",
            "trust_ir.vnn.reshape"
        ]
    );
    assert_eq!(module.ops[2].attrs["global"], Value::Bool(true));
    assert_eq!(
        module.ops[4].attrs["target_shape"],
        Value::Array(vec![Value::from(1), Value::from(3)])
    );
}

#[test]
fn rejects_non_constant_mul() {
    let err = import_graph_fixture_str(
        r#"{
          "name": "bad_mul",
          "inputs": [
            { "name": "a", "shape": [1, 4], "dtype": "f32", "layout": "nc" },
            { "name": "b", "shape": [1, 4], "dtype": "f32", "layout": "nc" }
          ],
          "outputs": ["out"],
          "tensors": [
            { "name": "out", "shape": [1, 4], "dtype": "f32", "layout": "nc" }
          ],
          "nodes": [
            { "name": "Mul_0", "op_type": "Mul", "inputs": ["a", "b"], "outputs": ["out"] }
          ]
        }"#,
    )
    .unwrap_err();
    assert!(matches!(err, Error::Unsupported(message) if message.contains("constant scale")));
}

#[test]
fn rejects_dynamic_shapes() {
    let err =
        import_graph_fixture_str(include_str!("fixtures/dynamic_shape.onnx.json")).unwrap_err();
    assert!(matches!(err, Error::Invalid(message) if message.contains("dynamic/unknown")));
}

#[test]
fn rejects_unknown_data_path_ops() {
    let err = import_graph_fixture_str(
        r#"{
          "name": "unsupported",
          "inputs": [
            { "name": "input", "shape": [1, 3], "dtype": "f32", "layout": "nc" }
          ],
          "outputs": ["out"],
          "tensors": [
            { "name": "out", "shape": [1, 3], "dtype": "f32", "layout": "nc" }
          ],
          "nodes": [
            { "name": "Clip_0", "op_type": "Clip", "inputs": ["input"], "outputs": ["out"] }
          ]
        }"#,
    )
    .unwrap_err();
    assert!(matches!(err, Error::Unsupported(message) if message.contains("Clip")));
}

#[test]
fn rejects_missing_required_initializers() {
    let err = import_graph_fixture_str(
        r#"{
          "name": "missing_weight",
          "inputs": [
            { "name": "input", "shape": [1, 3, 8, 8], "dtype": "f32", "layout": "nchw" }
          ],
          "outputs": ["out"],
          "tensors": [
            { "name": "out", "shape": [1, 4, 8, 8], "dtype": "f32", "layout": "nchw" }
          ],
          "nodes": [
            { "name": "Conv_0", "op_type": "Conv", "inputs": ["input", "missing.weight"], "outputs": ["out"] }
          ]
        }"#,
    )
    .unwrap_err();
    assert!(matches!(err, Error::Invalid(message) if message.contains("must be an initializer")));
}

#[test]
fn rejects_raw_onnx_binary_boundary() {
    let path = std::env::temp_dir().join(format!(
        "trust-cg-onnx-import-{}-raw.onnx",
        std::process::id()
    ));
    std::fs::write(&path, b"not protobuf").unwrap();
    let err = import_path(&path).unwrap_err();
    let _ = std::fs::remove_file(&path);
    assert!(matches!(err, Error::Invalid(message) if message.contains("ONNX protobuf")));
}

#[test]
fn imports_raw_onnx_model_proto_single_conv2d() {
    let raw_model = raw_single_conv2d_model_proto();
    let module = import_onnx_model_proto_bytes(&raw_model).unwrap();
    assert_eq!(module.dialect, "trust_ir.vnn");
    assert_eq!(module.entry, "raw_single_conv2d");
    assert_eq!(module.ops.len(), 1);
    assert_eq!(module.ops[0].op, "trust_ir.vnn.conv2d");
    assert_eq!(module.ops[0].weights, ["conv.weight", "conv.bias"]);
    assert_eq!(
        module.ops[0].attrs["kernel_shape"],
        Value::Array(vec![3.into(), 3.into()])
    );
    assert_eq!(module.tensors["%input"].role, TensorRole::Input);
    assert_eq!(module.tensors["%conv_out"].role, TensorRole::Output);
    assert_eq!(
        module.initializers["conv.weight"].layout,
        trust_cg_onnx_import::Layout::Oihw
    );
}

#[test]
fn imports_raw_onnx_path() {
    let path = std::env::temp_dir().join(format!(
        "trust-cg-onnx-import-{}-single-conv.onnx",
        std::process::id()
    ));
    std::fs::write(&path, raw_single_conv2d_model_proto()).unwrap();
    let module = import_path(&path).unwrap();
    let _ = std::fs::remove_file(&path);
    assert_eq!(module.ops[0].provenance.onnx_op_type, "Conv");
}

#[test]
fn imports_raw_conv_relu_maxpool_without_intermediate_value_info() {
    let module = import_onnx_model_proto_bytes(&raw_conv_relu_maxpool_model_proto()).unwrap();
    let op_names = module
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        op_names,
        [
            "trust_ir.vnn.conv2d",
            "trust_ir.vnn.relu",
            "trust_ir.vnn.max_pool2d"
        ]
    );
    assert_eq!(module.edges.len(), 2);
    assert_eq!(module.tensors["%conv_out"].shape, vec![1, 8, 32, 32]);
    assert_eq!(module.tensors["%relu_out"].shape, vec![1, 8, 32, 32]);
    assert_eq!(module.tensors["%pool_out"].shape, vec![1, 8, 16, 16]);
    assert_eq!(module.tensors["%pool_out"].role, TensorRole::Output);
}

#[test]
fn imports_raw_cnn_with_flatten_without_intermediate_value_info() {
    let module = import_onnx_model_proto_bytes(&raw_cnn_with_flatten_model_proto()).unwrap();
    let op_names = module
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        op_names,
        [
            "trust_ir.vnn.conv2d",
            "trust_ir.vnn.flatten",
            "trust_ir.vnn.linear"
        ]
    );
    assert_eq!(module.tensors["%conv_out"].shape, vec![1, 4, 8, 8]);
    assert_eq!(module.tensors["%flat"].shape, vec![1, 256]);
    assert_eq!(module.tensors["%logits"].shape, vec![1, 10]);
    assert_eq!(module.tensors["%logits"].role, TensorRole::Output);
    assert_eq!(module.ops[2].provenance.onnx_op_type, "Gemm");
}

#[test]
fn imports_raw_simple_mlp_without_intermediate_value_info() {
    let module = import_onnx_model_proto_bytes(&raw_simple_mlp_model_proto()).unwrap();
    let op_names = module
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(op_names, ["trust_ir.vnn.linear", "trust_ir.vnn.add"]);
    assert_eq!(module.tensors["%mm"].shape, vec![1, 3]);
    assert_eq!(module.tensors["%biased"].shape, vec![1, 3]);
    assert_eq!(
        module.ops[0].attrs["source_op"],
        Value::String("MatMul".to_string())
    );
    assert_eq!(
        module.ops[1].attrs["kind"],
        Value::String("bias".to_string())
    );
}

#[test]
fn imports_gamma_crown_raw_onnx_fixtures_without_intermediate_value_info() {
    let conv = import_onnx_model_proto_bytes(&raw_gamma_conv_relu_maxpool_model_proto()).unwrap();
    let conv_ops = conv.ops.iter().map(|op| op.op.as_str()).collect::<Vec<_>>();
    assert_eq!(
        conv_ops,
        [
            "trust_ir.vnn.conv2d",
            "trust_ir.vnn.relu",
            "trust_ir.vnn.max_pool2d"
        ]
    );
    assert_eq!(conv.tensors["%conv_out"].shape, vec![1, 2, 8, 8]);
    assert_eq!(conv.tensors["%relu_out"].shape, vec![1, 2, 8, 8]);
    assert_eq!(conv.tensors["%output"].shape, vec![1, 2, 4, 4]);
    assert_eq!(conv.tensors["%output"].role, TensorRole::Output);

    let cnn = import_onnx_model_proto_bytes(&raw_gamma_cnn_with_flatten_model_proto()).unwrap();
    let cnn_ops = cnn.ops.iter().map(|op| op.op.as_str()).collect::<Vec<_>>();
    assert_eq!(
        cnn_ops,
        [
            "trust_ir.vnn.conv2d",
            "trust_ir.vnn.relu",
            "trust_ir.vnn.max_pool2d",
            "trust_ir.vnn.flatten",
            "trust_ir.vnn.linear"
        ]
    );
    assert_eq!(cnn.tensors["%_flatten_Flatten_output_0"].shape, vec![1, 64]);
    assert_eq!(cnn.tensors["%output"].shape, vec![1, 2]);
    assert_eq!(cnn.tensors["%output"].role, TensorRole::Output);

    let mlp = import_onnx_model_proto_bytes(&raw_gamma_simple_mlp_model_proto()).unwrap();
    let mlp_ops = mlp.ops.iter().map(|op| op.op.as_str()).collect::<Vec<_>>();
    assert_eq!(
        mlp_ops,
        [
            "trust_ir.vnn.linear",
            "trust_ir.vnn.relu",
            "trust_ir.vnn.linear"
        ]
    );
    assert_eq!(mlp.tensors["%fc1_out"].shape, vec![1, 4]);
    assert_eq!(mlp.tensors["%relu_out"].shape, vec![1, 4]);
    assert_eq!(mlp.tensors["%output"].shape, vec![1, 2]);

    let linear_softmax =
        import_onnx_model_proto_bytes(&raw_gamma_linear_softmax_model_proto()).unwrap();
    let linear_softmax_ops = linear_softmax
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        linear_softmax_ops,
        ["trust_ir.vnn.linear", "trust_ir.vnn.softmax"]
    );
    assert_eq!(linear_softmax.tensors["%logits"].shape, vec![1, 3]);
    assert_eq!(
        linear_softmax.tensors["%probabilities"].role,
        TensorRole::Output
    );
    assert_eq!(linear_softmax.ops[1].attrs["axis"], Value::from(1));
    assert_eq!(linear_softmax.ops[1].provenance.onnx_op_type, "Softmax");

    let class_model = import_onnx_model_proto_bytes(&raw_gamma_class_model_proto()).unwrap();
    let class_ops = class_model
        .ops
        .iter()
        .map(|op| op.op.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        class_ops,
        [
            "trust_ir.vnn.conv2d",
            "trust_ir.vnn.relu",
            "trust_ir.vnn.max_pool2d",
            "trust_ir.vnn.flatten",
            "trust_ir.vnn.linear",
            "trust_ir.vnn.softmax"
        ]
    );
    assert_eq!(class_model.tensors["%image"].shape, vec![1, 3, 8, 8]);
    assert_eq!(class_model.tensors["%probabilities"].shape, vec![1, 100]);
    assert_eq!(
        class_model.tensors["%probabilities"].role,
        TensorRole::Output
    );
    assert_eq!(class_model.ops[5].provenance.onnx_op_type, "Softmax");
}

fn transformer_attention_fixture_value() -> Value {
    serde_json::from_str(include_str!("fixtures/transformer_attention.onnx.json")).unwrap()
}

fn assert_attention_rejects(
    module: &trust_cg_onnx_import::VnnModule,
    reason: AttentionFusionUnsupportedReason,
) {
    let report = attention_fusion_report(module, AttentionFusionOptions::default());
    assert!(!report.eligible, "{report:?}");
    assert!(report.candidates.is_empty(), "{report:?}");
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason == reason),
        "{report:?}"
    );
}

fn assert_attention_fixture_rejects(
    fixture: Value,
    reason: AttentionFusionUnsupportedReason,
    source_op: &str,
) {
    let graph: GraphFixture = serde_json::from_value(fixture).unwrap();
    let report =
        attention_fusion_report_for_graph_fixture(&graph, AttentionFusionOptions::default());
    assert!(!report.eligible, "{report:?}");
    assert!(report.candidates.is_empty(), "{report:?}");
    assert!(
        report.diagnostics.iter().any(|diagnostic| {
            diagnostic.reason == reason
                && diagnostic
                    .source_ops
                    .iter()
                    .any(|op| op.as_str() == source_op)
        }),
        "{report:?}"
    );
}

fn raw_single_conv2d_model_proto() -> Vec<u8> {
    let input = value_info("input", 1, &[1, 3, 32, 32]);
    let output = value_info("conv_out", 1, &[1, 8, 30, 30]);
    let weight = tensor(
        "conv.weight",
        1,
        &[8, 3, 3, 3],
        &f32_raw(&[0.1, 0.2, 0.3, 0.4]),
    );
    let bias = tensor("conv.bias", 1, &[8], &f32_raw(&[0.0]));
    let node = message(&[
        field_string(3, "Conv_0"),
        field_string(4, "Conv"),
        field_string(1, "input"),
        field_string(1, "conv.weight"),
        field_string(1, "conv.bias"),
        field_string(2, "conv_out"),
        field_message(5, &attribute_ints("kernel_shape", &[3, 3])),
        field_message(5, &attribute_ints("strides", &[1, 1])),
        field_message(5, &attribute_ints("pads", &[0, 0, 0, 0])),
        field_message(5, &attribute_int("groups", 1)),
    ]);
    let graph = message(&[
        field_string(2, "raw_single_conv2d"),
        field_message(1, &node),
        field_message(5, &weight),
        field_message(5, &bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn raw_conv_relu_maxpool_model_proto() -> Vec<u8> {
    let input = value_info("input", 1, &[1, 3, 32, 32]);
    let output = value_info("pool_out", 1, &[1, 8, 16, 16]);
    let weight = tensor(
        "conv.weight",
        1,
        &[8, 3, 3, 3],
        &f32_raw(&[0.1, 0.2, 0.3, 0.4]),
    );
    let bias = tensor("conv.bias", 1, &[8], &f32_raw(&[0.0]));
    let conv = message(&[
        field_string(3, "Conv_0"),
        field_string(4, "Conv"),
        field_string(1, "input"),
        field_string(1, "conv.weight"),
        field_string(1, "conv.bias"),
        field_string(2, "conv_out"),
        field_message(5, &attribute_ints("kernel_shape", &[3, 3])),
        field_message(5, &attribute_ints("strides", &[1, 1])),
        field_message(5, &attribute_ints("pads", &[1, 1, 1, 1])),
    ]);
    let relu = message(&[
        field_string(3, "Relu_1"),
        field_string(4, "Relu"),
        field_string(1, "conv_out"),
        field_string(2, "relu_out"),
    ]);
    let pool = message(&[
        field_string(3, "MaxPool_2"),
        field_string(4, "MaxPool"),
        field_string(1, "relu_out"),
        field_string(2, "pool_out"),
        field_message(5, &attribute_ints("kernel_shape", &[2, 2])),
        field_message(5, &attribute_ints("strides", &[2, 2])),
        field_message(5, &attribute_ints("pads", &[0, 0, 0, 0])),
    ]);
    let graph = message(&[
        field_string(2, "raw_conv_relu_maxpool"),
        field_message(1, &conv),
        field_message(1, &relu),
        field_message(1, &pool),
        field_message(5, &weight),
        field_message(5, &bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn raw_cnn_with_flatten_model_proto() -> Vec<u8> {
    let input = value_info("input", 1, &[1, 3, 8, 8]);
    let output = value_info("logits", 1, &[1, 10]);
    let conv_weight = tensor(
        "conv.weight",
        1,
        &[4, 3, 3, 3],
        &f32_raw(&[0.1, 0.2, 0.3, 0.4]),
    );
    let conv_bias = tensor("conv.bias", 1, &[4], &f32_raw(&[0.0]));
    let fc_weight = tensor("fc.weight", 1, &[10, 256], &f32_raw(&[0.2, 0.3]));
    let fc_bias = tensor("fc.bias", 1, &[10], &f32_raw(&[0.0]));
    let conv = message(&[
        field_string(3, "Conv_0"),
        field_string(4, "Conv"),
        field_string(1, "input"),
        field_string(1, "conv.weight"),
        field_string(1, "conv.bias"),
        field_string(2, "conv_out"),
        field_message(5, &attribute_ints("kernel_shape", &[3, 3])),
        field_message(5, &attribute_ints("strides", &[1, 1])),
        field_message(5, &attribute_ints("pads", &[1, 1, 1, 1])),
    ]);
    let flatten = message(&[
        field_string(3, "Flatten_1"),
        field_string(4, "Flatten"),
        field_string(1, "conv_out"),
        field_string(2, "flat"),
        field_message(5, &attribute_int("axis", 1)),
    ]);
    let gemm = message(&[
        field_string(3, "Gemm_2"),
        field_string(4, "Gemm"),
        field_string(1, "flat"),
        field_string(1, "fc.weight"),
        field_string(1, "fc.bias"),
        field_string(2, "logits"),
        field_message(5, &attribute_int("transB", 1)),
    ]);
    let graph = message(&[
        field_string(2, "raw_cnn_with_flatten"),
        field_message(1, &conv),
        field_message(1, &flatten),
        field_message(1, &gemm),
        field_message(5, &conv_weight),
        field_message(5, &conv_bias),
        field_message(5, &fc_weight),
        field_message(5, &fc_bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn raw_simple_mlp_model_proto() -> Vec<u8> {
    let input = value_info("input", 1, &[1, 4]);
    let output = value_info("biased", 1, &[1, 3]);
    let weight = tensor("matmul.weight", 1, &[4, 3], &f32_raw(&[0.1, 0.2]));
    let bias = tensor("bias", 1, &[3], &f32_raw(&[0.0]));
    let matmul = message(&[
        field_string(3, "MatMul_0"),
        field_string(4, "MatMul"),
        field_string(1, "input"),
        field_string(1, "matmul.weight"),
        field_string(2, "mm"),
    ]);
    let add = message(&[
        field_string(3, "Add_1"),
        field_string(4, "Add"),
        field_string(1, "mm"),
        field_string(1, "bias"),
        field_string(2, "biased"),
    ]);
    let graph = message(&[
        field_string(2, "raw_simple_mlp"),
        field_message(1, &matmul),
        field_message(1, &add),
        field_message(5, &weight),
        field_message(5, &bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn raw_gamma_conv_relu_maxpool_model_proto() -> Vec<u8> {
    let input = value_info("input", 1, &[1, 1, 8, 8]);
    let output = value_info("output", 1, &[1, 2, 4, 4]);
    let weight = tensor("conv.weight", 1, &[2, 1, 3, 3], &f32_raw(&[0.1, 0.2]));
    let bias = tensor("conv.bias", 1, &[2], &f32_raw(&[0.0]));
    let conv = message(&[
        field_string(3, "Conv_0"),
        field_string(4, "Conv"),
        field_string(1, "input"),
        field_string(1, "conv.weight"),
        field_string(1, "conv.bias"),
        field_string(2, "conv_out"),
        field_message(5, &attribute_ints("kernel_shape", &[3, 3])),
        field_message(5, &attribute_ints("strides", &[1, 1])),
        field_message(5, &attribute_ints("pads", &[1, 1, 1, 1])),
    ]);
    let relu = message(&[
        field_string(3, "Relu_1"),
        field_string(4, "Relu"),
        field_string(1, "conv_out"),
        field_string(2, "relu_out"),
    ]);
    let pool = message(&[
        field_string(3, "MaxPool_2"),
        field_string(4, "MaxPool"),
        field_string(1, "relu_out"),
        field_string(2, "output"),
        field_message(5, &attribute_ints("kernel_shape", &[2, 2])),
        field_message(5, &attribute_ints("strides", &[2, 2])),
        field_message(5, &attribute_ints("pads", &[0, 0, 0, 0])),
    ]);
    let graph = message(&[
        field_string(2, "gamma_conv_relu_maxpool"),
        field_message(1, &conv),
        field_message(1, &relu),
        field_message(1, &pool),
        field_message(5, &weight),
        field_message(5, &bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn raw_gamma_cnn_with_flatten_model_proto() -> Vec<u8> {
    let input = value_info("input", 1, &[1, 1, 8, 8]);
    let output = value_info("output", 1, &[1, 2]);
    let conv_weight = tensor("conv.weight", 1, &[4, 1, 3, 3], &f32_raw(&[0.1, 0.2]));
    let conv_bias = tensor("conv.bias", 1, &[4], &f32_raw(&[0.0]));
    let fc_weight = tensor("fc.weight", 1, &[2, 64], &f32_raw(&[0.2, 0.3]));
    let fc_bias = tensor("fc.bias", 1, &[2], &f32_raw(&[0.0]));
    let conv = message(&[
        field_string(3, "Conv_0"),
        field_string(4, "Conv"),
        field_string(1, "input"),
        field_string(1, "conv.weight"),
        field_string(1, "conv.bias"),
        field_string(2, "conv_out"),
        field_message(5, &attribute_ints("kernel_shape", &[3, 3])),
        field_message(5, &attribute_ints("strides", &[1, 1])),
        field_message(5, &attribute_ints("pads", &[1, 1, 1, 1])),
    ]);
    let relu = message(&[
        field_string(3, "Relu_1"),
        field_string(4, "Relu"),
        field_string(1, "conv_out"),
        field_string(2, "relu_out"),
    ]);
    let pool = message(&[
        field_string(3, "MaxPool_2"),
        field_string(4, "MaxPool"),
        field_string(1, "relu_out"),
        field_string(2, "pool_out"),
        field_message(5, &attribute_ints("kernel_shape", &[2, 2])),
        field_message(5, &attribute_ints("strides", &[2, 2])),
        field_message(5, &attribute_ints("pads", &[0, 0, 0, 0])),
    ]);
    let flatten = message(&[
        field_string(3, "Flatten_3"),
        field_string(4, "Flatten"),
        field_string(1, "pool_out"),
        field_string(2, "_flatten_Flatten_output_0"),
        field_message(5, &attribute_int("axis", 1)),
    ]);
    let gemm = message(&[
        field_string(3, "Gemm_4"),
        field_string(4, "Gemm"),
        field_string(1, "_flatten_Flatten_output_0"),
        field_string(1, "fc.weight"),
        field_string(1, "fc.bias"),
        field_string(2, "output"),
        field_message(5, &attribute_int("transB", 1)),
    ]);
    let graph = message(&[
        field_string(2, "gamma_cnn_with_flatten"),
        field_message(1, &conv),
        field_message(1, &relu),
        field_message(1, &pool),
        field_message(1, &flatten),
        field_message(1, &gemm),
        field_message(5, &conv_weight),
        field_message(5, &conv_bias),
        field_message(5, &fc_weight),
        field_message(5, &fc_bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn raw_gamma_simple_mlp_model_proto() -> Vec<u8> {
    let input = value_info("input", 1, &[1, 3]);
    let output = value_info("output", 1, &[1, 2]);
    let fc1_weight = tensor("fc1.weight", 1, &[4, 3], &f32_raw(&[0.1, 0.2]));
    let fc1_bias = tensor("fc1.bias", 1, &[4], &f32_raw(&[0.0]));
    let fc2_weight = tensor("fc2.weight", 1, &[2, 4], &f32_raw(&[0.2, 0.3]));
    let fc2_bias = tensor("fc2.bias", 1, &[2], &f32_raw(&[0.0]));
    let fc1 = message(&[
        field_string(3, "Gemm_0"),
        field_string(4, "Gemm"),
        field_string(1, "input"),
        field_string(1, "fc1.weight"),
        field_string(1, "fc1.bias"),
        field_string(2, "fc1_out"),
        field_message(5, &attribute_int("transB", 1)),
    ]);
    let relu = message(&[
        field_string(3, "Relu_1"),
        field_string(4, "Relu"),
        field_string(1, "fc1_out"),
        field_string(2, "relu_out"),
    ]);
    let fc2 = message(&[
        field_string(3, "Gemm_2"),
        field_string(4, "Gemm"),
        field_string(1, "relu_out"),
        field_string(1, "fc2.weight"),
        field_string(1, "fc2.bias"),
        field_string(2, "output"),
        field_message(5, &attribute_int("transB", 1)),
    ]);
    let graph = message(&[
        field_string(2, "gamma_simple_mlp"),
        field_message(1, &fc1),
        field_message(1, &relu),
        field_message(1, &fc2),
        field_message(5, &fc1_weight),
        field_message(5, &fc1_bias),
        field_message(5, &fc2_weight),
        field_message(5, &fc2_bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn raw_gamma_linear_softmax_model_proto() -> Vec<u8> {
    let input = value_info("input", 1, &[1, 4]);
    let output = value_info("probabilities", 1, &[1, 3]);
    let weight = tensor("linear.weight", 1, &[3, 4], &f32_raw(&[0.1, 0.2]));
    let bias = tensor("linear.bias", 1, &[3], &f32_raw(&[0.0]));
    let linear = message(&[
        field_string(3, "Gemm_0"),
        field_string(4, "Gemm"),
        field_string(1, "input"),
        field_string(1, "linear.weight"),
        field_string(1, "linear.bias"),
        field_string(2, "logits"),
        field_message(5, &attribute_int("transB", 1)),
    ]);
    let softmax = message(&[
        field_string(3, "Softmax_1"),
        field_string(4, "Softmax"),
        field_string(1, "logits"),
        field_string(2, "probabilities"),
        field_message(5, &attribute_int("axis", 1)),
    ]);
    let graph = message(&[
        field_string(2, "gamma_linear_softmax"),
        field_message(1, &linear),
        field_message(1, &softmax),
        field_message(5, &weight),
        field_message(5, &bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn raw_gamma_class_model_proto() -> Vec<u8> {
    let input = value_info("image", 1, &[1, 3, 8, 8]);
    let output = value_info("probabilities", 1, &[1, 100]);
    let conv_weight = tensor("conv.weight", 1, &[4, 3, 3, 3], &f32_raw(&[0.1, 0.2]));
    let conv_bias = tensor("conv.bias", 1, &[4], &f32_raw(&[0.0]));
    let fc_weight = tensor("fc.weight", 1, &[100, 64], &f32_raw(&[0.2, 0.3]));
    let fc_bias = tensor("fc.bias", 1, &[100], &f32_raw(&[0.0]));
    let conv = message(&[
        field_string(3, "Conv_0"),
        field_string(4, "Conv"),
        field_string(1, "image"),
        field_string(1, "conv.weight"),
        field_string(1, "conv.bias"),
        field_string(2, "conv_out"),
        field_message(5, &attribute_ints("kernel_shape", &[3, 3])),
        field_message(5, &attribute_ints("strides", &[1, 1])),
        field_message(5, &attribute_ints("pads", &[1, 1, 1, 1])),
    ]);
    let relu = message(&[
        field_string(3, "Relu_1"),
        field_string(4, "Relu"),
        field_string(1, "conv_out"),
        field_string(2, "relu_out"),
    ]);
    let pool = message(&[
        field_string(3, "MaxPool_2"),
        field_string(4, "MaxPool"),
        field_string(1, "relu_out"),
        field_string(2, "pool_out"),
        field_message(5, &attribute_ints("kernel_shape", &[2, 2])),
        field_message(5, &attribute_ints("strides", &[2, 2])),
        field_message(5, &attribute_ints("pads", &[0, 0, 0, 0])),
    ]);
    let flatten = message(&[
        field_string(3, "Flatten_3"),
        field_string(4, "Flatten"),
        field_string(1, "pool_out"),
        field_string(2, "flat"),
        field_message(5, &attribute_int("axis", 1)),
    ]);
    let linear = message(&[
        field_string(3, "Gemm_4"),
        field_string(4, "Gemm"),
        field_string(1, "flat"),
        field_string(1, "fc.weight"),
        field_string(1, "fc.bias"),
        field_string(2, "logits"),
        field_message(5, &attribute_int("transB", 1)),
    ]);
    let softmax = message(&[
        field_string(3, "Softmax_5"),
        field_string(4, "Softmax"),
        field_string(1, "logits"),
        field_string(2, "probabilities"),
        field_message(5, &attribute_int("axis", 1)),
    ]);
    let graph = message(&[
        field_string(2, "gamma_class"),
        field_message(1, &conv),
        field_message(1, &relu),
        field_message(1, &pool),
        field_message(1, &flatten),
        field_message(1, &linear),
        field_message(1, &softmax),
        field_message(5, &conv_weight),
        field_message(5, &conv_bias),
        field_message(5, &fc_weight),
        field_message(5, &fc_bias),
        field_message(11, &input),
        field_message(12, &output),
    ]);
    message(&[field_message(7, &graph)])
}

fn value_info(name: &str, elem_type: u64, dims: &[i64]) -> Vec<u8> {
    let shape = message(
        &dims
            .iter()
            .map(|dim| field_message(1, &message(&[field_varint(1, *dim as u64)])))
            .collect::<Vec<_>>(),
    );
    let tensor_type = message(&[field_varint(1, elem_type), field_message(2, &shape)]);
    let ty = message(&[field_message(1, &tensor_type)]);
    message(&[field_string(1, name), field_message(2, &ty)])
}

fn tensor(name: &str, elem_type: u64, dims: &[i64], raw_data: &[u8]) -> Vec<u8> {
    let mut fields = dims
        .iter()
        .map(|dim| field_varint(1, *dim as u64))
        .collect::<Vec<_>>();
    fields.push(field_varint(2, elem_type));
    fields.push(field_string(8, name));
    fields.push(field_bytes(9, raw_data));
    message(&fields)
}

fn attribute_int(name: &str, value: i64) -> Vec<u8> {
    message(&[field_string(1, name), field_varint(3, value as u64)])
}

fn attribute_ints(name: &str, values: &[i64]) -> Vec<u8> {
    let mut packed = Vec::new();
    for value in values {
        push_varint(&mut packed, *value as u64);
    }
    message(&[field_string(1, name), field_bytes(8, &packed)])
}

fn f32_raw(values: &[f32]) -> Vec<u8> {
    values
        .iter()
        .flat_map(|value| value.to_le_bytes())
        .collect()
}

fn message(fields: &[Vec<u8>]) -> Vec<u8> {
    fields.iter().flatten().copied().collect()
}

fn field_string(number: u32, value: &str) -> Vec<u8> {
    field_bytes(number, value.as_bytes())
}

fn field_message(number: u32, value: &[u8]) -> Vec<u8> {
    field_bytes(number, value)
}

fn field_bytes(number: u32, value: &[u8]) -> Vec<u8> {
    let mut bytes = Vec::new();
    push_varint(&mut bytes, u64::from(number << 3 | 2));
    push_varint(&mut bytes, value.len() as u64);
    bytes.extend_from_slice(value);
    bytes
}

fn field_varint(number: u32, value: u64) -> Vec<u8> {
    let mut bytes = Vec::new();
    push_varint(&mut bytes, u64::from(number << 3));
    push_varint(&mut bytes, value);
    bytes
}

fn push_varint(bytes: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        bytes.push((value as u8) | 0x80);
        value >>= 7;
    }
    bytes.push(value as u8);
}
