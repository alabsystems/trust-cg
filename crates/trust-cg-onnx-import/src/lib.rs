// trust-cg-onnx-import / lib.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// MVP ONNX graph importer for the VNN tensor trust_ir JSON contract from #538.
// The JSON fixture path remains supported for focused tests, and raw `.onnx`
// files are decoded through the subset of ONNX ModelProto needed by the VNN MVP.

#![forbid(unsafe_code)]

use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::io::Read;
use std::path::Path;

pub type Result<T> = std::result::Result<T, Error>;

/// Maximum `.onnx` protobuf model bytes accepted from a filesystem path or API input.
pub const MAX_ONNX_MODEL_BYTES: u64 = 64 * 1024 * 1024;
/// Maximum JSON graph fixture bytes accepted from a filesystem path.
pub const MAX_ONNX_GRAPH_FIXTURE_BYTES: u64 = 16 * 1024 * 1024;
/// Maximum raw tensor payload bytes decoded from one ONNX TensorProto.
pub const MAX_ONNX_RAW_TENSOR_BYTES: usize = 16 * 1024 * 1024;
/// Maximum statically materialized tensor elements accepted by the importer.
pub const MAX_ONNX_TENSOR_ELEMENTS: usize = 4 * 1024 * 1024;
/// Maximum tensor rank accepted by the importer.
pub const MAX_ONNX_TENSOR_RANK: usize = 64;
/// Maximum graph nodes accepted by the VNN importer.
pub const MAX_ONNX_NODES: usize = 10_000;
/// Maximum graph initializers accepted by the VNN importer.
pub const MAX_ONNX_INITIALIZERS: usize = 10_000;
/// Maximum declared input/intermediate/output tensors accepted by the importer.
pub const MAX_ONNX_TENSORS: usize = 50_000;
/// Maximum individual protobuf string payload accepted by the importer.
pub const MAX_ONNX_STRING_BYTES: usize = 1024 * 1024;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("json error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("unsupported ONNX import: {0}")]
    Unsupported(String),
    #[error("invalid ONNX graph fixture: {0}")]
    Invalid(String),
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct GraphFixture {
    pub name: Option<String>,
    #[serde(default)]
    pub inputs: Vec<TensorFixture>,
    #[serde(default)]
    pub outputs: Vec<String>,
    #[serde(default)]
    pub tensors: Vec<TensorFixture>,
    #[serde(default)]
    pub initializers: Vec<InitializerFixture>,
    #[serde(default)]
    pub nodes: Vec<NodeFixture>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct TensorFixture {
    pub name: String,
    pub shape: Vec<i64>,
    pub dtype: DType,
    pub layout: Layout,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct InitializerFixture {
    pub name: String,
    pub shape: Vec<i64>,
    pub dtype: DType,
    pub layout: Layout,
    #[serde(default)]
    pub values: Vec<Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct NodeFixture {
    pub name: String,
    pub op_type: String,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    #[serde(default)]
    pub attributes: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum DType {
    F32,
    F16,
    I32,
    I64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Layout {
    Nchw,
    Nhwc,
    Nc,
    Nld,
    Oihw,
    Oi,
    Vector,
    Scalar,
    Strided,
}

#[derive(Debug, Clone, Serialize)]
pub struct VnnModule {
    pub version: u32,
    pub dialect: &'static str,
    pub entry: String,
    pub tensors: BTreeMap<String, VnnTensor>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub initializers: BTreeMap<String, VnnInitializer>,
    pub ops: Vec<VnnOp>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub edges: Vec<VnnEdge>,
}

#[derive(Debug, Clone, Serialize)]
pub struct VnnTensor {
    pub shape: Vec<usize>,
    pub dtype: DType,
    pub layout: Layout,
    pub role: TensorRole,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum TensorRole {
    Input,
    Activation,
    Output,
    Initializer,
}

#[derive(Debug, Clone, Serialize)]
pub struct VnnInitializer {
    pub shape: Vec<usize>,
    pub dtype: DType,
    pub layout: Layout,
    pub storage: InitializerStorage,
    pub sha256: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct InitializerStorage {
    pub kind: &'static str,
    pub name: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct VnnOp {
    pub id: String,
    pub op: String,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub weights: Vec<String>,
    pub attrs: BTreeMap<String, Value>,
    pub provenance: VnnProvenance,
}

#[derive(Debug, Clone, Serialize)]
pub struct VnnProvenance {
    pub gamma_layer_id: String,
    pub gamma_layer_type: String,
    pub onnx_node_name: String,
    pub onnx_op_type: String,
    pub onnx_outputs: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct VnnEdge {
    pub from: String,
    pub to: String,
    pub from_layer: String,
    pub to_layer: String,
    pub onnx_tensor: String,
}

#[derive(Debug, Clone, Default)]
pub struct AttentionFusionOptions {
    pub certified: bool,
    pub relaxation_policy: Option<String>,
    pub checker_obligation_schema: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct AttentionFusionReport {
    pub fusion: &'static str,
    pub eligible: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub candidates: Vec<AttentionFusionCandidate>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<AttentionFusionDiagnostic>,
}

#[derive(Debug, Clone, Serialize)]
pub struct AttentionFusionCandidate {
    pub source_ops: Vec<String>,
    pub batch: usize,
    pub sequence: usize,
    pub head_count: usize,
    pub head_dim: usize,
    pub hidden_dim: usize,
    pub scale: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub relaxation_policy: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub checker_obligation_schema: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct AttentionFusionDiagnostic {
    pub code: &'static str,
    pub phase: &'static str,
    pub fusion: &'static str,
    pub target: &'static str,
    pub reason: AttentionFusionUnsupportedReason,
    pub source_ops: Vec<String>,
    pub message: String,
    pub blocked_by: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AttentionFusionUnsupportedReason {
    DynamicShape,
    UnsupportedDtype,
    ShapeMismatch,
    MissingInitializer,
    MissingStaticShapeMetadata,
    MissingTransposeMetadata,
    UnsupportedAttentionMask,
    UnsupportedDropout,
    UnsupportedSoftmaxAxis,
    DataDependentIndexing,
    MissingRelaxationMetadata,
    PatternNotFound,
}

pub fn import_path(path: &Path) -> Result<VnnModule> {
    if path.extension().is_some_and(|ext| ext == "onnx") {
        let bytes = read_path_bounded(path, MAX_ONNX_MODEL_BYTES, "ONNX model")?;
        return import_onnx_model_proto_bytes(&bytes);
    }
    let text =
        read_path_to_string_bounded(path, MAX_ONNX_GRAPH_FIXTURE_BYTES, "ONNX graph fixture")?;
    import_graph_fixture_str(&text)
}

pub fn import_onnx_model_proto_bytes(bytes: &[u8]) -> Result<VnnModule> {
    if bytes.len() as u64 > MAX_ONNX_MODEL_BYTES {
        return Err(Error::Unsupported(format!(
            "ONNX model is {} byte(s), over importer limit {}",
            bytes.len(),
            MAX_ONNX_MODEL_BYTES
        )));
    }
    import_graph_fixture(parse_onnx_model_proto(bytes)?)
}

pub fn import_graph_fixture_str(text: &str) -> Result<VnnModule> {
    if text.len() as u64 > MAX_ONNX_GRAPH_FIXTURE_BYTES {
        return Err(Error::Unsupported(format!(
            "ONNX graph fixture is {} byte(s), over importer limit {}",
            text.len(),
            MAX_ONNX_GRAPH_FIXTURE_BYTES
        )));
    }
    import_graph_fixture(serde_json::from_str(text)?)
}

fn read_path_to_string_bounded(path: &Path, limit: u64, kind: &str) -> Result<String> {
    let bytes = read_path_bounded(path, limit, kind)?;
    String::from_utf8(bytes).map_err(|err| {
        Error::Invalid(format!(
            "{kind} '{}' is not valid UTF-8: {err}",
            path.display()
        ))
    })
}

fn read_path_bounded(path: &Path, limit: u64, kind: &str) -> Result<Vec<u8>> {
    let size = fs::metadata(path)?.len();
    if size > limit {
        return Err(Error::Unsupported(format!(
            "{kind} '{}' is {} byte(s), over importer limit {}",
            path.display(),
            size,
            limit
        )));
    }

    let file = fs::File::open(path)?;
    let mut bytes = Vec::with_capacity(size as usize);
    let mut bounded = file.take(limit + 1);
    bounded.read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limit {
        return Err(Error::Unsupported(format!(
            "{kind} '{}' grew over importer limit {} while reading",
            path.display(),
            limit
        )));
    }
    Ok(bytes)
}

pub fn attention_fusion_report_for_graph_fixture(
    graph: &GraphFixture,
    options: AttentionFusionOptions,
) -> AttentionFusionReport {
    let mut report = AttentionFusionReport::new();
    let preflight_diagnostics = attention_fixture_preflight_diagnostics(graph);
    if !preflight_diagnostics.is_empty() {
        report.diagnostics = preflight_diagnostics;
        return report;
    }

    match import_graph_fixture(graph.clone()) {
        Ok(module) => attention_fusion_report(&module, options),
        Err(err) => {
            report.diagnostics.push(attention_diag(
                AttentionFusionUnsupportedReason::PatternNotFound,
                Vec::new(),
                format!("attention fusion preflight could not import fixture: {err}"),
            ));
            report
        }
    }
}

pub fn attention_fusion_report(
    module: &VnnModule,
    options: AttentionFusionOptions,
) -> AttentionFusionReport {
    let mut report = AttentionFusionReport::new();
    let mut diagnostics = Vec::new();
    diagnostics.extend(attention_module_global_diagnostics(module));

    for context_matmul_index in module
        .ops
        .iter()
        .enumerate()
        .filter_map(|(index, op)| (op.op == "trust_ir.vnn.matmul").then_some(index))
    {
        match attention_candidate_from_context_matmul(module, context_matmul_index, &options) {
            Ok(candidate) => report.candidates.push(candidate),
            Err(mut candidate_diagnostics) => diagnostics.append(&mut candidate_diagnostics),
        }
    }

    if report.candidates.is_empty() && diagnostics.is_empty() {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::PatternNotFound,
            Vec::new(),
            "fixed inference Q/K/V, QK^T, scale, softmax, PV pattern was not found".to_string(),
        ));
    }

    report.diagnostics = dedupe_attention_diagnostics(diagnostics);
    report.eligible = !report.candidates.is_empty() && report.diagnostics.is_empty();
    if !report.eligible {
        report.candidates.clear();
    }
    report
}

fn validate_graph_limits(graph: &GraphFixture) -> Result<()> {
    ensure_count_limit("ONNX graph nodes", graph.nodes.len(), MAX_ONNX_NODES)?;
    ensure_count_limit(
        "ONNX graph initializers",
        graph.initializers.len(),
        MAX_ONNX_INITIALIZERS,
    )?;
    let tensor_count = graph
        .inputs
        .len()
        .checked_add(graph.tensors.len())
        .and_then(|count| count.checked_add(graph.outputs.len()))
        .ok_or_else(|| Error::Unsupported("ONNX graph tensor count overflows".to_string()))?;
    ensure_count_limit("ONNX graph tensors", tensor_count, MAX_ONNX_TENSORS)?;

    for tensor in graph.inputs.iter().chain(graph.tensors.iter()) {
        validate_shape_element_limit("tensor", &tensor.name, &tensor.shape)?;
    }
    for initializer in &graph.initializers {
        validate_shape_element_limit("initializer", &initializer.name, &initializer.shape)?;
        ensure_count_limit(
            "ONNX initializer values",
            initializer.values.len(),
            MAX_ONNX_TENSOR_ELEMENTS,
        )?;
    }

    Ok(())
}

fn ensure_count_limit(kind: &str, count: usize, limit: usize) -> Result<()> {
    if count > limit {
        return Err(Error::Unsupported(format!(
            "{kind} count {count} exceeds importer limit {limit}"
        )));
    }
    Ok(())
}

fn validate_shape_element_limit(kind: &str, name: &str, shape: &[i64]) -> Result<()> {
    let Some(elements) = static_shape_element_count(shape)? else {
        return Ok(());
    };
    if elements > MAX_ONNX_TENSOR_ELEMENTS {
        return Err(Error::Unsupported(format!(
            "ONNX {kind} '{name}' has {elements} element(s), over importer limit {}",
            MAX_ONNX_TENSOR_ELEMENTS
        )));
    }
    Ok(())
}

fn static_shape_element_count(shape: &[i64]) -> Result<Option<usize>> {
    if shape.iter().any(|dim| *dim <= 0) {
        return Ok(None);
    }
    let mut elements = 1usize;
    for dim in shape {
        let dim = usize::try_from(*dim)
            .map_err(|_| Error::Unsupported("ONNX tensor dimension overflows usize".to_string()))?;
        elements = elements
            .checked_mul(dim)
            .ok_or_else(|| Error::Unsupported("ONNX tensor element count overflows".to_string()))?;
    }
    Ok(Some(elements))
}

pub fn import_graph_fixture(graph: GraphFixture) -> Result<VnnModule> {
    validate_graph_limits(&graph)?;
    if graph.nodes.is_empty() {
        return Err(Error::Invalid("graph has no nodes".to_string()));
    }

    let output_names: std::collections::HashSet<&str> =
        graph.outputs.iter().map(String::as_str).collect();
    let mut tensors = BTreeMap::new();
    let mut known_specs: HashMap<String, TensorFixture> = HashMap::new();

    for input in &graph.inputs {
        let trust_ir_name = ssa_name(&input.name);
        tensors.insert(
            trust_ir_name,
            VnnTensor {
                shape: static_shape(&input.name, &input.shape)?,
                dtype: input.dtype,
                layout: input.layout,
                role: TensorRole::Input,
            },
        );
        known_specs.insert(input.name.clone(), input.clone());
    }

    for tensor in &graph.tensors {
        let role = if output_names.contains(tensor.name.as_str()) {
            TensorRole::Output
        } else {
            TensorRole::Activation
        };
        tensors.insert(
            ssa_name(&tensor.name),
            VnnTensor {
                shape: static_shape(&tensor.name, &tensor.shape)?,
                dtype: tensor.dtype,
                layout: tensor.layout,
                role,
            },
        );
        known_specs.insert(tensor.name.clone(), tensor.clone());
    }

    let mut initializers = BTreeMap::new();
    let mut initializer_names = std::collections::HashSet::new();
    let mut initializer_specs = HashMap::new();
    for initializer in &graph.initializers {
        initializer_names.insert(initializer.name.clone());
        initializer_specs.insert(initializer.name.clone(), initializer.clone());
        initializers.insert(
            initializer.name.clone(),
            VnnInitializer {
                shape: static_initializer_shape(&initializer.name, &initializer.shape)?,
                dtype: initializer.dtype,
                layout: initializer.layout,
                storage: InitializerStorage {
                    kind: "external",
                    name: initializer.name.clone(),
                },
                sha256: deterministic_initializer_sha(initializer)?,
            },
        );
    }

    let mut producer_by_tensor: HashMap<String, (String, String)> = HashMap::new();
    let mut ops = Vec::with_capacity(graph.nodes.len());
    let mut edges = Vec::new();

    for (idx, node) in graph.nodes.iter().enumerate() {
        validate_node(node)?;
        let id = format!("vnn.{idx}");
        let gamma_layer_id = format!("layer.{idx}");
        let op = map_op_type(&node.op_type, node, &initializer_names)?;
        let weights = collect_weights(node, &op.gamma_layer_type, &initializer_names)?;
        let outputs = node
            .outputs
            .iter()
            .map(|output| {
                if !known_specs.contains_key(output) {
                    return Err(Error::Invalid(format!(
                        "node '{}' output '{}' lacks tensor metadata",
                        node.name, output
                    )));
                }
                Ok(ssa_name(output))
            })
            .collect::<Result<Vec<_>>>()?;

        let data_inputs = node
            .inputs
            .iter()
            .map(|input| {
                if weights.contains(input) {
                    Ok(None)
                } else if known_specs.contains_key(input) {
                    Ok(Some(ssa_name(input)))
                } else if initializer_names.contains(input) {
                    Ok(Some(input.clone()))
                } else {
                    Err(Error::Invalid(format!(
                        "node '{}' input '{}' lacks tensor metadata",
                        node.name, input
                    )))
                }
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        for input in node
            .inputs
            .iter()
            .filter(|input| !initializer_names.contains(*input))
        {
            if let Some((from_layer, _from_node)) = producer_by_tensor.get(input) {
                edges.push(VnnEdge {
                    from: ssa_name(input),
                    to: id.clone(),
                    from_layer: from_layer.clone(),
                    to_layer: gamma_layer_id.clone(),
                    onnx_tensor: input.clone(),
                });
            }
        }

        let attrs = canonical_attrs(node, &op, &initializers, &initializer_specs, &known_specs)?;
        ops.push(VnnOp {
            id: id.clone(),
            op: op.trust_ir_op,
            inputs: data_inputs,
            outputs,
            weights,
            attrs,
            provenance: VnnProvenance {
                gamma_layer_id: gamma_layer_id.clone(),
                gamma_layer_type: op.gamma_layer_type,
                onnx_node_name: node.name.clone(),
                onnx_op_type: node.op_type.clone(),
                onnx_outputs: node.outputs.clone(),
            },
        });

        for output in &node.outputs {
            producer_by_tensor.insert(output.clone(), (gamma_layer_id.clone(), node.name.clone()));
        }
    }

    Ok(VnnModule {
        version: 1,
        dialect: "trust_ir.vnn",
        entry: graph.name.unwrap_or_else(|| "model".to_string()),
        tensors,
        initializers,
        ops,
        edges,
    })
}

struct OpMapping {
    trust_ir_op: String,
    gamma_layer_type: String,
}

fn map_op_type(
    op_type: &str,
    node: &NodeFixture,
    initializer_names: &std::collections::HashSet<String>,
) -> Result<OpMapping> {
    let (trust_ir_op, gamma_layer_type) = match op_type {
        "Conv" => ("trust_ir.vnn.conv2d", "Conv2d"),
        "BatchNormalization" => ("trust_ir.vnn.batch_norm", "BatchNorm"),
        "Relu" => ("trust_ir.vnn.relu", "ReLU"),
        "Add" => ("trust_ir.vnn.add", "Add"),
        "Mul" => {
            if node
                .inputs
                .iter()
                .any(|input| initializer_names.contains(input))
            {
                ("trust_ir.vnn.scale", "Scale")
            } else {
                return Err(Error::Unsupported(format!(
                    "Mul node '{}' without a constant scale input is not in the transformer importer subset",
                    node.name
                )));
            }
        }
        "AveragePool" | "GlobalAveragePool" => ("trust_ir.vnn.avg_pool2d", "AveragePool"),
        "MaxPool" => {
            if node.outputs.len() > 1 {
                return Err(Error::Unsupported(format!(
                    "MaxPool node '{}' has index output form",
                    node.name
                )));
            }
            ("trust_ir.vnn.max_pool2d", "MaxPool")
        }
        "Gemm" => ("trust_ir.vnn.linear", "Linear"),
        "MatMul" => {
            if node
                .inputs
                .iter()
                .any(|input| initializer_names.contains(input))
            {
                ("trust_ir.vnn.linear", "Linear")
            } else {
                ("trust_ir.vnn.matmul", "MatMul")
            }
        }
        "Softmax" => ("trust_ir.vnn.softmax", "Softmax"),
        "LayerNormalization" => ("trust_ir.vnn.layer_norm", "LayerNorm"),
        "Flatten" => ("trust_ir.vnn.flatten", "Flatten"),
        "Reshape" => ("trust_ir.vnn.reshape", "Reshape"),
        "Transpose" => ("trust_ir.vnn.transpose", "Transpose"),
        other => {
            return Err(Error::Unsupported(format!(
                "op '{}' on node '{}' is not in the ONNX VNN importer subset",
                other, node.name
            )));
        }
    };
    Ok(OpMapping {
        trust_ir_op: trust_ir_op.to_string(),
        gamma_layer_type: gamma_layer_type.to_string(),
    })
}

fn validate_node(node: &NodeFixture) -> Result<()> {
    if node.name.is_empty() {
        return Err(Error::Invalid("node missing ONNX node name".to_string()));
    }
    if node.op_type.is_empty() {
        return Err(Error::Invalid(format!(
            "node '{}' missing ONNX op type",
            node.name
        )));
    }
    if node.outputs.is_empty() {
        return Err(Error::Invalid(format!(
            "node '{}' has no outputs",
            node.name
        )));
    }
    Ok(())
}

fn collect_weights(
    node: &NodeFixture,
    gamma_layer_type: &str,
    initializer_names: &std::collections::HashSet<String>,
) -> Result<Vec<String>> {
    let required_indices: &[usize] = match gamma_layer_type {
        "Conv2d" | "Linear" | "Reshape" => &[1],
        "BatchNorm" => &[1, 2, 3, 4],
        "LayerNorm" => &[1],
        _ => &[],
    };
    let optional_indices: &[usize] = match gamma_layer_type {
        "Conv2d" | "Linear" => &[2],
        "LayerNorm" => &[2],
        "Scale" => &[0, 1],
        _ => &[],
    };
    let mut weights = Vec::new();
    for index in required_indices {
        let Some(input) = node.inputs.get(*index) else {
            return Err(Error::Invalid(format!(
                "{} node '{}' missing required initializer input {}",
                gamma_layer_type, node.name, index
            )));
        };
        if initializer_names.contains(input) {
            weights.push(input.clone());
        } else {
            return Err(Error::Invalid(format!(
                "{} node '{}' input '{}' must be an initializer",
                gamma_layer_type, node.name, input
            )));
        }
    }
    for index in optional_indices {
        let Some(input) = node.inputs.get(*index) else {
            continue;
        };
        if initializer_names.contains(input) {
            weights.push(input.clone());
        }
    }
    Ok(weights)
}

fn canonical_attrs(
    node: &NodeFixture,
    op: &OpMapping,
    initializers: &BTreeMap<String, VnnInitializer>,
    initializer_specs: &HashMap<String, InitializerFixture>,
    known_specs: &HashMap<String, TensorFixture>,
) -> Result<BTreeMap<String, Value>> {
    let mut attrs = node.attributes.clone();
    match op.gamma_layer_type.as_str() {
        "Conv2d" => {
            ensure_int_array_attr(&mut attrs, "strides", &[1, 1]);
            ensure_int_array_attr(&mut attrs, "pads", &[0, 0, 0, 0]);
            ensure_int_array_attr(&mut attrs, "dilations", &[1, 1]);
            ensure_int_attr(&mut attrs, "groups", 1);
            if !attrs.contains_key("kernel_shape") {
                let weight = node.inputs.get(1).ok_or_else(|| {
                    Error::Invalid(format!("Conv node '{}' missing weight", node.name))
                })?;
                let shape = &initializers
                    .get(weight)
                    .ok_or_else(|| {
                        Error::Invalid(format!(
                            "Conv node '{}' weight '{}' missing",
                            node.name, weight
                        ))
                    })?
                    .shape;
                if shape.len() != 4 {
                    return Err(Error::Invalid(format!(
                        "Conv node '{}' weight '{}' is not OIHW rank 4",
                        node.name, weight
                    )));
                }
                attrs.insert(
                    "kernel_shape".to_string(),
                    int_array_value(&[shape[2], shape[3]]),
                );
            }
        }
        "AveragePool" | "MaxPool" => {
            ensure_int_array_attr(&mut attrs, "strides", &[1, 1]);
            ensure_int_array_attr(&mut attrs, "pads", &[0, 0, 0, 0]);
            ensure_int_attr(&mut attrs, "ceil_mode", 0);
            if node.op_type == "GlobalAveragePool" {
                let input = node.inputs.first().ok_or_else(|| {
                    Error::Invalid(format!(
                        "GlobalAveragePool node '{}' missing input",
                        node.name
                    ))
                })?;
                let shape = &known_specs
                    .get(input)
                    .ok_or_else(|| {
                        Error::Invalid(format!(
                            "GlobalAveragePool node '{}' lacks input shape",
                            node.name
                        ))
                    })?
                    .shape;
                if shape.len() != 4 {
                    return Err(Error::Invalid(format!(
                        "GlobalAveragePool node '{}' requires NCHW rank 4 input",
                        node.name
                    )));
                }
                attrs.insert("global".to_string(), Value::Bool(true));
                attrs.insert(
                    "kernel_shape".to_string(),
                    int_array_value(&[shape[2] as usize, shape[3] as usize]),
                );
            }
            if !attrs.contains_key("kernel_shape") {
                return Err(Error::Invalid(format!(
                    "{} node '{}' missing static kernel_shape",
                    node.op_type, node.name
                )));
            }
        }
        "Add" => {
            attrs
                .entry("broadcast".to_string())
                .or_insert_with(|| Value::String("numpy".to_string()));
            attrs
                .entry("kind".to_string())
                .or_insert_with(|| Value::String(add_kind(node, initializers)));
        }
        "Linear" => {
            ensure_number_attr(&mut attrs, "alpha", 1.0);
            ensure_number_attr(&mut attrs, "beta", 1.0);
            ensure_int_attr(&mut attrs, "transA", 0);
            ensure_int_attr(&mut attrs, "transB", 0);
            if node.op_type == "MatMul" {
                attrs.insert("source_op".to_string(), Value::String("MatMul".to_string()));
            }
        }
        "MatMul" => {
            annotate_matmul_shape(node, &mut attrs, known_specs)?;
        }
        "Scale" => {
            annotate_scale(node, &mut attrs, initializer_specs)?;
        }
        "Softmax" => {
            ensure_int_attr(&mut attrs, "axis", -1);
        }
        "LayerNorm" => {
            ensure_number_attr(&mut attrs, "epsilon", 0.00001);
            ensure_int_attr(&mut attrs, "axis", -1);
        }
        "Flatten" => {
            ensure_int_attr(&mut attrs, "axis", 1);
        }
        "Reshape" => {
            let shape_input = node.inputs.get(1).ok_or_else(|| {
                Error::Invalid(format!("Reshape node '{}' missing shape input", node.name))
            })?;
            let initializer = initializers.get(shape_input).ok_or_else(|| {
                Error::Invalid(format!(
                    "Reshape node '{}' shape input '{}' is not an initializer",
                    node.name, shape_input
                ))
            })?;
            if initializer.dtype != DType::I64 {
                return Err(Error::Invalid(format!(
                    "Reshape node '{}' shape input '{}' must be i64",
                    node.name, shape_input
                )));
            }
            ensure_int_attr(&mut attrs, "allowzero", 0);
            attrs
                .entry("target_shape".to_string())
                .or_insert_with(|| initializer_i64_array_value(initializer_specs, shape_input));
        }
        "Transpose" if !attrs.contains_key("perm") => {
            return Err(Error::Invalid(format!(
                "Transpose node '{}' missing static perm",
                node.name
            )));
        }
        "Transpose" => {}
        _ => {}
    }
    Ok(attrs)
}

fn add_kind(node: &NodeFixture, initializers: &BTreeMap<String, VnnInitializer>) -> String {
    if node
        .inputs
        .iter()
        .any(|input| initializers.contains_key(input))
    {
        "bias".to_string()
    } else {
        "residual".to_string()
    }
}

fn annotate_matmul_shape(
    node: &NodeFixture,
    attrs: &mut BTreeMap<String, Value>,
    known_specs: &HashMap<String, TensorFixture>,
) -> Result<()> {
    let lhs = node
        .inputs
        .first()
        .ok_or_else(|| Error::Invalid(format!("MatMul node '{}' missing lhs input", node.name)))?;
    let rhs = node
        .inputs
        .get(1)
        .ok_or_else(|| Error::Invalid(format!("MatMul node '{}' missing rhs input", node.name)))?;
    let lhs_shape = &known_specs
        .get(lhs)
        .ok_or_else(|| {
            Error::Invalid(format!(
                "MatMul node '{}' lhs input '{}' lacks tensor metadata",
                node.name, lhs
            ))
        })?
        .shape;
    let rhs_shape = &known_specs
        .get(rhs)
        .ok_or_else(|| {
            Error::Invalid(format!(
                "MatMul node '{}' rhs input '{}' lacks tensor metadata",
                node.name, rhs
            ))
        })?
        .shape;
    let (m, k) = matrix_tail(lhs_shape).ok_or_else(|| {
        Error::Unsupported(format!(
            "MatMul node '{}' lhs input '{}' rank {} is not in the static transformer subset",
            node.name,
            lhs,
            lhs_shape.len()
        ))
    })?;
    let (rhs_k, n) = matrix_tail(rhs_shape).ok_or_else(|| {
        Error::Unsupported(format!(
            "MatMul node '{}' rhs input '{}' rank {} is not in the static transformer subset",
            node.name,
            rhs,
            rhs_shape.len()
        ))
    })?;
    if k != rhs_k {
        return Err(Error::Invalid(format!(
            "MatMul node '{}' has incompatible K dimensions: {} vs {}",
            node.name, k, rhs_k
        )));
    }
    attrs
        .entry("m".to_string())
        .or_insert_with(|| Value::from(m));
    attrs
        .entry("k".to_string())
        .or_insert_with(|| Value::from(k));
    attrs
        .entry("n".to_string())
        .or_insert_with(|| Value::from(n));
    attrs
        .entry("source_op".to_string())
        .or_insert_with(|| Value::String("MatMul".to_string()));
    Ok(())
}

fn matrix_tail(shape: &[i64]) -> Option<(i64, i64)> {
    if shape.len() < 2 {
        None
    } else {
        Some((shape[shape.len() - 2], shape[shape.len() - 1]))
    }
}

fn annotate_scale(
    node: &NodeFixture,
    attrs: &mut BTreeMap<String, Value>,
    initializer_specs: &HashMap<String, InitializerFixture>,
) -> Result<()> {
    let scale_input = node
        .inputs
        .iter()
        .find(|input| initializer_specs.contains_key(*input))
        .ok_or_else(|| {
            Error::Unsupported(format!(
                "Mul node '{}' missing constant scale initializer",
                node.name
            ))
        })?;
    attrs
        .entry("scale_initializer".to_string())
        .or_insert_with(|| Value::String(scale_input.clone()));
    let initializer = initializer_specs.get(scale_input).expect("checked above");
    if initializer.shape.len() > 1 {
        return Err(Error::Unsupported(format!(
            "Mul node '{}' scale initializer '{}' must be scalar or vector, got rank {}",
            node.name,
            scale_input,
            initializer.shape.len()
        )));
    }
    if let Some(value) = initializer.values.first() {
        attrs
            .entry("scale_value".to_string())
            .or_insert_with(|| value.clone());
    }
    Ok(())
}

fn initializer_i64_array_value(
    initializer_specs: &HashMap<String, InitializerFixture>,
    name: &str,
) -> Value {
    initializer_specs.get(name).map_or_else(
        || Value::String(name.to_string()),
        |initializer| Value::Array(initializer.values.clone()),
    )
}

fn parse_onnx_model_proto(bytes: &[u8]) -> Result<GraphFixture> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut graph = None;
    while let Some(field) = cursor.next_field()? {
        match field.number {
            7 => graph = Some(parse_onnx_graph_proto(field.length_delimited()?)?),
            _ => field.skip()?,
        }
    }
    graph.ok_or_else(|| Error::Invalid("ONNX ModelProto missing graph field".to_string()))
}

fn parse_onnx_graph_proto(bytes: &[u8]) -> Result<GraphFixture> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut name = None;
    let mut nodes = Vec::new();
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    let mut value_info = Vec::new();
    let mut initializers = Vec::new();

    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => {
                nodes.push(parse_onnx_node_proto(field.length_delimited()?)?);
                ensure_count_limit("ONNX graph nodes", nodes.len(), MAX_ONNX_NODES)?;
            }
            2 => name = Some(proto_string(field.length_delimited()?)?),
            5 => {
                initializers.push(parse_onnx_tensor_proto(field.length_delimited()?)?);
                ensure_count_limit(
                    "ONNX graph initializers",
                    initializers.len(),
                    MAX_ONNX_INITIALIZERS,
                )?;
            }
            11 => {
                inputs.push(parse_onnx_value_info_proto(
                    field.length_delimited()?,
                    TensorRole::Input,
                )?);
                ensure_count_limit("ONNX graph inputs", inputs.len(), MAX_ONNX_TENSORS)?;
            }
            12 => {
                outputs.push(parse_onnx_value_info_proto(
                    field.length_delimited()?,
                    TensorRole::Output,
                )?);
                ensure_count_limit("ONNX graph outputs", outputs.len(), MAX_ONNX_TENSORS)?;
            }
            13 => {
                value_info.push(parse_onnx_value_info_proto(
                    field.length_delimited()?,
                    TensorRole::Activation,
                )?);
                ensure_count_limit("ONNX graph value_info", value_info.len(), MAX_ONNX_TENSORS)?;
            }
            _ => field.skip()?,
        }
    }

    let initializer_names = initializers
        .iter()
        .map(|initializer| initializer.name.as_str())
        .collect::<std::collections::HashSet<_>>();
    inputs.retain(|input| !initializer_names.contains(input.name.as_str()));

    let output_names = outputs
        .iter()
        .map(|output| output.name.clone())
        .collect::<Vec<_>>();
    let mut tensors_by_name = BTreeMap::new();
    for tensor in value_info {
        tensors_by_name.entry(tensor.name.clone()).or_insert(tensor);
    }
    for tensor in outputs {
        tensors_by_name.insert(tensor.name.clone(), tensor);
    }
    materialize_missing_raw_tensor_metadata(&nodes, &inputs, &mut tensors_by_name, &initializers)?;

    Ok(GraphFixture {
        name,
        inputs,
        outputs: output_names,
        tensors: tensors_by_name.into_values().collect(),
        initializers,
        nodes,
    })
}

fn materialize_missing_raw_tensor_metadata(
    nodes: &[NodeFixture],
    inputs: &[TensorFixture],
    tensors_by_name: &mut BTreeMap<String, TensorFixture>,
    initializers: &[InitializerFixture],
) -> Result<()> {
    let mut known_specs = HashMap::new();
    for input in inputs {
        known_specs.insert(input.name.clone(), input.clone());
    }
    for tensor in tensors_by_name.values() {
        known_specs.insert(tensor.name.clone(), tensor.clone());
    }
    let initializer_specs = initializers
        .iter()
        .map(|initializer| (initializer.name.as_str(), initializer))
        .collect::<HashMap<_, _>>();

    for node in nodes {
        if node
            .outputs
            .iter()
            .all(|output| known_specs.contains_key(output))
        {
            continue;
        }

        let inferred_outputs =
            infer_raw_node_output_metadata(node, &known_specs, &initializer_specs)?;
        if inferred_outputs.len() != node.outputs.len() {
            return Err(Error::Invalid(format!(
                "{} node '{}' shape inference produced {} outputs for {} ONNX outputs",
                node.op_type,
                node.name,
                inferred_outputs.len(),
                node.outputs.len()
            )));
        }

        for tensor in inferred_outputs {
            if known_specs.contains_key(&tensor.name) {
                continue;
            }
            tensors_by_name.insert(tensor.name.clone(), tensor.clone());
            known_specs.insert(tensor.name.clone(), tensor);
        }
    }

    Ok(())
}

fn infer_raw_node_output_metadata(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<Vec<TensorFixture>> {
    match node.op_type.as_str() {
        "Conv" => Ok(vec![infer_conv_output_spec(
            node,
            known_specs,
            initializer_specs,
        )?]),
        "BatchNormalization" | "Relu" | "Softmax" | "LayerNormalization" => {
            let input = required_tensor_spec(node, 0, known_specs, initializer_specs)?;
            Ok(node
                .outputs
                .iter()
                .map(|output| tensor_like(output, &input))
                .collect())
        }
        "Add" | "Mul" => Ok(vec![infer_elementwise_output_spec(
            node,
            known_specs,
            initializer_specs,
        )?]),
        "AveragePool" | "GlobalAveragePool" | "MaxPool" => Ok(vec![infer_pool_output_spec(
            node,
            known_specs,
            initializer_specs,
        )?]),
        "Gemm" => Ok(vec![infer_gemm_output_spec(
            node,
            known_specs,
            initializer_specs,
        )?]),
        "MatMul" => Ok(vec![infer_matmul_output_spec(
            node,
            known_specs,
            initializer_specs,
        )?]),
        "Flatten" => Ok(vec![infer_flatten_output_spec(
            node,
            known_specs,
            initializer_specs,
        )?]),
        "Reshape" => Ok(vec![infer_reshape_output_spec(
            node,
            known_specs,
            initializer_specs,
        )?]),
        "Transpose" => Ok(vec![infer_transpose_output_spec(
            node,
            known_specs,
            initializer_specs,
        )?]),
        other => Err(Error::Unsupported(format!(
            "raw ONNX node '{}' op '{}' has outputs without tensor metadata, and shape inference for that op is not in the VNN MVP subset",
            node.name, other
        ))),
    }
}

fn infer_conv_output_spec(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    ensure_single_output(node)?;
    let input = required_tensor_spec(node, 0, known_specs, initializer_specs)?;
    let weight = required_tensor_spec(node, 1, known_specs, initializer_specs)?;
    require_rank(node, &input, 4)?;
    require_rank(node, &weight, 4)?;

    let kernel_shape = int_array_attr(node, "kernel_shape", &weight.shape[2..4])?;
    let strides = int_array_attr(node, "strides", &[1, 1])?;
    let pads = int_array_attr(node, "pads", &[0, 0, 0, 0])?;
    let dilations = int_array_attr(node, "dilations", &[1, 1])?;
    let groups = int_attr(node, "groups", 1)?;
    require_len(node, "kernel_shape", &kernel_shape, 2)?;
    require_len(node, "strides", &strides, 2)?;
    require_len(node, "pads", &pads, 4)?;
    require_len(node, "dilations", &dilations, 2)?;
    if groups <= 0 {
        return Err(Error::Invalid(format!(
            "Conv node '{}' has non-positive groups {groups}",
            node.name
        )));
    }
    if input.shape[1] != weight.shape[1] * groups {
        return Err(Error::Invalid(format!(
            "Conv node '{}' has input channels {} but weight channels {} x groups {}",
            node.name, input.shape[1], weight.shape[1], groups
        )));
    }

    let shape = vec![
        input.shape[0],
        weight.shape[0],
        spatial_output_dim(
            node,
            "height",
            input.shape[2],
            kernel_shape[0],
            strides[0],
            pads[0],
            pads[2],
            dilations[0],
            false,
        )?,
        spatial_output_dim(
            node,
            "width",
            input.shape[3],
            kernel_shape[1],
            strides[1],
            pads[1],
            pads[3],
            dilations[1],
            false,
        )?,
    ];
    Ok(TensorFixture {
        name: node.outputs[0].clone(),
        shape,
        dtype: input.dtype,
        layout: Layout::Nchw,
    })
}

fn infer_pool_output_spec(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    ensure_single_output(node)?;
    let input = required_tensor_spec(node, 0, known_specs, initializer_specs)?;
    require_rank(node, &input, 4)?;
    if node.op_type == "GlobalAveragePool" {
        return Ok(TensorFixture {
            name: node.outputs[0].clone(),
            shape: vec![input.shape[0], input.shape[1], 1, 1],
            dtype: input.dtype,
            layout: input.layout,
        });
    }

    let kernel_shape = required_int_array_attr(node, "kernel_shape")?;
    let strides = int_array_attr(node, "strides", &[1, 1])?;
    let pads = int_array_attr(node, "pads", &[0, 0, 0, 0])?;
    let dilations = int_array_attr(node, "dilations", &[1, 1])?;
    let ceil_mode = int_attr(node, "ceil_mode", 0)?;
    require_len(node, "kernel_shape", &kernel_shape, 2)?;
    require_len(node, "strides", &strides, 2)?;
    require_len(node, "pads", &pads, 4)?;
    require_len(node, "dilations", &dilations, 2)?;

    let shape = vec![
        input.shape[0],
        input.shape[1],
        spatial_output_dim(
            node,
            "height",
            input.shape[2],
            kernel_shape[0],
            strides[0],
            pads[0],
            pads[2],
            dilations[0],
            ceil_mode != 0,
        )?,
        spatial_output_dim(
            node,
            "width",
            input.shape[3],
            kernel_shape[1],
            strides[1],
            pads[1],
            pads[3],
            dilations[1],
            ceil_mode != 0,
        )?,
    ];
    Ok(TensorFixture {
        name: node.outputs[0].clone(),
        shape,
        dtype: input.dtype,
        layout: input.layout,
    })
}

fn infer_elementwise_output_spec(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    ensure_single_output(node)?;
    let specs = node
        .inputs
        .iter()
        .filter_map(|input| lookup_tensor_spec(input, known_specs, initializer_specs))
        .collect::<Vec<_>>();
    if specs.is_empty() {
        return Err(Error::Invalid(format!(
            "{} node '{}' has no statically-shaped inputs",
            node.op_type, node.name
        )));
    }
    let shape = broadcast_shapes(
        node,
        &specs
            .iter()
            .map(|spec| spec.shape.as_slice())
            .collect::<Vec<_>>(),
    )?;
    let dtype = specs[0].dtype;
    let layout = specs
        .iter()
        .find(|spec| spec.shape == shape)
        .map_or_else(|| infer_layout(&shape, false), |spec| spec.layout);
    Ok(TensorFixture {
        name: node.outputs[0].clone(),
        shape,
        dtype,
        layout,
    })
}

fn infer_gemm_output_spec(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    ensure_single_output(node)?;
    let a = required_tensor_spec(node, 0, known_specs, initializer_specs)?;
    let b = required_tensor_spec(node, 1, known_specs, initializer_specs)?;
    require_rank(node, &a, 2)?;
    require_rank(node, &b, 2)?;
    let trans_a = int_attr(node, "transA", 0)? != 0;
    let trans_b = int_attr(node, "transB", 0)? != 0;
    let (m, k) = if trans_a {
        (a.shape[1], a.shape[0])
    } else {
        (a.shape[0], a.shape[1])
    };
    let (rhs_k, n) = if trans_b {
        (b.shape[1], b.shape[0])
    } else {
        (b.shape[0], b.shape[1])
    };
    if k != rhs_k {
        return Err(Error::Invalid(format!(
            "Gemm node '{}' has incompatible K dimensions: {} vs {}",
            node.name, k, rhs_k
        )));
    }
    Ok(TensorFixture {
        name: node.outputs[0].clone(),
        shape: vec![m, n],
        dtype: a.dtype,
        layout: Layout::Nc,
    })
}

fn infer_matmul_output_spec(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    ensure_single_output(node)?;
    let lhs = required_tensor_spec(node, 0, known_specs, initializer_specs)?;
    let rhs = required_tensor_spec(node, 1, known_specs, initializer_specs)?;
    if lhs.shape.len() < 2 || rhs.shape.len() < 2 {
        return Err(Error::Unsupported(format!(
            "MatMul node '{}' rank-1 broadcasting is outside the raw shape inference MVP",
            node.name
        )));
    }
    let (m, k) = matrix_tail(&lhs.shape).expect("rank checked");
    let (rhs_k, n) = matrix_tail(&rhs.shape).expect("rank checked");
    if k != rhs_k {
        return Err(Error::Invalid(format!(
            "MatMul node '{}' has incompatible K dimensions: {} vs {}",
            node.name, k, rhs_k
        )));
    }
    let mut shape = broadcast_prefix_shapes(
        node,
        &lhs.shape[..lhs.shape.len() - 2],
        &rhs.shape[..rhs.shape.len() - 2],
    )?;
    shape.push(m);
    shape.push(n);
    Ok(TensorFixture {
        name: node.outputs[0].clone(),
        layout: infer_layout(&shape, false),
        shape,
        dtype: lhs.dtype,
    })
}

fn infer_flatten_output_spec(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    ensure_single_output(node)?;
    let input = required_tensor_spec(node, 0, known_specs, initializer_specs)?;
    let axis = normalize_axis(node, int_attr(node, "axis", 1)?, input.shape.len(), true)?;
    let outer = checked_shape_product(node, &input.shape[..axis])?;
    let inner = checked_shape_product(node, &input.shape[axis..])?;
    Ok(TensorFixture {
        name: node.outputs[0].clone(),
        shape: vec![outer, inner],
        dtype: input.dtype,
        layout: Layout::Nc,
    })
}

fn infer_reshape_output_spec(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    ensure_single_output(node)?;
    let input = required_tensor_spec(node, 0, known_specs, initializer_specs)?;
    let shape_input = node.inputs.get(1).ok_or_else(|| {
        Error::Invalid(format!("Reshape node '{}' missing shape input", node.name))
    })?;
    let shape_initializer = initializer_specs.get(shape_input.as_str()).ok_or_else(|| {
        Error::Invalid(format!(
            "Reshape node '{}' shape input '{}' is not an initializer",
            node.name, shape_input
        ))
    })?;
    if shape_initializer.dtype != DType::I64 {
        return Err(Error::Invalid(format!(
            "Reshape node '{}' shape input '{}' must be i64",
            node.name, shape_input
        )));
    }
    let target = initializer_i64_values(shape_initializer)?;
    let allowzero = int_attr(node, "allowzero", 0)? != 0;
    let shape = reshape_target_shape(node, &input.shape, &target, allowzero)?;
    Ok(TensorFixture {
        name: node.outputs[0].clone(),
        layout: infer_layout(&shape, false),
        shape,
        dtype: input.dtype,
    })
}

fn infer_transpose_output_spec(
    node: &NodeFixture,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    ensure_single_output(node)?;
    let input = required_tensor_spec(node, 0, known_specs, initializer_specs)?;
    let perm = required_int_array_attr(node, "perm")?;
    require_len(node, "perm", &perm, input.shape.len())?;
    let mut seen = HashSet::new();
    let mut shape = Vec::with_capacity(input.shape.len());
    for dim in perm {
        let index = usize::try_from(dim).map_err(|_| {
            Error::Invalid(format!(
                "Transpose node '{}' has negative perm dimension {dim}",
                node.name
            ))
        })?;
        if index >= input.shape.len() || !seen.insert(index) {
            return Err(Error::Invalid(format!(
                "Transpose node '{}' has invalid perm dimension {dim}",
                node.name
            )));
        }
        shape.push(input.shape[index]);
    }
    Ok(TensorFixture {
        name: node.outputs[0].clone(),
        layout: infer_layout(&shape, false),
        shape,
        dtype: input.dtype,
    })
}

fn required_tensor_spec(
    node: &NodeFixture,
    input_index: usize,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Result<TensorFixture> {
    let input = node.inputs.get(input_index).ok_or_else(|| {
        Error::Invalid(format!(
            "{} node '{}' missing input {}",
            node.op_type, node.name, input_index
        ))
    })?;
    lookup_tensor_spec(input, known_specs, initializer_specs).ok_or_else(|| {
        Error::Invalid(format!(
            "{} node '{}' input '{}' lacks tensor metadata for raw ONNX shape inference",
            node.op_type, node.name, input
        ))
    })
}

fn lookup_tensor_spec(
    name: &str,
    known_specs: &HashMap<String, TensorFixture>,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> Option<TensorFixture> {
    known_specs.get(name).cloned().or_else(|| {
        initializer_specs
            .get(name)
            .map(|initializer| TensorFixture {
                name: initializer.name.clone(),
                shape: initializer.shape.clone(),
                dtype: initializer.dtype,
                layout: initializer.layout,
            })
    })
}

fn tensor_like(name: &str, input: &TensorFixture) -> TensorFixture {
    TensorFixture {
        name: name.to_string(),
        shape: input.shape.clone(),
        dtype: input.dtype,
        layout: input.layout,
    }
}

fn ensure_single_output(node: &NodeFixture) -> Result<()> {
    if node.outputs.len() != 1 {
        return Err(Error::Unsupported(format!(
            "{} node '{}' has {} outputs; raw shape inference supports one output",
            node.op_type,
            node.name,
            node.outputs.len()
        )));
    }
    Ok(())
}

fn require_rank(node: &NodeFixture, tensor: &TensorFixture, rank: usize) -> Result<()> {
    if tensor.shape.len() != rank {
        return Err(Error::Invalid(format!(
            "{} node '{}' tensor '{}' requires rank {}, got {}",
            node.op_type,
            node.name,
            tensor.name,
            rank,
            tensor.shape.len()
        )));
    }
    Ok(())
}

fn require_len(node: &NodeFixture, attr: &str, values: &[i64], expected: usize) -> Result<()> {
    if values.len() != expected {
        return Err(Error::Invalid(format!(
            "{} node '{}' attribute '{}' requires {} values, got {}",
            node.op_type,
            node.name,
            attr,
            expected,
            values.len()
        )));
    }
    Ok(())
}

fn int_attr(node: &NodeFixture, name: &str, default: i64) -> Result<i64> {
    match node.attributes.get(name) {
        Some(value) => value.as_i64().ok_or_else(|| {
            Error::Invalid(format!(
                "{} node '{}' attribute '{}' must be an integer",
                node.op_type, node.name, name
            ))
        }),
        None => Ok(default),
    }
}

fn required_int_array_attr(node: &NodeFixture, name: &str) -> Result<Vec<i64>> {
    let value = node.attributes.get(name).ok_or_else(|| {
        Error::Invalid(format!(
            "{} node '{}' missing static '{}' attribute for raw shape inference",
            node.op_type, node.name, name
        ))
    })?;
    value_to_i64_array(node, name, value)
}

fn int_array_attr(node: &NodeFixture, name: &str, default: &[i64]) -> Result<Vec<i64>> {
    match node.attributes.get(name) {
        Some(value) => value_to_i64_array(node, name, value),
        None => Ok(default.to_vec()),
    }
}

fn value_to_i64_array(node: &NodeFixture, name: &str, value: &Value) -> Result<Vec<i64>> {
    let array = value.as_array().ok_or_else(|| {
        Error::Invalid(format!(
            "{} node '{}' attribute '{}' must be an integer array",
            node.op_type, node.name, name
        ))
    })?;
    array
        .iter()
        .map(|value| {
            value.as_i64().ok_or_else(|| {
                Error::Invalid(format!(
                    "{} node '{}' attribute '{}' must contain only integers",
                    node.op_type, node.name, name
                ))
            })
        })
        .collect()
}

#[allow(clippy::too_many_arguments)] // Mirrors the ONNX spatial-axis parameter tuple.
fn spatial_output_dim(
    node: &NodeFixture,
    axis: &str,
    input: i64,
    kernel: i64,
    stride: i64,
    pad_begin: i64,
    pad_end: i64,
    dilation: i64,
    ceil_mode: bool,
) -> Result<i64> {
    for (name, value) in [
        ("input", input),
        ("kernel", kernel),
        ("stride", stride),
        ("pad_begin", pad_begin),
        ("pad_end", pad_end),
        ("dilation", dilation),
    ] {
        if value <= 0 && !name.starts_with("pad") {
            return Err(Error::Invalid(format!(
                "{} node '{}' has non-positive {axis} {name} {value}",
                node.op_type, node.name
            )));
        }
        if value < 0 {
            return Err(Error::Invalid(format!(
                "{} node '{}' has negative {axis} {name} {value}",
                node.op_type, node.name
            )));
        }
    }
    let effective_kernel = dilation
        .checked_mul(kernel - 1)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| {
            Error::Invalid(format!(
                "{} node '{}' {axis} effective kernel overflows",
                node.op_type, node.name
            ))
        })?;
    let numerator = input
        .checked_add(pad_begin)
        .and_then(|value| value.checked_add(pad_end))
        .and_then(|value| value.checked_sub(effective_kernel))
        .ok_or_else(|| {
            Error::Invalid(format!(
                "{} node '{}' {axis} output dimension overflows",
                node.op_type, node.name
            ))
        })?;
    if numerator < 0 {
        return Err(Error::Invalid(format!(
            "{} node '{}' {axis} output dimension is non-positive",
            node.op_type, node.name
        )));
    }
    let quotient = if ceil_mode {
        (numerator + stride - 1) / stride
    } else {
        numerator / stride
    };
    Ok(quotient + 1)
}

fn broadcast_shapes(node: &NodeFixture, shapes: &[&[i64]]) -> Result<Vec<i64>> {
    let mut result = Vec::new();
    for shape in shapes {
        result = broadcast_prefix_shapes(node, &result, shape)?;
    }
    Ok(result)
}

fn broadcast_prefix_shapes(node: &NodeFixture, lhs: &[i64], rhs: &[i64]) -> Result<Vec<i64>> {
    let len = lhs.len().max(rhs.len());
    let mut result = Vec::with_capacity(len);
    for index in 0..len {
        let lhs_dim = lhs
            .get(lhs.len().wrapping_sub(1 + index))
            .copied()
            .unwrap_or(1);
        let rhs_dim = rhs
            .get(rhs.len().wrapping_sub(1 + index))
            .copied()
            .unwrap_or(1);
        let dim = match (lhs_dim, rhs_dim) {
            (lhs_dim, rhs_dim) if lhs_dim <= 0 || rhs_dim <= 0 => {
                return Err(Error::Invalid(format!(
                    "{} node '{}' cannot broadcast dynamic/unknown dimensions {} and {}",
                    node.op_type, node.name, lhs_dim, rhs_dim
                )));
            }
            (1, rhs_dim) => rhs_dim,
            (lhs_dim, 1) => lhs_dim,
            (lhs_dim, rhs_dim) if lhs_dim == rhs_dim => lhs_dim,
            _ => {
                return Err(Error::Invalid(format!(
                    "{} node '{}' cannot broadcast shapes {:?} and {:?}",
                    node.op_type, node.name, lhs, rhs
                )));
            }
        };
        result.push(dim);
    }
    result.reverse();
    Ok(result)
}

fn normalize_axis(node: &NodeFixture, axis: i64, rank: usize, allow_end: bool) -> Result<usize> {
    let rank = rank as i64;
    let normalized = if axis < 0 { axis + rank } else { axis };
    let upper = if allow_end { rank } else { rank - 1 };
    if normalized < 0 || normalized > upper {
        return Err(Error::Invalid(format!(
            "{} node '{}' axis {} is out of bounds for rank {}",
            node.op_type, node.name, axis, rank
        )));
    }
    Ok(normalized as usize)
}

fn checked_shape_product(node: &NodeFixture, dims: &[i64]) -> Result<i64> {
    dims.iter().try_fold(1i64, |product, dim| {
        if *dim <= 0 {
            return Err(Error::Invalid(format!(
                "{} node '{}' cannot infer shape from dynamic/unknown dimension {}",
                node.op_type, node.name, dim
            )));
        }
        product.checked_mul(*dim).ok_or_else(|| {
            Error::Invalid(format!(
                "{} node '{}' shape product overflows",
                node.op_type, node.name
            ))
        })
    })
}

fn initializer_i64_values(initializer: &InitializerFixture) -> Result<Vec<i64>> {
    initializer
        .values
        .iter()
        .map(|value| {
            value.as_i64().ok_or_else(|| {
                Error::Invalid(format!(
                    "Reshape shape initializer '{}' must contain i64 values",
                    initializer.name
                ))
            })
        })
        .collect()
}

fn reshape_target_shape(
    node: &NodeFixture,
    input_shape: &[i64],
    target: &[i64],
    allowzero: bool,
) -> Result<Vec<i64>> {
    if target.is_empty() {
        return Err(Error::Invalid(format!(
            "Reshape node '{}' has empty target shape initializer",
            node.name
        )));
    }

    let input_elements = checked_shape_product(node, input_shape)?;
    let mut output = Vec::with_capacity(target.len());
    let mut known_elements = 1i64;
    let mut infer_index = None;
    for (index, dim) in target.iter().copied().enumerate() {
        let output_dim = match dim {
            dim if dim > 0 => dim,
            0 if !allowzero => *input_shape.get(index).ok_or_else(|| {
                Error::Invalid(format!(
                    "Reshape node '{}' target dim 0 at index {} has no input dim to copy",
                    node.name, index
                ))
            })?,
            0 => {
                return Err(Error::Unsupported(format!(
                    "Reshape node '{}' allowzero=1 is outside the static VNN shape subset",
                    node.name
                )));
            }
            -1 => {
                if infer_index.replace(index).is_some() {
                    return Err(Error::Invalid(format!(
                        "Reshape node '{}' has more than one inferred dimension",
                        node.name
                    )));
                }
                output.push(-1);
                continue;
            }
            _ => {
                return Err(Error::Invalid(format!(
                    "Reshape node '{}' has invalid target dimension {}",
                    node.name, dim
                )));
            }
        };
        known_elements = known_elements.checked_mul(output_dim).ok_or_else(|| {
            Error::Invalid(format!(
                "Reshape node '{}' target shape product overflows",
                node.name
            ))
        })?;
        output.push(output_dim);
    }

    if let Some(index) = infer_index {
        if known_elements <= 0 || input_elements % known_elements != 0 {
            return Err(Error::Invalid(format!(
                "Reshape node '{}' cannot infer target dimension from input elements {} and known product {}",
                node.name, input_elements, known_elements
            )));
        }
        output[index] = input_elements / known_elements;
    }

    let output_elements = checked_shape_product(node, &output)?;
    if output_elements != input_elements {
        return Err(Error::Invalid(format!(
            "Reshape node '{}' changes element count from {} to {}",
            node.name, input_elements, output_elements
        )));
    }
    Ok(output)
}

fn parse_onnx_node_proto(bytes: &[u8]) -> Result<NodeFixture> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut name = String::new();
    let mut op_type = String::new();
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    let mut attributes = BTreeMap::new();

    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => inputs.push(proto_string(field.length_delimited()?)?),
            2 => outputs.push(proto_string(field.length_delimited()?)?),
            3 => name = proto_string(field.length_delimited()?)?,
            4 => op_type = proto_string(field.length_delimited()?)?,
            5 => {
                let (attr_name, attr_value) =
                    parse_onnx_attribute_proto(field.length_delimited()?)?;
                attributes.insert(attr_name, attr_value);
            }
            _ => field.skip()?,
        }
    }

    if name.is_empty() && !op_type.is_empty() {
        name = format!("{op_type}_unnamed");
    }

    Ok(NodeFixture {
        name,
        op_type,
        inputs,
        outputs,
        attributes,
    })
}

fn parse_onnx_attribute_proto(bytes: &[u8]) -> Result<(String, Value)> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut name = None;
    let mut float_value = None;
    let mut int_value = None;
    let mut string_value = None;
    let mut floats = Vec::new();
    let mut ints = Vec::new();

    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => name = Some(proto_string(field.length_delimited()?)?),
            2 => float_value = Some(field.fixed32()?),
            3 => int_value = Some(field.varint()? as i64),
            4 => string_value = Some(proto_string(field.length_delimited()?)?),
            7 => floats.extend(field.repeated_f32()?),
            8 => ints.extend(field.repeated_i64()?),
            _ => field.skip()?,
        }
    }

    let name =
        name.ok_or_else(|| Error::Invalid("ONNX AttributeProto missing name".to_string()))?;
    let value = if !ints.is_empty() {
        Value::Array(ints.into_iter().map(Value::from).collect())
    } else if !floats.is_empty() {
        Value::Array(
            floats
                .into_iter()
                .map(|value| Value::from(value as f64))
                .collect(),
        )
    } else if let Some(value) = int_value {
        Value::from(value)
    } else if let Some(value) = float_value {
        Value::from(value as f64)
    } else if let Some(value) = string_value {
        Value::String(value)
    } else {
        Value::Null
    };
    Ok((name, value))
}

fn parse_onnx_tensor_proto(bytes: &[u8]) -> Result<InitializerFixture> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut name = None;
    let mut shape = Vec::new();
    let mut dtype = None;
    let mut float_values = Vec::new();
    let mut int32_values = Vec::new();
    let mut int64_values = Vec::new();
    let mut raw_data = None;

    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => {
                shape.extend(field.repeated_i64()?);
                ensure_count_limit("ONNX tensor rank", shape.len(), MAX_ONNX_TENSOR_RANK)?;
            }
            2 => dtype = Some(onnx_dtype(field.varint()? as i32)?),
            4 => {
                float_values.extend(field.repeated_f32()?);
                ensure_count_limit(
                    "ONNX tensor float_data",
                    float_values.len(),
                    MAX_ONNX_TENSOR_ELEMENTS,
                )?;
            }
            5 => {
                int32_values.extend(field.repeated_i64()?);
                ensure_count_limit(
                    "ONNX tensor int32_data",
                    int32_values.len(),
                    MAX_ONNX_TENSOR_ELEMENTS,
                )?;
            }
            7 => {
                int64_values.extend(field.repeated_i64()?);
                ensure_count_limit(
                    "ONNX tensor int64_data",
                    int64_values.len(),
                    MAX_ONNX_TENSOR_ELEMENTS,
                )?;
            }
            8 => name = Some(proto_string(field.length_delimited()?)?),
            9 => {
                let data = field.length_delimited()?;
                ensure_raw_tensor_payload_limit(data.len())?;
                raw_data = Some(data);
            }
            _ => field.skip()?,
        }
    }

    let name = name.ok_or_else(|| Error::Invalid("ONNX TensorProto missing name".to_string()))?;
    let dtype = dtype
        .ok_or_else(|| Error::Invalid(format!("ONNX TensorProto '{name}' missing data_type")))?;
    validate_shape_element_limit("initializer", &name, &shape)?;
    if let Some(raw_data) = raw_data {
        validate_raw_tensor_payload(&name, dtype, raw_data.len())?;
    }
    let values = tensor_values(dtype, &float_values, &int32_values, &int64_values, raw_data)?;

    Ok(InitializerFixture {
        layout: infer_layout(&shape, true),
        name,
        shape,
        dtype,
        values,
    })
}

fn parse_onnx_value_info_proto(bytes: &[u8], role: TensorRole) -> Result<TensorFixture> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut name = None;
    let mut dtype = None;
    let mut shape = None;

    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => name = Some(proto_string(field.length_delimited()?)?),
            2 => {
                let (elem_type, tensor_shape) = parse_onnx_type_proto(field.length_delimited()?)?;
                dtype = elem_type;
                shape = tensor_shape;
            }
            _ => field.skip()?,
        }
    }

    let name =
        name.ok_or_else(|| Error::Invalid("ONNX ValueInfoProto missing name".to_string()))?;
    let dtype = dtype.ok_or_else(|| {
        Error::Invalid(format!(
            "ONNX ValueInfoProto '{name}' missing tensor elem_type"
        ))
    })?;
    let shape = shape
        .ok_or_else(|| Error::Invalid(format!("ONNX ValueInfoProto '{name}' missing shape")))?;
    Ok(TensorFixture {
        layout: infer_layout(&shape, matches!(role, TensorRole::Initializer)),
        name,
        shape,
        dtype,
    })
}

fn parse_onnx_type_proto(bytes: &[u8]) -> Result<(Option<DType>, Option<Vec<i64>>)> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut dtype = None;
    let mut shape = None;
    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => {
                let (elem_type, tensor_shape) =
                    parse_onnx_tensor_type_proto(field.length_delimited()?)?;
                dtype = elem_type;
                shape = tensor_shape;
            }
            _ => field.skip()?,
        }
    }
    Ok((dtype, shape))
}

fn parse_onnx_tensor_type_proto(bytes: &[u8]) -> Result<(Option<DType>, Option<Vec<i64>>)> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut dtype = None;
    let mut shape = None;
    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => dtype = Some(onnx_dtype(field.varint()? as i32)?),
            2 => shape = Some(parse_onnx_tensor_shape_proto(field.length_delimited()?)?),
            _ => field.skip()?,
        }
    }
    Ok((dtype, shape))
}

fn parse_onnx_tensor_shape_proto(bytes: &[u8]) -> Result<Vec<i64>> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut shape = Vec::new();
    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => {
                shape.push(parse_onnx_dimension_proto(field.length_delimited()?)?);
                ensure_count_limit("ONNX tensor rank", shape.len(), MAX_ONNX_TENSOR_RANK)?;
            }
            _ => field.skip()?,
        }
    }
    Ok(shape)
}

fn parse_onnx_dimension_proto(bytes: &[u8]) -> Result<i64> {
    let mut cursor = ProtoCursor::new(bytes);
    let mut dim = None;
    while let Some(field) = cursor.next_field()? {
        match field.number {
            1 => dim = Some(field.varint()? as i64),
            2 => {
                let _ = field.length_delimited()?;
                dim = Some(-1);
            }
            _ => field.skip()?,
        }
    }
    Ok(dim.unwrap_or(-1))
}

fn onnx_dtype(elem_type: i32) -> Result<DType> {
    match elem_type {
        1 => Ok(DType::F32),
        6 => Ok(DType::I32),
        7 => Ok(DType::I64),
        10 => Ok(DType::F16),
        other => Err(Error::Unsupported(format!(
            "ONNX tensor elem_type {other} is not in the VNN MVP subset"
        ))),
    }
}

fn infer_layout(shape: &[i64], initializer: bool) -> Layout {
    match (initializer, shape.len()) {
        (true, 0) => Layout::Scalar,
        (true, 1) => Layout::Vector,
        (true, 2) => Layout::Oi,
        (true, 4) => Layout::Oihw,
        (false, 1) => Layout::Vector,
        (false, 2) => Layout::Nc,
        (false, 3) => Layout::Nld,
        (false, 4) => Layout::Nchw,
        _ => Layout::Strided,
    }
}

fn tensor_values(
    dtype: DType,
    float_values: &[f32],
    int32_values: &[i64],
    int64_values: &[i64],
    raw_data: Option<&[u8]>,
) -> Result<Vec<Value>> {
    if let Some(raw_data) = raw_data {
        return raw_tensor_values(dtype, raw_data);
    }
    Ok(match dtype {
        DType::F32 | DType::F16 => float_values
            .iter()
            .map(|value| Value::from(*value as f64))
            .collect(),
        DType::I32 => int32_values
            .iter()
            .map(|value| Value::from(*value))
            .collect(),
        DType::I64 => int64_values
            .iter()
            .map(|value| Value::from(*value))
            .collect(),
    })
}

fn ensure_raw_tensor_payload_limit(byte_len: usize) -> Result<()> {
    if byte_len > MAX_ONNX_RAW_TENSOR_BYTES {
        return Err(Error::Unsupported(format!(
            "ONNX raw tensor payload is {byte_len} byte(s), over importer limit {MAX_ONNX_RAW_TENSOR_BYTES}"
        )));
    }
    Ok(())
}

fn validate_raw_tensor_payload(name: &str, dtype: DType, byte_len: usize) -> Result<()> {
    ensure_raw_tensor_payload_limit(byte_len)?;
    let width = dtype_byte_width(dtype);
    if !byte_len.is_multiple_of(width) {
        return Err(Error::Invalid(format!(
            "ONNX TensorProto '{name}' raw_data length {byte_len} is not a multiple of {width}"
        )));
    }
    let elements = byte_len / width;
    ensure_count_limit(
        "ONNX raw tensor elements",
        elements,
        MAX_ONNX_TENSOR_ELEMENTS,
    )?;
    Ok(())
}

fn dtype_byte_width(dtype: DType) -> usize {
    match dtype {
        DType::F16 => 2,
        DType::F32 | DType::I32 => 4,
        DType::I64 => 8,
    }
}

fn raw_tensor_values(dtype: DType, bytes: &[u8]) -> Result<Vec<Value>> {
    ensure_raw_tensor_payload_limit(bytes.len())?;
    let width = dtype_byte_width(dtype);
    if !bytes.len().is_multiple_of(width) {
        return Err(Error::Invalid(format!(
            "ONNX raw tensor payload length {} is not a multiple of {width}",
            bytes.len()
        )));
    }
    Ok(match dtype {
        DType::F32 => bytes
            .chunks_exact(4)
            .map(|chunk| {
                Value::from(f32::from_le_bytes(chunk.try_into().expect("exact chunk")) as f64)
            })
            .collect(),
        DType::I32 => bytes
            .chunks_exact(4)
            .map(|chunk| Value::from(i32::from_le_bytes(chunk.try_into().expect("exact chunk"))))
            .collect(),
        DType::I64 => bytes
            .chunks_exact(8)
            .map(|chunk| Value::from(i64::from_le_bytes(chunk.try_into().expect("exact chunk"))))
            .collect(),
        DType::F16 if bytes.is_empty() => Vec::new(),
        DType::F16 => {
            return Err(Error::Unsupported(
                "ONNX f16 raw tensor decoding is not in the VNN MVP subset".to_string(),
            ));
        }
    })
}

fn proto_string(bytes: &[u8]) -> Result<String> {
    if bytes.len() > MAX_ONNX_STRING_BYTES {
        return Err(Error::Unsupported(format!(
            "ONNX protobuf string is {} byte(s), over importer limit {}",
            bytes.len(),
            MAX_ONNX_STRING_BYTES
        )));
    }
    std::str::from_utf8(bytes)
        .map(str::to_string)
        .map_err(|err| Error::Invalid(format!("invalid UTF-8 in ONNX protobuf string: {err}")))
}

#[derive(Clone, Copy)]
struct ProtoField<'a> {
    number: u32,
    wire_type: u8,
    data: &'a [u8],
}

impl<'a> ProtoField<'a> {
    fn length_delimited(self) -> Result<&'a [u8]> {
        if self.wire_type != 2 {
            return Err(Error::Invalid(format!(
                "ONNX protobuf field {} has wire type {}, expected length-delimited",
                self.number, self.wire_type
            )));
        }
        Ok(self.data)
    }

    fn varint(self) -> Result<u64> {
        if self.wire_type != 0 {
            return Err(Error::Invalid(format!(
                "ONNX protobuf field {} has wire type {}, expected varint",
                self.number, self.wire_type
            )));
        }
        let mut cursor = ProtoCursor::new(self.data);
        cursor.read_varint()
    }

    fn fixed32(self) -> Result<f32> {
        if self.wire_type != 5 || self.data.len() != 4 {
            return Err(Error::Invalid(format!(
                "ONNX protobuf field {} has wire type {}, expected fixed32",
                self.number, self.wire_type
            )));
        }
        Ok(f32::from_le_bytes(
            self.data.try_into().expect("fixed32 length checked"),
        ))
    }

    fn repeated_i64(self) -> Result<Vec<i64>> {
        match self.wire_type {
            0 => Ok(vec![self.varint()? as i64]),
            2 => {
                let mut cursor = ProtoCursor::new(self.data);
                let mut values = Vec::new();
                while !cursor.is_empty() {
                    ensure_count_limit(
                        "ONNX repeated int64 values",
                        values.len() + 1,
                        MAX_ONNX_TENSOR_ELEMENTS,
                    )?;
                    values.push(cursor.read_varint()? as i64);
                }
                Ok(values)
            }
            _ => Err(Error::Invalid(format!(
                "ONNX protobuf field {} has wire type {}, expected repeated int64",
                self.number, self.wire_type
            ))),
        }
    }

    fn repeated_f32(self) -> Result<Vec<f32>> {
        match self.wire_type {
            5 => Ok(vec![self.fixed32()?]),
            2 => {
                if !self.data.len().is_multiple_of(4) {
                    return Err(Error::Invalid(format!(
                        "ONNX protobuf field {} has malformed packed float data",
                        self.number
                    )));
                }
                ensure_count_limit(
                    "ONNX repeated float values",
                    self.data.len() / 4,
                    MAX_ONNX_TENSOR_ELEMENTS,
                )?;
                Ok(self
                    .data
                    .chunks_exact(4)
                    .map(|chunk| f32::from_le_bytes(chunk.try_into().expect("exact chunk")))
                    .collect())
            }
            _ => Err(Error::Invalid(format!(
                "ONNX protobuf field {} has wire type {}, expected repeated float",
                self.number, self.wire_type
            ))),
        }
    }

    fn skip(self) -> Result<()> {
        Ok(())
    }
}

struct ProtoCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ProtoCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn is_empty(&self) -> bool {
        self.offset >= self.bytes.len()
    }

    fn next_field(&mut self) -> Result<Option<ProtoField<'a>>> {
        if self.is_empty() {
            return Ok(None);
        }
        let key = self.read_varint()?;
        let number = (key >> 3) as u32;
        let wire_type = (key & 0x07) as u8;
        if number == 0 {
            return Err(Error::Invalid("ONNX protobuf field number 0".to_string()));
        }
        let data = match wire_type {
            0 => {
                let start = self.offset;
                self.read_varint()?;
                &self.bytes[start..self.offset]
            }
            1 => self.read_exact(8)?,
            2 => {
                let len = usize::try_from(self.read_varint()?).map_err(|_| {
                    Error::Invalid("ONNX protobuf length overflows usize".to_string())
                })?;
                self.read_exact(len)?
            }
            5 => self.read_exact(4)?,
            _ => {
                return Err(Error::Invalid(format!(
                    "unsupported ONNX protobuf wire type {wire_type}"
                )));
            }
        };
        Ok(Some(ProtoField {
            number,
            wire_type,
            data,
        }))
    }

    fn read_varint(&mut self) -> Result<u64> {
        let mut value = 0u64;
        for shift in (0..64).step_by(7) {
            let byte = *self
                .bytes
                .get(self.offset)
                .ok_or_else(|| Error::Invalid("truncated ONNX protobuf varint".to_string()))?;
            self.offset += 1;
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(value);
            }
        }
        Err(Error::Invalid("overlong ONNX protobuf varint".to_string()))
    }

    fn read_exact(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or_else(|| Error::Invalid("ONNX protobuf length overflow".to_string()))?;
        if end > self.bytes.len() {
            return Err(Error::Invalid("truncated ONNX protobuf field".to_string()));
        }
        let data = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(data)
    }
}

impl AttentionFusionReport {
    fn new() -> Self {
        Self {
            fusion: "attention_qk_softmax_v",
            eligible: false,
            candidates: Vec::new(),
            diagnostics: Vec::new(),
        }
    }
}

fn attention_fixture_preflight_diagnostics(graph: &GraphFixture) -> Vec<AttentionFusionDiagnostic> {
    let mut diagnostics = Vec::new();
    let initializer_specs = graph
        .initializers
        .iter()
        .map(|initializer| (initializer.name.as_str(), initializer))
        .collect::<HashMap<_, _>>();
    let tensor_specs = graph
        .inputs
        .iter()
        .chain(graph.tensors.iter())
        .map(|tensor| (tensor.name.as_str(), tensor))
        .collect::<HashMap<_, _>>();

    for tensor in graph.inputs.iter().chain(graph.tensors.iter()) {
        if tensor.shape.iter().any(|dim| *dim <= 0) {
            diagnostics.push(attention_diag(
                AttentionFusionUnsupportedReason::DynamicShape,
                Vec::new(),
                format!(
                    "tensor '{}' has dynamic/unknown shape {:?}; attention fusion requires static batch, sequence, and hidden dimensions",
                    tensor.name, tensor.shape
                ),
            ));
        }
    }
    for node in &graph.nodes {
        match node.op_type.as_str() {
            "Dropout" => diagnostics.push(attention_diag(
                AttentionFusionUnsupportedReason::UnsupportedDropout,
                vec![node.name.clone()],
                format!("Dropout node '{}' is not allowed in inference attention fusion", node.name),
            )),
            "Gather" | "GatherElements" | "GatherND" | "Scatter" | "ScatterElements"
            | "ScatterND" => diagnostics.push(attention_diag(
                AttentionFusionUnsupportedReason::DataDependentIndexing,
                vec![node.name.clone()],
                format!(
                    "{} node '{}' is data-dependent indexing and is outside the v1 attention fusion contract",
                    node.op_type, node.name
                ),
            )),
            "Reshape" if !reshape_has_static_shape_metadata(node, &initializer_specs) => {
                diagnostics.push(missing_static_shape_metadata_diag(
                    node,
                    "Reshape requires a static i64 target shape initializer or target_shape metadata",
                ));
            }
            "Split" if !split_has_static_shape_metadata(node, &initializer_specs) => {
                diagnostics.push(missing_static_shape_metadata_diag(
                    node,
                    "Split requires static axis and split-size metadata",
                ));
            }
            "Concat" if !concat_has_static_shape_metadata(node, &tensor_specs) => {
                diagnostics.push(missing_static_shape_metadata_diag(
                    node,
                    "Concat requires static axis metadata and statically-shaped inputs/outputs",
                ));
            }
            _ => {}
        }
    }
    dedupe_attention_diagnostics(diagnostics)
}

fn is_data_dependent_indexing_op(op_type: &str) -> bool {
    matches!(
        op_type,
        "Gather" | "GatherElements" | "GatherND" | "Scatter" | "ScatterElements" | "ScatterND"
    )
}

fn missing_static_shape_metadata_diag(
    node: &NodeFixture,
    requirement: &'static str,
) -> AttentionFusionDiagnostic {
    attention_diag(
        AttentionFusionUnsupportedReason::MissingStaticShapeMetadata,
        vec![node.name.clone()],
        format!(
            "{} node '{}' is missing static shape metadata: {requirement}",
            node.op_type, node.name
        ),
    )
}

fn reshape_has_static_shape_metadata(
    node: &NodeFixture,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> bool {
    if node
        .attributes
        .get("target_shape")
        .is_some_and(static_i64_array_value)
    {
        return true;
    }
    let Some(shape_input) = node.inputs.get(1) else {
        return false;
    };
    initializer_specs
        .get(shape_input.as_str())
        .is_some_and(|initializer| initializer_has_static_i64_values(initializer))
}

fn split_has_static_shape_metadata(
    node: &NodeFixture,
    initializer_specs: &HashMap<&str, &InitializerFixture>,
) -> bool {
    let has_axis = node
        .attributes
        .get("axis")
        .and_then(Value::as_i64)
        .is_some();
    let has_split_attr = node
        .attributes
        .get("split")
        .is_some_and(static_i64_array_value);
    let has_split_initializer = node
        .inputs
        .get(1)
        .and_then(|input| initializer_specs.get(input.as_str()))
        .is_some_and(|initializer| initializer_has_static_i64_values(initializer));

    has_axis && (has_split_attr || has_split_initializer)
}

fn concat_has_static_shape_metadata(
    node: &NodeFixture,
    tensor_specs: &HashMap<&str, &TensorFixture>,
) -> bool {
    let has_axis = node
        .attributes
        .get("axis")
        .and_then(Value::as_i64)
        .is_some();
    has_axis
        && !node.inputs.is_empty()
        && !node.outputs.is_empty()
        && node.inputs.iter().all(|input| {
            tensor_specs
                .get(input.as_str())
                .is_some_and(tensor_has_static_shape)
        })
        && node.outputs.iter().all(|output| {
            tensor_specs
                .get(output.as_str())
                .is_some_and(tensor_has_static_shape)
        })
}

fn vnn_reshape_has_static_shape_metadata(op: &VnnOp) -> bool {
    op.attrs
        .get("target_shape")
        .is_some_and(static_i64_array_value)
}

fn static_i64_array_value(value: &Value) -> bool {
    value.as_array().is_some_and(|dims| {
        !dims.is_empty()
            && dims
                .iter()
                .all(|dim| dim.as_i64().is_some_and(|dim| dim > 0))
    })
}

fn initializer_has_static_i64_values(initializer: &InitializerFixture) -> bool {
    initializer.dtype == DType::I64
        && !initializer.values.is_empty()
        && initializer
            .values
            .iter()
            .all(|dim| dim.as_i64().is_some_and(|dim| dim > 0))
}

fn tensor_has_static_shape(tensor: &&TensorFixture) -> bool {
    !tensor.shape.is_empty() && tensor.shape.iter().all(|dim| *dim > 0)
}

fn attention_module_global_diagnostics(module: &VnnModule) -> Vec<AttentionFusionDiagnostic> {
    let mut diagnostics = Vec::new();
    for op in &module.ops {
        if op.provenance.onnx_op_type == "Dropout" || op.op == "trust_ir.vnn.dropout" {
            diagnostics.push(attention_diag(
                AttentionFusionUnsupportedReason::UnsupportedDropout,
                vec![op.provenance.onnx_node_name.clone()],
                format!(
                    "Dropout node '{}' is not allowed in inference attention fusion",
                    op.provenance.onnx_node_name
                ),
            ));
        }
        if is_data_dependent_indexing_op(&op.provenance.onnx_op_type)
            || matches!(
                op.op.as_str(),
                "trust_ir.vnn.gather"
                    | "trust_ir.vnn.gather_elements"
                    | "trust_ir.vnn.gather_nd"
                    | "trust_ir.vnn.scatter"
                    | "trust_ir.vnn.scatter_elements"
                    | "trust_ir.vnn.scatter_nd"
            )
        {
            diagnostics.push(attention_diag(
                AttentionFusionUnsupportedReason::DataDependentIndexing,
                vec![op.provenance.onnx_node_name.clone()],
                format!(
                    "{} node '{}' is data-dependent indexing and is outside the v1 attention fusion contract",
                    op.provenance.onnx_op_type, op.provenance.onnx_node_name
                ),
            ));
        }
    }
    diagnostics
}

fn attention_candidate_from_context_matmul(
    module: &VnnModule,
    context_matmul_index: usize,
    options: &AttentionFusionOptions,
) -> std::result::Result<AttentionFusionCandidate, Vec<AttentionFusionDiagnostic>> {
    let producers = producers_by_tensor(module);
    let context_matmul = &module.ops[context_matmul_index];
    let mut diagnostics = Vec::new();
    let mut source_ops = vec![context_matmul.provenance.onnx_node_name.clone()];

    let Some(prob_tensor) = context_matmul.inputs.first() else {
        return Err(vec![attention_diag(
            AttentionFusionUnsupportedReason::PatternNotFound,
            source_ops,
            format!(
                "context MatMul '{}' is missing probability input",
                context_matmul.id
            ),
        )]);
    };
    let Some(value_tensor) = context_matmul.inputs.get(1) else {
        return Err(vec![attention_diag(
            AttentionFusionUnsupportedReason::PatternNotFound,
            source_ops,
            format!(
                "context MatMul '{}' is missing value input",
                context_matmul.id
            ),
        )]);
    };

    let Some(softmax_index) = producers.get(prob_tensor.as_str()).copied() else {
        return Err(Vec::new());
    };
    let softmax = &module.ops[softmax_index];
    if softmax.op != "trust_ir.vnn.softmax" {
        return Err(Vec::new());
    }
    source_ops.push(softmax.provenance.onnx_node_name.clone());

    if !softmax_axis_is_last(module, softmax) {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::UnsupportedSoftmaxAxis,
            source_ops.clone(),
            format!(
                "Softmax node '{}' must use the last axis for attention fusion",
                softmax.provenance.onnx_node_name
            ),
        ));
    }

    let Some(softmax_input) = softmax.inputs.first() else {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::PatternNotFound,
            source_ops.clone(),
            format!("Softmax node '{}' is missing input", softmax.id),
        ));
        return Err(diagnostics);
    };

    let Some(mut score_path_index) = producers.get(softmax_input.as_str()).copied() else {
        return Err(Vec::new());
    };
    if module.ops[score_path_index].op == "trust_ir.vnn.add" {
        source_ops.push(
            module.ops[score_path_index]
                .provenance
                .onnx_node_name
                .clone(),
        );
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::UnsupportedAttentionMask,
            source_ops.clone(),
            format!(
                "Add node '{}' on the attention score path is treated as a causal/padding mask and is unsupported in v1",
                module.ops[score_path_index].provenance.onnx_node_name
            ),
        ));
        if let Some(index) =
            first_data_input_producer(module, &producers, &module.ops[score_path_index])
        {
            score_path_index = index;
        }
    }

    let scale = &module.ops[score_path_index];
    if scale.op != "trust_ir.vnn.scale" {
        return Err(Vec::new());
    }
    source_ops.push(scale.provenance.onnx_node_name.clone());
    let scale_value = validate_attention_scale(module, scale, &mut diagnostics, &source_ops);

    let Some(scores_tensor) = scale.inputs.first() else {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::PatternNotFound,
            source_ops.clone(),
            format!("Scale node '{}' is missing score input", scale.id),
        ));
        return Err(diagnostics);
    };
    let Some(scores_matmul_index) = producers.get(scores_tensor.as_str()).copied() else {
        return Err(Vec::new());
    };
    let scores_matmul = &module.ops[scores_matmul_index];
    if scores_matmul.op != "trust_ir.vnn.matmul" {
        return Err(Vec::new());
    }
    source_ops.push(scores_matmul.provenance.onnx_node_name.clone());

    let Some(query_tensor) = scores_matmul.inputs.first() else {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::PatternNotFound,
            source_ops.clone(),
            format!("QK MatMul '{}' is missing query input", scores_matmul.id),
        ));
        return Err(diagnostics);
    };
    let Some(transposed_key_tensor) = scores_matmul.inputs.get(1) else {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::PatternNotFound,
            source_ops.clone(),
            format!(
                "QK MatMul '{}' is missing transposed-key input",
                scores_matmul.id
            ),
        ));
        return Err(diagnostics);
    };

    let Some(query_linear_index) =
        (match trace_attention_projection(module, &producers, query_tensor, &source_ops) {
            Ok(index) => index,
            Err(diagnostic) => {
                diagnostics.push(diagnostic);
                return Err(diagnostics);
            }
        })
    else {
        return Err(Vec::new());
    };
    source_ops.push(
        module.ops[query_linear_index]
            .provenance
            .onnx_node_name
            .clone(),
    );

    let Some(transpose_index) = producers.get(transposed_key_tensor.as_str()).copied() else {
        return Err(Vec::new());
    };
    let transpose = &module.ops[transpose_index];
    if transpose.op != "trust_ir.vnn.transpose" {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::MissingTransposeMetadata,
            source_ops.clone(),
            format!(
                "QK MatMul '{}' must consume an explicit Transpose(K) input",
                scores_matmul.provenance.onnx_node_name
            ),
        ));
        return Err(diagnostics);
    }
    source_ops.push(transpose.provenance.onnx_node_name.clone());
    if !transpose_swaps_last_two_dims(module, transpose) {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::MissingTransposeMetadata,
            source_ops.clone(),
            format!(
                "Transpose node '{}' must carry a static perm that swaps only the last two dimensions",
                transpose.provenance.onnx_node_name
            ),
        ));
    }

    let Some(key_tensor) = transpose.inputs.first() else {
        return Err(Vec::new());
    };
    let Some(key_linear_index) =
        (match trace_attention_projection(module, &producers, key_tensor, &source_ops) {
            Ok(index) => index,
            Err(diagnostic) => {
                diagnostics.push(diagnostic);
                return Err(diagnostics);
            }
        })
    else {
        return Err(Vec::new());
    };
    source_ops.push(
        module.ops[key_linear_index]
            .provenance
            .onnx_node_name
            .clone(),
    );

    let Some(value_linear_index) =
        (match trace_attention_projection(module, &producers, value_tensor, &source_ops) {
            Ok(index) => index,
            Err(diagnostic) => {
                diagnostics.push(diagnostic);
                return Err(diagnostics);
            }
        })
    else {
        return Err(Vec::new());
    };
    source_ops.push(
        module.ops[value_linear_index]
            .provenance
            .onnx_node_name
            .clone(),
    );

    validate_projection_inputs_match(
        module,
        query_linear_index,
        key_linear_index,
        value_linear_index,
        &mut diagnostics,
        &source_ops,
    );

    validate_attention_dtypes(
        module,
        &[
            query_tensor,
            key_tensor,
            value_tensor,
            transposed_key_tensor,
            scores_tensor,
            softmax_input,
            prob_tensor,
        ],
        &[
            query_linear_index,
            key_linear_index,
            value_linear_index,
            scores_matmul_index,
            score_path_index,
            softmax_index,
            context_matmul_index,
        ],
        &mut diagnostics,
        &source_ops,
    );

    let Some(dims) = attention_dims(module, query_tensor, value_tensor, scores_tensor) else {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::ShapeMismatch,
            source_ops.clone(),
            "attention tensor ranks/shapes do not match the fixed inference contract".to_string(),
        ));
        return Err(diagnostics);
    };

    if options.certified
        && (options.relaxation_policy.is_none() || options.checker_obligation_schema.is_none())
    {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::MissingRelaxationMetadata,
            source_ops.clone(),
            "certified attention fusion requires a softmax/attention relaxation policy and checker obligation schema".to_string(),
        ));
    }

    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    Ok(AttentionFusionCandidate {
        source_ops: stable_source_ops(source_ops),
        batch: dims.batch,
        sequence: dims.sequence,
        head_count: dims.head_count,
        head_dim: dims.head_dim,
        hidden_dim: dims.hidden_dim,
        scale: scale_value,
        relaxation_policy: options.relaxation_policy.clone(),
        checker_obligation_schema: options.checker_obligation_schema.clone(),
    })
}

fn producers_by_tensor(module: &VnnModule) -> HashMap<&str, usize> {
    let mut producers = HashMap::new();
    for (index, op) in module.ops.iter().enumerate() {
        for output in &op.outputs {
            producers.insert(output.as_str(), index);
        }
    }
    producers
}

fn first_data_input_producer(
    module: &VnnModule,
    producers: &HashMap<&str, usize>,
    op: &VnnOp,
) -> Option<usize> {
    op.inputs
        .iter()
        .filter_map(|input| producers.get(input.as_str()).copied())
        .find(|index| {
            matches!(
                module.ops[*index].op.as_str(),
                "trust_ir.vnn.scale" | "trust_ir.vnn.matmul"
            )
        })
}

#[allow(clippy::result_large_err)] // Preserve the structured diagnostic as the public error value.
fn trace_attention_projection(
    module: &VnnModule,
    producers: &HashMap<&str, usize>,
    tensor: &str,
    source_ops: &[String],
) -> std::result::Result<Option<usize>, AttentionFusionDiagnostic> {
    let Some(mut index) = producers.get(tensor).copied() else {
        return Ok(None);
    };
    if module.ops[index].op == "trust_ir.vnn.reshape" {
        let reshape = &module.ops[index];
        if !vnn_reshape_has_static_shape_metadata(reshape) {
            let mut diagnostic_source_ops = source_ops.to_vec();
            diagnostic_source_ops.push(reshape.provenance.onnx_node_name.clone());
            return Err(attention_diag(
                AttentionFusionUnsupportedReason::MissingStaticShapeMetadata,
                diagnostic_source_ops,
                format!(
                    "Reshape node '{}' must carry static target_shape metadata for attention projection tracing",
                    reshape.provenance.onnx_node_name
                ),
            ));
        }
        let Some(input) = module.ops[index].inputs.first() else {
            return Ok(None);
        };
        let Some(producer_index) = producers.get(input.as_str()).copied() else {
            return Ok(None);
        };
        index = producer_index;
    }
    let op = &module.ops[index];
    Ok((op.op == "trust_ir.vnn.linear"
        && op
            .attrs
            .get("source_op")
            .and_then(Value::as_str)
            .is_none_or(|source| source == "MatMul"))
    .then_some(index))
}

fn validate_attention_scale(
    module: &VnnModule,
    scale: &VnnOp,
    diagnostics: &mut Vec<AttentionFusionDiagnostic>,
    source_ops: &[String],
) -> Option<f64> {
    let Some(scale_initializer) = scale
        .attrs
        .get("scale_initializer")
        .and_then(Value::as_str)
        .or_else(|| scale.weights.first().map(String::as_str))
    else {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::MissingInitializer,
            source_ops.to_vec(),
            format!(
                "Scale node '{}' does not identify a constant scalar initializer",
                scale.provenance.onnx_node_name
            ),
        ));
        return None;
    };
    let Some(initializer) = module.initializers.get(scale_initializer) else {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::MissingInitializer,
            source_ops.to_vec(),
            format!(
                "Scale node '{}' references missing initializer '{}'",
                scale.provenance.onnx_node_name, scale_initializer
            ),
        ));
        return None;
    };
    if !initializer.shape.is_empty() || initializer.dtype != DType::F32 {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::UnsupportedDtype,
            source_ops.to_vec(),
            format!(
                "Scale initializer '{}' must be an f32 scalar for attention fusion",
                scale_initializer
            ),
        ));
    }
    scale.attrs.get("scale_value").and_then(Value::as_f64)
}

fn softmax_axis_is_last(module: &VnnModule, softmax: &VnnOp) -> bool {
    let Some(input) = softmax.inputs.first() else {
        return false;
    };
    let Some(tensor) = module.tensors.get(input) else {
        return false;
    };
    let Some(axis) = softmax.attrs.get("axis").and_then(Value::as_i64) else {
        return false;
    };
    let rank = tensor.shape.len() as i64;
    axis == -1 || axis == rank - 1
}

fn transpose_swaps_last_two_dims(module: &VnnModule, transpose: &VnnOp) -> bool {
    let Some(input) = transpose.inputs.first() else {
        return false;
    };
    let Some(tensor) = module.tensors.get(input) else {
        return false;
    };
    let Some(perm) = transpose.attrs.get("perm").and_then(Value::as_array) else {
        return false;
    };
    let rank = tensor.shape.len();
    if perm.len() != rank || rank < 2 {
        return false;
    }
    let expected = (0..rank)
        .map(|index| {
            if index == rank - 2 {
                rank - 1
            } else if index == rank - 1 {
                rank - 2
            } else {
                index
            }
        })
        .collect::<Vec<_>>();
    perm.iter()
        .map(|value| value.as_u64().map(|value| value as usize))
        .collect::<Option<Vec<_>>>()
        .is_some_and(|actual| actual == expected)
}

fn validate_projection_inputs_match(
    module: &VnnModule,
    query_linear_index: usize,
    key_linear_index: usize,
    value_linear_index: usize,
    diagnostics: &mut Vec<AttentionFusionDiagnostic>,
    source_ops: &[String],
) {
    let query_input = module.ops[query_linear_index].inputs.first();
    let key_input = module.ops[key_linear_index].inputs.first();
    let value_input = module.ops[value_linear_index].inputs.first();
    if query_input.is_none()
        || key_input.is_none()
        || value_input.is_none()
        || query_input != key_input
        || query_input != value_input
    {
        diagnostics.push(attention_diag(
            AttentionFusionUnsupportedReason::ShapeMismatch,
            source_ops.to_vec(),
            "Q/K/V projections must read the same hidden-state activation".to_string(),
        ));
    }
}

fn validate_attention_dtypes(
    module: &VnnModule,
    tensors: &[&str],
    op_indices: &[usize],
    diagnostics: &mut Vec<AttentionFusionDiagnostic>,
    source_ops: &[String],
) {
    for tensor_name in tensors {
        let Some(tensor) = module.tensors.get(*tensor_name) else {
            diagnostics.push(attention_diag(
                AttentionFusionUnsupportedReason::ShapeMismatch,
                source_ops.to_vec(),
                format!("attention tensor '{}' is missing VNN metadata", tensor_name),
            ));
            continue;
        };
        if tensor.dtype != DType::F32 {
            diagnostics.push(attention_diag(
                AttentionFusionUnsupportedReason::UnsupportedDtype,
                source_ops.to_vec(),
                format!(
                    "attention tensor '{}' has dtype {:?}; only f32 is supported",
                    tensor_name, tensor.dtype
                ),
            ));
        }
    }
    for index in op_indices {
        for weight in &module.ops[*index].weights {
            let Some(initializer) = module.initializers.get(weight) else {
                diagnostics.push(attention_diag(
                    AttentionFusionUnsupportedReason::MissingInitializer,
                    source_ops.to_vec(),
                    format!(
                        "op '{}' references missing initializer '{}'",
                        module.ops[*index].provenance.onnx_node_name, weight
                    ),
                ));
                continue;
            };
            if initializer.dtype != DType::F32 {
                diagnostics.push(attention_diag(
                    AttentionFusionUnsupportedReason::UnsupportedDtype,
                    source_ops.to_vec(),
                    format!(
                        "initializer '{}' has dtype {:?}; only f32 attention fusion is supported",
                        weight, initializer.dtype
                    ),
                ));
            }
        }
    }
}

struct AttentionDims {
    batch: usize,
    sequence: usize,
    head_count: usize,
    head_dim: usize,
    hidden_dim: usize,
}

fn attention_dims(
    module: &VnnModule,
    query_tensor: &str,
    value_tensor: &str,
    scores_tensor: &str,
) -> Option<AttentionDims> {
    let query = &module.tensors.get(query_tensor)?.shape;
    let value = &module.tensors.get(value_tensor)?.shape;
    let scores = &module.tensors.get(scores_tensor)?.shape;
    match (query.as_slice(), value.as_slice(), scores.as_slice()) {
        (
            [batch, sequence, hidden_dim],
            [value_batch, value_sequence, value_hidden],
            [score_batch, score_m, score_n],
        ) if batch == value_batch
            && batch == score_batch
            && sequence == value_sequence
            && sequence == score_m
            && sequence == score_n
            && hidden_dim == value_hidden =>
        {
            Some(AttentionDims {
                batch: *batch,
                sequence: *sequence,
                head_count: 1,
                head_dim: *hidden_dim,
                hidden_dim: *hidden_dim,
            })
        }
        (
            [batch, heads, sequence, head_dim],
            [value_batch, value_heads, value_sequence, value_head_dim],
            [score_batch, score_heads, score_m, score_n],
        ) if batch == value_batch
            && batch == score_batch
            && heads == value_heads
            && heads == score_heads
            && sequence == value_sequence
            && sequence == score_m
            && sequence == score_n
            && head_dim == value_head_dim =>
        {
            Some(AttentionDims {
                batch: *batch,
                sequence: *sequence,
                head_count: *heads,
                head_dim: *head_dim,
                hidden_dim: *heads * *head_dim,
            })
        }
        _ => None,
    }
}

fn attention_diag(
    reason: AttentionFusionUnsupportedReason,
    source_ops: Vec<String>,
    message: String,
) -> AttentionFusionDiagnostic {
    AttentionFusionDiagnostic {
        code: "gpu.fusion.unsupported",
        phase: "select_gpu_fusion",
        fusion: "attention_qk_softmax_v",
        target: "gpu.metal.msl",
        reason,
        source_ops: stable_source_ops(source_ops),
        message,
        blocked_by: "#563",
    }
}

fn dedupe_attention_diagnostics(
    diagnostics: Vec<AttentionFusionDiagnostic>,
) -> Vec<AttentionFusionDiagnostic> {
    let mut seen = HashSet::new();
    let mut deduped = Vec::new();
    for diagnostic in diagnostics {
        let key = (
            diagnostic.reason,
            diagnostic.message.clone(),
            diagnostic.source_ops.join("\n"),
        );
        if seen.insert(key) {
            deduped.push(diagnostic);
        }
    }
    deduped
}

fn stable_source_ops(source_ops: Vec<String>) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut stable = Vec::new();
    for op in source_ops {
        if seen.insert(op.clone()) {
            stable.push(op);
        }
    }
    stable
}

fn static_shape(name: &str, shape: &[i64]) -> Result<Vec<usize>> {
    if shape.is_empty() {
        return Err(Error::Invalid(format!("tensor '{name}' has missing shape")));
    }
    static_dims(name, shape)
}

fn static_initializer_shape(name: &str, shape: &[i64]) -> Result<Vec<usize>> {
    static_dims(name, shape)
}

fn static_dims(name: &str, shape: &[i64]) -> Result<Vec<usize>> {
    let mut dims = Vec::with_capacity(shape.len());
    let mut elements = 1usize;
    for dim in shape {
        if *dim <= 0 {
            return Err(Error::Invalid(format!(
                "tensor '{name}' has dynamic/unknown dimension {dim}"
            )));
        }
        let dim = usize::try_from(*dim).map_err(|_| {
            Error::Unsupported(format!("tensor '{name}' dimension overflows usize"))
        })?;
        elements = elements.checked_mul(dim).ok_or_else(|| {
            Error::Unsupported(format!("tensor '{name}' element count overflows"))
        })?;
        if elements > MAX_ONNX_TENSOR_ELEMENTS {
            return Err(Error::Unsupported(format!(
                "tensor '{name}' has {elements} element(s), over importer limit {}",
                MAX_ONNX_TENSOR_ELEMENTS
            )));
        }
        dims.push(dim);
    }
    Ok(dims)
}

fn ssa_name(name: &str) -> String {
    let sanitized: String = name
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' || ch == '.' {
                ch
            } else {
                '_'
            }
        })
        .collect();
    format!("%{sanitized}")
}

fn deterministic_initializer_sha(initializer: &InitializerFixture) -> Result<String> {
    let bytes = serde_json::to_vec(initializer)?;
    let digest = Sha256::digest(bytes);
    Ok(digest.iter().map(|byte| format!("{byte:02x}")).collect())
}

fn int_array_value(values: &[usize]) -> Value {
    Value::Array(
        values
            .iter()
            .map(|value| Value::from(*value as u64))
            .collect(),
    )
}

fn ensure_int_array_attr(attrs: &mut BTreeMap<String, Value>, name: &str, default: &[usize]) {
    attrs
        .entry(name.to_string())
        .or_insert_with(|| int_array_value(default));
}

fn ensure_int_attr(attrs: &mut BTreeMap<String, Value>, name: &str, default: i64) {
    attrs
        .entry(name.to_string())
        .or_insert_with(|| Value::from(default));
}

fn ensure_number_attr(attrs: &mut BTreeMap<String, Value>, name: &str, default: f64) {
    attrs
        .entry(name.to_string())
        .or_insert_with(|| Value::from(default));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_path(name: &str, extension: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "trust-cg-onnx-import-{name}-{}-{}.{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
            extension
        ))
    }

    #[test]
    fn import_path_rejects_oversized_onnx_file_before_reading() {
        let path = temp_path("oversized-model", "onnx");
        let file = fs::File::create(&path).unwrap();
        file.set_len(MAX_ONNX_MODEL_BYTES + 1).unwrap();
        drop(file);

        let result = import_path(&path);
        let _ = fs::remove_file(&path);

        match result {
            Err(Error::Unsupported(message)) => {
                assert!(message.contains("ONNX model"), "{message}");
                assert!(message.contains("over importer limit"), "{message}");
            }
            other => panic!("expected oversized ONNX model rejection, got {:?}", other),
        }
    }

    #[test]
    fn import_path_rejects_oversized_json_fixture_before_reading() {
        let path = temp_path("oversized-fixture", "json");
        let file = fs::File::create(&path).unwrap();
        file.set_len(MAX_ONNX_GRAPH_FIXTURE_BYTES + 1).unwrap();
        drop(file);

        let result = import_path(&path);
        let _ = fs::remove_file(&path);

        match result {
            Err(Error::Unsupported(message)) => {
                assert!(message.contains("ONNX graph fixture"), "{message}");
                assert!(message.contains("over importer limit"), "{message}");
            }
            other => panic!(
                "expected oversized graph fixture rejection, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn graph_fixture_rejects_oversized_tensor_element_count() {
        let graph = GraphFixture {
            name: Some("oversized".to_string()),
            inputs: vec![TensorFixture {
                name: "x".to_string(),
                shape: vec![MAX_ONNX_TENSOR_ELEMENTS as i64 + 1],
                dtype: DType::F32,
                layout: Layout::Vector,
            }],
            outputs: vec!["y".to_string()],
            tensors: vec![TensorFixture {
                name: "y".to_string(),
                shape: vec![1],
                dtype: DType::F32,
                layout: Layout::Vector,
            }],
            initializers: vec![],
            nodes: vec![NodeFixture {
                name: "Relu_0".to_string(),
                op_type: "Relu".to_string(),
                inputs: vec!["x".to_string()],
                outputs: vec!["y".to_string()],
                attributes: BTreeMap::new(),
            }],
        };

        match import_graph_fixture(graph) {
            Err(Error::Unsupported(message)) => {
                assert!(message.contains("over importer limit"), "{message}");
            }
            other => panic!("expected tensor element count rejection, got {:?}", other),
        }
    }

    #[test]
    fn raw_tensor_payload_limit_rejects_metadata_without_payload_allocation() {
        match validate_raw_tensor_payload("weight", DType::F32, MAX_ONNX_RAW_TENSOR_BYTES + 1) {
            Err(Error::Unsupported(message)) => {
                assert!(message.contains("raw tensor payload"), "{message}");
            }
            other => panic!("expected raw tensor payload rejection, got {:?}", other),
        }
    }

    #[test]
    fn graph_count_limit_rejects_metadata_without_large_graph() {
        match ensure_count_limit("ONNX graph nodes", MAX_ONNX_NODES + 1, MAX_ONNX_NODES) {
            Err(Error::Unsupported(message)) => {
                assert!(message.contains("ONNX graph nodes"), "{message}");
            }
            other => panic!("expected graph node count rejection, got {:?}", other),
        }
    }
}
