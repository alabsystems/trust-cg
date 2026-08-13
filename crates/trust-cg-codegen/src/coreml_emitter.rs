// trust-cg-codegen/coreml_emitter.rs - CoreML MIL operation emitter for ANE targeting
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Provides CoreML Model Intermediate Language (MIL) construction primitives.
// Production ComputeGraph-to-CoreML emission remains unavailable until TrustIR
// carries an exact tensor recipe; see COREML_COMPUTE_GRAPH_EMISSION_SUPPORTED.
//
// Design doc: designs/2026-04-14-coreml-ane-lowering.md
// Reference: Apple. "Core ML Model Specification." coremltools documentation.
// Reference: Apple. "MIL Ops." coremltools source, converters/mil/mil/ops.

//! CoreML Model Intermediate Language (MIL) operation generation for ANE targeting.
//!
//! This module provides typed MIL program construction primitives for Neural
//! Engine work. It does **not** currently provide a production TrustIR/
//! [`ComputeNode`] emission path: no exact compiler-derived CoreML tensor recipe
//! exists, so [`CoreMLEmitter::emit_program_from_nodes`] always fails closed
//! with [`CoreMLEmitError::NoExactCoreMlRecipe`] after validating the node's
//! semantic binding.
//!
//! # MIL construction primitives
//!
//! The low-level builder can represent:
//!
//! - **GEMM**: `mil.matmul(A, B)` -- general matrix multiply
//! - **Conv2D**: `mil.conv(input, weight, bias, ...)` -- 2D convolution
//! - **Activations**: relu, leaky_relu, sigmoid, tanh, gelu
//! - **Element-wise**: add, sub, mul, real_div
//! - **Reduce**: reduce_sum, reduce_mean, reduce_max, reduce_min
//!
//! # Fused Patterns
//!
//! Callers may construct fused MIL patterns such as GEMM+bias+ReLU and
//! MatMul+GELU directly. These primitives are not accelerator-placement or
//! semantic authority and are not reachable from production ComputeGraphs.

use std::fmt;

use trust_cg_lower::compute_graph::{AcceleratorBackend, ComputeNode, ComputeNodeId, NodeKind};

/// Whether production `ComputeNode` → CoreML MIL emission is available.
///
/// This remains `false` until TrustIR carries exact tensor operations, shapes,
/// attributes, and operand bindings and the graph builder derives a sealed
/// [`AcceleratorBackend::CoreMl`] recipe from them. Low-level MIL construction
/// helpers do not change this status.
pub const COREML_COMPUTE_GRAPH_EMISSION_SUPPORTED: bool = false;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors that can occur during CoreML MIL emission from ComputeGraph nodes.
#[derive(Debug, Clone)]
pub enum CoreMLEmitError {
    /// The node has no exact compiler-derived CoreML semantic binding, or its
    /// public metadata no longer matches that binding.
    SemanticBinding {
        node_id: ComputeNodeId,
        reason: String,
    },
    /// The current TrustIR vocabulary has no exactly representable CoreML
    /// recipe for this node.  Heuristic tensor-op inference is forbidden.
    NoExactCoreMlRecipe { node_id: ComputeNodeId },
    /// A NeuralEngine dispatch assignment references no graph node.
    MissingPlanNode { node_id: ComputeNodeId },
    /// A node is not legal on the NeuralEngine target.
    NotAneCompatible {
        node_id: ComputeNodeId,
        kind: NodeKind,
    },
    /// Empty node list provided.
    EmptyNodeList,
    /// A node references a predecessor that was not emitted yet.
    MissingPredecessor {
        node_id: ComputeNodeId,
        missing_dep: String,
    },
    /// Unsupported dominant operation for ANE lowering.
    UnsupportedOp { node_id: ComputeNodeId, op: String },
}

impl fmt::Display for CoreMLEmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CoreMLEmitError::SemanticBinding { node_id, reason } => {
                write!(
                    f,
                    "node {node_id} has no valid CoreML semantic binding: {reason}"
                )
            }
            CoreMLEmitError::NoExactCoreMlRecipe { node_id } => {
                write!(
                    f,
                    "node {node_id} has no exactly representable CoreML recipe"
                )
            }
            CoreMLEmitError::MissingPlanNode { node_id } => {
                write!(
                    f,
                    "CoreML dispatch plan references missing graph node {node_id}"
                )
            }
            CoreMLEmitError::NotAneCompatible { node_id, kind } => {
                write!(f, "node {} ({}) is not ANE-compatible", node_id, kind)
            }
            CoreMLEmitError::EmptyNodeList => write!(f, "empty node list"),
            CoreMLEmitError::MissingPredecessor {
                node_id,
                missing_dep,
            } => {
                write!(
                    f,
                    "node {} references missing predecessor '{}'",
                    node_id, missing_dep
                )
            }
            CoreMLEmitError::UnsupportedOp { node_id, op } => {
                write!(f, "node {} has unsupported op '{}' for ANE", node_id, op)
            }
        }
    }
}

impl std::error::Error for CoreMLEmitError {}

// ---------------------------------------------------------------------------
// MIL data types
// ---------------------------------------------------------------------------

/// CoreML MIL tensor element data type.
///
/// Maps to CoreML's `MLMultiArrayDataType` and MIL type annotations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MilDataType {
    /// IEEE 754 half-precision (FP16). Primary ANE type.
    Float16,
    /// IEEE 754 single-precision (FP32). Requires quantization for ANE.
    Float32,
    /// 32-bit signed integer. Limited ANE support.
    Int32,
}

impl fmt::Display for MilDataType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MilDataType::Float16 => write!(f, "fp16"),
            MilDataType::Float32 => write!(f, "fp32"),
            MilDataType::Int32 => write!(f, "i32"),
        }
    }
}

// ---------------------------------------------------------------------------
// Tensor shape for MIL
// ---------------------------------------------------------------------------

/// Static tensor shape for MIL operations (NCHW layout).
///
/// All dimensions must be known at compile time for ANE execution.
/// Mirrors `AneTensorShape` from `ane_semantics.rs` but decoupled from
/// the SMT encoding layer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MilTensorShape {
    /// Batch dimension (N). 1 for non-batched.
    pub batch: u64,
    /// Channel dimension (C).
    pub channels: u64,
    /// Height dimension (H).
    pub height: u64,
    /// Width dimension (W).
    pub width: u64,
}

impl MilTensorShape {
    /// Create a 2D matrix shape (M x N), stored as (1, 1, M, N) in NCHW.
    pub fn matrix(rows: u64, cols: u64) -> Self {
        MilTensorShape {
            batch: 1,
            channels: 1,
            height: rows,
            width: cols,
        }
    }

    /// Create a 4D tensor shape.
    pub fn tensor_4d(batch: u64, channels: u64, height: u64, width: u64) -> Self {
        MilTensorShape {
            batch,
            channels,
            height,
            width,
        }
    }

    /// Create a 1D vector shape (1, 1, 1, N).
    pub fn vector(length: u64) -> Self {
        MilTensorShape {
            batch: 1,
            channels: 1,
            height: 1,
            width: length,
        }
    }

    /// Total number of elements.
    pub fn numel(&self) -> u64 {
        self.batch * self.channels * self.height * self.width
    }

    /// Return shape as a 4-element array [N, C, H, W].
    pub fn dims(&self) -> [u64; 4] {
        [self.batch, self.channels, self.height, self.width]
    }

    /// Rank of the shape (number of non-trivial dimensions from the left).
    pub fn rank(&self) -> u32 {
        if self.batch > 1 {
            4
        } else if self.channels > 1 {
            3
        } else if self.height > 1 {
            2
        } else {
            1
        }
    }
}

impl fmt::Display for MilTensorShape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({}, {}, {}, {})",
            self.batch, self.channels, self.height, self.width
        )
    }
}

// ---------------------------------------------------------------------------
// MIL SSA values
// ---------------------------------------------------------------------------

/// An SSA value reference in the MIL program.
///
/// MIL is SSA-based: every value is defined exactly once and referenced by name.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MilValue {
    /// SSA name (e.g., "x_0", "matmul_1", "relu_2").
    pub name: String,
    /// Tensor shape (static).
    pub shape: MilTensorShape,
    /// Element data type.
    pub dtype: MilDataType,
}

impl MilValue {
    pub fn new(name: &str, shape: MilTensorShape, dtype: MilDataType) -> Self {
        MilValue {
            name: name.to_string(),
            shape,
            dtype,
        }
    }
}

// ---------------------------------------------------------------------------
// MIL operations
// ---------------------------------------------------------------------------

/// A single MIL operation in the program graph.
///
/// Each operation consumes SSA inputs and produces an SSA output.
/// The operation names and semantics follow Apple's MIL specification.
///
/// Ref: https://github.com/apple/coremltools/tree/main/coremltools/converters/mil/mil/ops
#[derive(Debug, Clone)]
pub enum MilOperation {
    /// `mil.matmul(x, y) -> tensor`
    MatMul {
        output: String,
        x: String,
        y: String,
        transpose_x: bool,
        transpose_y: bool,
    },

    /// `mil.conv(x, weight, bias, strides, pad_type, dilations, groups) -> tensor`
    Conv {
        output: String,
        x: String,
        weight: String,
        bias: Option<String>,
        strides: [u64; 2],
        pad_type: PadType,
        dilations: [u64; 2],
        groups: u64,
    },

    /// Element-wise binary: `mil.add`, `mil.sub`, `mil.mul`, `mil.real_div`.
    ElementWise {
        output: String,
        op: MilElementWiseOp,
        x: String,
        y: String,
    },

    /// Activation function: `mil.relu`, `mil.sigmoid`, etc.
    Activation {
        output: String,
        op: MilActivationOp,
        x: String,
    },

    /// Reduction: `mil.reduce_sum`, `mil.reduce_mean`, etc.
    Reduce {
        output: String,
        op: MilReduceOp,
        x: String,
        axes: Vec<i64>,
        keep_dims: bool,
    },

    /// Reshape: `mil.reshape(x, shape) -> tensor`
    Reshape {
        output: String,
        x: String,
        shape: Vec<i64>,
    },

    /// Transpose: `mil.transpose(x, perm) -> tensor`
    Transpose {
        output: String,
        x: String,
        perm: Vec<u32>,
    },
}

impl MilOperation {
    /// Return the output SSA name for this operation.
    pub fn output_name(&self) -> &str {
        match self {
            MilOperation::MatMul { output, .. } => output,
            MilOperation::Conv { output, .. } => output,
            MilOperation::ElementWise { output, .. } => output,
            MilOperation::Activation { output, .. } => output,
            MilOperation::Reduce { output, .. } => output,
            MilOperation::Reshape { output, .. } => output,
            MilOperation::Transpose { output, .. } => output,
        }
    }

    /// Return the MIL operation type name as a string.
    pub fn op_type(&self) -> &'static str {
        match self {
            MilOperation::MatMul { .. } => "matmul",
            MilOperation::Conv { .. } => "conv",
            MilOperation::ElementWise { op, .. } => op.mil_name(),
            MilOperation::Activation { op, .. } => op.mil_name(),
            MilOperation::Reduce { op, .. } => op.mil_name(),
            MilOperation::Reshape { .. } => "reshape",
            MilOperation::Transpose { .. } => "transpose",
        }
    }
}

// ---------------------------------------------------------------------------
// Sub-enums for operation variants
// ---------------------------------------------------------------------------

/// Element-wise binary operations in MIL.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MilElementWiseOp {
    Add,
    Sub,
    Mul,
    RealDiv,
}

impl MilElementWiseOp {
    /// MIL operation name.
    pub fn mil_name(&self) -> &'static str {
        match self {
            MilElementWiseOp::Add => "add",
            MilElementWiseOp::Sub => "sub",
            MilElementWiseOp::Mul => "mul",
            MilElementWiseOp::RealDiv => "real_div",
        }
    }
}

/// Activation functions supported by MIL / ANE.
#[derive(Debug, Clone, PartialEq)]
pub enum MilActivationOp {
    ReLU,
    LeakyReLU { alpha: f32 },
    Sigmoid,
    Tanh,
    GELU { mode: GeLUMode },
}

impl MilActivationOp {
    /// MIL operation name.
    pub fn mil_name(&self) -> &'static str {
        match self {
            MilActivationOp::ReLU => "relu",
            MilActivationOp::LeakyReLU { .. } => "leaky_relu",
            MilActivationOp::Sigmoid => "sigmoid",
            MilActivationOp::Tanh => "tanh",
            MilActivationOp::GELU { .. } => "gelu",
        }
    }
}

/// GELU approximation mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeLUMode {
    /// Exact: `x * 0.5 * (1 + erf(x / sqrt(2)))`.
    Exact,
    /// Tanh approximation (faster, used in BERT etc.).
    TanhApprox,
}

/// Reduction operations in MIL.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MilReduceOp {
    Sum,
    Mean,
    Max,
    Min,
}

impl MilReduceOp {
    /// MIL operation name.
    pub fn mil_name(&self) -> &'static str {
        match self {
            MilReduceOp::Sum => "reduce_sum",
            MilReduceOp::Mean => "reduce_mean",
            MilReduceOp::Max => "reduce_max",
            MilReduceOp::Min => "reduce_min",
        }
    }
}

/// Padding type for convolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PadType {
    /// No padding.
    Valid,
    /// Pad to preserve spatial dimensions.
    Same,
    /// Custom padding (specified separately).
    Custom,
}

impl fmt::Display for PadType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PadType::Valid => write!(f, "valid"),
            PadType::Same => write!(f, "same"),
            PadType::Custom => write!(f, "custom"),
        }
    }
}

// ---------------------------------------------------------------------------
// CoreML compute unit preference
// ---------------------------------------------------------------------------

/// CoreML compute unit routing preference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlComputeUnits {
    /// Let CoreML decide (default). May use CPU, GPU, or ANE.
    All,
    /// Prefer CPU + Neural Engine (skip GPU).
    CpuAndNeuralEngine,
    /// CPU only (fallback).
    CpuOnly,
}

// ---------------------------------------------------------------------------
// CoreML feature descriptor
// ---------------------------------------------------------------------------

/// A model input or output feature description.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreMLFeature {
    /// Feature name (matches model spec).
    pub name: String,
    /// Tensor shape (static, NCHW).
    pub shape: MilTensorShape,
    /// Element data type.
    pub dtype: MilDataType,
}

impl CoreMLFeature {
    pub fn new(name: &str, shape: MilTensorShape, dtype: MilDataType) -> Self {
        CoreMLFeature {
            name: name.to_string(),
            shape,
            dtype,
        }
    }
}

// ---------------------------------------------------------------------------
// MIL program (SSA operation graph)
// ---------------------------------------------------------------------------

/// A complete MIL program representing a CoreML model's computation.
///
/// The program is an ordered sequence of SSA operations with declared
/// inputs and outputs. It is serialized to protobuf for `.mlmodel` emission.
#[derive(Debug, Clone)]
pub struct MilProgram {
    /// Model inputs (feature descriptions).
    pub inputs: Vec<CoreMLFeature>,
    /// Model outputs (feature descriptions).
    pub outputs: Vec<CoreMLFeature>,
    /// Ordered sequence of MIL operations (SSA, topologically sorted).
    pub operations: Vec<MilOperation>,
    /// CoreML specification version (7+ for MIL support).
    pub spec_version: u32,
}

impl MilProgram {
    /// Create an empty MIL program with default spec version 8 (iOS 18).
    pub fn new() -> Self {
        MilProgram {
            inputs: Vec::new(),
            outputs: Vec::new(),
            operations: Vec::new(),
            spec_version: 8,
        }
    }

    /// Add an input feature to the model.
    pub fn add_input(&mut self, feature: CoreMLFeature) {
        self.inputs.push(feature);
    }

    /// Add an output feature to the model.
    pub fn add_output(&mut self, feature: CoreMLFeature) {
        self.outputs.push(feature);
    }

    /// Append an operation to the program.
    pub fn push_op(&mut self, op: MilOperation) {
        self.operations.push(op);
    }

    /// Return the total number of operations.
    pub fn op_count(&self) -> usize {
        self.operations.len()
    }

    /// Validate the program: check that all input references resolve to
    /// either program inputs or earlier operation outputs.
    ///
    /// Returns `Ok(())` if valid, or an error describing the first
    /// unresolved reference.
    pub fn validate(&self) -> Result<(), String> {
        let mut defined: std::collections::HashSet<&str> = std::collections::HashSet::new();

        // Program inputs are defined
        for inp in &self.inputs {
            defined.insert(&inp.name);
        }

        // Check each operation's inputs
        for op in &self.operations {
            let refs = op_input_refs(op);
            for r in &refs {
                if !defined.contains(r.as_str()) {
                    return Err(format!(
                        "MIL validation: operation '{}' references undefined value '{}'",
                        op.output_name(),
                        r,
                    ));
                }
            }
            defined.insert(op.output_name());
        }

        // Check outputs reference defined values
        for out in &self.outputs {
            if !defined.contains(out.name.as_str()) {
                return Err(format!(
                    "MIL validation: output '{}' references undefined value",
                    out.name,
                ));
            }
        }

        Ok(())
    }
}

impl Default for MilProgram {
    fn default() -> Self {
        Self::new()
    }
}

/// Collect all input SSA name references for an operation.
fn op_input_refs(op: &MilOperation) -> Vec<String> {
    match op {
        MilOperation::MatMul { x, y, .. } => vec![x.clone(), y.clone()],
        MilOperation::Conv {
            x, weight, bias, ..
        } => {
            let mut refs = vec![x.clone(), weight.clone()];
            if let Some(b) = bias {
                refs.push(b.clone());
            }
            refs
        }
        MilOperation::ElementWise { x, y, .. } => vec![x.clone(), y.clone()],
        MilOperation::Activation { x, .. } => vec![x.clone()],
        MilOperation::Reduce { x, .. } => vec![x.clone()],
        MilOperation::Reshape { x, .. } => vec![x.clone()],
        MilOperation::Transpose { x, .. } => vec![x.clone()],
    }
}

// ---------------------------------------------------------------------------
// CoreML MIL emitter
// ---------------------------------------------------------------------------

/// Emits MIL programs from ANE operation descriptors.
///
/// The emitter translates high-level ANE operations (matching those verified
/// by `ane_semantics.rs`) into MIL SSA operations. The resulting `MilProgram`
/// can be serialized to protobuf for `.mlmodel` output.
///
/// Ref: designs/2026-04-14-coreml-ane-lowering.md
pub struct CoreMLEmitter {
    /// Auto-incrementing counter for SSA value names.
    next_id: u32,
    /// Target data type for ANE operations.
    dtype: MilDataType,
}

impl CoreMLEmitter {
    /// Create a new emitter targeting FP16 by default.
    pub fn new() -> Self {
        CoreMLEmitter {
            next_id: 0,
            dtype: MilDataType::Float16,
        }
    }

    /// Create a new emitter with a specified data type.
    pub fn with_dtype(dtype: MilDataType) -> Self {
        CoreMLEmitter { next_id: 0, dtype }
    }

    /// Generate a fresh SSA name with the given prefix.
    fn fresh_name(&mut self, prefix: &str) -> String {
        let name = format!("{}_{}", prefix, self.next_id);
        self.next_id += 1;
        name
    }

    /// Emit a matrix multiply operation: `C = matmul(A, B)`.
    ///
    /// Corresponds to `encode_ane_gemm()` in `ane_semantics.rs`.
    pub fn emit_matmul(
        &mut self,
        program: &mut MilProgram,
        x: &str,
        y: &str,
        transpose_x: bool,
        transpose_y: bool,
    ) -> String {
        let name = self.fresh_name("matmul");
        program.push_op(MilOperation::MatMul {
            output: name.clone(),
            x: x.to_string(),
            y: y.to_string(),
            transpose_x,
            transpose_y,
        });
        name
    }

    /// Emit an element-wise binary operation.
    ///
    /// Corresponds to `encode_ane_elementwise()` in `ane_semantics.rs`.
    pub fn emit_elementwise(
        &mut self,
        program: &mut MilProgram,
        op: MilElementWiseOp,
        x: &str,
        y: &str,
    ) -> String {
        let name = self.fresh_name(op.mil_name());
        program.push_op(MilOperation::ElementWise {
            output: name.clone(),
            op,
            x: x.to_string(),
            y: y.to_string(),
        });
        name
    }

    /// Emit an activation function.
    ///
    /// Corresponds to `encode_ane_activation()` in `ane_semantics.rs`.
    pub fn emit_activation(
        &mut self,
        program: &mut MilProgram,
        op: MilActivationOp,
        x: &str,
    ) -> String {
        let name = self.fresh_name(op.mil_name());
        program.push_op(MilOperation::Activation {
            output: name.clone(),
            op,
            x: x.to_string(),
        });
        name
    }

    /// Emit a 2D convolution operation.
    ///
    /// Corresponds to `encode_ane_conv2d()` in `ane_semantics.rs`.
    pub fn emit_conv2d(
        &mut self,
        program: &mut MilProgram,
        x: &str,
        weight: &str,
        bias: Option<&str>,
        strides: [u64; 2],
        pad_type: PadType,
        dilations: [u64; 2],
        groups: u64,
    ) -> String {
        let name = self.fresh_name("conv");
        program.push_op(MilOperation::Conv {
            output: name.clone(),
            x: x.to_string(),
            weight: weight.to_string(),
            bias: bias.map(|s| s.to_string()),
            strides,
            pad_type,
            dilations,
            groups,
        });
        name
    }

    /// Emit a reduction operation.
    pub fn emit_reduce(
        &mut self,
        program: &mut MilProgram,
        op: MilReduceOp,
        x: &str,
        axes: &[i64],
        keep_dims: bool,
    ) -> String {
        let name = self.fresh_name(op.mil_name());
        program.push_op(MilOperation::Reduce {
            output: name.clone(),
            op,
            x: x.to_string(),
            axes: axes.to_vec(),
            keep_dims,
        });
        name
    }

    /// Emit a fused GEMM + bias + ReLU pattern (single ANE pass).
    ///
    /// This is a common fusion pattern that CoreML recognizes and maps to
    /// a single ANE pass for maximum throughput.
    pub fn emit_gemm_bias_relu(
        &mut self,
        program: &mut MilProgram,
        x: &str,
        weight: &str,
        bias: &str,
    ) -> String {
        let mm = self.emit_matmul(program, x, weight, false, false);
        let add = self.emit_elementwise(program, MilElementWiseOp::Add, &mm, bias);
        self.emit_activation(program, MilActivationOp::ReLU, &add)
    }

    /// Emit a fused MatMul + GELU pattern (single ANE pass).
    pub fn emit_matmul_gelu(&mut self, program: &mut MilProgram, x: &str, weight: &str) -> String {
        let mm = self.emit_matmul(program, x, weight, false, false);
        self.emit_activation(
            program,
            MilActivationOp::GELU {
                mode: GeLUMode::Exact,
            },
            &mm,
        )
    }

    /// Return the current SSA counter (for testing/debugging).
    pub fn next_id(&self) -> u32 {
        self.next_id
    }

    /// Return the target data type.
    pub fn dtype(&self) -> MilDataType {
        self.dtype
    }
}

impl Default for CoreMLEmitter {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// ComputeGraph -> MIL program generation
// ---------------------------------------------------------------------------

impl CoreMLEmitter {
    /// Attempt production MIL generation from ANE-targeted ComputeNodes.
    ///
    /// Current status is explicitly unsupported: the method validates that the
    /// first node carries a sealed CoreML binding, then returns
    /// [`CoreMLEmitError::NoExactCoreMlRecipe`]. It must not infer tensor
    /// semantics from node kinds, dominant-operation strings, or cost metadata.
    /// See [`COREML_COMPUTE_GRAPH_EMISSION_SUPPORTED`].
    pub fn emit_program_from_nodes(
        &mut self,
        nodes: &[ComputeNode],
    ) -> Result<MilProgram, CoreMLEmitError> {
        let node = nodes.first().ok_or(CoreMLEmitError::EmptyNodeList)?;
        let recipe = node
            .validated_accelerator_recipe(AcceleratorBackend::CoreMl)
            .map_err(|error| CoreMLEmitError::SemanticBinding {
                node_id: node.id,
                reason: error.to_string(),
            })?;

        // No TrustIR instruction currently denotes CoreML's tensor-level
        // matmul/conv/activation/batch-normalization semantics together with
        // their complete shapes and attributes.  In particular, a scalar or
        // vector BinOp is not a GEMM, a dominant-op string is not semantics,
        // and repeating one operand is not a binary-input binding.  Keep this
        // boundary closed until GraphBuilder grows a dedicated, exact CoreML
        // recipe and this match consumes all of its fields.
        let _ = recipe;
        Err(CoreMLEmitError::NoExactCoreMlRecipe { node_id: node.id })
    }
}

// ---------------------------------------------------------------------------
// ANE compatibility validation
// ---------------------------------------------------------------------------

/// ANE-compatible MIL operation types.
///
/// Operations outside this set will be rejected by the ANE compiler and
/// fall back to CPU/GPU execution, defeating the purpose of ANE targeting.
const ANE_COMPATIBLE_OPS: &[&str] = &[
    "matmul",
    "conv",
    "add",
    "sub",
    "mul",
    "real_div",
    "relu",
    "leaky_relu",
    "sigmoid",
    "tanh",
    "gelu",
    "reduce_sum",
    "reduce_mean",
    "reduce_max",
    "reduce_min",
    "reshape",
    "transpose",
];

/// Validate that all operations in a MIL program are ANE-compatible.
///
/// Returns a list of warning messages for operations that are not known
/// to run efficiently on the Apple Neural Engine. An empty list means
/// the program is fully ANE-compatible.
///
/// Checks performed:
/// 1. All operation types are in the ANE-compatible set
/// 2. Data types are FP16 (primary ANE type) or FP32 (requires quantization)
/// 3. No unsupported reduction axes configurations
pub fn validate_ane_compatibility(program: &MilProgram) -> Vec<String> {
    let mut warnings = Vec::new();

    // Check operation types
    for (idx, op) in program.operations.iter().enumerate() {
        let op_type = op.op_type();
        if !ANE_COMPATIBLE_OPS.contains(&op_type) {
            warnings.push(format!(
                "op[{}] '{}' (type '{}') is not in ANE-compatible op set",
                idx,
                op.output_name(),
                op_type,
            ));
        }
    }

    // Check input data types
    for input in &program.inputs {
        if input.dtype == MilDataType::Int32 {
            warnings.push(format!(
                "input '{}' uses Int32 which has limited ANE support; prefer Float16",
                input.name,
            ));
        }
    }

    // Check output data types
    for output in &program.outputs {
        if output.dtype == MilDataType::Int32 {
            warnings.push(format!(
                "output '{}' uses Int32 which has limited ANE support; prefer Float16",
                output.name,
            ));
        }
    }

    // Check for excessive reduction dimensions (ANE prefers single-axis reductions)
    for (idx, op) in program.operations.iter().enumerate() {
        if let MilOperation::Reduce { axes, .. } = op
            && axes.len() > 2
        {
            warnings.push(format!(
                "op[{}] '{}' reduces over {} axes; ANE may fall back to CPU for >2 axes",
                idx,
                op.output_name(),
                axes.len(),
            ));
        }
    }

    warnings
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use trust_cg_lower::target_analysis::ComputeTarget;

    #[test]
    fn test_mil_tensor_shape_matrix() {
        let shape = MilTensorShape::matrix(64, 128);
        assert_eq!(shape.numel(), 64 * 128);
        assert_eq!(shape.dims(), [1, 1, 64, 128]);
        assert_eq!(shape.rank(), 2);
    }

    #[test]
    fn test_mil_tensor_shape_4d() {
        let shape = MilTensorShape::tensor_4d(2, 3, 224, 224);
        assert_eq!(shape.numel(), 2 * 3 * 224 * 224);
        assert_eq!(shape.rank(), 4);
        assert_eq!(shape.to_string(), "(2, 3, 224, 224)");
    }

    #[test]
    fn test_mil_data_type_display() {
        assert_eq!(MilDataType::Float16.to_string(), "fp16");
        assert_eq!(MilDataType::Float32.to_string(), "fp32");
        assert_eq!(MilDataType::Int32.to_string(), "i32");
    }

    #[test]
    fn test_emitter_matmul() {
        let mut emitter = CoreMLEmitter::new();
        let mut program = MilProgram::new();
        program.add_input(CoreMLFeature::new(
            "A",
            MilTensorShape::matrix(64, 32),
            MilDataType::Float16,
        ));
        program.add_input(CoreMLFeature::new(
            "B",
            MilTensorShape::matrix(32, 64),
            MilDataType::Float16,
        ));

        let out = emitter.emit_matmul(&mut program, "A", "B", false, false);
        assert_eq!(out, "matmul_0");
        assert_eq!(program.op_count(), 1);
        assert_eq!(program.operations[0].op_type(), "matmul");
    }

    #[test]
    fn test_emitter_elementwise_chain() {
        let mut emitter = CoreMLEmitter::new();
        let mut program = MilProgram::new();
        program.add_input(CoreMLFeature::new(
            "x",
            MilTensorShape::vector(1024),
            MilDataType::Float16,
        ));
        program.add_input(CoreMLFeature::new(
            "y",
            MilTensorShape::vector(1024),
            MilDataType::Float16,
        ));

        let add = emitter.emit_elementwise(&mut program, MilElementWiseOp::Add, "x", "y");
        assert_eq!(add, "add_0");

        let relu = emitter.emit_activation(&mut program, MilActivationOp::ReLU, &add);
        assert_eq!(relu, "relu_1");
        assert_eq!(program.op_count(), 2);
    }

    #[test]
    fn test_gemm_bias_relu_fusion() {
        let mut emitter = CoreMLEmitter::new();
        let mut program = MilProgram::new();
        program.add_input(CoreMLFeature::new(
            "x",
            MilTensorShape::matrix(128, 64),
            MilDataType::Float16,
        ));
        program.add_input(CoreMLFeature::new(
            "w",
            MilTensorShape::matrix(64, 32),
            MilDataType::Float16,
        ));
        program.add_input(CoreMLFeature::new(
            "b",
            MilTensorShape::vector(32),
            MilDataType::Float16,
        ));

        let out = emitter.emit_gemm_bias_relu(&mut program, "x", "w", "b");

        // Should produce 3 operations: matmul, add, relu
        assert_eq!(program.op_count(), 3);
        assert_eq!(program.operations[0].op_type(), "matmul");
        assert_eq!(program.operations[1].op_type(), "add");
        assert_eq!(program.operations[2].op_type(), "relu");
        assert_eq!(out, "relu_2");
    }

    #[test]
    fn test_program_validate_ok() {
        let mut emitter = CoreMLEmitter::new();
        let mut program = MilProgram::new();
        program.add_input(CoreMLFeature::new(
            "x",
            MilTensorShape::vector(100),
            MilDataType::Float16,
        ));

        let relu_name = emitter.emit_activation(&mut program, MilActivationOp::ReLU, "x");
        program.add_output(CoreMLFeature::new(
            &relu_name,
            MilTensorShape::vector(100),
            MilDataType::Float16,
        ));

        assert!(program.validate().is_ok());
    }

    #[test]
    fn test_program_validate_undefined_ref() {
        let mut emitter = CoreMLEmitter::new();
        let mut program = MilProgram::new();
        // No inputs defined — "x" is undefined
        let _relu = emitter.emit_activation(&mut program, MilActivationOp::ReLU, "x");

        let result = program.validate();
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("undefined value 'x'"));
    }

    #[test]
    fn test_conv2d_emission() {
        let mut emitter = CoreMLEmitter::new();
        let mut program = MilProgram::new();
        program.add_input(CoreMLFeature::new(
            "input",
            MilTensorShape::tensor_4d(1, 3, 224, 224),
            MilDataType::Float16,
        ));
        program.add_input(CoreMLFeature::new(
            "weight",
            MilTensorShape::tensor_4d(64, 3, 7, 7),
            MilDataType::Float16,
        ));

        let out = emitter.emit_conv2d(
            &mut program,
            "input",
            "weight",
            None,
            [2, 2],
            PadType::Same,
            [1, 1],
            1,
        );

        assert_eq!(out, "conv_0");
        assert_eq!(program.op_count(), 1);
        if let MilOperation::Conv {
            pad_type, strides, ..
        } = &program.operations[0]
        {
            assert_eq!(*pad_type, PadType::Same);
            assert_eq!(*strides, [2, 2]);
        } else {
            panic!("expected Conv operation");
        }
    }

    fn forged_ane_node(dominant_op: &str) -> ComputeNode {
        let mut costs = HashMap::new();
        costs.insert(
            ComputeTarget::NeuralEngine,
            trust_cg_lower::compute_graph::ComputeCost {
                latency_cycles: 1,
                throughput_ops_per_kcycle: 1,
            },
        );
        ComputeNode {
            id: ComputeNodeId(7),
            instructions: vec![],
            costs,
            legal_targets: vec![ComputeTarget::NeuralEngine],
            kind: NodeKind::MatrixHeavy,
            data_size_bytes: 1 << 20,
            produced_values: vec![],
            consumed_values: vec![],
            dominant_op: dominant_op.to_string(),
            target_legality: None,
            matmul_shape: Some(trust_cg_lower::compute_graph::MatMulShape::new(
                64,
                64,
                64,
                trust_cg_lower::types::Type::F32,
            )),
        }
    }

    #[test]
    fn emit_program_from_nodes_rejects_empty_input() {
        let error = CoreMLEmitter::new()
            .emit_program_from_nodes(&[])
            .expect_err("empty ANE node list must fail");
        assert!(matches!(error, CoreMLEmitError::EmptyNodeList));
    }

    #[test]
    fn forged_legal_target_and_dominant_op_cannot_mint_coreml_semantics() {
        for op in ["GEMM", "CONV2D", "BATCHNORM", "RELU", "ADD", "UNKNOWN"] {
            let error = CoreMLEmitter::new()
                .emit_program_from_nodes(&[forged_ane_node(op)])
                .expect_err("caller-authored operation labels must not emit MIL");
            assert!(matches!(error, CoreMLEmitError::SemanticBinding { .. }));
        }
    }

    #[test]
    fn heuristic_binary_same_operand_lowering_is_unreachable() {
        let mut forged = forged_ane_node("ADD");
        forged.consumed_values = vec![trust_cg_lower::compute_graph::TrustIrValueId::new(
            0,
            trust_ir::ValueId::new(9),
        )];
        let error = CoreMLEmitter::new()
            .emit_program_from_nodes(&[forged])
            .expect_err("one input cannot be silently reused as both binary operands");
        assert!(matches!(error, CoreMLEmitError::SemanticBinding { .. }));
    }

    // -----------------------------------------------------------------------
    // validate_ane_compatibility tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_ane_all_compatible() {
        let mut program = MilProgram::new();
        program.add_input(CoreMLFeature::new(
            "x",
            MilTensorShape::vector(64),
            MilDataType::Float16,
        ));
        let mut emitter = CoreMLEmitter::new();
        let out = emitter.emit_activation(&mut program, MilActivationOp::ReLU, "x");
        program.add_output(CoreMLFeature::new(
            &out,
            MilTensorShape::vector(64),
            MilDataType::Float16,
        ));

        let warnings = validate_ane_compatibility(&program);
        assert!(
            warnings.is_empty(),
            "expected no warnings, got: {:?}",
            warnings
        );
    }

    #[test]
    fn test_validate_ane_int32_warning() {
        let mut program = MilProgram::new();
        program.add_input(CoreMLFeature::new(
            "x",
            MilTensorShape::vector(64),
            MilDataType::Int32,
        ));
        let mut emitter = CoreMLEmitter::with_dtype(MilDataType::Float16);
        let out = emitter.emit_activation(&mut program, MilActivationOp::ReLU, "x");
        program.add_output(CoreMLFeature::new(
            &out,
            MilTensorShape::vector(64),
            MilDataType::Float16,
        ));

        let warnings = validate_ane_compatibility(&program);
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].contains("Int32"));
    }

    #[test]
    fn test_validate_ane_multi_axis_reduce_warning() {
        let mut program = MilProgram::new();
        program.add_input(CoreMLFeature::new(
            "x",
            MilTensorShape::tensor_4d(1, 3, 8, 8),
            MilDataType::Float16,
        ));
        program.push_op(MilOperation::Reduce {
            output: "reduce_0".to_string(),
            op: MilReduceOp::Sum,
            x: "x".to_string(),
            axes: vec![1, 2, 3], // 3 axes -- triggers warning
            keep_dims: false,
        });
        program.add_output(CoreMLFeature::new(
            "reduce_0",
            MilTensorShape::vector(1),
            MilDataType::Float16,
        ));

        let warnings = validate_ane_compatibility(&program);
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].contains("3 axes"));
    }
}
