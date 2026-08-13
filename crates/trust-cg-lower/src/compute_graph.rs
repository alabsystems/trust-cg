// trust-cg-lower/compute_graph.rs - Computation graph analysis for heterogeneous compute
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-13-heterogeneous-compute.md (Computation Graph Analysis)
//
// Builds a computation graph from trust_ir programs: a DAG of ComputeNodes
// connected by DataEdges. Each node represents a group of instructions
// that can be assigned to a compute target (CPU, SIMD, GPU, ANE). Edges
// carry data dependency and transfer cost information.
//
// Pattern detection identifies:
// - Data-parallel regions (map/reduce over arrays)
// - Matrix-heavy regions (nested loops with multiply-accumulate)
// - Sequential scalar ops (grouped into CPU nodes)

//! Computation graph analysis for heterogeneous compute allocation.
//!
//! This module implements Phase 1 of the heterogeneous compute pipeline:
//! building a computation graph from trust_ir and identifying regions suitable
//! for different compute targets.
//!
//! Production accelerator placement remains fail-closed without validator
//! replay authority. Metal has one narrow exact recipe shape; CoreML currently
//! has no exact recipe constructor, so Neural Engine graph emission is an
//! explicitly unsupported capability rather than an inferred fallback.
//!
//! # Architecture
//!
//! ```text
//! trust_ir Module
//!     |
//!     v
//! GraphBuilder::build_from_module()
//!     |
//!     v
//! ComputeGraph { nodes: Vec<ComputeNode>, edges: Vec<DataEdge> }
//!     |
//!     v
//! partition_cost() -- evaluate a target assignment
//! ```

use std::collections::{HashMap, HashSet};
use std::fmt;

use serde::{Deserialize, Serialize};

use trust_ir::proof::ProofDigest;
use trust_ir::{BinOp, BlockId, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId};

use crate::instructions::Value;
use crate::target_analysis::{
    ComputeTarget, ProofAnalyzer, SubgraphDescriptor, SubgraphId, TargetLegality,
    TargetProofContext,
};
use crate::types::Type as LirType;

use trust_cg_ir::cost_model::{
    ComputeTarget as CostComputeTarget, CostModelGen, ProfitabilityAnalyzer,
};

// ---------------------------------------------------------------------------
// Node and edge identifiers
// ---------------------------------------------------------------------------

/// Unique identifier for a node in the computation graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ComputeNodeId(pub u32);

impl fmt::Display for ComputeNodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "node_{}", self.0)
    }
}

/// Unique identifier for an edge in the computation graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DataEdgeId(pub u32);

// ---------------------------------------------------------------------------
// Instruction identifier within trust_ir
// ---------------------------------------------------------------------------

/// A reference to a trust_ir instruction within the computation graph.
///
/// Identifies an instruction by its containing function, block, and
/// instruction index within that block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TrustIrInstId {
    /// Index of the function in the module.
    pub func_idx: u32,
    /// Block ID within the function.
    pub block_id: u32,
    /// Instruction index within the block body.
    pub inst_idx: u32,
}

/// A module-stable reference to one function-local TrustIR SSA value.
///
/// [`ValueId`] numbering restarts in every TrustIR function.  Compute graphs
/// span a whole module, so carrying a bare `ValueId` aliases unrelated values
/// from different functions and can create false dependency edges or bind an
/// accelerator kernel to another function's buffer.  This identity is used at
/// every graph, recipe, and launch boundary where values outlive the local
/// function walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TrustIrValueId {
    /// Index of the owning function in the module.
    pub func_idx: u32,
    /// Function-local SSA value identifier.
    pub value_id: ValueId,
}

impl TrustIrValueId {
    /// Bind a function-local value to its owning module function.
    pub const fn new(func_idx: u32, value_id: ValueId) -> Self {
        Self { func_idx, value_id }
    }

    /// Stable numeric key for generated host buffer maps.
    ///
    /// Both components are 32-bit, so this packing is injective and has no
    /// truncation or hashing collision.
    pub fn stable_key(self) -> u64 {
        (u64::from(self.func_idx) << 32) | u64::from(self.value_id.index())
    }
}

impl fmt::Display for TrustIrValueId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "func_{}:%{}", self.func_idx, self.value_id.index())
    }
}

// ---------------------------------------------------------------------------
// Cost types (cycle-count based for deterministic testing)
// ---------------------------------------------------------------------------

/// Estimated computation cost on a single target, measured in cycles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ComputeCost {
    /// Estimated execution latency in cycles.
    pub latency_cycles: u64,
    /// Estimated throughput in operations per kilocycle.
    pub throughput_ops_per_kcycle: u64,
}

impl Default for ComputeCost {
    fn default() -> Self {
        Self {
            latency_cycles: 1,
            throughput_ops_per_kcycle: 1000,
        }
    }
}

/// Cost of transferring data between compute targets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TransferCost {
    /// Fixed overhead in cycles (e.g., kernel launch latency).
    pub overhead_cycles: u64,
    /// Per-byte transfer cost in nanocycles (cycles * 1e9 / byte).
    /// Use nanocycles to avoid floating point.
    pub per_byte_nanocycles: u64,
    /// Total estimated cost in cycles.
    pub total_cycles: u64,
}

impl TransferCost {
    /// Compute transfer cost for a given byte count.
    pub fn for_bytes(bytes: u64, overhead: u64, per_byte_nanocycles: u64) -> Self {
        let transfer_cycles = bytes.saturating_mul(per_byte_nanocycles) / 1_000_000_000;
        Self {
            overhead_cycles: overhead,
            per_byte_nanocycles,
            total_cycles: overhead.saturating_add(transfer_cycles),
        }
    }

    /// Zero cost (same-target transfer).
    pub fn zero() -> Self {
        Self {
            overhead_cycles: 0,
            per_byte_nanocycles: 0,
            total_cycles: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Node classification
// ---------------------------------------------------------------------------

/// Classification of a computation node's workload pattern.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NodeKind {
    /// Sequential scalar operations (best on CPU scalar).
    Scalar,
    /// Data-parallel operations (map/reduce over arrays).
    /// Candidates for SIMD or GPU.
    DataParallel,
    /// Matrix-heavy operations (multiply-accumulate patterns).
    /// Candidates for GPU or Neural Engine.
    MatrixHeavy,
}

impl fmt::Display for NodeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeKind::Scalar => write!(f, "Scalar"),
            NodeKind::DataParallel => write!(f, "DataParallel"),
            NodeKind::MatrixHeavy => write!(f, "MatrixHeavy"),
        }
    }
}

// ---------------------------------------------------------------------------
// MatMul shape (issue #404)
// ---------------------------------------------------------------------------

/// Explicit shape for a `NodeKind::MatrixHeavy` compute node.
///
/// For C = A * B where:
///   * A is `m` rows by `k` columns,
///   * B is `k` rows by `n` columns,
///   * C is `m` rows by `n` columns.
///
/// Issue #404: Structural shape metadata for matrix-heavy cost modeling and
/// future exact lowering.  The sealed Metal node-emission path does not
/// consume this field: it currently accepts only an exact typed elementwise
/// recipe and refuses `MatrixHeavy` nodes fail-closed.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MatMulShape {
    /// Rows of A (and C).
    pub m: u64,
    /// Columns of A / rows of B (contracted dimension).
    pub k: u64,
    /// Columns of B (and C).
    pub n: u64,
    /// Element type (used to compute buffer sizes and choose MSL scalar).
    pub elem_type: LirType,
}

// ---------------------------------------------------------------------------
// Compiler-derived accelerator semantics
// ---------------------------------------------------------------------------

/// Accelerator backend for which an exact semantic recipe was derived.
///
/// This is deliberately distinct from [`ComputeTarget`].  A target-legality
/// judgment says that moving a computation is permitted; a semantic recipe
/// says exactly what code may be emitted after that move.  Both are required.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AcceleratorBackend {
    /// Metal compute kernel emission.
    Metal,
    /// Reserved CoreML MIL backend identity. No production exact CoreML recipe
    /// is currently derivable, so this variant cannot authorize emission.
    CoreMl,
}

/// Scalar element types whose accelerator semantics are represented exactly.
///
/// The first production recipe is intentionally narrow.  Unsigned 32-bit
/// arithmetic has the same modulo-2^32 semantics in TrustIR and Metal.  Signed
/// overflow and floating-point contraction/denormal behavior require a richer
/// target-semantics contract and therefore remain fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AcceleratorElementType {
    U32,
}

/// Exact element-wise binary operations supported by the semantic recipe.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AcceleratorBinaryOp {
    Add,
    Sub,
    Mul,
}

/// Exact operation carried by a compiler-derived accelerator recipe.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AcceleratorOperation {
    /// Pointwise binary operation over two distinct, equally-shaped arrays.
    ElementwiseBinary {
        op: AcceleratorBinaryOp,
        elem_type: AcceleratorElementType,
        element_count: u64,
        lhs: TrustIrValueId,
        rhs: TrustIrValueId,
        result: TrustIrValueId,
    },
}

/// Opaque compiler-derived binding from a TrustIR subgraph to accelerator
/// semantics.
///
/// All fields are private and there is no public constructor.  Consequently a
/// caller can construct a [`ComputeNode`] or deserialize a [`ComputeGraph`],
/// but cannot mint accelerator-emission authority.  The recipe is installed
/// only by [`GraphBuilder`] and lives in the non-serialized target-legality
/// record.  It binds the semantic operation to the exact node, instruction
/// identities, classification, size, and diagnostic operation spelling so
/// mutating any of those public fields cannot retarget the recipe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AcceleratorSemanticRecipe {
    backend: AcceleratorBackend,
    node_id: ComputeNodeId,
    instructions: Vec<TrustIrInstId>,
    kind: NodeKind,
    data_size_bytes: u64,
    dominant_op: String,
    produced_values: Vec<TrustIrValueId>,
    consumed_values: Vec<TrustIrValueId>,
    operation: AcceleratorOperation,
    target_authorized: bool,
    semantic_digest: ProofDigest,
}

struct AcceleratorDigestInput<'a> {
    backend: AcceleratorBackend,
    node_id: ComputeNodeId,
    instructions: &'a [TrustIrInstId],
    kind: NodeKind,
    data_size_bytes: u64,
    dominant_op: &'a str,
    produced_values: &'a [TrustIrValueId],
    consumed_values: &'a [TrustIrValueId],
    operation: &'a AcceleratorOperation,
    target_authorized: bool,
}

impl AcceleratorSemanticRecipe {
    fn canonical_digest(input: AcceleratorDigestInput<'_>) -> ProofDigest {
        let AcceleratorDigestInput {
            backend,
            node_id,
            instructions,
            kind,
            data_size_bytes,
            dominant_op,
            produced_values,
            consumed_values,
            operation,
            target_authorized,
        } = input;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(b"trust-cg.accelerator-recipe.v1\0");
        bytes.push(match backend {
            AcceleratorBackend::Metal => 1,
            AcceleratorBackend::CoreMl => 2,
        });
        bytes.extend_from_slice(&node_id.0.to_be_bytes());
        bytes.extend_from_slice(
            &u64::try_from(instructions.len())
                .expect("accelerator recipe instruction count exceeds u64")
                .to_be_bytes(),
        );
        for id in instructions {
            bytes.extend_from_slice(&id.func_idx.to_be_bytes());
            bytes.extend_from_slice(&id.block_id.to_be_bytes());
            bytes.extend_from_slice(&id.inst_idx.to_be_bytes());
        }
        bytes.push(match kind {
            NodeKind::Scalar => 1,
            NodeKind::DataParallel => 2,
            NodeKind::MatrixHeavy => 3,
        });
        bytes.extend_from_slice(&data_size_bytes.to_be_bytes());
        bytes.extend_from_slice(
            &u64::try_from(dominant_op.len())
                .expect("accelerator recipe operation spelling exceeds u64")
                .to_be_bytes(),
        );
        bytes.extend_from_slice(dominant_op.as_bytes());
        bytes.push(u8::from(target_authorized));
        for values in [produced_values, consumed_values] {
            bytes.extend_from_slice(
                &u64::try_from(values.len())
                    .expect("accelerator recipe value count exceeds u64")
                    .to_be_bytes(),
            );
            for value in values {
                bytes.extend_from_slice(&value.func_idx.to_be_bytes());
                bytes.extend_from_slice(&value.value_id.index().to_be_bytes());
            }
        }
        match operation {
            AcceleratorOperation::ElementwiseBinary {
                op,
                elem_type,
                element_count,
                lhs,
                rhs,
                result,
            } => {
                bytes.push(1);
                bytes.push(match op {
                    AcceleratorBinaryOp::Add => 1,
                    AcceleratorBinaryOp::Sub => 2,
                    AcceleratorBinaryOp::Mul => 3,
                });
                bytes.push(match elem_type {
                    AcceleratorElementType::U32 => 1,
                });
                bytes.extend_from_slice(&element_count.to_be_bytes());
                bytes.extend_from_slice(&lhs.func_idx.to_be_bytes());
                bytes.extend_from_slice(&lhs.value_id.index().to_be_bytes());
                bytes.extend_from_slice(&rhs.func_idx.to_be_bytes());
                bytes.extend_from_slice(&rhs.value_id.index().to_be_bytes());
                bytes.extend_from_slice(&result.func_idx.to_be_bytes());
                bytes.extend_from_slice(&result.value_id.index().to_be_bytes());
            }
        }
        ProofDigest::sha256_domain("trust-cg.accelerator-semantic-recipe.v1", &bytes)
    }

    fn new_metal_elementwise(
        node_id: ComputeNodeId,
        instructions: Vec<TrustIrInstId>,
        data_size_bytes: u64,
        dominant_op: String,
        produced_values: Vec<TrustIrValueId>,
        consumed_values: Vec<TrustIrValueId>,
        operation: AcceleratorOperation,
    ) -> Self {
        let backend = AcceleratorBackend::Metal;
        let kind = NodeKind::DataParallel;
        let semantic_digest = Self::canonical_digest(AcceleratorDigestInput {
            backend,
            node_id,
            instructions: &instructions,
            kind,
            data_size_bytes,
            dominant_op: &dominant_op,
            produced_values: &produced_values,
            consumed_values: &consumed_values,
            operation: &operation,
            target_authorized: false,
        });
        Self {
            backend,
            node_id,
            instructions,
            kind,
            data_size_bytes,
            dominant_op,
            produced_values,
            consumed_values,
            operation,
            target_authorized: false,
            semantic_digest,
        }
    }

    fn bind_target_authority(&mut self, authorized: bool) {
        self.target_authorized = authorized;
        self.semantic_digest = Self::canonical_digest(AcceleratorDigestInput {
            backend: self.backend,
            node_id: self.node_id,
            instructions: &self.instructions,
            kind: self.kind,
            data_size_bytes: self.data_size_bytes,
            dominant_op: &self.dominant_op,
            produced_values: &self.produced_values,
            consumed_values: &self.consumed_values,
            operation: &self.operation,
            target_authorized: self.target_authorized,
        });
    }

    /// Backend authorized by this exact recipe.
    pub fn backend(&self) -> AcceleratorBackend {
        self.backend
    }

    /// Exact compiler-derived operation.  Emitters must consume this value,
    /// never infer semantics from `ComputeNode::dominant_op`.
    pub fn operation(&self) -> &AcceleratorOperation {
        &self.operation
    }

    /// Domain-separated SHA-256 of the complete canonical recipe binding.
    pub fn semantic_digest(&self) -> ProofDigest {
        self.semantic_digest
    }

    /// Compute node identity sealed into this recipe.
    pub fn node_id(&self) -> ComputeNodeId {
        self.node_id
    }

    /// Exact byte-size metadata sealed into this recipe.
    pub fn data_size_bytes(&self) -> u64 {
        self.data_size_bytes
    }

    fn validate_node_metadata(&self, node: &ComputeNode) -> Result<(), AcceleratorBindingError> {
        if self.node_id != node.id {
            return Err(AcceleratorBindingError::NodeIdentityMismatch {
                expected: self.node_id,
                actual: node.id,
            });
        }
        if self.instructions != node.instructions {
            return Err(AcceleratorBindingError::InstructionIdentityMismatch { node_id: node.id });
        }
        if self.kind != node.kind
            || self.data_size_bytes != node.data_size_bytes
            || self.dominant_op != node.dominant_op
            || self.produced_values != node.produced_values
            || self.consumed_values != node.consumed_values
            || node.matmul_shape.is_some()
        {
            return Err(AcceleratorBindingError::NodeMetadataMismatch { node_id: node.id });
        }
        let digest = Self::canonical_digest(AcceleratorDigestInput {
            backend: self.backend,
            node_id: self.node_id,
            instructions: &self.instructions,
            kind: self.kind,
            data_size_bytes: self.data_size_bytes,
            dominant_op: &self.dominant_op,
            produced_values: &self.produced_values,
            consumed_values: &self.consumed_values,
            operation: &self.operation,
            target_authorized: self.target_authorized,
        });
        if digest != self.semantic_digest {
            return Err(AcceleratorBindingError::SemanticDigestMismatch { node_id: node.id });
        }
        Ok(())
    }
}

/// Failure to establish compiler-derived authority for accelerator emission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AcceleratorBindingError {
    MissingCompilerBinding {
        node_id: ComputeNodeId,
    },
    BackendMismatch {
        node_id: ComputeNodeId,
        expected: AcceleratorBackend,
        actual: AcceleratorBackend,
    },
    NodeIdentityMismatch {
        expected: ComputeNodeId,
        actual: ComputeNodeId,
    },
    InstructionIdentityMismatch {
        node_id: ComputeNodeId,
    },
    NodeMetadataMismatch {
        node_id: ComputeNodeId,
    },
    SemanticDigestMismatch {
        node_id: ComputeNodeId,
    },
    TargetNotAuthorized {
        node_id: ComputeNodeId,
        target: ComputeTarget,
    },
}

impl fmt::Display for AcceleratorBindingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingCompilerBinding { node_id } => {
                write!(
                    f,
                    "node {node_id} has no compiler-derived accelerator semantic binding"
                )
            }
            Self::BackendMismatch {
                node_id,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "node {node_id} semantic binding is for {actual:?}, not {expected:?}"
                )
            }
            Self::NodeIdentityMismatch { expected, actual } => {
                write!(
                    f,
                    "accelerator semantic binding is for {expected}, not {actual}"
                )
            }
            Self::InstructionIdentityMismatch { node_id } => write!(
                f,
                "node {node_id} instruction identities do not match its accelerator binding"
            ),
            Self::NodeMetadataMismatch { node_id } => {
                write!(
                    f,
                    "node {node_id} metadata does not match its accelerator binding"
                )
            }
            Self::SemanticDigestMismatch { node_id } => {
                write!(
                    f,
                    "node {node_id} accelerator semantic binding digest does not verify"
                )
            }
            Self::TargetNotAuthorized { node_id, target } => {
                write!(
                    f,
                    "node {node_id} compiler analysis did not authorize target {target}"
                )
            }
        }
    }
}

impl std::error::Error for AcceleratorBindingError {}

impl MatMulShape {
    /// Create a new MatMulShape.
    pub fn new(m: u64, k: u64, n: u64, elem_type: LirType) -> Self {
        Self { m, k, n, elem_type }
    }

    /// Returns the total number of elements across A, B, C: `m*k + k*n + m*n`.
    pub fn total_elements(&self) -> u64 {
        self.m
            .saturating_mul(self.k)
            .saturating_add(self.k.saturating_mul(self.n))
            .saturating_add(self.m.saturating_mul(self.n))
    }

    /// Returns the total byte footprint of A + B + C given this shape's
    /// `elem_type`.
    pub fn total_bytes(&self) -> u64 {
        self.total_elements()
            .saturating_mul(self.elem_type.bytes() as u64)
    }

    /// Returns `true` if this is a square matmul (M == K == N).
    pub fn is_square(&self) -> bool {
        self.m == self.k && self.k == self.n
    }
}

// ---------------------------------------------------------------------------
// Core graph types
// ---------------------------------------------------------------------------

/// A node in the computation graph representing a group of trust_ir instructions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComputeNode {
    /// Unique node identifier.
    pub id: ComputeNodeId,
    /// The trust_ir instructions belonging to this subgraph.
    pub instructions: Vec<TrustIrInstId>,
    /// Estimated cost on each legal compute target.
    pub costs: HashMap<ComputeTarget, ComputeCost>,
    /// Which compute targets can legally execute this node.
    pub legal_targets: Vec<ComputeTarget>,
    /// Workload classification.
    pub kind: NodeKind,
    /// Estimated data size in bytes processed by this node.
    pub data_size_bytes: u64,
    /// Values produced by this node (used for edge construction).
    #[serde(skip)]
    pub produced_values: Vec<TrustIrValueId>,
    /// Values consumed by this node (used for edge construction).
    #[serde(skip)]
    pub consumed_values: Vec<TrustIrValueId>,
    /// Dominant operation name (e.g., "ADD", "MUL", "GEMM") for cost model queries.
    /// Derived from the most common instruction in the node.
    pub dominant_op: String,
    /// Full target legality analysis from ProofAnalyzer, including justifications,
    /// parallel reduction legality, and per-target judgments.
    /// `None` for manually constructed nodes that bypass proof analysis.
    #[serde(skip)]
    pub target_legality: Option<TargetLegality>,
    /// Explicit matmul shape for `NodeKind::MatrixHeavy` nodes (issue #404).
    ///
    /// For MatrixHeavy nodes this SHOULD be `Some` whenever M, K, N can be
    /// recovered from the trust_ir (e.g. loop-nest bounds).  It is currently
    /// diagnostic/cost metadata only: the sealed Metal emitter refuses
    /// `MatrixHeavy` nodes until an exact typed matrix recipe is available.
    ///
    /// For non-MatrixHeavy nodes this is always `None`.
    #[serde(default)]
    pub matmul_shape: Option<MatMulShape>,
}

impl ComputeNode {
    /// Return the exact compiler-derived recipe for `backend` after checking
    /// both semantic binding and target authority.
    ///
    /// Public node fields are intentionally treated as untrusted inputs.  In
    /// particular, adding GPU/ANE to `legal_targets`, changing
    /// `dominant_op`, or deserializing a node cannot satisfy this method.
    pub fn validated_accelerator_recipe(
        &self,
        backend: AcceleratorBackend,
    ) -> Result<&AcceleratorSemanticRecipe, AcceleratorBindingError> {
        let target = match backend {
            AcceleratorBackend::Metal => ComputeTarget::Gpu,
            AcceleratorBackend::CoreMl => ComputeTarget::NeuralEngine,
        };
        let legality = self
            .target_legality
            .as_ref()
            .ok_or(AcceleratorBindingError::MissingCompilerBinding { node_id: self.id })?;
        let recipe = legality
            .accelerator_recipe()
            .ok_or(AcceleratorBindingError::MissingCompilerBinding { node_id: self.id })?;
        if legality.subgraph != SubgraphId(self.id.0) || !legality.is_legal(target) {
            return Err(AcceleratorBindingError::TargetNotAuthorized {
                node_id: self.id,
                target,
            });
        }
        let analyzed_targets = legality.legal_targets();
        if analyzed_targets.len() != self.legal_targets.len()
            || analyzed_targets
                .iter()
                .any(|candidate| !self.legal_targets.contains(candidate))
        {
            return Err(AcceleratorBindingError::NodeMetadataMismatch { node_id: self.id });
        }
        if recipe.backend != backend {
            return Err(AcceleratorBindingError::BackendMismatch {
                node_id: self.id,
                expected: backend,
                actual: recipe.backend,
            });
        }
        if !recipe.target_authorized {
            return Err(AcceleratorBindingError::TargetNotAuthorized {
                node_id: self.id,
                target,
            });
        }
        recipe.validate_node_metadata(self)?;
        Ok(recipe)
    }
}

/// A data dependency edge between two computation nodes.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataEdge {
    /// Source node (producer).
    pub from: ComputeNodeId,
    /// Destination node (consumer).
    pub to: ComputeNodeId,
    /// Number of bytes that must be transferred if nodes are on different targets.
    pub transfer_bytes: u64,
    /// Transfer cost estimate (populated based on target pair).
    pub transfer_cost: TransferCost,
}

/// The computation graph: a DAG of nodes connected by data dependency edges.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComputeGraph {
    /// Computation nodes (subgraphs).
    pub nodes: Vec<ComputeNode>,
    /// Data dependency edges.
    pub edges: Vec<DataEdge>,
    /// Profitability analyzer for GPU/ANE dispatch decisions.
    /// Uses proper thresholds from the cost model instead of ad-hoc checks.
    #[serde(skip)]
    pub(crate) profitability: Option<ProfitabilityAnalyzer>,
    /// Whether the source trust_ir module's proof obligations are fully verified.
    ///
    /// Populated from `trust_ir::Module::proof_summary().is_fully_verified()` during
    /// graph construction. When false, downstream dispatch should be conservative
    /// (prefer CPU targets over GPU/ANE since proof status is incomplete).
    pub module_fully_verified: bool,
}

impl ComputeGraph {
    /// Create an empty computation graph.
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            profitability: None,
            module_fully_verified: false,
        }
    }

    /// Create an empty computation graph with a profitability analyzer.
    pub fn new_with_profitability(generation: CostModelGen) -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            profitability: Some(ProfitabilityAnalyzer::new(generation)),
            module_fully_verified: false,
        }
    }

    /// Set the profitability analyzer for this graph.
    pub fn set_profitability(&mut self, analyzer: ProfitabilityAnalyzer) {
        self.profitability = Some(analyzer);
    }

    /// Returns true if this graph has a profitability analyzer attached.
    pub fn has_profitability(&self) -> bool {
        self.profitability.is_some()
    }

    /// Get a node by ID.
    pub fn node(&self, id: ComputeNodeId) -> Option<&ComputeNode> {
        self.nodes.iter().find(|n| n.id == id)
    }

    /// Get all edges originating from a node.
    pub fn outgoing_edges(&self, node_id: ComputeNodeId) -> Vec<&DataEdge> {
        self.edges.iter().filter(|e| e.from == node_id).collect()
    }

    /// Get all edges targeting a node.
    pub fn incoming_edges(&self, node_id: ComputeNodeId) -> Vec<&DataEdge> {
        self.edges.iter().filter(|e| e.to == node_id).collect()
    }

    /// Compute the total cost of a target assignment (partition).
    ///
    /// Given a mapping from each node to a compute target, this returns
    /// the total cost = sum of compute costs + sum of transfer costs for
    /// edges between nodes on different targets.
    ///
    /// Returns `None` if any node is missing from the assignment or if
    /// the assigned target is not legal for that node.
    pub fn partition_cost(
        &self,
        assignment: &HashMap<ComputeNodeId, ComputeTarget>,
    ) -> Option<u64> {
        let mut total: u64 = 0;

        // Add compute costs for each node.
        for node in &self.nodes {
            let target = assignment.get(&node.id)?;
            if !node.legal_targets.contains(target) {
                return None; // Illegal assignment
            }
            let cost = node.costs.get(target)?;
            total = total.saturating_add(cost.latency_cycles);
        }

        // Add transfer costs for edges between different targets.
        for edge in &self.edges {
            let from_target = assignment.get(&edge.from)?;
            let to_target = assignment.get(&edge.to)?;
            if from_target != to_target {
                let transfer =
                    estimate_transfer_cost(edge.transfer_bytes, *from_target, *to_target);
                total = total.saturating_add(transfer.total_cycles);
            }
        }

        Some(total)
    }

    /// Number of nodes.
    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Number of edges.
    pub fn num_edges(&self) -> usize {
        self.edges.len()
    }
}

impl Default for ComputeGraph {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Target mapping: trust-cg-lower ComputeTarget <-> trust-cg-ir cost_model ComputeTarget
// ---------------------------------------------------------------------------

/// Map a `trust-cg-lower` ComputeTarget to the `trust-cg-ir::cost_model` ComputeTarget.
/// Returns `None` for targets with no direct cost model equivalent.
fn to_cost_target(target: ComputeTarget) -> Option<CostComputeTarget> {
    match target {
        ComputeTarget::CpuScalar => Some(CostComputeTarget::CpuScalar),
        ComputeTarget::CpuSimd => Some(CostComputeTarget::Neon),
        ComputeTarget::Gpu => Some(CostComputeTarget::Gpu),
        ComputeTarget::NeuralEngine => Some(CostComputeTarget::Ane),
    }
}

/// Convert a BinOp to the operation name string used by ProfitabilityAnalyzer.
fn binop_to_op_name(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "ADD",
        BinOp::Sub => "SUB",
        BinOp::Mul => "MUL",
        BinOp::SDiv => "SDIV",
        BinOp::UDiv => "UDIV",
        BinOp::SRem => "SDIV", // closest equivalent
        BinOp::URem => "UDIV", // closest equivalent
        BinOp::And => "AND",
        BinOp::Or => "ORR",
        BinOp::Xor => "EOR",
        BinOp::Shl => "SHL",
        BinOp::AShr => "ASR",
        BinOp::LShr => "LSR",
        BinOp::FAdd => "FADD",
        BinOp::FSub => "FSUB",
        BinOp::FMul => "FMUL",
        BinOp::FDiv => "FDIV",
        BinOp::FRem => "FDIV", // closest equivalent
        BinOp::FMin => "FMIN",
        BinOp::FMax => "FMAX",
    }
}

/// Derive the dominant operation name from a block's instructions.
///
/// Examines BinOp instructions and returns the most frequent operation name.
/// Falls back to a kind-based heuristic if no BinOps are found.
fn derive_dominant_op(body: &[InstrNode], kind: NodeKind) -> String {
    let mut op_counts: HashMap<&'static str, usize> = HashMap::new();

    for node in body {
        if let Inst::BinOp { op, .. } = &node.inst {
            let name = binop_to_op_name(op);
            *op_counts.entry(name).or_insert(0) += 1;
        }
    }

    // Return the most frequent BinOp if any were found.
    if let Some((&name, _)) = op_counts.iter().max_by_key(|(_, count)| **count) {
        return name.to_string();
    }

    // Fallback based on NodeKind.
    match kind {
        NodeKind::MatrixHeavy => "GEMM".to_string(),
        NodeKind::DataParallel => "ADD".to_string(),
        NodeKind::Scalar => "ADD".to_string(),
    }
}

/// Derive the first exact accelerator semantic recipe.
///
/// Only a validated TrustIR-shaped fixed vector operation is admitted:
///
/// ```text
/// %result = {add,sub,mul} <N x u32> %lhs, %rhs
/// return %result
/// ```
///
/// The operands must be distinct and have the declared vector type, the
/// operation must have exactly one result, and the return must return exactly
/// that result.  This is an actual TrustIR vector BinOp (whose semantics are
/// pointwise modulo-2^32), not the historical invalid `BinOp<Array>` pattern.
/// Every scalar/signed/floating/division/reduction/matmul/multi-instruction
/// shape remains fail-closed.
struct ExactMetalRecipeInput<'a> {
    node_id: ComputeNodeId,
    func_idx: u32,
    instructions: &'a [TrustIrInstId],
    body: &'a [InstrNode],
    block_params: &'a [(ValueId, Ty)],
    is_closed_single_block_function: bool,
    value_types: &'a HashMap<ValueId, Ty>,
    data_size_bytes: u64,
    produced_values: &'a [TrustIrValueId],
    consumed_values: &'a [TrustIrValueId],
}

fn derive_exact_metal_recipe(
    input: ExactMetalRecipeInput<'_>,
) -> Option<AcceleratorSemanticRecipe> {
    let ExactMetalRecipeInput {
        node_id,
        func_idx,
        instructions,
        body,
        block_params,
        is_closed_single_block_function,
        value_types,
        data_size_bytes,
        produced_values,
        consumed_values,
    } = input;
    if !is_closed_single_block_function {
        return None;
    }
    let [operation_node, return_node] = body else {
        return None;
    };
    let Inst::BinOp { op, ty, lhs, rhs } = &operation_node.inst else {
        return None;
    };
    let Ty::Vector(elem, element_count) = ty else {
        return None;
    };
    if elem.as_ref() != &Ty::U32 || *element_count == 0 || lhs == rhs {
        return None;
    }
    if block_params != [(*lhs, ty.clone()), (*rhs, ty.clone())] {
        return None;
    }
    if value_types.get(lhs) != Some(ty) || value_types.get(rhs) != Some(ty) {
        return None;
    }
    let [result] = operation_node.results.as_slice() else {
        return None;
    };
    if value_types.get(result) != Some(ty) {
        return None;
    }
    let Inst::Return { values } = &return_node.inst else {
        return None;
    };
    if values.as_slice() != [*result] || !return_node.results.is_empty() {
        return None;
    }

    let (op, dominant_op) = match op {
        BinOp::Add => (AcceleratorBinaryOp::Add, "ADD"),
        BinOp::Sub => (AcceleratorBinaryOp::Sub, "SUB"),
        BinOp::Mul => (AcceleratorBinaryOp::Mul, "MUL"),
        _ => return None,
    };
    let operation = AcceleratorOperation::ElementwiseBinary {
        op,
        elem_type: AcceleratorElementType::U32,
        element_count: u64::from(*element_count),
        lhs: TrustIrValueId::new(func_idx, *lhs),
        rhs: TrustIrValueId::new(func_idx, *rhs),
        result: TrustIrValueId::new(func_idx, *result),
    };
    Some(AcceleratorSemanticRecipe::new_metal_elementwise(
        node_id,
        instructions.to_vec(),
        data_size_bytes,
        dominant_op.to_string(),
        produced_values.to_vec(),
        consumed_values.to_vec(),
        operation,
    ))
}

// ---------------------------------------------------------------------------
// Proof-guided target recommendations
// ---------------------------------------------------------------------------

/// Per-node target recommendation produced by proof-guided analysis.
///
/// Combines the [`TargetLegality`] from [`ProofAnalyzer`] with the cost model
/// to recommend the cheapest legal target for each computation node.
#[derive(Debug, Clone)]
pub struct TargetRecommendation {
    /// The node this recommendation applies to.
    pub node_id: ComputeNodeId,
    /// The recommended compute target (lowest cost among legal targets).
    pub recommended_target: ComputeTarget,
    /// All legal targets for this node.
    pub legal_targets: Vec<ComputeTarget>,
    /// Human-readable justification for the recommendation.
    pub reason: String,
    /// Whether parallel reduction is legal for this node's subgraph.
    pub parallel_reduction_legal: bool,
}

impl ComputeGraph {
    /// Build a graph from a trust_ir module with a custom proof context and analyzer.
    ///
    /// This is the primary entry point for proof-guided graph construction.
    /// Each node's `target_legality` is populated with full [`TargetLegality`]
    /// from the analyzer, including justifications and parallel reduction info.
    /// A default M1 ProfitabilityAnalyzer is attached for target dispatch.
    pub fn with_proof_context(
        module: &TrustIrModule,
        proof_ctx: TargetProofContext,
        analyzer: &ProofAnalyzer,
    ) -> Self {
        let mut builder = GraphBuilder::new(analyzer.clone(), proof_ctx);
        let mut graph = builder.build_from_module(module);
        graph.profitability = Some(ProfitabilityAnalyzer::new(CostModelGen::M1));
        graph
    }

    /// Build a graph from a trust_ir module with proof context and a custom
    /// ProfitabilityAnalyzer for GPU/ANE dispatch thresholds.
    pub fn with_profitability(
        module: &TrustIrModule,
        proof_ctx: TargetProofContext,
        analyzer: &ProofAnalyzer,
        profitability: ProfitabilityAnalyzer,
    ) -> Self {
        let mut builder = GraphBuilder::new(analyzer.clone(), proof_ctx);
        let mut graph = builder.build_from_module(module);
        graph.profitability = Some(profitability);
        graph
    }

    /// Return per-node target recommendations using stored proof-guided legality
    /// and profitability analysis.
    ///
    /// For each node, filters legal targets through the [`ProfitabilityAnalyzer`]
    /// (when available) to exclude targets that are legal but unprofitable for
    /// the node's workload size. Then picks the cheapest remaining target by
    /// `latency_cycles`. Nodes without `target_legality` fall back to CpuScalar.
    ///
    /// When no `ProfitabilityAnalyzer` is set, falls back to the previous
    /// behavior of picking the cheapest legal target without profitability
    /// filtering.
    pub fn target_recommendations(&self) -> Vec<TargetRecommendation> {
        self.nodes
            .iter()
            .map(|node| {
                let legal = if let Some(ref legality) = node.target_legality {
                    legality.legal_targets()
                } else {
                    node.legal_targets.clone()
                };

                // Filter legal targets through ProfitabilityAnalyzer when available.
                // GPU and ANE have dispatch overhead that makes them unprofitable for
                // small workloads. ProfitabilityAnalyzer encodes these thresholds.
                let profitable = if let Some(ref pa) = self.profitability {
                    let op = &node.dominant_op;
                    let data_size = node.data_size_bytes;
                    // Approximate element count: assume 4-byte elements as default.
                    let element_count = (data_size / 4).max(1);
                    // Approximate tensor shape as a flat array for profitability checks.
                    let tensor_shape = [element_count];

                    legal
                        .iter()
                        .copied()
                        .filter(|&target| {
                            match target {
                                ComputeTarget::Gpu => {
                                    if let Some(cost_target) = to_cost_target(target) {
                                        pa.target_legality(op, cost_target)
                                            && pa.is_gpu_profitable(op, data_size, element_count)
                                    } else {
                                        false
                                    }
                                }
                                ComputeTarget::NeuralEngine => {
                                    if let Some(cost_target) = to_cost_target(target) {
                                        pa.target_legality(op, cost_target)
                                            && pa.is_ane_profitable(op, data_size, &tensor_shape)
                                    } else {
                                        false
                                    }
                                }
                                // CPU Scalar and SIMD are always considered profitable.
                                _ => true,
                            }
                        })
                        .collect::<Vec<_>>()
                } else {
                    legal.clone()
                };

                // If profitability filtering removed all targets, fall back to
                // the original legal set (CPU targets will still be there).
                let effective = if profitable.is_empty() {
                    &legal
                } else {
                    &profitable
                };

                // Pick cheapest legal+profitable target by latency.
                let recommended = effective
                    .iter()
                    .filter_map(|t| node.costs.get(t).map(|c| (*t, c.latency_cycles)))
                    .min_by_key(|(_, cost)| *cost)
                    .map(|(t, _)| t)
                    .unwrap_or(ComputeTarget::CpuScalar);

                let parallel_reduction_legal = node
                    .target_legality
                    .as_ref()
                    .map(|l| l.parallel_reduction_legal)
                    .unwrap_or(false);

                let reason = if let Some(ref legality) = node.target_legality {
                    let base = legality
                        .reason(recommended)
                        .unwrap_or("no justification available");
                    if self.profitability.is_some() && !profitable.contains(&recommended) {
                        format!("{} (profitability-filtered fallback)", base)
                    } else if self.profitability.is_some() {
                        format!("{} (profitability-verified)", base)
                    } else {
                        base.to_string()
                    }
                } else {
                    format!(
                        "{} selected as cheapest legal target (no proof context)",
                        recommended
                    )
                };

                TargetRecommendation {
                    node_id: node.id,
                    recommended_target: recommended,
                    legal_targets: effective.to_vec(),
                    reason,
                    parallel_reduction_legal,
                }
            })
            .collect()
    }

    /// Compute the total cost of the proof-guided optimal assignment.
    ///
    /// For each node, assigns the cheapest legal target. Then computes total
    /// cost including transfer costs for edges between nodes on different targets.
    /// Returns `None` if any node has no legal targets or no cost data.
    pub fn proof_guided_partition_cost(&self) -> Option<u64> {
        let mut assignment = HashMap::new();
        for node in &self.nodes {
            let legal = if let Some(ref legality) = node.target_legality {
                legality.legal_targets()
            } else {
                node.legal_targets.clone()
            };

            let best = legal
                .iter()
                .filter_map(|t| node.costs.get(t).map(|c| (*t, c.latency_cycles)))
                .min_by_key(|(_, cost)| *cost)
                .map(|(t, _)| t)?;

            assignment.insert(node.id, best);
        }
        self.partition_cost(&assignment)
    }

    /// Re-analyze all nodes with a new proof context, updating target legality
    /// and legal_targets on each node in-place.
    ///
    /// This is useful when proof annotations become available after initial graph
    /// construction (e.g., after a verification pass discovers new proofs).
    pub fn annotate_with_proofs(
        &mut self,
        module: &TrustIrModule,
        proof_ctx: &TargetProofContext,
        analyzer: &ProofAnalyzer,
    ) {
        for node in &mut self.nodes {
            let subgraph_id = SubgraphId(node.id.0);

            // Build a SubgraphDescriptor from the node.
            let mut desc = SubgraphDescriptor::new(subgraph_id);
            desc.data_size_bytes = node.data_size_bytes;

            // Propagate subgraph-level proofs from the proof context.
            desc.subgraph_proofs = proof_ctx.subgraph_proofs_for(subgraph_id);

            // Map node values into the descriptor.
            let all_values: Vec<TrustIrValueId> = node
                .consumed_values
                .iter()
                .chain(node.produced_values.iter())
                .copied()
                .collect();

            // Collect type information from the module for these values.
            let mut value_types_map: HashMap<TrustIrValueId, Ty> = HashMap::new();
            for (func_idx, func) in module.functions.iter().enumerate() {
                let func_idx = u32::try_from(func_idx).expect(
                    "TrustIR module function count exceeds the u32 function-identity domain",
                );
                for block in func.blocks.iter() {
                    for (vid, ty) in &block.params {
                        let scoped = TrustIrValueId::new(func_idx, *vid);
                        if all_values.contains(&scoped) {
                            value_types_map.insert(scoped, ty.clone());
                        }
                    }
                    for instr_node in &block.body {
                        match &instr_node.inst {
                            Inst::BinOp { ty, lhs, rhs, .. } => {
                                let lhs = TrustIrValueId::new(func_idx, *lhs);
                                let rhs = TrustIrValueId::new(func_idx, *rhs);
                                if all_values.contains(&lhs) {
                                    value_types_map.entry(lhs).or_insert_with(|| ty.clone());
                                }
                                if all_values.contains(&rhs) {
                                    value_types_map.entry(rhs).or_insert_with(|| ty.clone());
                                }
                                for r in &instr_node.results {
                                    let scoped = TrustIrValueId::new(func_idx, *r);
                                    if all_values.contains(&scoped) {
                                        value_types_map.insert(scoped, ty.clone());
                                    }
                                }
                            }
                            Inst::UnOp { ty, operand, .. } => {
                                let operand = TrustIrValueId::new(func_idx, *operand);
                                if all_values.contains(&operand) {
                                    value_types_map.entry(operand).or_insert_with(|| ty.clone());
                                }
                                for r in &instr_node.results {
                                    let scoped = TrustIrValueId::new(func_idx, *r);
                                    if all_values.contains(&scoped) {
                                        value_types_map.insert(scoped, ty.clone());
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }

            // Map ValueIds -> internal Values for the analyzer.
            let mut lir_values = Vec::new();
            for (i, vid) in all_values.iter().enumerate() {
                let val =
                    Value(u32::try_from(i).expect(
                        "compute-node value count exceeds the u32 analyzer identity domain",
                    ));
                lir_values.push(val);
                if let Some(ty) = value_types_map.get(vid)
                    && let Some(lir_ty) = trust_ir_ty_to_lir_type_for_analyzer(ty)
                {
                    desc.value_types.insert(val, lir_ty);
                }
            }
            desc.values = lir_values;

            // Run proof-guided analysis.
            let preserved_recipe = node
                .target_legality
                .as_ref()
                .and_then(TargetLegality::accelerator_recipe)
                .cloned();
            let mut legality = analyzer.analyze(&desc, proof_ctx);
            if let Some(mut recipe) = preserved_recipe {
                recipe.bind_target_authority(match recipe.backend {
                    AcceleratorBackend::Metal => legality.is_legal(ComputeTarget::Gpu),
                    AcceleratorBackend::CoreMl => legality.is_legal(ComputeTarget::NeuralEngine),
                });
                legality.bind_accelerator_recipe(recipe);
            }
            node.legal_targets = legality.legal_targets();

            // Update costs for newly legal targets.
            for &target in &node.legal_targets {
                node.costs.entry(target).or_insert_with(|| {
                    estimate_compute_cost(
                        node.kind,
                        node.instructions.len(),
                        node.data_size_bytes,
                        target,
                    )
                });
            }

            node.target_legality = Some(legality);
        }
    }
}

// ---------------------------------------------------------------------------
// Transfer cost estimation
// ---------------------------------------------------------------------------

/// Estimate the cost of transferring data between two compute targets.
///
/// Cost model (Apple Silicon):
/// - CPU <-> SIMD: zero cost (same core, same address space)
/// - CPU <-> GPU: kernel launch overhead + DMA transfer
/// - CPU <-> ANE: model compilation overhead + DMA transfer
/// - GPU <-> ANE: must go through CPU (double transfer)
pub fn estimate_transfer_cost(bytes: u64, from: ComputeTarget, to: ComputeTarget) -> TransferCost {
    if from == to {
        return TransferCost::zero();
    }

    match (from, to) {
        // CPU <-> SIMD: same core, negligible cost
        (ComputeTarget::CpuScalar, ComputeTarget::CpuSimd)
        | (ComputeTarget::CpuSimd, ComputeTarget::CpuScalar) => {
            TransferCost::for_bytes(bytes, 0, 0)
        }

        // CPU <-> GPU: Metal command buffer overhead + shared memory transfer
        // Apple Silicon uses unified memory, but there's still cache coherency cost.
        // Overhead: ~5000 cycles for kernel launch
        // Per-byte: ~1 nanocycle (very fast due to unified memory)
        (ComputeTarget::CpuScalar, ComputeTarget::Gpu)
        | (ComputeTarget::CpuSimd, ComputeTarget::Gpu)
        | (ComputeTarget::Gpu, ComputeTarget::CpuScalar)
        | (ComputeTarget::Gpu, ComputeTarget::CpuSimd) => {
            TransferCost::for_bytes(bytes, 5000, 1_000_000_000)
        }

        // CPU <-> ANE: CoreML model compilation/load overhead + transfer
        // Overhead: ~50000 cycles for model load
        // Per-byte: ~2 nanocycles
        (ComputeTarget::CpuScalar, ComputeTarget::NeuralEngine)
        | (ComputeTarget::CpuSimd, ComputeTarget::NeuralEngine)
        | (ComputeTarget::NeuralEngine, ComputeTarget::CpuScalar)
        | (ComputeTarget::NeuralEngine, ComputeTarget::CpuSimd) => {
            TransferCost::for_bytes(bytes, 50000, 2_000_000_000)
        }

        // GPU <-> ANE: must transit through CPU (double hop)
        (ComputeTarget::Gpu, ComputeTarget::NeuralEngine)
        | (ComputeTarget::NeuralEngine, ComputeTarget::Gpu) => {
            let cpu_gpu =
                estimate_transfer_cost(bytes, ComputeTarget::Gpu, ComputeTarget::CpuScalar);
            let cpu_ane = estimate_transfer_cost(
                bytes,
                ComputeTarget::CpuScalar,
                ComputeTarget::NeuralEngine,
            );
            TransferCost {
                overhead_cycles: cpu_gpu.overhead_cycles + cpu_ane.overhead_cycles,
                per_byte_nanocycles: cpu_gpu.per_byte_nanocycles + cpu_ane.per_byte_nanocycles,
                total_cycles: cpu_gpu.total_cycles + cpu_ane.total_cycles,
            }
        }

        // Same-target: unreachable due to early return above, but needed for exhaustiveness.
        (f, t) if f == t => TransferCost::zero(),

        // Fallback: should not be reachable with current variants.
        _ => TransferCost::zero(),
    }
}

// ---------------------------------------------------------------------------
// Per-target cost estimation
// ---------------------------------------------------------------------------

/// Estimate the compute cost for a node on a specific target.
///
/// This is a simplified cost model. Real costs would come from profiling
/// data or microarchitectural models.
fn estimate_compute_cost(
    kind: NodeKind,
    num_instructions: usize,
    data_size_bytes: u64,
    target: ComputeTarget,
) -> ComputeCost {
    let base_cycles = num_instructions as u64;

    match (kind, target) {
        // Scalar on CPU scalar: 1 cycle per instruction (baseline)
        (NodeKind::Scalar, ComputeTarget::CpuScalar) => ComputeCost {
            latency_cycles: base_cycles,
            throughput_ops_per_kcycle: 1000,
        },
        // Scalar on SIMD: slight overhead for vector setup
        (NodeKind::Scalar, ComputeTarget::CpuSimd) => ComputeCost {
            latency_cycles: base_cycles + 2,
            throughput_ops_per_kcycle: 800,
        },

        // Data-parallel on CPU scalar: N iterations
        (NodeKind::DataParallel, ComputeTarget::CpuScalar) => {
            let iterations = (data_size_bytes / 8).max(1); // assume 8-byte elements
            ComputeCost {
                latency_cycles: base_cycles * iterations,
                throughput_ops_per_kcycle: 1000,
            }
        }
        // Data-parallel on SIMD: 4x speedup (128-bit NEON)
        (NodeKind::DataParallel, ComputeTarget::CpuSimd) => {
            let iterations = (data_size_bytes / 8).max(1);
            ComputeCost {
                latency_cycles: base_cycles * iterations / 4,
                throughput_ops_per_kcycle: 4000,
            }
        }
        // Data-parallel on GPU: massive parallelism, but launch overhead
        (NodeKind::DataParallel, ComputeTarget::Gpu) => {
            let iterations = (data_size_bytes / 8).max(1);
            ComputeCost {
                latency_cycles: base_cycles + iterations / 64, // 64-wide warps
                throughput_ops_per_kcycle: 64000,
            }
        }
        // Data-parallel on ANE: not ideal (no reduce support)
        (NodeKind::DataParallel, ComputeTarget::NeuralEngine) => {
            let iterations = (data_size_bytes / 8).max(1);
            ComputeCost {
                latency_cycles: base_cycles * iterations / 8,
                throughput_ops_per_kcycle: 8000,
            }
        }

        // Matrix-heavy on CPU scalar: O(n^2) or O(n^3)
        (NodeKind::MatrixHeavy, ComputeTarget::CpuScalar) => {
            let elements = (data_size_bytes / 8).max(1);
            ComputeCost {
                latency_cycles: base_cycles * elements * elements,
                throughput_ops_per_kcycle: 1000,
            }
        }
        // Matrix-heavy on SIMD: partial vectorization
        (NodeKind::MatrixHeavy, ComputeTarget::CpuSimd) => {
            let elements = (data_size_bytes / 8).max(1);
            ComputeCost {
                latency_cycles: base_cycles * elements * elements / 4,
                throughput_ops_per_kcycle: 4000,
            }
        }
        // Matrix-heavy on GPU: excellent (GEMM kernels)
        (NodeKind::MatrixHeavy, ComputeTarget::Gpu) => {
            let elements = (data_size_bytes / 8).max(1);
            ComputeCost {
                latency_cycles: base_cycles + elements * elements / 256,
                throughput_ops_per_kcycle: 256000,
            }
        }
        // Matrix-heavy on ANE: best target (dedicated matrix multiply hardware)
        (NodeKind::MatrixHeavy, ComputeTarget::NeuralEngine) => {
            let elements = (data_size_bytes / 8).max(1);
            ComputeCost {
                latency_cycles: base_cycles + elements * elements / 512,
                throughput_ops_per_kcycle: 512000,
            }
        }

        // Scalar on GPU/ANE: never efficient but compute a cost anyway
        (NodeKind::Scalar, ComputeTarget::Gpu) => ComputeCost {
            latency_cycles: base_cycles + 5000, // launch overhead dominates
            throughput_ops_per_kcycle: 100,
        },
        (NodeKind::Scalar, ComputeTarget::NeuralEngine) => ComputeCost {
            latency_cycles: base_cycles + 50000,
            throughput_ops_per_kcycle: 10,
        },
    }
}

// ---------------------------------------------------------------------------
// Pattern detection
// ---------------------------------------------------------------------------

/// Minimum array element count to consider a pattern suitable for SIMD/GPU dispatch.
/// Below this threshold, the overhead of vectorized or GPU dispatch exceeds
/// the benefit, so we classify the region as scalar even if it operates on arrays.
const MIN_VECTORIZABLE_ELEMENTS: u64 = 4;

/// Check if a sequence of trust_ir instructions represents a data-parallel pattern.
///
/// Heuristic: a block operating on array-typed values with element-wise
/// binary operations (FAdd, FMul, Add, Mul) is data-parallel, provided:
/// 1. At least one array-typed value exists
/// 2. The array has enough elements to justify vectorization
/// 3. Element-wise binary operations are present
/// 4. The operations actually consume array-typed operands (not just
///    happening to coexist with array parameters)
/// 5. No loop-carried dependency pattern is detected (an operation whose
///    result feeds back into itself via a consumed value)
fn detect_data_parallel(instrs: &[&InstrNode], value_types: &HashMap<ValueId, Ty>) -> bool {
    // Need at least one array-typed value with sufficient element count
    let has_large_array = value_types.values().any(|ty| match ty {
        Ty::Array(_, len) => *len >= MIN_VECTORIZABLE_ELEMENTS,
        _ => false,
    });
    if !has_large_array {
        return false;
    }

    // Check for element-wise operations whose operands are actually array-typed.
    // This prevents false positives where scalar ops coexist with array parameters
    // but don't actually operate on the arrays.
    let has_array_elementwise = instrs.iter().any(|node| match &node.inst {
        Inst::BinOp { op, lhs, rhs, .. } => {
            let is_elementwise = matches!(
                op,
                BinOp::Add | BinOp::Mul | BinOp::FAdd | BinOp::FMul | BinOp::FSub | BinOp::Sub
            );
            if !is_elementwise {
                return false;
            }
            // At least one operand must be array-typed
            let lhs_is_array = value_types
                .get(lhs)
                .is_some_and(|ty| matches!(ty, Ty::Array(..)));
            let rhs_is_array = value_types
                .get(rhs)
                .is_some_and(|ty| matches!(ty, Ty::Array(..)));
            lhs_is_array || rhs_is_array
        }
        _ => false,
    });
    if !has_array_elementwise {
        return false;
    }

    // Check for loop-carried dependencies: if an operation's result is also
    // one of its own operands (via consumed values of other instructions),
    // this indicates a reduction or accumulation that may not be parallelizable
    // without associativity proofs. We allow the data-parallel classification
    // but flag it conservatively -- the ProofAnalyzer will gate actual GPU
    // dispatch on associativity/commutativity proofs.
    //
    // Note: we do NOT reject here because data-parallel with reductions is
    // still a valid pattern (e.g., map-reduce). The target legality analysis
    // handles the reduction legality separately.

    has_array_elementwise
}

/// Check if a sequence of trust_ir instructions represents a matrix-heavy pattern.
///
/// Heuristic: multiply-accumulate pattern (FMul followed by FAdd) operating
/// on array data indicates matrix multiplication or similar, provided:
/// 1. Array-typed values exist with sufficient element count
/// 2. The multiply and accumulate operations have a data dependency
///    (the FAdd consumes the FMul result, not independent values)
/// 3. At least one operand of the multiply is array-typed
fn detect_matrix_heavy(instrs: &[&InstrNode], value_types: &HashMap<ValueId, Ty>) -> bool {
    // Need array-typed values with sufficient element count
    let has_large_array = value_types.values().any(|ty| match ty {
        Ty::Array(_, len) => *len >= MIN_VECTORIZABLE_ELEMENTS,
        _ => false,
    });
    if !has_large_array {
        return false;
    }

    // Look for multiply-accumulate pattern with data dependency validation:
    // FMul/Mul must produce a result that is consumed by a subsequent FAdd/Add.
    // Additionally, at least one operand of the multiply must be array-typed.
    let mut mul_results: HashSet<ValueId> = HashSet::new();
    let mut has_mac_pattern = false;

    for node in instrs {
        match &node.inst {
            Inst::BinOp {
                op: BinOp::FMul | BinOp::Mul,
                lhs,
                rhs,
                ..
            } => {
                // Check that at least one operand is array-typed
                let lhs_is_array = value_types
                    .get(lhs)
                    .is_some_and(|ty| matches!(ty, Ty::Array(..)));
                let rhs_is_array = value_types
                    .get(rhs)
                    .is_some_and(|ty| matches!(ty, Ty::Array(..)));
                if lhs_is_array || rhs_is_array {
                    for r in &node.results {
                        mul_results.insert(*r);
                    }
                }
            }
            Inst::BinOp {
                op: BinOp::FAdd | BinOp::Add,
                lhs,
                rhs,
                ..
            } => {
                // The accumulate must consume a multiply result
                let lhs_match = mul_results.contains(lhs);
                let rhs_match = mul_results.contains(rhs);
                if lhs_match || rhs_match {
                    has_mac_pattern = true;
                }
            }
            _ => {}
        }
    }

    has_mac_pattern
}

/// Classify a group of instructions into a NodeKind.
fn classify_node(instrs: &[&InstrNode], value_types: &HashMap<ValueId, Ty>) -> NodeKind {
    if detect_matrix_heavy(instrs, value_types) {
        NodeKind::MatrixHeavy
    } else if detect_data_parallel(instrs, value_types) {
        NodeKind::DataParallel
    } else {
        NodeKind::Scalar
    }
}

// ---------------------------------------------------------------------------
// Graph builder
// ---------------------------------------------------------------------------

/// Builds a ComputeGraph from a trust_ir module.
///
/// The builder walks each function's blocks, groups instructions into
/// computation nodes, detects patterns (data-parallel, matrix-heavy),
/// and creates data dependency edges between nodes.
pub struct GraphBuilder {
    /// Proof analyzer for determining target legality.
    analyzer: ProofAnalyzer,
    /// Proof context for the module.
    proof_ctx: TargetProofContext,
    /// Next node ID.
    next_node_id: u32,
}

impl GraphBuilder {
    /// Create a new graph builder with the given proof analyzer and context.
    pub fn new(analyzer: ProofAnalyzer, proof_ctx: TargetProofContext) -> Self {
        Self {
            analyzer,
            proof_ctx,
            next_node_id: 0,
        }
    }

    /// Create a graph builder with default configuration.
    pub fn with_defaults() -> Self {
        Self::new(
            ProofAnalyzer::with_defaults(),
            TargetProofContext::default(),
        )
    }

    /// Allocate a fresh node ID.
    fn fresh_node_id(&mut self) -> ComputeNodeId {
        let id = ComputeNodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }

    /// Build a computation graph from a trust_ir module.
    ///
    /// Each basic block becomes one or more computation nodes. Sequential
    /// scalar ops are grouped together. Data-parallel and matrix-heavy
    /// patterns are split into their own nodes.
    pub fn build_from_module(&mut self, module: &TrustIrModule) -> ComputeGraph {
        let mut graph = ComputeGraph::new();

        // Check module verification status using trust_ir's proof summary API.
        // Record this in the graph so downstream dispatch can be conservative
        // when proof obligations are incomplete (pending or failed).
        let proof_summary = module.proof_summary();
        graph.module_fully_verified = proof_summary.is_fully_verified();

        // Track which function-scoped ValueId is produced by which node.
        let mut value_to_nodes: HashMap<TrustIrValueId, Vec<ComputeNodeId>> = HashMap::new();

        // Track which BlockId maps to which ComputeNodeId (for cross-block edges)
        let mut block_to_node: HashMap<(u32, u32), ComputeNodeId> = HashMap::new();

        for (func_idx, func) in module.functions.iter().enumerate() {
            // TrustIrValueId reserves exactly 32 bits for the owning function.
            // Reject an unrepresentable module instead of truncating and
            // aliasing values from two functions.
            let func_idx = u32::try_from(func_idx)
                .expect("TrustIR module function count exceeds the u32 function-identity domain");
            // Collect type information for all values in the function
            let mut value_types: HashMap<ValueId, Ty> = HashMap::new();
            for block in func.blocks.iter() {
                for (vid, ty) in &block.params {
                    value_types.insert(*vid, ty.clone());
                }
                for node in &block.body {
                    // Infer types from instructions (skip constant operands)
                    match &node.inst {
                        Inst::BinOp { ty, lhs, rhs, .. } => {
                            value_types.entry(*lhs).or_insert_with(|| ty.clone());
                            value_types.entry(*rhs).or_insert_with(|| ty.clone());
                            for r in &node.results {
                                value_types.insert(*r, ty.clone());
                            }
                        }
                        Inst::UnOp { ty, operand, .. } => {
                            value_types.entry(*operand).or_insert_with(|| ty.clone());
                            for r in &node.results {
                                value_types.insert(*r, ty.clone());
                            }
                        }
                        Inst::ICmp { ty, lhs, rhs, .. } | Inst::FCmp { ty, lhs, rhs, .. } => {
                            value_types.entry(*lhs).or_insert_with(|| ty.clone());
                            value_types.entry(*rhs).or_insert_with(|| ty.clone());
                            for r in &node.results {
                                value_types.insert(*r, Ty::Bool);
                            }
                        }
                        Inst::Const { ty, .. } => {
                            for r in &node.results {
                                value_types.insert(*r, ty.clone());
                            }
                        }
                        Inst::Load { ty, .. } => {
                            for r in &node.results {
                                value_types.insert(*r, ty.clone());
                            }
                        }
                        _ => {}
                    }
                }
            }

            for block in func.blocks.iter() {
                let nodes = self.build_nodes_for_block(
                    func_idx,
                    block.id,
                    &block.body,
                    &block.params,
                    func.blocks.len() == 1 && func.entry == block.id,
                    &value_types,
                );

                for node in nodes {
                    // Track value producers
                    for vid in &node.produced_values {
                        let producers = value_to_nodes.entry(*vid).or_default();
                        if !producers.contains(&node.id) {
                            producers.push(node.id);
                        }
                    }
                    // Track block -> node mapping
                    block_to_node.insert((func_idx, block.id.0), node.id);
                    graph.nodes.push(node);
                }
            }

            // Second pass: resolve branch-arg-to-block-param data flow.
            // When a Br instruction in block A passes args to block B's params,
            // the block B params are effectively "produced" by block A's node
            // (since the branch transfers the values).
            for block in func.blocks.iter() {
                let source_node_id = block_to_node.get(&(func_idx, block.id.0)).copied();

                for node in &block.body {
                    let targets: Vec<(BlockId, &[ValueId])> = match &node.inst {
                        Inst::Br { target, args } => {
                            vec![(*target, args.as_slice())]
                        }
                        Inst::CondBr {
                            then_target,
                            then_args,
                            else_target,
                            else_args,
                            ..
                        } => {
                            vec![
                                (*then_target, then_args.as_slice()),
                                (*else_target, else_args.as_slice()),
                            ]
                        }
                        _ => vec![],
                    };

                    for (target_block_id, args) in targets {
                        if let Some(target_block) =
                            func.blocks.iter().find(|b| b.id == target_block_id)
                        {
                            // Map branch args -> target block params.
                            // The target block's params are produced by the source block.
                            for (arg_vid, (param_vid, _param_ty)) in
                                args.iter().zip(target_block.params.iter())
                            {
                                if let Some(src_node) = source_node_id {
                                    // The param is "produced" by the source node
                                    // (it flows through the branch)
                                    let producers = value_to_nodes
                                        .entry(TrustIrValueId::new(func_idx, *param_vid))
                                        .or_default();
                                    if !producers.contains(&src_node) {
                                        producers.push(src_node);
                                    }
                                    // Also ensure the arg itself is tracked
                                    let _ = arg_vid; // already tracked as consumed
                                }
                            }
                        }
                    }
                }
            }
        }

        // Build edges based on data dependencies
        self.build_edges(&mut graph, &value_to_nodes);

        graph
    }

    /// Build computation nodes for a single basic block.
    ///
    /// Groups instructions into nodes based on pattern detection:
    /// - Consecutive scalar ops -> single Scalar node
    /// - Data-parallel patterns -> DataParallel node
    /// - Matrix-heavy patterns -> MatrixHeavy node
    fn build_nodes_for_block(
        &mut self,
        func_idx: u32,
        block_id: BlockId,
        body: &[InstrNode],
        block_params: &[(ValueId, Ty)],
        is_closed_single_block_function: bool,
        value_types: &HashMap<ValueId, Ty>,
    ) -> Vec<ComputeNode> {
        if body.is_empty() {
            return Vec::new();
        }

        // Collect instruction references for pattern detection
        let instr_refs: Vec<&InstrNode> = body.iter().collect();

        // Try to detect if the whole block is a single pattern
        let mut kind = classify_node(&instr_refs, value_types);

        // For now, group entire block into one node (future: split into
        // multiple nodes when different patterns are detected within a block)
        let node_id = self.fresh_node_id();
        let subgraph_id = SubgraphId(node_id.0);

        // Collect TrustIrInstIds, produced/consumed values, and data size
        let mut instructions = Vec::new();
        let mut produced_values = Vec::new();
        let mut consumed_values = Vec::new();
        let mut data_size_bytes: u64 = 0;

        for (inst_idx, node) in body.iter().enumerate() {
            instructions.push(TrustIrInstId {
                func_idx,
                block_id: block_id.0,
                inst_idx: u32::try_from(inst_idx).expect(
                    "TrustIR block instruction count exceeds the u32 instruction-identity domain",
                ),
            });

            // Track produced values
            produced_values.extend(
                node.results
                    .iter()
                    .copied()
                    .map(|value| TrustIrValueId::new(func_idx, value)),
            );

            // Track consumed values and estimate data size.
            // All operands are ValueId in the real trust_ir API.
            match &node.inst {
                Inst::BinOp { ty, lhs, rhs, .. } => {
                    consumed_values.push(TrustIrValueId::new(func_idx, *lhs));
                    consumed_values.push(TrustIrValueId::new(func_idx, *rhs));
                    data_size_bytes =
                        data_size_bytes.saturating_add(estimate_type_bytes(ty).saturating_mul(2));
                }
                Inst::UnOp { ty, operand, .. } => {
                    consumed_values.push(TrustIrValueId::new(func_idx, *operand));
                    data_size_bytes = data_size_bytes.saturating_add(estimate_type_bytes(ty));
                }
                Inst::ICmp { lhs, rhs, .. } | Inst::FCmp { lhs, rhs, .. } => {
                    consumed_values.push(TrustIrValueId::new(func_idx, *lhs));
                    consumed_values.push(TrustIrValueId::new(func_idx, *rhs));
                }
                Inst::Load { ptr, .. } => {
                    consumed_values.push(TrustIrValueId::new(func_idx, *ptr));
                }
                Inst::Store { ptr, value, .. } => {
                    consumed_values.push(TrustIrValueId::new(func_idx, *ptr));
                    consumed_values.push(TrustIrValueId::new(func_idx, *value));
                }
                Inst::Br { args, .. } => {
                    consumed_values.extend(
                        args.iter()
                            .copied()
                            .map(|value| TrustIrValueId::new(func_idx, value)),
                    );
                }
                Inst::CondBr {
                    cond,
                    then_args,
                    else_args,
                    ..
                } => {
                    consumed_values.push(TrustIrValueId::new(func_idx, *cond));
                    consumed_values.extend(
                        then_args
                            .iter()
                            .copied()
                            .map(|value| TrustIrValueId::new(func_idx, value)),
                    );
                    consumed_values.extend(
                        else_args
                            .iter()
                            .copied()
                            .map(|value| TrustIrValueId::new(func_idx, value)),
                    );
                }
                Inst::Return { values } => {
                    consumed_values.extend(
                        values
                            .iter()
                            .copied()
                            .map(|value| TrustIrValueId::new(func_idx, value)),
                    );
                }
                Inst::Call { args, .. } => {
                    consumed_values.extend(
                        args.iter()
                            .copied()
                            .map(|value| TrustIrValueId::new(func_idx, value)),
                    );
                }
                Inst::ExtractElement { array, index, .. } => {
                    consumed_values.push(TrustIrValueId::new(func_idx, *array));
                    consumed_values.push(TrustIrValueId::new(func_idx, *index));
                }
                _ => {}
            }
        }

        // Accelerator semantics are derived from the exact typed TrustIR
        // shape, independently of heuristic workload classification.  A
        // fixed-vector operation admitted here is data-parallel by
        // construction; all other shapes retain the reporting classifier and
        // receive no emission recipe.
        let accelerator_recipe = derive_exact_metal_recipe(ExactMetalRecipeInput {
            node_id,
            func_idx,
            instructions: &instructions,
            body,
            block_params,
            is_closed_single_block_function,
            value_types,
            data_size_bytes,
            produced_values: &produced_values,
            consumed_values: &consumed_values,
        });
        if accelerator_recipe.is_some() {
            kind = NodeKind::DataParallel;
        }

        // Build SubgraphDescriptor for target legality analysis
        let mut subgraph_desc = SubgraphDescriptor::new(subgraph_id);
        subgraph_desc.data_size_bytes = data_size_bytes;

        // Propagate subgraph-level proofs from the TargetProofContext into the
        // descriptor. This bridges Gap 1: proof annotations flow from the proof
        // context into each node's legality analysis.
        subgraph_desc.subgraph_proofs = self.proof_ctx.subgraph_proofs_for(subgraph_id);

        // Map ValueIds to internal Values for the analyzer
        let mut lir_values = Vec::new();
        for (i, vid) in consumed_values
            .iter()
            .chain(produced_values.iter())
            .enumerate()
        {
            let val = Value(
                u32::try_from(i)
                    .expect("compute-node value count exceeds the u32 analyzer identity domain"),
            );
            lir_values.push(val);
            if let Some(ty) = value_types.get(&vid.value_id)
                && let Some(lir_ty) = trust_ir_ty_to_lir_type_for_analyzer(ty)
            {
                subgraph_desc.value_types.insert(val, lir_ty);
            }
        }
        subgraph_desc.values = lir_values;

        // Determine target legality via ProofAnalyzer
        let mut legality = self.analyzer.analyze(&subgraph_desc, &self.proof_ctx);
        if let Some(mut recipe) = accelerator_recipe {
            recipe.bind_target_authority(match recipe.backend {
                AcceleratorBackend::Metal => legality.is_legal(ComputeTarget::Gpu),
                AcceleratorBackend::CoreMl => legality.is_legal(ComputeTarget::NeuralEngine),
            });
            legality.bind_accelerator_recipe(recipe);
        }
        let legal_targets = legality.legal_targets();

        // Estimate costs for each legal target
        let mut costs = HashMap::new();
        for &target in &legal_targets {
            let cost = estimate_compute_cost(kind, instructions.len(), data_size_bytes, target);
            costs.insert(target, cost);
        }

        // Derive dominant operation name from instructions for profitability queries.
        let dominant_op = legality
            .accelerator_recipe()
            .map(|recipe| recipe.dominant_op.clone())
            .unwrap_or_else(|| derive_dominant_op(body, kind));

        // For MatrixHeavy nodes, derive a best-effort square shape from
        // `data_size_bytes` as diagnostic/future cost-model metadata (issue
        // #404).  This does not confer emission authority: the sealed Metal
        // path refuses MatrixHeavy nodes until exact typed matrix semantics
        // are represented by an accelerator recipe.
        //
        // Future work: once trust_ir loop-nest analysis is wired into
        // `GraphBuilder`, populate M, K, N from the loop bounds directly.
        let matmul_shape = if kind == NodeKind::MatrixHeavy {
            derive_square_matmul_shape(data_size_bytes, &dominant_op, node_id)
        } else {
            None
        };

        vec![ComputeNode {
            id: node_id,
            instructions,
            costs,
            legal_targets,
            kind,
            data_size_bytes,
            produced_values,
            consumed_values,
            dominant_op,
            target_legality: Some(legality),
            matmul_shape,
        }]
    }

    /// Build data dependency edges between nodes.
    fn build_edges(
        &self,
        graph: &mut ComputeGraph,
        value_to_nodes: &HashMap<TrustIrValueId, Vec<ComputeNodeId>>,
    ) {
        let mut seen_edges: HashSet<(ComputeNodeId, ComputeNodeId)> = HashSet::new();

        for node in &graph.nodes {
            for vid in &node.consumed_values {
                if let Some(producer_ids) = value_to_nodes.get(vid) {
                    for &producer_id in producer_ids {
                        if producer_id == node.id || !seen_edges.insert((producer_id, node.id)) {
                            continue;
                        }

                        // Estimate transfer size: use the node's data size as approximation
                        let transfer_bytes = node
                            .data_size_bytes
                            .min(
                                graph
                                    .node(producer_id)
                                    .map(|n| n.data_size_bytes)
                                    .unwrap_or(0),
                            )
                            .max(8); // minimum 8 bytes (one register)

                        graph.edges.push(DataEdge {
                            from: producer_id,
                            to: node.id,
                            transfer_bytes,
                            transfer_cost: TransferCost::zero(), // filled in by partition_cost
                        });
                    }
                }
            }
        }
    }
}

/// Estimate byte size of a trust_ir type.
fn estimate_type_bytes(ty: &Ty) -> u64 {
    ty.bit_width()
        .map(|w| u64::from(w.div_ceil(8)))
        .unwrap_or(match ty {
            Ty::Struct(_) => 8,                              // rough estimate
            Ty::Array(_, len) => 8_u64.saturating_mul(*len), // rough: 8 bytes per element
            Ty::Func(_) => 8,
            Ty::Unit | Ty::Never => 0,
            _ => 8,
        })
}

/// Pick a plausible LIR element type for a MatrixHeavy node, based on the
/// dominant operation name (a string like `"FMUL"`, `"GEMM"`, `"ADD"`).
///
/// This is retained only for the legacy diagnostic/cost-model
/// [`MatMulShape`]. It does not feed the sealed Metal recipe or grant emission
/// authority: operation-name inference was deliberately removed from the
/// emitter. If the op name starts with `F` it is treated as `F32`; otherwise
/// it is treated as `I32`.
fn infer_matmul_elem_type(dominant_op: &str) -> LirType {
    let op = dominant_op.to_uppercase();
    if op.starts_with('F') || op.contains("FLOAT") || op.contains("FP") {
        LirType::F32
    } else {
        LirType::I32
    }
}

/// Derive a square `MatMulShape` from `data_size_bytes` (issue #404).
///
/// This preserves the legacy "square matmul, A+B+C combined" estimate as
/// diagnostic/future cost-model metadata. It is not consumed by the sealed
/// Metal emission path and cannot authorize a MatrixHeavy launch.
/// For `total_elements = data_size_bytes / elem_bytes` and
/// `total_elements = 3 * dim^2`, we solve `dim = sqrt(total / 3)`.
///
/// Returns `None` for zero-byte nodes and for byte counts that round down
/// to `dim == 0`. Logs a warning via `eprintln!` on the deprecated
/// square-derivation path so stragglers are visible during migration to real
/// trust_ir loop-nest-driven shape inference.
pub(crate) fn derive_square_matmul_shape(
    data_size_bytes: u64,
    dominant_op: &str,
    node_id: ComputeNodeId,
) -> Option<MatMulShape> {
    if data_size_bytes == 0 {
        return None;
    }
    let elem_type = infer_matmul_elem_type(dominant_op);
    let elem_bytes = elem_type.bytes() as u64;
    if elem_bytes == 0 {
        return None;
    }
    let total_elements = data_size_bytes / elem_bytes;
    let dim_sq = total_elements / 3;
    let dim = (dim_sq as f64).sqrt() as u64;
    if dim == 0 {
        return None;
    }
    eprintln!(
        "[trust-cg-lower] warning: ComputeNode {node_id} MatrixHeavy shape \
         derived from data_size_bytes={data_size_bytes} via square-matmul \
         heuristic (dominant_op={dominant_op}, elem_type={elem_type:?}, \
         dim={dim}); migrate construction site to populate \
         `matmul_shape` explicitly (issue #404)."
    );
    Some(MatMulShape::new(dim, dim, dim, elem_type))
}

/// Translate a trust_ir `Ty` into an LIR `Type` for the proof analyzer's
/// `SubgraphDescriptor::value_types` map.
///
/// This differs from [`crate::adapter::translate_type`] in that it produces
/// a best-effort `Type::Array` for `Ty::Array` inputs instead of erroring.
/// The analyzer only inspects the top-level variant (e.g., via
/// `operates_on_arrays()`), so using a scalar placeholder (I64) for the
/// element type is sufficient when the trust_ir type table has not resolved
/// the element's `TyId`. This keeps heterogeneous-compute target
/// recommendations (GPU/ANE) working regardless of type-table resolution.
///
/// Returns `None` for types that `translate_type` rejects AND are not
/// `Ty::Array` (e.g., `Ty::Tuple`, `Ty::Enum`, `Ty::Func`, `Ty::Unit`,
/// `Ty::Never`). Returning `None` preserves the prior conservative
/// behavior of simply not inserting into `value_types` for those cases.
fn trust_ir_ty_to_lir_type_for_analyzer(ty: &Ty) -> Option<LirType> {
    if let Ok(lir_ty) = crate::adapter::translate_type(ty) {
        return Some(lir_ty);
    }
    match ty {
        // The adapter's machine-lowering shape recognizer intentionally
        // spells unsigned vectors with the signed carrier type.  Target
        // analysis only needs the aggregate/vector classification, so retain
        // the exact TrustIR U32 signedness in the recipe and represent its
        // supported 128-bit storage class here.
        Ty::Vector(elem, 4) if elem.as_ref() == &Ty::U32 => Some(LirType::V128),
        Ty::Array(_, len) => u32::try_from(*len)
            .ok()
            .map(|len| LirType::Array(Box::new(LirType::I64), len)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Convenience constructors for testing / manual graph building
// ---------------------------------------------------------------------------

impl ComputeGraph {
    /// Build a graph from a trust_ir module with default configuration.
    pub fn from_module(module: &TrustIrModule) -> Self {
        let mut builder = GraphBuilder::with_defaults();
        builder.build_from_module(module)
    }

    /// Build a graph with a custom proof context.
    /// Attaches a default M1 ProfitabilityAnalyzer for GPU/ANE dispatch.
    pub fn from_module_with_proofs(module: &TrustIrModule, proof_ctx: TargetProofContext) -> Self {
        let analyzer = ProofAnalyzer::with_defaults();
        let mut builder = GraphBuilder::new(analyzer, proof_ctx);
        let mut graph = builder.build_from_module(module);
        graph.profitability = Some(ProfitabilityAnalyzer::new(CostModelGen::M1));
        graph
    }

    /// Add a node manually (for testing).
    pub fn add_node(&mut self, node: ComputeNode) {
        self.nodes.push(node);
    }

    /// Add an edge manually (for testing).
    pub fn add_edge(&mut self, edge: DataEdge) {
        self.edges.push(edge);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{
        BinOp, Block as TrustIrBlock, BlockId, CallingConv, FuncId, FuncTy, FuncTyId,
        Function as TrustIrFunction, Inst, InstrNode, Linkage, Module, Ty, TyId, ValueId,
    };

    // -------------------------------------------------------------------
    // Test helpers
    // -------------------------------------------------------------------

    /// Build a simple trust_ir module: fn add(a: i32, b: i32) -> i32 { a + b }
    fn build_scalar_add_module() -> Module {
        Module {
            name: "scalar_add".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "add".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
                    body: vec![
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::Add,
                                ty: Ty::I32,
                                lhs: ValueId::new(0),
                                rhs: ValueId::new(1),
                            },
                            results: vec![ValueId::new(2)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(2)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                    ],
                }],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        }
    }

    fn build_exact_u32x4_module(op: BinOp, extra_operation: bool) -> Module {
        let vector_ty = Ty::Vector(Box::new(Ty::U32), 4);
        let mut body = vec![InstrNode {
            inst: Inst::BinOp {
                op,
                ty: vector_ty.clone(),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }];
        let returned = if extra_operation {
            body.push(InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::Add,
                    ty: vector_ty.clone(),
                    lhs: ValueId::new(2),
                    rhs: ValueId::new(1),
                },
                results: vec![ValueId::new(3)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            });
            ValueId::new(3)
        } else {
            ValueId::new(2)
        };
        body.push(InstrNode {
            inst: Inst::Return {
                values: vec![returned],
            },
            results: vec![],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        });
        Module {
            name: "exact_u32x4".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "map2".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![
                        (ValueId::new(0), vector_ty.clone()),
                        (ValueId::new(1), vector_ty.clone()),
                    ],
                    body,
                }],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![vector_ty.clone(), vector_ty.clone()],
                returns: vec![vector_ty],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        }
    }

    fn exact_recipe_graph(op: BinOp) -> ComputeGraph {
        use crate::adapter::Proof;
        use crate::target_analysis::{CostConfig, SubgraphProof};

        let mut proof_ctx = TargetProofContext::default();
        proof_ctx.add_subgraph_proof(SubgraphId(0), SubgraphProof::Pure);
        proof_ctx.proof_ctx.value_proofs.insert(
            Value(0),
            vec![
                Proof::InBounds {
                    base: ValueId::new(0),
                    index: ValueId::new(0),
                },
                Proof::ValidBorrow {
                    borrow: ValueId::new(0),
                },
            ],
        );
        let analyzer = ProofAnalyzer::new(CostConfig {
            gpu_launch_threshold_bytes: 0,
            ane_launch_threshold_bytes: u64::MAX,
            simd_threshold_bytes: 0,
        });
        GraphBuilder::new(analyzer, proof_ctx)
            .build_from_module(&build_exact_u32x4_module(op, false))
    }

    #[test]
    fn exact_u32_vector_recipe_is_canonical_and_authorized_in_structural_test_model() {
        let graph = exact_recipe_graph(BinOp::Add);
        let node = &graph.nodes[0];
        assert_eq!(node.kind, NodeKind::DataParallel);
        let recipe = node
            .validated_accelerator_recipe(AcceleratorBackend::Metal)
            .expect("exact recipe with structural test authority");
        assert!(matches!(
            recipe.operation(),
            AcceleratorOperation::ElementwiseBinary {
                op: AcceleratorBinaryOp::Add,
                elem_type: AcceleratorElementType::U32,
                element_count: 4,
                lhs,
                rhs,
                result,
            } if *lhs == TrustIrValueId::new(0, ValueId::new(0))
                && *rhs == TrustIrValueId::new(0, ValueId::new(1))
                && *result == TrustIrValueId::new(0, ValueId::new(2))
        ));
        assert_ne!(recipe.semantic_digest().bytes, [0; 32]);
        let rebuilt = exact_recipe_graph(BinOp::Add);
        assert_eq!(
            recipe.semantic_digest(),
            rebuilt.nodes[0]
                .validated_accelerator_recipe(AcceleratorBackend::Metal)
                .unwrap()
                .semantic_digest()
        );
    }

    #[test]
    fn recipe_rejects_every_public_semantic_metadata_mutation() {
        let baseline = exact_recipe_graph(BinOp::Mul).nodes.remove(0);
        let mut mutations = Vec::new();

        let mut node = baseline.clone();
        node.dominant_op = "GEMM".to_string();
        mutations.push(node);

        let mut node = baseline.clone();
        node.instructions.push(TrustIrInstId {
            func_idx: 0,
            block_id: 0,
            inst_idx: 99,
        });
        mutations.push(node);

        let mut node = baseline.clone();
        node.consumed_values
            .push(TrustIrValueId::new(0, ValueId::new(99)));
        mutations.push(node);

        let mut node = baseline.clone();
        node.produced_values.clear();
        mutations.push(node);

        let mut node = baseline.clone();
        node.legal_targets
            .retain(|target| *target != ComputeTarget::Gpu);
        mutations.push(node);

        for node in mutations {
            assert!(
                node.validated_accelerator_recipe(AcceleratorBackend::Metal)
                    .is_err()
            );
        }
    }

    #[test]
    fn reused_value_ids_across_functions_remain_distinct_in_graph_and_recipe() {
        use crate::adapter::Proof;
        use crate::target_analysis::{CostConfig, SubgraphProof};

        let mut module = build_exact_u32x4_module(BinOp::Add, false);
        let mut second = module.functions[0].clone();
        second.id = FuncId::new(1);
        second.name = "map2_second".to_string();
        module.functions.push(second);

        let mut proof_ctx = TargetProofContext::default();
        for subgraph in [SubgraphId(0), SubgraphId(1)] {
            proof_ctx.add_subgraph_proof(subgraph, SubgraphProof::Pure);
        }
        proof_ctx.proof_ctx.value_proofs.insert(
            Value(0),
            vec![
                Proof::InBounds {
                    base: ValueId::new(0),
                    index: ValueId::new(0),
                },
                Proof::ValidBorrow {
                    borrow: ValueId::new(0),
                },
            ],
        );
        let analyzer = ProofAnalyzer::new(CostConfig {
            gpu_launch_threshold_bytes: 0,
            ane_launch_threshold_bytes: u64::MAX,
            simd_threshold_bytes: 0,
        });
        let graph = GraphBuilder::new(analyzer, proof_ctx).build_from_module(&module);

        assert_eq!(graph.nodes.len(), 2);
        assert!(
            graph.edges.is_empty(),
            "function-local ValueId reuse must not synthesize a cross-function dependency: {:?}",
            graph.edges
        );

        let first = graph.nodes[0]
            .validated_accelerator_recipe(AcceleratorBackend::Metal)
            .expect("first exact recipe");
        let second = graph.nodes[1]
            .validated_accelerator_recipe(AcceleratorBackend::Metal)
            .expect("second exact recipe");
        let values = |recipe: &AcceleratorSemanticRecipe| match recipe.operation() {
            AcceleratorOperation::ElementwiseBinary {
                lhs, rhs, result, ..
            } => (*lhs, *rhs, *result),
        };
        let first_values = values(first);
        let second_values = values(second);
        assert_eq!(first_values.0, TrustIrValueId::new(0, ValueId::new(0)));
        assert_eq!(second_values.0, TrustIrValueId::new(1, ValueId::new(0)));
        assert_ne!(first_values.0.stable_key(), second_values.0.stable_key());
        assert_ne!(
            first.semantic_digest(),
            second.semantic_digest(),
            "the sealed recipe must bind the owning function, not only local SSA numbers"
        );
    }

    #[test]
    fn scoped_value_stable_key_is_injective_at_component_boundaries() {
        let last_local = TrustIrValueId::new(0, ValueId::new(u32::MAX));
        let next_function = TrustIrValueId::new(1, ValueId::new(0));
        let last_possible = TrustIrValueId::new(u32::MAX, ValueId::new(u32::MAX));

        assert_eq!(last_local.stable_key(), u64::from(u32::MAX));
        assert_eq!(next_function.stable_key(), 1_u64 << 32);
        assert_ne!(last_local.stable_key(), next_function.stable_key());
        assert_eq!(last_possible.stable_key(), u64::MAX);
    }

    #[test]
    fn forged_target_judgment_cannot_upgrade_sealed_recipe_authority() {
        let mut graph = ComputeGraph::from_module(&build_exact_u32x4_module(BinOp::Add, false));
        let node = &mut graph.nodes[0];
        let legality = node.target_legality.as_mut().unwrap();
        legality
            .judgments
            .get_mut(&ComputeTarget::Gpu)
            .unwrap()
            .legal = true;
        node.legal_targets = legality.legal_targets();
        assert!(matches!(
            node.validated_accelerator_recipe(AcceleratorBackend::Metal),
            Err(AcceleratorBindingError::TargetNotAuthorized { .. })
        ));
    }

    #[test]
    fn unsupported_or_multi_instruction_blocks_receive_no_recipe() {
        for module in [
            build_exact_u32x4_module(BinOp::UDiv, false),
            build_exact_u32x4_module(BinOp::Add, true),
        ] {
            let graph = ComputeGraph::from_module(&module);
            assert!(matches!(
                graph.nodes[0].validated_accelerator_recipe(AcceleratorBackend::Metal),
                Err(AcceleratorBindingError::MissingCompilerBinding { .. })
            ));
        }
    }

    /// Build a trust_ir module with array FAdd operations (data-parallel pattern).
    fn build_data_parallel_module() -> Module {
        Module {
            name: "data_parallel".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "vec_add".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![
                        (ValueId::new(0), Ty::Array(TyId::new(0), 1000)),
                        (ValueId::new(1), Ty::Array(TyId::new(0), 1000)),
                    ],
                    body: vec![
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::FAdd,
                                ty: Ty::Array(TyId::new(0), 1000),
                                lhs: ValueId::new(0),
                                rhs: ValueId::new(1),
                            },
                            results: vec![ValueId::new(2)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(2)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                    ],
                }],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        }
    }

    /// Build a trust_ir module with FMul+FAdd pattern (matrix-heavy / MAC).
    fn build_matrix_heavy_module() -> Module {
        Module {
            name: "matrix_heavy".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "dot_product".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![
                        (ValueId::new(0), Ty::Array(TyId::new(0), 1000)),
                        (ValueId::new(1), Ty::Array(TyId::new(0), 1000)),
                    ],
                    body: vec![
                        // FMul: multiply elements
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::FMul,
                                ty: Ty::Array(TyId::new(0), 1000),
                                lhs: ValueId::new(0),
                                rhs: ValueId::new(1),
                            },
                            results: vec![ValueId::new(2)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        // FAdd: accumulate (MAC pattern)
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::FAdd,
                                ty: Ty::F64,
                                lhs: ValueId::new(2),
                                rhs: ValueId::new(2),
                            },
                            results: vec![ValueId::new(3)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(3)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                    ],
                }],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        }
    }

    /// Build a large data-parallel module (100K-element arrays).
    /// Workload large enough for GPU profitability thresholds.
    fn build_large_data_parallel_module() -> Module {
        Module {
            name: "large_data_parallel".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "large_vec_add".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![
                        (ValueId::new(0), Ty::Array(TyId::new(0), 100_000)),
                        (ValueId::new(1), Ty::Array(TyId::new(0), 100_000)),
                    ],
                    body: vec![
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::FAdd,
                                ty: Ty::Array(TyId::new(0), 100_000),
                                lhs: ValueId::new(0),
                                rhs: ValueId::new(1),
                            },
                            results: vec![ValueId::new(2)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(2)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                    ],
                }],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        }
    }

    /// Build a large matrix-heavy module (100K-element arrays).
    /// Workload large enough for GPU/ANE profitability thresholds.
    fn build_large_matrix_heavy_module() -> Module {
        Module {
            name: "large_matrix_heavy".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "large_dot_product".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![
                        (ValueId::new(0), Ty::Array(TyId::new(0), 100_000)),
                        (ValueId::new(1), Ty::Array(TyId::new(0), 100_000)),
                    ],
                    body: vec![
                        // FMul: multiply elements
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::FMul,
                                ty: Ty::Array(TyId::new(0), 100_000),
                                lhs: ValueId::new(0),
                                rhs: ValueId::new(1),
                            },
                            results: vec![ValueId::new(2)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        // FAdd: accumulate (MAC pattern)
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::FAdd,
                                ty: Ty::F64,
                                lhs: ValueId::new(2),
                                rhs: ValueId::new(2),
                            },
                            results: vec![ValueId::new(3)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(3)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                    ],
                }],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        }
    }

    /// Build a module with two functions that have a data dependency
    /// (second function consumes values from the first).
    fn build_two_block_module() -> Module {
        Module {
            name: "two_block".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "two_blocks".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![
                    TrustIrBlock {
                        id: BlockId::new(0),
                        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
                        body: vec![
                            InstrNode {
                                inst: Inst::BinOp {
                                    op: BinOp::Add,
                                    ty: Ty::I32,
                                    lhs: ValueId::new(0),
                                    rhs: ValueId::new(1),
                                },
                                results: vec![ValueId::new(2)],
                                proofs: vec![],
                                span: None,
                                proof_context: None,
                                scope: None,
                            },
                            InstrNode {
                                inst: Inst::Br {
                                    target: BlockId::new(1),
                                    args: vec![ValueId::new(2)],
                                },
                                results: vec![],
                                proofs: vec![],
                                span: None,
                                proof_context: None,
                                scope: None,
                            },
                        ],
                    },
                    TrustIrBlock {
                        id: BlockId::new(1),
                        params: vec![(ValueId::new(3), Ty::I32)],
                        body: vec![
                            InstrNode {
                                inst: Inst::BinOp {
                                    op: BinOp::Mul,
                                    ty: Ty::I32,
                                    lhs: ValueId::new(3),
                                    rhs: ValueId::new(3),
                                },
                                results: vec![ValueId::new(4)],
                                proofs: vec![],
                                span: None,
                                proof_context: None,
                                scope: None,
                            },
                            InstrNode {
                                inst: Inst::Return {
                                    values: vec![ValueId::new(4)],
                                },
                                results: vec![],
                                proofs: vec![],
                                span: None,
                                proof_context: None,
                                scope: None,
                            },
                        ],
                    },
                ],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        }
    }

    /// Build a diamond CFG whose join parameter has two incoming producers.
    fn build_diamond_module() -> Module {
        let mut module = build_two_block_module();
        module.name = "diamond".to_string();
        let function = &mut module.functions[0];
        function.name = "diamond".to_string();
        function.blocks = vec![
            TrustIrBlock {
                id: BlockId::new(0),
                params: vec![
                    (ValueId::new(0), Ty::Bool),
                    (ValueId::new(1), Ty::I32),
                    (ValueId::new(2), Ty::I32),
                ],
                body: vec![InstrNode {
                    inst: Inst::CondBr {
                        cond: ValueId::new(0),
                        then_target: BlockId::new(1),
                        then_args: vec![],
                        else_target: BlockId::new(2),
                        else_args: vec![],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                }],
            },
            TrustIrBlock {
                id: BlockId::new(1),
                params: vec![],
                body: vec![
                    InstrNode {
                        inst: Inst::BinOp {
                            op: BinOp::Add,
                            ty: Ty::I32,
                            lhs: ValueId::new(1),
                            rhs: ValueId::new(1),
                        },
                        results: vec![ValueId::new(3)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    InstrNode {
                        inst: Inst::Br {
                            target: BlockId::new(3),
                            args: vec![ValueId::new(3)],
                        },
                        results: vec![],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                ],
            },
            TrustIrBlock {
                id: BlockId::new(2),
                params: vec![],
                body: vec![
                    InstrNode {
                        inst: Inst::BinOp {
                            op: BinOp::Sub,
                            ty: Ty::I32,
                            lhs: ValueId::new(2),
                            rhs: ValueId::new(2),
                        },
                        results: vec![ValueId::new(4)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    InstrNode {
                        inst: Inst::Br {
                            target: BlockId::new(3),
                            args: vec![ValueId::new(4)],
                        },
                        results: vec![],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                ],
            },
            TrustIrBlock {
                id: BlockId::new(3),
                params: vec![(ValueId::new(5), Ty::I32)],
                body: vec![
                    InstrNode {
                        inst: Inst::BinOp {
                            op: BinOp::Mul,
                            ty: Ty::I32,
                            lhs: ValueId::new(5),
                            rhs: ValueId::new(5),
                        },
                        results: vec![ValueId::new(6)],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    InstrNode {
                        inst: Inst::Return {
                            values: vec![ValueId::new(6)],
                        },
                        results: vec![],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                ],
            },
        ];
        module.func_types[0] = FuncTy {
            params: vec![Ty::Bool, Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        };
        module
    }

    // -------------------------------------------------------------------
    // Test: Scalar module produces a Scalar node
    // -------------------------------------------------------------------

    #[test]
    fn test_scalar_module_produces_scalar_node() {
        let module = build_scalar_add_module();
        let graph = ComputeGraph::from_module(&module);

        assert_eq!(graph.num_nodes(), 1);
        assert_eq!(graph.nodes[0].kind, NodeKind::Scalar);
        assert!(
            graph.nodes[0]
                .legal_targets
                .contains(&ComputeTarget::CpuScalar)
        );
    }

    // -------------------------------------------------------------------
    // Test: Data-parallel module detection
    // -------------------------------------------------------------------

    #[test]
    fn test_data_parallel_detection() {
        let module = build_data_parallel_module();
        let graph = ComputeGraph::from_module(&module);

        assert_eq!(graph.num_nodes(), 1);
        assert_eq!(graph.nodes[0].kind, NodeKind::DataParallel);
    }

    // -------------------------------------------------------------------
    // Test: Matrix-heavy module detection (FMul + FAdd pattern)
    // -------------------------------------------------------------------

    #[test]
    fn test_matrix_heavy_detection() {
        let module = build_matrix_heavy_module();
        let graph = ComputeGraph::from_module(&module);

        assert_eq!(graph.num_nodes(), 1);
        assert_eq!(graph.nodes[0].kind, NodeKind::MatrixHeavy);
    }

    // -------------------------------------------------------------------
    // Test: Two-block module produces edges
    // -------------------------------------------------------------------

    #[test]
    fn test_two_block_produces_edges() {
        let module = build_two_block_module();
        let graph = ComputeGraph::from_module(&module);

        // Two blocks -> two nodes
        assert_eq!(graph.num_nodes(), 2);

        // Block 1 consumes ValueId::new(2) produced by block 0 (via branch args)
        // So there should be an edge from node 0 to node 1
        assert!(
            graph.num_edges() >= 1,
            "Expected at least 1 edge, got {}",
            graph.num_edges()
        );

        let edge = &graph.edges[0];
        assert_eq!(edge.from, ComputeNodeId(0));
        assert_eq!(edge.to, ComputeNodeId(1));
    }

    #[test]
    fn diamond_join_preserves_every_incoming_parameter_producer() {
        let graph = ComputeGraph::from_module(&build_diamond_module());

        assert_eq!(graph.num_nodes(), 4);
        let incoming = graph
            .edges
            .iter()
            .filter(|edge| edge.to == ComputeNodeId(3))
            .map(|edge| edge.from)
            .collect::<Vec<_>>();
        assert_eq!(
            incoming,
            vec![ComputeNodeId(1), ComputeNodeId(2)],
            "both phi-like branch-parameter producers must reach the join deterministically"
        );
    }

    // -------------------------------------------------------------------
    // Test: Partition cost calculation — all on CPU scalar
    // -------------------------------------------------------------------

    #[test]
    fn test_partition_cost_all_cpu() {
        let module = build_scalar_add_module();
        let graph = ComputeGraph::from_module(&module);

        let mut assignment = HashMap::new();
        assignment.insert(ComputeNodeId(0), ComputeTarget::CpuScalar);

        let cost = graph.partition_cost(&assignment);
        assert!(
            cost.is_some(),
            "Cost should be computable for legal assignment"
        );
        assert!(cost.unwrap() > 0, "Cost should be positive");
    }

    // -------------------------------------------------------------------
    // Test: Partition cost with illegal target returns None
    // -------------------------------------------------------------------

    #[test]
    fn test_partition_cost_illegal_target() {
        let module = build_scalar_add_module();
        let graph = ComputeGraph::from_module(&module);

        // Without proofs, GPU is not legal for scalar ops
        let mut assignment = HashMap::new();
        assignment.insert(ComputeNodeId(0), ComputeTarget::Gpu);

        let cost = graph.partition_cost(&assignment);
        assert!(cost.is_none(), "GPU should be illegal without proofs");
    }

    // -------------------------------------------------------------------
    // Test: Partition cost with missing node returns None
    // -------------------------------------------------------------------

    #[test]
    fn test_partition_cost_missing_node() {
        let module = build_scalar_add_module();
        let graph = ComputeGraph::from_module(&module);

        let assignment: HashMap<ComputeNodeId, ComputeTarget> = HashMap::new();
        let cost = graph.partition_cost(&assignment);
        assert!(cost.is_none(), "Missing node assignment should return None");
    }

    // -------------------------------------------------------------------
    // Test: Transfer cost between same targets is zero
    // -------------------------------------------------------------------

    #[test]
    fn test_transfer_cost_same_target_zero() {
        let cost = estimate_transfer_cost(1000, ComputeTarget::CpuScalar, ComputeTarget::CpuScalar);
        assert_eq!(cost.total_cycles, 0);
    }

    // -------------------------------------------------------------------
    // Test: Transfer cost CPU <-> SIMD is zero (same core)
    // -------------------------------------------------------------------

    #[test]
    fn test_transfer_cost_cpu_simd_zero() {
        let cost = estimate_transfer_cost(8000, ComputeTarget::CpuScalar, ComputeTarget::CpuSimd);
        assert_eq!(cost.total_cycles, 0);
    }

    // -------------------------------------------------------------------
    // Test: Transfer cost CPU <-> GPU has overhead
    // -------------------------------------------------------------------

    #[test]
    fn test_transfer_cost_cpu_gpu_has_overhead() {
        let cost = estimate_transfer_cost(8000, ComputeTarget::CpuScalar, ComputeTarget::Gpu);
        assert!(
            cost.total_cycles >= 5000,
            "GPU transfer should have launch overhead"
        );
        assert!(cost.overhead_cycles == 5000);
    }

    // -------------------------------------------------------------------
    // Test: Transfer cost CPU <-> ANE has higher overhead than GPU
    // -------------------------------------------------------------------

    #[test]
    fn test_transfer_cost_cpu_ane_higher_than_gpu() {
        let gpu_cost = estimate_transfer_cost(8000, ComputeTarget::CpuScalar, ComputeTarget::Gpu);
        let ane_cost =
            estimate_transfer_cost(8000, ComputeTarget::CpuScalar, ComputeTarget::NeuralEngine);
        assert!(
            ane_cost.total_cycles > gpu_cost.total_cycles,
            "ANE transfer should cost more than GPU: ANE={}, GPU={}",
            ane_cost.total_cycles,
            gpu_cost.total_cycles,
        );
    }

    // -------------------------------------------------------------------
    // Test: GPU <-> ANE double-hop cost
    // -------------------------------------------------------------------

    #[test]
    fn test_transfer_cost_gpu_ane_double_hop() {
        let gpu_ane = estimate_transfer_cost(8000, ComputeTarget::Gpu, ComputeTarget::NeuralEngine);
        let gpu_cpu = estimate_transfer_cost(8000, ComputeTarget::Gpu, ComputeTarget::CpuScalar);
        let cpu_ane =
            estimate_transfer_cost(8000, ComputeTarget::CpuScalar, ComputeTarget::NeuralEngine);

        assert_eq!(
            gpu_ane.total_cycles,
            gpu_cpu.total_cycles + cpu_ane.total_cycles,
            "GPU<->ANE should be sum of GPU<->CPU + CPU<->ANE"
        );
    }

    // -------------------------------------------------------------------
    // Test: Two-block partition cost with mixed targets includes transfer
    // -------------------------------------------------------------------

    #[test]
    fn test_partition_cost_with_transfer() {
        let module = build_two_block_module();
        let graph = ComputeGraph::from_module(&module);

        // Both on CpuScalar: no transfer cost
        let mut all_cpu = HashMap::new();
        for node in &graph.nodes {
            all_cpu.insert(node.id, ComputeTarget::CpuScalar);
        }
        let cost_all_cpu = graph.partition_cost(&all_cpu).unwrap();

        // One on CpuScalar, one on CpuSimd: still no transfer cost (same core)
        let mut mixed_cpu_simd = HashMap::new();
        mixed_cpu_simd.insert(graph.nodes[0].id, ComputeTarget::CpuScalar);
        mixed_cpu_simd.insert(graph.nodes[1].id, ComputeTarget::CpuSimd);
        let cost_mixed = graph.partition_cost(&mixed_cpu_simd).unwrap();

        // Both should be computable
        assert!(cost_all_cpu > 0);
        assert!(cost_mixed > 0);
    }

    // -------------------------------------------------------------------
    // Test: ComputeNodeId display
    // -------------------------------------------------------------------

    #[test]
    fn test_compute_node_id_display() {
        assert_eq!(format!("{}", ComputeNodeId(42)), "node_42");
    }

    // -------------------------------------------------------------------
    // Test: NodeKind display
    // -------------------------------------------------------------------

    #[test]
    fn test_node_kind_display() {
        assert_eq!(format!("{}", NodeKind::Scalar), "Scalar");
        assert_eq!(format!("{}", NodeKind::DataParallel), "DataParallel");
        assert_eq!(format!("{}", NodeKind::MatrixHeavy), "MatrixHeavy");
    }

    // -------------------------------------------------------------------
    // Test: Empty module produces empty graph
    // -------------------------------------------------------------------

    #[test]
    fn test_empty_module_empty_graph() {
        let module = Module::new("empty");
        let graph = ComputeGraph::from_module(&module);
        assert_eq!(graph.num_nodes(), 0);
        assert_eq!(graph.num_edges(), 0);
    }

    // -------------------------------------------------------------------
    // Test: Partition cost of empty graph
    // -------------------------------------------------------------------

    #[test]
    fn test_empty_graph_partition_cost() {
        let graph = ComputeGraph::new();
        let assignment = HashMap::new();
        let cost = graph.partition_cost(&assignment);
        assert_eq!(cost, Some(0));
    }

    // -------------------------------------------------------------------
    // Test: TransferCost::zero
    // -------------------------------------------------------------------

    #[test]
    fn test_transfer_cost_zero() {
        let zero = TransferCost::zero();
        assert_eq!(zero.total_cycles, 0);
        assert_eq!(zero.overhead_cycles, 0);
        assert_eq!(zero.per_byte_nanocycles, 0);
    }

    // -------------------------------------------------------------------
    // Test: ComputeCost default
    // -------------------------------------------------------------------

    #[test]
    fn test_compute_cost_default() {
        let cost = ComputeCost::default();
        assert_eq!(cost.latency_cycles, 1);
        assert_eq!(cost.throughput_ops_per_kcycle, 1000);
    }

    // -------------------------------------------------------------------
    // Test: Graph outgoing/incoming edges
    // -------------------------------------------------------------------

    #[test]
    fn test_graph_edge_queries() {
        let module = build_two_block_module();
        let graph = ComputeGraph::from_module(&module);

        if graph.num_edges() > 0 {
            let outgoing = graph.outgoing_edges(ComputeNodeId(0));
            let incoming = graph.incoming_edges(ComputeNodeId(1));
            assert!(!outgoing.is_empty(), "Node 0 should have outgoing edges");
            assert!(!incoming.is_empty(), "Node 1 should have incoming edges");
        }
    }

    // -------------------------------------------------------------------
    // Test: Pattern detection helper - scalar instructions
    // -------------------------------------------------------------------

    #[test]
    fn test_detect_data_parallel_requires_arrays() {
        let instrs = [InstrNode {
            inst: Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::I32);
        types.insert(ValueId::new(1), Ty::I32);

        assert!(!detect_data_parallel(&refs, &types));
    }

    // -------------------------------------------------------------------
    // Test: Pattern detection helper - array FAdd is data-parallel
    // -------------------------------------------------------------------

    #[test]
    fn test_detect_data_parallel_with_arrays() {
        let instrs = [InstrNode {
            inst: Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::Array(TyId::new(0), 100),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::Array(TyId::new(0), 100));
        types.insert(ValueId::new(1), Ty::Array(TyId::new(0), 100));

        assert!(detect_data_parallel(&refs, &types));
    }

    // -------------------------------------------------------------------
    // Test: Pattern detection - MAC pattern requires both FMul and FAdd
    // -------------------------------------------------------------------

    #[test]
    fn test_detect_matrix_heavy_requires_mac() {
        // FMul alone is not matrix-heavy
        let instrs = [InstrNode {
            inst: Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::Array(TyId::new(0), 100),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::Array(TyId::new(0), 100));

        assert!(!detect_matrix_heavy(&refs, &types));
    }

    // -------------------------------------------------------------------
    // Test: classify_node prioritizes MatrixHeavy over DataParallel
    // -------------------------------------------------------------------

    #[test]
    fn test_classify_node_matrix_over_parallel() {
        let instrs = [
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FMul,
                    ty: Ty::Array(TyId::new(0), 100),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                results: vec![ValueId::new(2)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: ValueId::new(2),
                    rhs: ValueId::new(2),
                },
                results: vec![ValueId::new(3)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
        ];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::Array(TyId::new(0), 100));
        types.insert(ValueId::new(1), Ty::Array(TyId::new(0), 100));

        // MAC pattern on arrays -> MatrixHeavy takes priority
        assert_eq!(classify_node(&refs, &types), NodeKind::MatrixHeavy);
    }

    // -------------------------------------------------------------------
    // Test: estimate_type_bytes
    // -------------------------------------------------------------------

    #[test]
    fn test_estimate_type_bytes() {
        assert_eq!(estimate_type_bytes(&Ty::Bool), 1);
        assert_eq!(estimate_type_bytes(&Ty::I8), 1);
        assert_eq!(estimate_type_bytes(&Ty::I16), 2);
        assert_eq!(estimate_type_bytes(&Ty::I32), 4);
        assert_eq!(estimate_type_bytes(&Ty::I64), 8);
        assert_eq!(estimate_type_bytes(&Ty::F32), 4);
        assert_eq!(estimate_type_bytes(&Ty::F64), 8);
        assert_eq!(estimate_type_bytes(&Ty::Array(TyId::new(0), 100)), 800);
        assert_eq!(estimate_type_bytes(&Ty::Ptr), 8);
    }

    #[test]
    fn huge_array_data_size_saturates_without_u32_truncation_or_u64_wrap() {
        let mut module = build_data_parallel_module();
        let huge_array = Ty::Array(TyId::new(0), u64::MAX);
        let block = &mut module.functions[0].blocks[0];
        block.params[0].1 = huge_array.clone();
        block.params[1].1 = huge_array.clone();
        let Inst::BinOp { ty, .. } = &mut block.body[0].inst else {
            panic!("data-parallel fixture must begin with a binary operation");
        };
        *ty = huge_array;

        let graph = ComputeGraph::from_module(&module);
        assert_eq!(graph.nodes[0].data_size_bytes, u64::MAX);
        assert_eq!(
            estimate_type_bytes(&Ty::Array(TyId::new(0), u64::MAX)),
            u64::MAX
        );
        assert_eq!(
            trust_ir_ty_to_lir_type_for_analyzer(&Ty::Array(TyId::new(0), u64::MAX)),
            None
        );
    }

    // -------------------------------------------------------------------
    // Issue #404: MatMulShape
    // -------------------------------------------------------------------

    #[test]
    fn test_matmul_shape_square_and_nonsquare() {
        // Non-square
        let shape = MatMulShape::new(128, 64, 32, LirType::F32);
        assert!(!shape.is_square());
        assert_eq!(shape.m, 128);
        assert_eq!(shape.k, 64);
        assert_eq!(shape.n, 32);
        // total = M*K + K*N + M*N = 128*64 + 64*32 + 128*32 = 8192+2048+4096 = 14336
        assert_eq!(shape.total_elements(), 14336);
        // F32 = 4 bytes, so 14336 * 4 = 57344 bytes
        assert_eq!(shape.total_bytes(), 57344);

        // Square
        let square = MatMulShape::new(64, 64, 64, LirType::F32);
        assert!(square.is_square());
        assert_eq!(square.total_elements(), 3 * 64 * 64);
        assert_eq!(square.total_bytes(), 3 * 64 * 64 * 4);
    }

    #[test]
    fn test_derive_square_matmul_shape_recovers_dim() {
        // 3 * 64^2 * 4 = 49152 -> dim = 64
        let shape = derive_square_matmul_shape(49152, "FMUL", ComputeNodeId(0));
        let shape = shape.expect("expected some shape");
        assert_eq!(shape.m, 64);
        assert_eq!(shape.k, 64);
        assert_eq!(shape.n, 64);
        assert_eq!(shape.elem_type, LirType::F32);

        // Integer path (dominant_op = ADD -> I32)
        let shape_i = derive_square_matmul_shape(49152, "ADD", ComputeNodeId(1));
        let shape_i = shape_i.expect("expected some shape");
        assert_eq!(shape_i.elem_type, LirType::I32);
    }

    #[test]
    fn test_derive_square_matmul_shape_zero_bytes_is_none() {
        assert!(derive_square_matmul_shape(0, "FMUL", ComputeNodeId(0)).is_none());
        // Too small to round up to dim>=1: total_elements = 0/4 = 0
        assert!(derive_square_matmul_shape(4, "FMUL", ComputeNodeId(0)).is_none());
    }

    // -------------------------------------------------------------------
    // Test: ComputeGraph manual construction
    // -------------------------------------------------------------------

    #[test]
    fn test_manual_graph_construction() {
        let mut graph = ComputeGraph::new();

        let mut costs_a = HashMap::new();
        costs_a.insert(
            ComputeTarget::CpuScalar,
            ComputeCost {
                latency_cycles: 10,
                throughput_ops_per_kcycle: 1000,
            },
        );
        costs_a.insert(
            ComputeTarget::CpuSimd,
            ComputeCost {
                latency_cycles: 5,
                throughput_ops_per_kcycle: 2000,
            },
        );

        graph.add_node(ComputeNode {
            id: ComputeNodeId(0),
            instructions: vec![],
            costs: costs_a,
            legal_targets: vec![ComputeTarget::CpuScalar, ComputeTarget::CpuSimd],
            kind: NodeKind::DataParallel,
            data_size_bytes: 1000,
            produced_values: vec![],
            consumed_values: vec![],
            dominant_op: "ADD".to_string(),
            target_legality: None,
            matmul_shape: None,
        });

        let mut costs_b = HashMap::new();
        costs_b.insert(
            ComputeTarget::CpuScalar,
            ComputeCost {
                latency_cycles: 20,
                throughput_ops_per_kcycle: 1000,
            },
        );
        costs_b.insert(
            ComputeTarget::CpuSimd,
            ComputeCost {
                latency_cycles: 8,
                throughput_ops_per_kcycle: 2000,
            },
        );

        graph.add_node(ComputeNode {
            id: ComputeNodeId(1),
            instructions: vec![],
            costs: costs_b,
            legal_targets: vec![ComputeTarget::CpuScalar, ComputeTarget::CpuSimd],
            kind: NodeKind::DataParallel,
            data_size_bytes: 2000,
            produced_values: vec![],
            consumed_values: vec![],
            dominant_op: "ADD".to_string(),
            target_legality: None,
            matmul_shape: None,
        });

        graph.add_edge(DataEdge {
            from: ComputeNodeId(0),
            to: ComputeNodeId(1),
            transfer_bytes: 1000,
            transfer_cost: TransferCost::zero(),
        });

        assert_eq!(graph.num_nodes(), 2);
        assert_eq!(graph.num_edges(), 1);

        // All on CpuScalar: 10 + 20 = 30 (no transfer cost between CPU nodes)
        let mut all_cpu = HashMap::new();
        all_cpu.insert(ComputeNodeId(0), ComputeTarget::CpuScalar);
        all_cpu.insert(ComputeNodeId(1), ComputeTarget::CpuScalar);
        assert_eq!(graph.partition_cost(&all_cpu), Some(30));

        // All on CpuSimd: 5 + 8 = 13
        let mut all_simd = HashMap::new();
        all_simd.insert(ComputeNodeId(0), ComputeTarget::CpuSimd);
        all_simd.insert(ComputeNodeId(1), ComputeTarget::CpuSimd);
        assert_eq!(graph.partition_cost(&all_simd), Some(13));

        // Mixed CPU/SIMD: 10 + 8 = 18 + 0 transfer (CPU<->SIMD is zero)
        let mut mixed = HashMap::new();
        mixed.insert(ComputeNodeId(0), ComputeTarget::CpuScalar);
        mixed.insert(ComputeNodeId(1), ComputeTarget::CpuSimd);
        assert_eq!(graph.partition_cost(&mixed), Some(18));
    }

    // -------------------------------------------------------------------
    // Test: Cost estimation varies by node kind and target
    // -------------------------------------------------------------------

    #[test]
    fn test_cost_estimation_scalar_vs_parallel() {
        let scalar_cpu = estimate_compute_cost(NodeKind::Scalar, 10, 80, ComputeTarget::CpuScalar);
        let parallel_cpu =
            estimate_compute_cost(NodeKind::DataParallel, 10, 80, ComputeTarget::CpuScalar);

        // Data-parallel on CPU scalar is more expensive than scalar (iterates over data)
        assert!(
            parallel_cpu.latency_cycles >= scalar_cpu.latency_cycles,
            "DataParallel should cost >= Scalar on CPU: parallel={}, scalar={}",
            parallel_cpu.latency_cycles,
            scalar_cpu.latency_cycles,
        );
    }

    // -------------------------------------------------------------------
    // Test: GPU cost lower than CPU for data-parallel
    // -------------------------------------------------------------------

    #[test]
    fn test_gpu_cheaper_for_data_parallel() {
        let data_size = 8000; // large enough for GPU
        let n_instrs = 5;

        let cpu_cost = estimate_compute_cost(
            NodeKind::DataParallel,
            n_instrs,
            data_size,
            ComputeTarget::CpuScalar,
        );
        let gpu_cost = estimate_compute_cost(
            NodeKind::DataParallel,
            n_instrs,
            data_size,
            ComputeTarget::Gpu,
        );

        assert!(
            gpu_cost.latency_cycles < cpu_cost.latency_cycles,
            "GPU should be cheaper for data-parallel: GPU={}, CPU={}",
            gpu_cost.latency_cycles,
            cpu_cost.latency_cycles,
        );
    }

    // -------------------------------------------------------------------
    // Test: ANE cheapest for matrix-heavy
    // -------------------------------------------------------------------

    #[test]
    fn test_ane_cheapest_for_matrix_heavy() {
        let data_size = 8000;
        let n_instrs = 5;

        let cpu_cost = estimate_compute_cost(
            NodeKind::MatrixHeavy,
            n_instrs,
            data_size,
            ComputeTarget::CpuScalar,
        );
        let gpu_cost = estimate_compute_cost(
            NodeKind::MatrixHeavy,
            n_instrs,
            data_size,
            ComputeTarget::Gpu,
        );
        let ane_cost = estimate_compute_cost(
            NodeKind::MatrixHeavy,
            n_instrs,
            data_size,
            ComputeTarget::NeuralEngine,
        );

        assert!(
            ane_cost.latency_cycles <= gpu_cost.latency_cycles,
            "ANE should be <= GPU for matrix-heavy: ANE={}, GPU={}",
            ane_cost.latency_cycles,
            gpu_cost.latency_cycles,
        );
        assert!(
            gpu_cost.latency_cycles < cpu_cost.latency_cycles,
            "GPU should be < CPU for matrix-heavy: GPU={}, CPU={}",
            gpu_cost.latency_cycles,
            cpu_cost.latency_cycles,
        );
    }

    // -------------------------------------------------------------------
    // Test: Multiple functions in module produce separate nodes
    // -------------------------------------------------------------------

    #[test]
    fn test_multiple_functions_produce_nodes() {
        let module = Module {
            name: "multi".to_string(),
            functions: vec![
                TrustIrFunction {
                    summary: None,
                    producer: None,
                    value_names: None,
                    scopes: None,
                    source_provenance: None,
                    attrs: Default::default(),
                    id: FuncId::new(0),
                    name: "foo".to_string(),
                    ty: FuncTyId::new(0),
                    entry: BlockId::new(0),
                    blocks: vec![TrustIrBlock {
                        id: BlockId::new(0),
                        params: vec![(ValueId::new(0), Ty::I32)],
                        body: vec![InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(0)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        }],
                    }],
                    proofs: vec![],
                    calling_conv: CallingConv::default(),
                    linkage: Linkage::default(),
                },
                TrustIrFunction {
                    summary: None,
                    producer: None,
                    value_names: None,
                    scopes: None,
                    source_provenance: None,
                    attrs: Default::default(),
                    id: FuncId::new(1),
                    name: "bar".to_string(),
                    ty: FuncTyId::new(0),
                    entry: BlockId::new(0),
                    blocks: vec![TrustIrBlock {
                        id: BlockId::new(0),
                        params: vec![(ValueId::new(10), Ty::I64)],
                        body: vec![InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(10)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        }],
                    }],
                    proofs: vec![],
                    calling_conv: CallingConv::default(),
                    linkage: Linkage::default(),
                },
            ],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        };

        let graph = ComputeGraph::from_module(&module);
        assert_eq!(
            graph.num_nodes(),
            2,
            "Two functions should produce two nodes"
        );
    }

    // ===================================================================
    // Proof-graph bridge tests (Gap 1: ProofAnalyzer <-> ComputeGraph)
    // ===================================================================

    // -------------------------------------------------------------------
    // Test helpers for proof-guided construction
    // -------------------------------------------------------------------

    use crate::adapter::{Proof, ProofContext};
    use crate::instructions::Value;
    use crate::target_analysis::{SubgraphId, SubgraphProof, TargetProofContext};

    /// Build a TargetProofContext with Pure subgraph proof on node 0,
    /// plus InBounds+ValidBorrow on the first two values.
    fn full_proof_context() -> TargetProofContext {
        let mut proof_ctx = ProofContext::default();
        // Add InBounds + ValidBorrow proofs on LIR Values 0 and 1.
        // These correspond to the consumed_values mapped as Value(0), Value(1)
        // by the graph builder.
        for i in 0..2 {
            proof_ctx.value_proofs.insert(
                Value(i),
                vec![
                    Proof::InBounds {
                        base: ValueId::new(i),
                        index: ValueId::new(i + 100),
                    },
                    Proof::ValidBorrow {
                        borrow: ValueId::new(i),
                    },
                ],
            );
        }
        let mut ctx = TargetProofContext::new(proof_ctx);
        // Add Pure proof on subgraph 0 (corresponds to first node).
        ctx.add_subgraph_proof(SubgraphId(0), SubgraphProof::Pure);
        ctx
    }

    /// Build a TargetProofContext with full proofs for GPU+parallel reduction.
    fn full_gpu_proof_context() -> TargetProofContext {
        let mut ctx = full_proof_context();
        ctx.add_subgraph_proof(SubgraphId(0), SubgraphProof::Associative);
        ctx.add_subgraph_proof(SubgraphId(0), SubgraphProof::Commutative);
        ctx
    }

    // -------------------------------------------------------------------
    // Test: with_proof_context propagates Pure proof to unlock SIMD+GPU
    // -------------------------------------------------------------------

    #[test]
    fn test_with_proof_context_unlocks_gpu() {
        let module = build_data_parallel_module();
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);

        assert_eq!(graph.num_nodes(), 1);
        let node = &graph.nodes[0];

        // With Pure + InBounds + ValidBorrow, GPU should be legal for
        // data-parallel array operations (data size is large enough).
        assert!(
            node.legal_targets.contains(&ComputeTarget::Gpu),
            "GPU should be legal with full proofs, got: {:?}",
            node.legal_targets
        );
        assert!(node.legal_targets.contains(&ComputeTarget::CpuScalar));
        assert!(node.legal_targets.contains(&ComputeTarget::CpuSimd));

        // target_legality should be populated.
        assert!(node.target_legality.is_some());
        let legality = node.target_legality.as_ref().unwrap();
        assert!(legality.is_legal(ComputeTarget::Gpu));
    }

    // -------------------------------------------------------------------
    // Test: without proofs, GPU is illegal
    // -------------------------------------------------------------------

    #[test]
    fn test_without_proofs_cpu_only() {
        let module = build_data_parallel_module();
        let graph = ComputeGraph::from_module(&module);

        assert_eq!(graph.num_nodes(), 1);
        let node = &graph.nodes[0];

        // Without proofs, side effects are not proven absent -> CPU/SIMD only.
        assert!(node.legal_targets.contains(&ComputeTarget::CpuScalar));
        assert!(node.legal_targets.contains(&ComputeTarget::CpuSimd));
        assert!(
            !node.legal_targets.contains(&ComputeTarget::Gpu),
            "GPU should be illegal without proofs"
        );
        assert!(
            !node.legal_targets.contains(&ComputeTarget::NeuralEngine),
            "ANE should be illegal without proofs"
        );
    }

    // -------------------------------------------------------------------
    // Test: target_recommendations picks cheapest legal target
    // -------------------------------------------------------------------

    #[test]
    fn test_target_recommendations_prefer_gpu() {
        // Use large module so workload exceeds GPU profitability thresholds.
        let module = build_large_data_parallel_module();
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);
        let recs = graph.target_recommendations();

        assert_eq!(recs.len(), 1);
        let rec = &recs[0];

        // For large data-parallel workloads with full proofs, GPU should pass
        // profitability check and be in the filtered legal targets.
        assert!(
            rec.legal_targets.contains(&ComputeTarget::Gpu),
            "GPU should be in legal targets for large workload"
        );

        // The recommendation should be GPU because it has the lowest latency
        // for large data-parallel workloads.
        assert_eq!(
            rec.recommended_target,
            ComputeTarget::Gpu,
            "Should recommend GPU for large data-parallel with full proofs, got: {}",
            rec.recommended_target
        );
    }

    // -------------------------------------------------------------------
    // Test: target_recommendations without proofs -> CPU recommendation
    // -------------------------------------------------------------------

    #[test]
    fn test_target_recommendations_no_proofs_cpu() {
        let module = build_scalar_add_module();
        let graph = ComputeGraph::from_module(&module);
        let recs = graph.target_recommendations();

        assert_eq!(recs.len(), 1);
        let rec = &recs[0];

        // Without proofs, should recommend CpuScalar (cheapest for scalar ops).
        assert_eq!(rec.recommended_target, ComputeTarget::CpuScalar);
        assert!(!rec.parallel_reduction_legal);
        assert!(
            !rec.legal_targets.contains(&ComputeTarget::Gpu),
            "GPU should not be in legal targets without proofs"
        );
    }

    // -------------------------------------------------------------------
    // Test: proof_guided_partition_cost returns a valid cost
    // -------------------------------------------------------------------

    #[test]
    fn test_proof_guided_partition_cost() {
        let module = build_data_parallel_module();
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);
        let cost = graph.proof_guided_partition_cost();

        assert!(cost.is_some(), "Should produce a valid partition cost");
        assert!(cost.unwrap() > 0, "Cost should be positive");
    }

    // -------------------------------------------------------------------
    // Test: proof_guided_partition_cost on empty graph
    // -------------------------------------------------------------------

    #[test]
    fn test_proof_guided_partition_cost_empty_graph() {
        let graph = ComputeGraph::new();
        let cost = graph.proof_guided_partition_cost();
        assert_eq!(cost, Some(0));
    }

    // -------------------------------------------------------------------
    // Test: subgraph proofs from TargetProofContext propagate to nodes
    // -------------------------------------------------------------------

    #[test]
    fn test_subgraph_proofs_propagate_to_nodes() {
        let module = build_data_parallel_module();
        let proof_ctx = full_gpu_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);

        let node = &graph.nodes[0];
        let legality = node.target_legality.as_ref().unwrap();

        // With Associative + Commutative proofs, parallel reduction should be legal.
        assert!(
            legality.parallel_reduction_legal,
            "Parallel reduction should be legal with Associative + Commutative proofs"
        );
    }

    // -------------------------------------------------------------------
    // Test: target_recommendations reports parallel reduction
    // -------------------------------------------------------------------

    #[test]
    fn test_recommendations_include_parallel_reduction() {
        let module = build_data_parallel_module();
        let proof_ctx = full_gpu_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);
        let recs = graph.target_recommendations();

        assert_eq!(recs.len(), 1);
        assert!(
            recs[0].parallel_reduction_legal,
            "Recommendation should report parallel reduction legal"
        );
    }

    // -------------------------------------------------------------------
    // Test: annotate_with_proofs upgrades node legality post-construction
    // -------------------------------------------------------------------

    #[test]
    fn test_annotate_with_proofs_upgrades_legality() {
        let module = build_data_parallel_module();

        // Build graph without proofs first.
        let mut graph = ComputeGraph::from_module(&module);
        assert!(
            !graph.nodes[0].legal_targets.contains(&ComputeTarget::Gpu),
            "GPU should be illegal before annotation"
        );

        // Now annotate with full proofs.
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();
        graph.annotate_with_proofs(&module, &proof_ctx, &analyzer);

        assert!(
            graph.nodes[0].legal_targets.contains(&ComputeTarget::Gpu),
            "GPU should be legal after annotation with proofs"
        );
        assert!(graph.nodes[0].target_legality.is_some());
    }

    // -------------------------------------------------------------------
    // Test: matrix-heavy with full proofs recommends GPU or ANE
    // -------------------------------------------------------------------

    #[test]
    fn test_matrix_heavy_with_proofs_recommends_accelerator() {
        // Use large module so workload exceeds GPU/ANE profitability thresholds.
        let module = build_large_matrix_heavy_module();

        let mut proof_ctx = ProofContext::default();
        for i in 0..2 {
            proof_ctx.value_proofs.insert(
                Value(i),
                vec![
                    Proof::InBounds {
                        base: ValueId::new(i),
                        index: ValueId::new(i + 100),
                    },
                    Proof::ValidBorrow {
                        borrow: ValueId::new(i),
                    },
                ],
            );
        }
        let mut ctx = TargetProofContext::new(proof_ctx);
        ctx.add_subgraph_proof(SubgraphId(0), SubgraphProof::Pure);

        let analyzer = ProofAnalyzer::with_defaults();
        let graph = ComputeGraph::with_proof_context(&module, ctx, &analyzer);
        let recs = graph.target_recommendations();

        assert_eq!(recs.len(), 1);
        let rec = &recs[0];

        // Matrix-heavy with large workload: GPU should be recommended
        // (profitability thresholds exceeded).
        assert!(
            rec.recommended_target == ComputeTarget::Gpu
                || rec.recommended_target == ComputeTarget::NeuralEngine,
            "Large matrix-heavy with proofs should recommend GPU or ANE, got: {}",
            rec.recommended_target
        );
    }

    // -------------------------------------------------------------------
    // Test: from_module_with_proofs builds graph with proof context
    // -------------------------------------------------------------------

    #[test]
    fn test_from_module_with_proofs() {
        let module = build_data_parallel_module();
        let proof_ctx = full_proof_context();

        let graph = ComputeGraph::from_module_with_proofs(&module, proof_ctx);

        assert_eq!(graph.num_nodes(), 1);
        // from_module_with_proofs uses the default analyzer, but passes proofs.
        assert!(graph.nodes[0].target_legality.is_some());
    }

    // -------------------------------------------------------------------
    // Test: proof_guided_partition_cost < naive CPU-only cost
    // -------------------------------------------------------------------

    #[test]
    fn test_proof_guided_cost_beats_cpu_only() {
        let module = build_data_parallel_module();
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);

        // Compute proof-guided cost (should pick GPU for data-parallel).
        let guided_cost = graph.proof_guided_partition_cost().unwrap();

        // Compute CPU-only cost.
        let mut cpu_assignment = HashMap::new();
        for node in &graph.nodes {
            cpu_assignment.insert(node.id, ComputeTarget::CpuScalar);
        }
        let cpu_cost = graph.partition_cost(&cpu_assignment).unwrap();

        assert!(
            guided_cost <= cpu_cost,
            "Proof-guided cost ({}) should be <= CPU-only cost ({})",
            guided_cost,
            cpu_cost
        );
    }

    // -------------------------------------------------------------------
    // Test: target_legality carries justification strings
    // -------------------------------------------------------------------

    #[test]
    fn test_legality_justification_strings() {
        let module = build_data_parallel_module();
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);
        let node = &graph.nodes[0];
        let legality = node.target_legality.as_ref().unwrap();

        // GPU reason should mention proof-related justification.
        let gpu_reason = legality.reason(ComputeTarget::Gpu);
        assert!(
            gpu_reason.is_some(),
            "GPU should have a justification string"
        );
        let reason_text = gpu_reason.unwrap();
        assert!(
            reason_text.contains("Pure")
                || reason_text.contains("legal")
                || reason_text.contains("InBounds"),
            "GPU justification should reference proofs: {}",
            reason_text
        );
    }

    // ===================================================================
    // False-positive prevention tests (#159)
    // ===================================================================

    // -------------------------------------------------------------------
    // Test: scalar ops with small array params should NOT be data-parallel
    // -------------------------------------------------------------------

    #[test]
    fn test_small_array_not_data_parallel() {
        // An array of 2 elements is too small to justify vectorization
        let instrs = [InstrNode {
            inst: Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::Array(TyId::new(0), 2),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::Array(TyId::new(0), 2));
        types.insert(ValueId::new(1), Ty::Array(TyId::new(0), 2));

        assert!(
            !detect_data_parallel(&refs, &types),
            "Arrays with < MIN_VECTORIZABLE_ELEMENTS should not be classified as data-parallel"
        );
    }

    // -------------------------------------------------------------------
    // Test: scalar binary op coexisting with array param is NOT data-parallel
    // -------------------------------------------------------------------

    #[test]
    fn test_scalar_op_with_array_param_not_data_parallel() {
        // The binary op operates on scalar i32 values, even though an array
        // parameter exists in the value types. This should NOT match.
        let instrs = [InstrNode {
            inst: Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::I32); // operand is scalar
        types.insert(ValueId::new(1), Ty::I32); // operand is scalar
        // Some other value is array-typed but not an operand of the Add
        types.insert(ValueId::new(10), Ty::Array(TyId::new(0), 1000));

        assert!(
            !detect_data_parallel(&refs, &types),
            "Scalar op with array in scope should not match data-parallel pattern"
        );
    }

    // -------------------------------------------------------------------
    // Test: FMul without subsequent FAdd is NOT matrix-heavy
    // (already tested, but verify the strengthened check still works)
    // -------------------------------------------------------------------

    #[test]
    fn test_fmul_only_with_array_not_matrix_heavy() {
        let instrs = [InstrNode {
            inst: Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::Array(TyId::new(0), 100),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![],
            span: None,
            proof_context: None,
            scope: None,
        }];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::Array(TyId::new(0), 100));
        types.insert(ValueId::new(1), Ty::Array(TyId::new(0), 100));

        assert!(
            !detect_matrix_heavy(&refs, &types),
            "FMul alone (no FAdd consuming result) should not be matrix-heavy"
        );
    }

    // -------------------------------------------------------------------
    // Test: FMul + FAdd with no data dependency is NOT matrix-heavy
    // -------------------------------------------------------------------

    #[test]
    fn test_independent_fmul_fadd_not_matrix_heavy() {
        // FMul produces ValueId::new(2), but FAdd does NOT consume it --
        // it consumes ValueId::new(3) and ValueId::new(4) instead.
        let instrs = [
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FMul,
                    ty: Ty::Array(TyId::new(0), 100),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                results: vec![ValueId::new(2)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: ValueId::new(3), // NOT ValueId::new(2)
                    rhs: ValueId::new(4), // NOT ValueId::new(2)
                },
                results: vec![ValueId::new(5)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
        ];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::Array(TyId::new(0), 100));
        types.insert(ValueId::new(1), Ty::Array(TyId::new(0), 100));
        types.insert(ValueId::new(3), Ty::F64);
        types.insert(ValueId::new(4), Ty::F64);

        assert!(
            !detect_matrix_heavy(&refs, &types),
            "FMul + FAdd without data dependency should not be matrix-heavy"
        );
    }

    // -------------------------------------------------------------------
    // Test: FMul on scalar + FAdd consuming result is NOT matrix-heavy
    //       (neither FMul operand is array-typed)
    // -------------------------------------------------------------------

    #[test]
    fn test_scalar_fmul_fadd_not_matrix_heavy() {
        let instrs = [
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FMul,
                    ty: Ty::F64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                results: vec![ValueId::new(2)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: ValueId::new(2),
                    rhs: ValueId::new(2),
                },
                results: vec![ValueId::new(3)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
        ];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::F64); // scalar
        types.insert(ValueId::new(1), Ty::F64); // scalar
        // There IS an array in scope, but the FMul operands are not array-typed
        types.insert(ValueId::new(10), Ty::Array(TyId::new(0), 1000));

        assert!(
            !detect_matrix_heavy(&refs, &types),
            "Scalar FMul + FAdd with array in scope should not be matrix-heavy"
        );
    }

    // -------------------------------------------------------------------
    // Test: small array with MAC pattern is NOT matrix-heavy
    // -------------------------------------------------------------------

    #[test]
    fn test_small_array_mac_not_matrix_heavy() {
        // Array has only 2 elements -- below MIN_VECTORIZABLE_ELEMENTS
        let instrs = [
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FMul,
                    ty: Ty::Array(TyId::new(0), 2),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                results: vec![ValueId::new(2)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: ValueId::new(2),
                    rhs: ValueId::new(2),
                },
                results: vec![ValueId::new(3)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
        ];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::Array(TyId::new(0), 2));
        types.insert(ValueId::new(1), Ty::Array(TyId::new(0), 2));

        assert!(
            !detect_matrix_heavy(&refs, &types),
            "Small arrays (< MIN_VECTORIZABLE_ELEMENTS) should not match matrix-heavy"
        );
    }

    // -------------------------------------------------------------------
    // Test: Confirm valid MAC pattern with data dep still matches
    // -------------------------------------------------------------------

    #[test]
    fn test_valid_mac_with_dependency_matches() {
        // FMul produces ValueId::new(2), FAdd consumes ValueId::new(2) -- valid MAC
        let instrs = [
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FMul,
                    ty: Ty::Array(TyId::new(0), 100),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                results: vec![ValueId::new(2)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: ValueId::new(2),
                    rhs: ValueId::new(2),
                },
                results: vec![ValueId::new(3)],
                proofs: vec![],
                span: None,
                proof_context: None,
                scope: None,
            },
        ];
        let refs: Vec<&InstrNode> = instrs.iter().collect();

        let mut types = HashMap::new();
        types.insert(ValueId::new(0), Ty::Array(TyId::new(0), 100));
        types.insert(ValueId::new(1), Ty::Array(TyId::new(0), 100));

        assert!(
            detect_matrix_heavy(&refs, &types),
            "Valid MAC pattern with array operands and data dep should match"
        );
    }

    // -------------------------------------------------------------------
    // Test: Module with small array ops classifies as Scalar
    // -------------------------------------------------------------------

    #[test]
    fn test_small_array_module_classifies_scalar() {
        // A module with 2-element arrays should be classified as Scalar
        // (below the MIN_VECTORIZABLE_ELEMENTS threshold)
        let module = Module {
            name: "small_array".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "tiny_add".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![
                        (ValueId::new(0), Ty::Array(TyId::new(0), 2)),
                        (ValueId::new(1), Ty::Array(TyId::new(0), 2)),
                    ],
                    body: vec![
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::FAdd,
                                ty: Ty::Array(TyId::new(0), 2),
                                lhs: ValueId::new(0),
                                rhs: ValueId::new(1),
                            },
                            results: vec![ValueId::new(2)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(2)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                    ],
                }],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        };

        let graph = ComputeGraph::from_module(&module);
        assert_eq!(graph.num_nodes(), 1);
        assert_eq!(
            graph.nodes[0].kind,
            NodeKind::Scalar,
            "Small array operations should be classified as Scalar, not DataParallel"
        );
    }

    // -------------------------------------------------------------------
    // ProfitabilityAnalyzer integration tests
    // -------------------------------------------------------------------

    #[test]
    fn test_small_workload_filters_gpu_ane() {
        // Small data-parallel module (1000-element arrays, ~16KB data).
        // GPU requires >= 4096 elements; ANE requires >= 32KB.
        // Both should be filtered out by ProfitabilityAnalyzer.
        let module = build_data_parallel_module();
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);
        let recs = graph.target_recommendations();

        assert_eq!(recs.len(), 1);
        let rec = &recs[0];

        // GPU and ANE should be filtered out by profitability checks.
        assert!(
            !rec.legal_targets.contains(&ComputeTarget::Gpu),
            "GPU should be filtered for small workload (profitability)"
        );
        assert!(
            !rec.legal_targets.contains(&ComputeTarget::NeuralEngine),
            "ANE should be filtered for small workload (profitability)"
        );

        // Should recommend CPU target instead.
        assert!(
            rec.recommended_target == ComputeTarget::CpuScalar
                || rec.recommended_target == ComputeTarget::CpuSimd,
            "Small workload should recommend CPU, got: {}",
            rec.recommended_target
        );
    }

    #[test]
    fn test_large_workload_includes_gpu() {
        // Large data-parallel module (100K-element arrays, ~1.6MB data).
        // Well above GPU thresholds.
        let module = build_large_data_parallel_module();
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);
        let recs = graph.target_recommendations();

        assert_eq!(recs.len(), 1);
        let rec = &recs[0];

        // Large workload: GPU should pass profitability check.
        assert!(
            rec.legal_targets.contains(&ComputeTarget::Gpu),
            "GPU should be profitable for large workload"
        );
    }

    #[test]
    fn test_target_legality_filters_bitwise_from_ane() {
        // Build a module with bitwise operations (AND).
        // ANE does not support bitwise ops per ProfitabilityAnalyzer::target_legality.
        let module = Module {
            name: "bitwise".to_string(),
            functions: vec![TrustIrFunction {
                summary: None,
                producer: None,
                value_names: None,
                scopes: None,
                source_provenance: None,
                attrs: Default::default(),
                id: FuncId::new(0),
                name: "bitwise_and".to_string(),
                ty: FuncTyId::new(0),
                entry: BlockId::new(0),
                blocks: vec![TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![
                        (ValueId::new(0), Ty::Array(TyId::new(0), 100_000)),
                        (ValueId::new(1), Ty::Array(TyId::new(0), 100_000)),
                    ],
                    body: vec![
                        InstrNode {
                            inst: Inst::BinOp {
                                op: BinOp::And,
                                ty: Ty::Array(TyId::new(0), 100_000),
                                lhs: ValueId::new(0),
                                rhs: ValueId::new(1),
                            },
                            results: vec![ValueId::new(2)],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                        InstrNode {
                            inst: Inst::Return {
                                values: vec![ValueId::new(2)],
                            },
                            results: vec![],
                            proofs: vec![],
                            span: None,
                            proof_context: None,
                            scope: None,
                        },
                    ],
                }],
                proofs: vec![],
                calling_conv: CallingConv::default(),
                linkage: Linkage::default(),
            }],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![],
            func_types: vec![FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            }],
            types: vec![],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        };

        // Give full proofs so GPU/ANE are at least proof-legal.
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        let graph = ComputeGraph::with_proof_context(&module, proof_ctx, &analyzer);
        let recs = graph.target_recommendations();

        assert_eq!(recs.len(), 1);
        let rec = &recs[0];

        // ANE should be filtered: ProfitabilityAnalyzer says AND is not
        // ANE-legal (bitwise ops are not supported by the Neural Engine).
        assert!(
            !rec.legal_targets.contains(&ComputeTarget::NeuralEngine),
            "ANE should not be legal for bitwise AND (hardware limitation)"
        );
    }

    #[test]
    fn test_profitability_set_and_get() {
        // Verify that setting a ProfitabilityAnalyzer on a graph affects
        // target_recommendations() behavior.
        let module = build_data_parallel_module();
        let proof_ctx = full_proof_context();
        let analyzer = ProofAnalyzer::with_defaults();

        // Build graph WITHOUT profitability analyzer.
        let mut builder = GraphBuilder::new(analyzer.clone(), proof_ctx.clone());
        let mut graph = builder.build_from_module(&module);

        // Without profitability: GPU should appear in recommendations
        // (it's proof-legal and has lowest latency).
        let recs_without = graph.target_recommendations();
        let has_gpu_without = recs_without
            .iter()
            .any(|r| r.legal_targets.contains(&ComputeTarget::Gpu));

        // Now set the profitability analyzer.
        graph.set_profitability(ProfitabilityAnalyzer::new(CostModelGen::M1));

        // With profitability: GPU should be filtered for this small workload.
        let recs_with = graph.target_recommendations();
        let has_gpu_with = recs_with
            .iter()
            .any(|r| r.legal_targets.contains(&ComputeTarget::Gpu));

        // The small workload should see GPU removed after profitability filtering.
        if has_gpu_without {
            assert!(
                !has_gpu_with,
                "ProfitabilityAnalyzer should filter GPU for small workload"
            );
        }
    }

    #[test]
    fn test_dominant_op_derived_from_instructions() {
        // Build modules and verify the dominant_op field is set correctly.
        let module = build_data_parallel_module();
        let graph = ComputeGraph::from_module(&module);

        assert_eq!(graph.num_nodes(), 1);
        // data_parallel module has a single FAdd -> dominant op is "FADD"
        assert_eq!(
            graph.nodes[0].dominant_op, "FADD",
            "Data-parallel module should have dominant_op FADD"
        );

        // Matrix-heavy module has FMul + FAdd -> dominant is tied,
        // HashMap iteration order is nondeterministic but both are valid.
        let mat_module = build_matrix_heavy_module();
        let mat_graph = ComputeGraph::from_module(&mat_module);

        assert_eq!(mat_graph.num_nodes(), 1);
        let dom = &mat_graph.nodes[0].dominant_op;
        assert!(
            dom == "FMUL" || dom == "FADD",
            "Matrix-heavy module should have dominant_op FMUL or FADD, got: {}",
            dom
        );
    }
}
