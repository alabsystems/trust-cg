// trust-cg-codegen/metal_emitter.rs - Metal Shading Language (MSL) kernel emitter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Generates Metal compute kernel source text from GpuKernelShape and kernel
// pattern descriptors. Phase 1 of the Metal emission pipeline (MSL source;
// Phase 2 will emit AIR bitcode directly).
//
// Design doc: designs/2026-04-14-metal-ir-emission.md
// Reference: Apple. "Metal Shading Language Specification," Version 3.2.

//! Metal Shading Language (MSL) kernel source code generation.
//!
//! This module implements Phase 1 of the Metal emission pipeline: generating
//! human-readable MSL source text for GPU compute kernels. The emitted source
//! is compiled to AIR bitcode via `xcrun -sdk macosx metal` and archived into
//! a `.metallib` via `xcrun -sdk macosx metallib`.
//!
//! # Supported Kernel Patterns
//!
//! - **Parallel Map**: element-wise `output[tid] = f(input[tid])`
//! - **Parallel Reduce**: tree reduction within threadgroups + SIMD acceleration
//! - **Map-Reduce (fused)**: avoids materializing intermediate array
//! - **MatMul**: scalar per-output-element matrix multiply
//!
//! # Usage
//!
//! ```text
//! let emitter = MetalKernelEmitter::new("node_42", MslElementType::Float);
//! let kernel = MslKernel::parallel_map("neg(x)", 1024, 256);
//! let source = emitter.emit(&kernel);
//! ```

use std::collections::HashSet;
use std::fmt;

use trust_cg_lower::compute_graph::{
    AcceleratorBackend, AcceleratorBinaryOp, AcceleratorElementType, AcceleratorOperation,
    ComputeNode, ComputeNodeId, NodeKind, TrustIrValueId, estimate_transfer_cost,
};
use trust_cg_lower::dispatch::{DispatchOp, DispatchPlan};
use trust_cg_lower::target_analysis::ComputeTarget;
use trust_cg_opt::{
    CertifiedPassCheckerRecord, CertifiedPassRunRecord, CertifiedPassRunStatus, StableHasher,
};
use trust_cg_verify::gpu_semantics::{ElemKind, GpuReduceOp, ReduceOrderClass};

// ---------------------------------------------------------------------------
// Metal emit errors
// ---------------------------------------------------------------------------

/// Errors that can occur during Metal kernel generation from ComputeGraph nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetalEmitError {
    /// The node lacks an exact, compiler-derived semantic binding or the
    /// binding no longer matches its public metadata.
    SemanticBinding {
        node_id: ComputeNodeId,
        reason: String,
    },
    /// A GPU launch in the dispatch plan references no graph node.
    MissingPlanNode { node_id: ComputeNodeId },
    /// A launch and the plan's assignment disagree about the target.
    PlanAssignmentMismatch { node_id: ComputeNodeId },
    /// A plan launches the same GPU node more than once; buffer/result
    /// ownership for repeated launches is not represented yet.
    DuplicateKernelLaunch { node_id: ComputeNodeId },
    /// The public dispatch plan is not an exact, internally consistent
    /// orchestration of graph edges, assignments, launches, and syncs.
    InvalidDispatchPlan { reason: String },
    /// Node kind is not suitable for GPU execution (e.g., scalar).
    UnsuitableNodeKind {
        node_id: ComputeNodeId,
        kind: NodeKind,
    },
    /// GPU is not a legal target for this node.
    GpuNotLegal { node_id: ComputeNodeId },
    /// Node has zero data size, cannot compute element count.
    ZeroDataSize { node_id: ComputeNodeId },
    /// MatMul node dimensions could not be inferred (data size not
    /// a valid square or rectangular matrix).
    MatMulDimensionError {
        node_id: ComputeNodeId,
        data_size_bytes: u64,
    },
    /// A reduce node requested a tree-schedule kernel (threadgroup tree /
    /// `simd_*` intrinsics) for an order-sensitive
    /// (`ReduceOrderClass::StrictTree`) op × element combination.
    /// Floating-point add/mul are not associative, so a tree reduction is
    /// NOT equivalent to the source-order fold; refuse, fail-closed. The
    /// release boundary is summarized in the repository-level `LIMITATIONS.md`.
    ReduceOrderUnsound {
        node_id: ComputeNodeId,
        op: MslReduceOp,
        elem: MslElementType,
    },
}

impl fmt::Display for MetalEmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MetalEmitError::SemanticBinding { node_id, reason } => {
                write!(
                    f,
                    "node {node_id} has no valid Metal semantic binding: {reason}"
                )
            }
            MetalEmitError::MissingPlanNode { node_id } => {
                write!(
                    f,
                    "Metal dispatch plan references missing graph node {node_id}"
                )
            }
            MetalEmitError::PlanAssignmentMismatch { node_id } => write!(
                f,
                "Metal launch target disagrees with dispatch assignment for node {node_id}"
            ),
            MetalEmitError::DuplicateKernelLaunch { node_id } => {
                write!(
                    f,
                    "Metal dispatch plan launches node {node_id} more than once"
                )
            }
            MetalEmitError::InvalidDispatchPlan { reason } => {
                write!(f, "invalid Metal dispatch plan: {reason}")
            }
            MetalEmitError::UnsuitableNodeKind { node_id, kind } => {
                write!(
                    f,
                    "node {} has kind {} which is not suitable for Metal GPU execution",
                    node_id, kind
                )
            }
            MetalEmitError::GpuNotLegal { node_id } => {
                write!(f, "GPU is not a legal compute target for node {}", node_id)
            }
            MetalEmitError::ZeroDataSize { node_id } => {
                write!(
                    f,
                    "node {} has zero data_size_bytes, cannot infer element count",
                    node_id
                )
            }
            MetalEmitError::MatMulDimensionError {
                node_id,
                data_size_bytes,
            } => {
                write!(
                    f,
                    "cannot infer MatMul dimensions for node {} with data_size_bytes={}",
                    node_id, data_size_bytes
                )
            }
            MetalEmitError::ReduceOrderUnsound { node_id, op, elem } => {
                write!(
                    f,
                    "node {}: tree-schedule reduction {:?} over {} elements is \
                     order-sensitive (StrictTree) — fp add/mul are not associative, \
                     so the tree kernel is not equivalent to the source-order fold; \
                     refusing to emit (see LIMITATIONS.md)",
                    node_id, op, elem
                )
            }
        }
    }
}

impl std::error::Error for MetalEmitError {}

// ---------------------------------------------------------------------------
// MSL element types
// ---------------------------------------------------------------------------

/// Metal Shading Language scalar element type.
///
/// Maps to MSL built-in types used in kernel buffer declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MslElementType {
    /// 16-bit floating point (`half`).
    Half,
    /// 32-bit floating point (`float`).
    Float,
    /// 32-bit signed integer (`int`).
    Int,
    /// 32-bit unsigned integer (`uint`).
    Uint,
}

impl MslElementType {
    /// The SMT-side element kind this MSL type corresponds to, used for
    /// reduction order classification (`GpuReduceOp::order_class`).
    pub fn elem_kind(&self) -> ElemKind {
        match self {
            MslElementType::Half | MslElementType::Float => ElemKind::Fp,
            MslElementType::Int | MslElementType::Uint => ElemKind::BitVec(32),
        }
    }
}

impl fmt::Display for MslElementType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MslElementType::Half => write!(f, "half"),
            MslElementType::Float => write!(f, "float"),
            MslElementType::Int => write!(f, "int"),
            MslElementType::Uint => write!(f, "uint"),
        }
    }
}

// ---------------------------------------------------------------------------
// MSL expression: trust_ir op -> inline MSL
// ---------------------------------------------------------------------------

/// A trust_ir operation mapped to an inline MSL expression.
///
/// The expression generator maps trust_ir operations to MSL operators following
/// the table in the Metal IR emission design doc.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MslOp {
    /// `a + b`
    Add,
    /// `a - b`
    Sub,
    /// `a * b`
    Mul,
    /// `a / b`
    Div,
    /// `-a`
    Neg,
    /// `abs(a)`
    Abs,
    /// `sqrt(a)`
    Sqrt,
    /// `fma(a, b, c)`
    Fma,
    /// `min(a, b)`
    Min,
    /// `max(a, b)`
    Max,
    /// `clamp(x, lo, hi)`
    Clamp,
    /// `select(f, t, c)` (Metal order: false, true, condition)
    Select,
}

impl MslOp {
    /// Emit this operation as an inline MSL expression applied to operand names.
    ///
    /// For unary ops, only `a` is used. For binary, `a` and `b`.
    /// For ternary (fma, clamp, select), `a`, `b`, and `c`.
    pub fn emit(&self, a: &str, b: &str, c: &str) -> String {
        match self {
            MslOp::Add => format!("{a} + {b}"),
            MslOp::Sub => format!("{a} - {b}"),
            MslOp::Mul => format!("{a} * {b}"),
            MslOp::Div => format!("{a} / {b}"),
            MslOp::Neg => format!("-{a}"),
            MslOp::Abs => format!("abs({a})"),
            MslOp::Sqrt => format!("sqrt({a})"),
            MslOp::Fma => format!("fma({a}, {b}, {c})"),
            MslOp::Min => format!("min({a}, {b})"),
            MslOp::Max => format!("max({a}, {b})"),
            MslOp::Clamp => format!("clamp({a}, {b}, {c})"),
            MslOp::Select => format!("select({b}, {a}, {c})"),
        }
    }

    /// Number of operands required by this operation.
    pub fn arity(&self) -> u32 {
        match self {
            MslOp::Neg | MslOp::Abs | MslOp::Sqrt => 1,
            MslOp::Add | MslOp::Sub | MslOp::Mul | MslOp::Div | MslOp::Min | MslOp::Max => 2,
            MslOp::Fma | MslOp::Clamp | MslOp::Select => 3,
        }
    }
}

// ---------------------------------------------------------------------------
// Reduction operator (MSL-side)
// ---------------------------------------------------------------------------

/// Reduction operator for GPU reduce kernels.
///
/// Mirrors `GpuReduceOp` from `trust-cg-verify/gpu_semantics.rs` but expressed
/// as MSL source fragments rather than SMT expressions.
///
/// Reduction order is semantics: the `ParallelReduce`/`MapReduce` kernel
/// templates execute a TREE schedule, which is equivalent to the source-order
/// fold only for `ReduceOrderClass::ExactAC` op × element combinations
/// (integer/bitwise). All floating-point reductions are
/// `ReduceOrderClass::StrictTree` (fp add/mul are not associative; fp min/max
/// fail-closed) and are refused by [`emit_kernel_from_node`]. See
/// [`MslReduceOp::order_class`] and the repository-level `LIMITATIONS.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MslReduceOp {
    Add,
    Mul,
    Min,
    Max,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

impl MslReduceOp {
    /// The SMT-side `gpu_semantics::GpuReduceOp` this MSL op mirrors.
    pub fn gpu_reduce_op(&self) -> GpuReduceOp {
        match self {
            MslReduceOp::Add => GpuReduceOp::Add,
            MslReduceOp::Mul => GpuReduceOp::Mul,
            MslReduceOp::Min => GpuReduceOp::Min,
            MslReduceOp::Max => GpuReduceOp::Max,
            MslReduceOp::BitwiseAnd => GpuReduceOp::BitwiseAnd,
            MslReduceOp::BitwiseOr => GpuReduceOp::BitwiseOr,
            MslReduceOp::BitwiseXor => GpuReduceOp::BitwiseXor,
        }
    }

    /// Reduction order class of this op over the given MSL element type.
    ///
    /// Tree-schedule kernels (the `ParallelReduce`/`MapReduce` templates and
    /// every `simd_*` reducing intrinsic) are sound only for
    /// `ReduceOrderClass::ExactAC`. All FP combinations (including Min/Max,
    /// deliberately fail-closed) are `ReduceOrderClass::StrictTree`: the
    /// reduction must execute in source order.
    pub fn order_class(&self, elem: MslElementType) -> ReduceOrderClass {
        self.gpu_reduce_op().order_class(elem.elem_kind())
    }

    /// Emit the binary expression `<a> <op> <b>` in MSL.
    pub fn emit_binary(&self, a: &str, b: &str) -> String {
        match self {
            MslReduceOp::Add => format!("{a} + {b}"),
            MslReduceOp::Mul => format!("{a} * {b}"),
            MslReduceOp::Min => format!("min({a}, {b})"),
            MslReduceOp::Max => format!("max({a}, {b})"),
            MslReduceOp::BitwiseAnd => format!("{a} & {b}"),
            MslReduceOp::BitwiseOr => format!("{a} | {b}"),
            MslReduceOp::BitwiseXor => format!("{a} ^ {b}"),
        }
    }

    /// Emit the SIMD intrinsic name for this reduction operation.
    ///
    /// Returns `None` for bitwise ops (no SIMD intrinsic available).
    ///
    /// NOTE: these intrinsics combine lanes in a hardware-defined order, so
    /// they are only sound where [`MslReduceOp::order_class`] is
    /// `ReduceOrderClass::ExactAC` (integer/bitwise element types).
    pub fn simd_intrinsic(&self) -> Option<&'static str> {
        match self {
            MslReduceOp::Add => Some("simd_sum"),
            MslReduceOp::Mul => Some("simd_product"),
            MslReduceOp::Min => Some("simd_min"),
            MslReduceOp::Max => Some("simd_max"),
            MslReduceOp::BitwiseAnd => Some("simd_and"),
            MslReduceOp::BitwiseOr => Some("simd_or"),
            MslReduceOp::BitwiseXor => Some("simd_xor"),
        }
    }

    /// Identity element literal for this operation and element type.
    pub fn identity(&self, elem: MslElementType) -> &'static str {
        match (self, elem) {
            (MslReduceOp::Add, _) => "0",
            (MslReduceOp::Mul, _) => "1",
            (MslReduceOp::Min, MslElementType::Float | MslElementType::Half) => "INFINITY",
            (MslReduceOp::Min, MslElementType::Int) => "INT_MAX",
            (MslReduceOp::Min, MslElementType::Uint) => "UINT_MAX",
            (MslReduceOp::Max, MslElementType::Float | MslElementType::Half) => "-INFINITY",
            (MslReduceOp::Max, MslElementType::Int) => "INT_MIN",
            (MslReduceOp::Max, MslElementType::Uint) => "0",
            (MslReduceOp::BitwiseAnd, _) => "~0u",
            (MslReduceOp::BitwiseOr | MslReduceOp::BitwiseXor, _) => "0",
        }
    }
}

// ---------------------------------------------------------------------------
// Metal dispatch parameters
// ---------------------------------------------------------------------------

/// Metal dispatch size (equivalent to `MTLSize`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MtlSize {
    pub width: u64,
    pub height: u64,
    pub depth: u64,
}

impl MtlSize {
    pub fn new_1d(width: u64) -> Self {
        MtlSize {
            width,
            height: 1,
            depth: 1,
        }
    }

    pub fn new_2d(width: u64, height: u64) -> Self {
        MtlSize {
            width,
            height,
            depth: 1,
        }
    }
}

/// Computed Metal dispatch parameters for a kernel launch.
///
/// Ref: designs/2026-04-14-metal-ir-emission.md, "Grid Size Calculation"
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetalDispatchParams {
    /// Total threads in the grid (1D, 2D, or 3D).
    pub grid_size: MtlSize,
    /// Threads per threadgroup.
    pub threadgroup_size: MtlSize,
}

impl MetalDispatchParams {
    /// Compute dispatch params for a 1D parallel map/reduce.
    pub fn for_1d(element_count: u64, threadgroup_size: u32) -> Self {
        let tg = threadgroup_size as u64;
        let grid_width = element_count.div_ceil(tg) * tg;
        MetalDispatchParams {
            grid_size: MtlSize::new_1d(grid_width),
            threadgroup_size: MtlSize::new_1d(tg),
        }
    }

    /// Compute dispatch params for 2D matrix operations.
    pub fn for_2d(rows: u64, cols: u64, tile_size: u32) -> Self {
        let ts = tile_size as u64;
        MetalDispatchParams {
            grid_size: MtlSize::new_2d(cols.div_ceil(ts) * ts, rows.div_ceil(ts) * ts),
            threadgroup_size: MtlSize::new_2d(ts, ts),
        }
    }
}

// ---------------------------------------------------------------------------
// Metal storage mode
// ---------------------------------------------------------------------------

/// Metal buffer storage mode.
///
/// On Apple UMA, `Shared` avoids any data copy between CPU and GPU.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MtlStorageMode {
    /// CPU + GPU access, no copy (UMA). Default for Trust Codegen.
    Shared,
    /// GPU-only access. Used for intermediate GPU-to-GPU buffers.
    Private,
    /// Tile memory (render only). Not used for compute.
    Memoryless,
}

impl fmt::Display for MtlStorageMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MtlStorageMode::Shared => write!(f, "MTLResourceStorageModeShared"),
            MtlStorageMode::Private => write!(f, "MTLResourceStorageModePrivate"),
            MtlStorageMode::Memoryless => write!(f, "MTLResourceStorageModeMemoryless"),
        }
    }
}

// ---------------------------------------------------------------------------
// MSL kernel descriptors
// ---------------------------------------------------------------------------

/// A complete MSL kernel specification ready for source emission.
#[derive(Debug, Clone)]
pub enum MslKernel {
    /// Element-wise unary or binary map: `output[tid] = f(input[tid])`.
    ParallelMap {
        /// Inline MSL expression for the per-element function body.
        /// Tokens `input[tid]` / `a[tid]`, `b[tid]` are used by convention.
        body_expr: String,
        /// Number of input buffers (1 for unary, 2 for binary).
        input_count: u32,
        /// Total element count (grid size).
        element_count: u64,
        /// Threadgroup size.
        threadgroup_size: u32,
    },

    /// Tree reduction within threadgroups, partial results collected.
    ParallelReduce {
        /// Reduction operation.
        op: MslReduceOp,
        /// Whether to use SIMD-accelerated reduction.
        use_simd: bool,
        /// Total element count.
        element_count: u64,
        /// Threadgroup size.
        threadgroup_size: u32,
    },

    /// Fused map-reduce (map then reduce without materializing intermediate).
    MapReduce {
        /// Inline MSL expression for the map function.
        map_expr: String,
        /// Reduction operation.
        reduce_op: MslReduceOp,
        /// Total element count.
        element_count: u64,
        /// Threadgroup size.
        threadgroup_size: u32,
    },

    /// Matrix multiply.
    MatMul {
        /// M dimension (rows of A / rows of C).
        m: u64,
        /// K dimension (cols of A / rows of B).
        k: u64,
        /// N dimension (cols of B / cols of C).
        n: u64,
    },
}

impl MslKernel {
    /// Create a unary parallel map kernel.
    pub fn parallel_map(body_expr: &str, element_count: u64, threadgroup_size: u32) -> Self {
        MslKernel::ParallelMap {
            body_expr: body_expr.to_string(),
            input_count: 1,
            element_count,
            threadgroup_size,
        }
    }

    /// Create a binary parallel map kernel (two input arrays).
    pub fn parallel_map2(body_expr: &str, element_count: u64, threadgroup_size: u32) -> Self {
        MslKernel::ParallelMap {
            body_expr: body_expr.to_string(),
            input_count: 2,
            element_count,
            threadgroup_size,
        }
    }

    /// Create a parallel reduce kernel.
    pub fn parallel_reduce(
        op: MslReduceOp,
        use_simd: bool,
        element_count: u64,
        threadgroup_size: u32,
    ) -> Self {
        MslKernel::ParallelReduce {
            op,
            use_simd,
            element_count,
            threadgroup_size,
        }
    }

    /// Create a fused map-reduce kernel.
    pub fn map_reduce(
        map_expr: &str,
        reduce_op: MslReduceOp,
        element_count: u64,
        threadgroup_size: u32,
    ) -> Self {
        MslKernel::MapReduce {
            map_expr: map_expr.to_string(),
            reduce_op,
            element_count,
            threadgroup_size,
        }
    }

    /// Create a matrix multiply kernel.
    pub fn matmul(m: u64, k: u64, n: u64) -> Self {
        MslKernel::MatMul { m, k, n }
    }
}

// ---------------------------------------------------------------------------
// MetalKernelEmitter
// ---------------------------------------------------------------------------

/// Emits Metal Shading Language (MSL) source text for compute kernels.
///
/// Each emitter instance is associated with a single compute node (identified
/// by `node_id`) and produces kernel functions named `trust_cg_<pattern>_<node_id>`.
///
/// Ref: designs/2026-04-14-metal-ir-emission.md
pub struct MetalKernelEmitter {
    /// Compute node identifier (used in kernel function names).
    node_id: String,
    /// Element type for kernel buffers.
    elem_type: MslElementType,
}

impl MetalKernelEmitter {
    /// Create a new emitter for a given compute node.
    pub fn new(node_id: &str, elem_type: MslElementType) -> Self {
        MetalKernelEmitter {
            node_id: node_id.to_string(),
            elem_type,
        }
    }

    /// Emit complete MSL source text for the given kernel specification.
    ///
    /// The output includes `#include <metal_stdlib>`, kernel declaration,
    /// bounds checking, and the pattern-specific body.
    pub fn emit(&self, kernel: &MslKernel) -> String {
        let mut out = String::new();

        // Header
        out.push_str("#include <metal_stdlib>\nusing namespace metal;\n\n");
        out.push_str("// Generated by Trust Codegen — verified correct via ay proof\n");
        out.push_str(&format!("// Compute node: {}\n\n", self.node_id));

        match kernel {
            MslKernel::ParallelMap {
                body_expr,
                input_count,
                element_count,
                threadgroup_size: _,
            } => {
                self.emit_parallel_map(&mut out, body_expr, *input_count, *element_count);
            }
            MslKernel::ParallelReduce {
                op,
                use_simd,
                element_count,
                threadgroup_size,
            } => {
                self.emit_parallel_reduce(
                    &mut out,
                    *op,
                    *use_simd,
                    *element_count,
                    *threadgroup_size,
                );
            }
            MslKernel::MapReduce {
                map_expr,
                reduce_op,
                element_count,
                threadgroup_size,
            } => {
                self.emit_map_reduce(
                    &mut out,
                    map_expr,
                    *reduce_op,
                    *element_count,
                    *threadgroup_size,
                );
            }
            MslKernel::MatMul { m, k, n } => {
                self.emit_matmul(&mut out, *m, *k, *n);
            }
        }

        out
    }

    /// Emit a unary or binary parallel map kernel.
    fn emit_parallel_map(
        &self,
        out: &mut String,
        body_expr: &str,
        input_count: u32,
        element_count: u64,
    ) {
        let ty = &self.elem_type;
        if input_count == 1 {
            out.push_str(&format!(
                "kernel void trust_cg_map_{node}(\n\
                 \x20   const device {ty}* input  [[buffer(0)]],\n\
                 \x20   device {ty}* output       [[buffer(1)]],\n\
                 \x20   uint tid [[thread_position_in_grid]])\n\
                 {{\n\
                 \x20   if (tid >= {n}u) return;\n\
                 \x20   output[tid] = {body};\n\
                 }}\n",
                node = self.node_id,
                ty = ty,
                n = element_count,
                body = body_expr,
            ));
        } else {
            out.push_str(&format!(
                "kernel void trust_cg_map2_{node}(\n\
                 \x20   const device {ty}* a [[buffer(0)]],\n\
                 \x20   const device {ty}* b [[buffer(1)]],\n\
                 \x20   device {ty}* output  [[buffer(2)]],\n\
                 \x20   uint tid [[thread_position_in_grid]])\n\
                 {{\n\
                 \x20   if (tid >= {n}u) return;\n\
                 \x20   output[tid] = {body};\n\
                 }}\n",
                node = self.node_id,
                ty = ty,
                n = element_count,
                body = body_expr,
            ));
        }
    }

    /// Emit a parallel reduce kernel (threadgroup tree or SIMD-accelerated).
    ///
    /// Both templates execute a TREE schedule, so they are only semantics-
    /// preserving for `ReduceOrderClass::ExactAC` op × element combinations
    /// (see [`MslReduceOp::order_class`]). Callers must gate StrictTree
    /// combinations (all FP reductions) before requesting this template —
    /// [`emit_kernel_from_node`] does so fail-closed.
    fn emit_parallel_reduce(
        &self,
        out: &mut String,
        op: MslReduceOp,
        use_simd: bool,
        element_count: u64,
        threadgroup_size: u32,
    ) {
        let ty = &self.elem_type;
        let identity = op.identity(*ty);

        if use_simd {
            let intrinsic = op.simd_intrinsic().unwrap_or("simd_sum");
            out.push_str(&format!(
                "kernel void trust_cg_reduce_simd_{node}(\n\
                 \x20   const device {ty}* input       [[buffer(0)]],\n\
                 \x20   device {ty}* partial_results   [[buffer(1)]],\n\
                 \x20   threadgroup {ty}* shared       [[threadgroup(0)]],\n\
                 \x20   uint tid  [[thread_position_in_grid]],\n\
                 \x20   uint lid  [[thread_position_in_threadgroup]],\n\
                 \x20   uint sgid [[simdgroup_index_in_threadgroup]],\n\
                 \x20   uint lane [[thread_index_in_simdgroup]],\n\
                 \x20   uint tgid [[threadgroup_position_in_grid]])\n\
                 {{\n\
                 \x20   {ty} val = (tid < {n}u) ? input[tid] : {id};\n\
                 \x20   {ty} simd_result = {intrinsic}(val);\n\
                 \x20   if (lane == 0) {{ shared[sgid] = simd_result; }}\n\
                 \x20   threadgroup_barrier(mem_flags::mem_threadgroup);\n\
                 \x20   if (sgid == 0) {{\n\
                 \x20       {ty} final_val = (lid < ({tg_size}u / 32u)) ? shared[lid] : {id};\n\
                 \x20       final_val = {intrinsic}(final_val);\n\
                 \x20       if (lane == 0) {{ partial_results[tgid] = final_val; }}\n\
                 \x20   }}\n\
                 }}\n",
                node = self.node_id,
                ty = ty,
                n = element_count,
                id = identity,
                intrinsic = intrinsic,
                tg_size = threadgroup_size,
            ));
        } else {
            let binary = op.emit_binary("shared[lid]", "shared[lid + stride]");
            out.push_str(&format!(
                "kernel void trust_cg_reduce_{node}(\n\
                 \x20   const device {ty}* input       [[buffer(0)]],\n\
                 \x20   device {ty}* partial_results   [[buffer(1)]],\n\
                 \x20   threadgroup {ty}* shared       [[threadgroup(0)]],\n\
                 \x20   uint tid  [[thread_position_in_grid]],\n\
                 \x20   uint lid  [[thread_position_in_threadgroup]],\n\
                 \x20   uint tgid [[threadgroup_position_in_grid]],\n\
                 \x20   uint tg_size [[threads_per_threadgroup]])\n\
                 {{\n\
                 \x20   shared[lid] = (tid < {n}u) ? input[tid] : {id};\n\
                 \x20   threadgroup_barrier(mem_flags::mem_threadgroup);\n\
                 \x20   for (uint stride = tg_size / 2; stride > 0; stride >>= 1) {{\n\
                 \x20       if (lid < stride) {{\n\
                 \x20           shared[lid] = {binary};\n\
                 \x20       }}\n\
                 \x20       threadgroup_barrier(mem_flags::mem_threadgroup);\n\
                 \x20   }}\n\
                 \x20   if (lid == 0) {{ partial_results[tgid] = shared[0]; }}\n\
                 }}\n",
                node = self.node_id,
                ty = ty,
                n = element_count,
                id = identity,
                binary = binary,
            ));
        }
    }

    /// Emit a fused map-reduce kernel.
    ///
    /// The accumulation uses `simd_*` intrinsics (a tree schedule): the same
    /// `ReduceOrderClass::ExactAC`-only soundness constraint as
    /// [`Self::emit_parallel_reduce`] applies.
    fn emit_map_reduce(
        &self,
        out: &mut String,
        map_expr: &str,
        reduce_op: MslReduceOp,
        element_count: u64,
        threadgroup_size: u32,
    ) {
        let ty = &self.elem_type;
        let identity = reduce_op.identity(*ty);
        let intrinsic = reduce_op.simd_intrinsic().unwrap_or("simd_sum");
        out.push_str(&format!(
            "kernel void trust_cg_map_reduce_{node}(\n\
             \x20   const device {ty}* a           [[buffer(0)]],\n\
             \x20   const device {ty}* b           [[buffer(1)]],\n\
             \x20   device {ty}* partial_results   [[buffer(2)]],\n\
             \x20   threadgroup {ty}* shared       [[threadgroup(0)]],\n\
             \x20   uint tid  [[thread_position_in_grid]],\n\
             \x20   uint lid  [[thread_position_in_threadgroup]],\n\
             \x20   uint sgid [[simdgroup_index_in_threadgroup]],\n\
             \x20   uint lane [[thread_index_in_simdgroup]],\n\
             \x20   uint tgid [[threadgroup_position_in_grid]])\n\
             {{\n\
             \x20   {ty} mapped = (tid < {n}u) ? {map} : {id};\n\
             \x20   {ty} simd_result = {intrinsic}(mapped);\n\
             \x20   if (lane == 0) {{ shared[sgid] = simd_result; }}\n\
             \x20   threadgroup_barrier(mem_flags::mem_threadgroup);\n\
             \x20   if (sgid == 0) {{\n\
             \x20       {ty} final_val = (lid < ({tg_size}u / 32u)) ? shared[lid] : {id};\n\
             \x20       final_val = {intrinsic}(final_val);\n\
             \x20       if (lane == 0) {{ partial_results[tgid] = final_val; }}\n\
             \x20   }}\n\
             }}\n",
            node = self.node_id,
            ty = ty,
            n = element_count,
            map = map_expr,
            id = identity,
            intrinsic = intrinsic,
            tg_size = threadgroup_size,
        ));
    }

    /// Emit a matrix multiply kernel.
    ///
    /// # Emission strategy
    ///
    /// The correctness path is a scalar per-thread accumulator loop: one thread
    /// computes one `C[row][col]` element via a straight
    /// `for (kk = 0; kk < K; ++kk)` multiply-add.
    ///
    /// The legacy `simdgroup_matrix` template is retained below, but it is not
    /// selected by the current launcher. That template needs tile-coordinate
    /// dispatch semantics and one simdgroup per output tile; the current host
    /// path dispatches a per-output-element 2D grid. Selecting the scalar path
    /// for all shapes keeps `K % 8` tails, partial `M`/`N` tiles, and rounded-up
    /// dispatch grids bounded uniformly. See issue #403.
    ///
    /// # Shape semantics (issue #404)
    ///
    /// `m`, `k`, `n` are passed as explicit parameters to this low-level
    /// helper. The sealed [`emit_kernel_from_node`] path does not call it and
    /// refuses `MatrixHeavy` nodes fail-closed until an exact typed matrix
    /// recipe is available.
    fn emit_matmul(&self, out: &mut String, m: u64, k: u64, n: u64) {
        self.emit_matmul_scalar(out, m, k, n);
    }

    /// Emit the aligned tiled 8x8 matmul using `simdgroup_matrix`.
    ///
    /// Precondition: caller has verified M, K, N are all multiples of 8.
    /// A grid-bounds early-return is still emitted so rounded-up dispatch
    /// grids (e.g. `MetalDispatchParams::for_2d`) stay safe.
    #[allow(dead_code)]
    fn emit_matmul_simdgroup(&self, out: &mut String, m: u64, k: u64, n: u64) {
        let ty = &self.elem_type;
        out.push_str("#include <metal_simdgroup_matrix>\n\n");
        out.push_str(&format!(
            "kernel void trust_cg_matmul_{node}(\n\
             \x20   const device {ty}* A  [[buffer(0)]],\n\
             \x20   const device {ty}* B  [[buffer(1)]],\n\
             \x20   device {ty}* C        [[buffer(2)]],\n\
             \x20   uint2 gid [[thread_position_in_grid]])\n\
             {{\n\
             \x20   const uint M = {m}u;\n\
             \x20   const uint K = {k}u;\n\
             \x20   const uint N = {n}u;\n\
             \x20   uint row = gid.y;\n\
             \x20   uint col = gid.x;\n\
             \x20   if (row >= M || col >= N) return;\n\
             \x20   simdgroup_matrix<{ty}, 8, 8> acc;\n\
             \x20   acc = make_filled_simdgroup_matrix<{ty}, 8, 8>(0.0{suffix});\n\
             \x20   for (uint kk = 0; kk < K; kk += 8) {{\n\
             \x20       simdgroup_matrix<{ty}, 8, 8> a_tile, b_tile;\n\
             \x20       simdgroup_load(a_tile, A + row * K + kk, K);\n\
             \x20       simdgroup_load(b_tile, B + kk * N + col, N);\n\
             \x20       simdgroup_multiply_accumulate(acc, a_tile, b_tile, acc);\n\
             \x20   }}\n\
             \x20   simdgroup_store(acc, C + row * N + col, N);\n\
             }}\n",
            node = self.node_id,
            ty = ty,
            m = m,
            k = k,
            n = n,
            suffix = if *ty == MslElementType::Half {
                "h"
            } else {
                "f"
            },
        ));
    }

    /// Emit a scalar per-thread matmul kernel for shapes not divisible by 8.
    ///
    /// One thread owns one output element `C[row, col]`. The per-thread
    /// accumulator loops over the full K dimension with element-wise
    /// multiply-add. A grid-bounds early-return handles rounded-up dispatch
    /// grids. Correct for any M, K, N.
    fn emit_matmul_scalar(&self, out: &mut String, m: u64, k: u64, n: u64) {
        let ty = &self.elem_type;
        let zero = match ty {
            MslElementType::Half => "0.0h",
            MslElementType::Float => "0.0f",
            MslElementType::Int | MslElementType::Uint => "0",
        };
        out.push_str(&format!(
            "kernel void trust_cg_matmul_{node}(\n\
             \x20   const device {ty}* A  [[buffer(0)]],\n\
             \x20   const device {ty}* B  [[buffer(1)]],\n\
             \x20   device {ty}* C        [[buffer(2)]],\n\
             \x20   uint2 gid [[thread_position_in_grid]])\n\
             {{\n\
             \x20   const uint M = {m}u;\n\
             \x20   const uint K = {k}u;\n\
             \x20   const uint N = {n}u;\n\
             \x20   uint row = gid.y;\n\
             \x20   uint col = gid.x;\n\
             \x20   if (row >= M || col >= N) return;\n\
             \x20   {ty} acc = {zero};\n\
             \x20   for (uint kk = 0; kk < K; ++kk) {{\n\
             \x20       acc += A[row * K + kk] * B[kk * N + col];\n\
             \x20   }}\n\
             \x20   C[row * N + col] = acc;\n\
             }}\n",
            node = self.node_id,
            ty = ty,
            m = m,
            k = k,
            n = n,
            zero = zero,
        ));
    }

    /// Emit buffer creation host-side code snippet (Objective-C).
    ///
    /// This is a helper for generating host dispatch code fragments.
    pub fn emit_buffer_creation(
        buf_name: &str,
        size_bytes: u64,
        storage_mode: MtlStorageMode,
    ) -> String {
        format!(
            "id<MTLBuffer> {} = [device newBufferWithLength:{} options:{}];",
            buf_name, size_bytes, storage_mode,
        )
    }
}

// ---------------------------------------------------------------------------
// ComputeGraph -> MSL kernel generation
// ---------------------------------------------------------------------------

/// Default threadgroup size for 1D kernels.
const DEFAULT_THREADGROUP_SIZE: u32 = 256;

/// Default 2D threadgroup width/height for MatMul kernels.
const DEFAULT_MATMUL_TILE: u32 = 8;

/// Exact Metal map specification recovered from the sealed compiler binding.
struct ExactMetalMap {
    op: MslOp,
    element_count: u64,
    lhs: TrustIrValueId,
    rhs: TrustIrValueId,
    result: TrustIrValueId,
    semantic_digest: [u8; 32],
}

fn exact_metal_map(node: &ComputeNode) -> Result<ExactMetalMap, MetalEmitError> {
    let recipe = node
        .validated_accelerator_recipe(AcceleratorBackend::Metal)
        .map_err(|error| MetalEmitError::SemanticBinding {
            node_id: node.id,
            reason: error.to_string(),
        })?;
    match recipe.operation() {
        AcceleratorOperation::ElementwiseBinary {
            op,
            elem_type,
            element_count,
            lhs,
            rhs,
            result,
        } => {
            if *elem_type != AcceleratorElementType::U32 || *element_count == 0 {
                return Err(MetalEmitError::SemanticBinding {
                    node_id: node.id,
                    reason: "unsupported exact element type or zero vector width".to_string(),
                });
            }
            let op = match op {
                AcceleratorBinaryOp::Add => MslOp::Add,
                AcceleratorBinaryOp::Sub => MslOp::Sub,
                AcceleratorBinaryOp::Mul => MslOp::Mul,
            };
            Ok(ExactMetalMap {
                op,
                element_count: *element_count,
                lhs: *lhs,
                rhs: *rhs,
                result: *result,
                semantic_digest: recipe.semantic_digest().bytes,
            })
        }
    }
}

/// Emit a complete MSL kernel only from an exact compiler-derived recipe.
///
/// `dominant_op`, `kind`, `data_size_bytes`, `matmul_shape`, and public
/// `legal_targets` are diagnostic/cost metadata and never select semantics.
/// Unknown operations, reductions, inferred matmuls, manually-created nodes,
/// deserialized nodes, and multi-instruction blocks therefore fail closed.
pub fn emit_kernel_from_node(node: &ComputeNode) -> Result<String, MetalEmitError> {
    let exact = exact_metal_map(node)?;
    let emitter = MetalKernelEmitter::new(&node.id.to_string(), MslElementType::Uint);
    let body_expr = exact.op.emit("a[tid]", "b[tid]", "");
    let kernel = MslKernel::ParallelMap {
        body_expr,
        input_count: 2,
        element_count: exact.element_count,
        threadgroup_size: DEFAULT_THREADGROUP_SIZE,
    };
    let mut source = emitter.emit(&kernel);
    source.push_str(&format!(
        "// exact TrustIR binding: {} , {} -> {}; semantic_sha256=",
        exact.lhs, exact.rhs, exact.result
    ));
    for byte in exact.semantic_digest {
        source.push_str(&format!("{byte:02x}"));
    }
    source.push('\n');
    Ok(source)
}

// ---------------------------------------------------------------------------
// Host-side Metal dispatch code generation
// ---------------------------------------------------------------------------

/// Emit host-side Objective-C Metal dispatch code for a DispatchPlan.
///
/// Generates a complete dispatch function that:
/// - Creates Metal buffers for data transfers
/// - Creates compute pipeline states for each kernel
/// - Encodes and dispatches compute commands
/// - Inserts synchronization barriers
///
/// The generated code assumes `_device` (id<MTLDevice>), `_queue`
/// (id<MTLCommandQueue>), and `_library` (id<MTLLibrary>) are in scope
/// as instance variables.
fn validate_metal_plan(
    plan: &DispatchPlan,
    graph: &trust_cg_lower::compute_graph::ComputeGraph,
) -> Result<(), MetalEmitError> {
    for node_id in plan.assignment.keys() {
        if graph.node(*node_id).is_none() {
            return Err(MetalEmitError::MissingPlanNode { node_id: *node_id });
        }
    }

    let mut launched_gpu_nodes = HashSet::new();
    let mut pending_gpu_nodes = HashSet::new();
    for op in &plan.ops {
        match op {
            DispatchOp::DataTransfer {
                src,
                dst,
                size_bytes,
                cost,
                edge_from,
                edge_to,
            } => {
                for node_id in [*edge_from, *edge_to] {
                    if graph.node(node_id).is_none() {
                        return Err(MetalEmitError::MissingPlanNode { node_id });
                    }
                }
                if matches!(
                    (src, dst),
                    (ComputeTarget::NeuralEngine, _) | (_, ComputeTarget::NeuralEngine)
                ) {
                    return Err(MetalEmitError::InvalidDispatchPlan {
                        reason: format!(
                            "Metal host emission cannot orchestrate NeuralEngine transfer {edge_from}->{edge_to}"
                        ),
                    });
                }
                let matching_edges = graph
                    .edges
                    .iter()
                    .filter(|edge| edge.from == *edge_from && edge.to == *edge_to)
                    .collect::<Vec<_>>();
                if matching_edges.len() != 1
                    || matching_edges[0].transfer_bytes != *size_bytes
                    || plan.assignment.get(edge_from) != Some(src)
                    || plan.assignment.get(edge_to) != Some(dst)
                    || *src == *dst
                    || *cost != estimate_transfer_cost(*size_bytes, *src, *dst)
                {
                    return Err(MetalEmitError::InvalidDispatchPlan {
                        reason: format!(
                            "transfer {edge_from}->{edge_to} is not exactly bound to one graph edge and its assignments"
                        ),
                    });
                }
            }
            DispatchOp::KernelLaunch {
                target,
                node_id,
                estimated_cycles,
            } => {
                let node = graph
                    .node(*node_id)
                    .ok_or(MetalEmitError::MissingPlanNode { node_id: *node_id })?;
                if plan.assignment.get(node_id) != Some(target)
                    || node.costs.get(target).map(|cost| cost.latency_cycles)
                        != Some(*estimated_cycles)
                {
                    return Err(MetalEmitError::PlanAssignmentMismatch { node_id: *node_id });
                }
                match target {
                    ComputeTarget::Gpu => {
                        if !launched_gpu_nodes.insert(*node_id) {
                            return Err(MetalEmitError::DuplicateKernelLaunch {
                                node_id: *node_id,
                            });
                        }
                        exact_metal_map(node)?;
                        pending_gpu_nodes.insert(*node_id);
                    }
                    ComputeTarget::NeuralEngine => {
                        return Err(MetalEmitError::InvalidDispatchPlan {
                            reason: format!(
                                "Metal host emission cannot orchestrate NeuralEngine launch {node_id}"
                            ),
                        });
                    }
                    ComputeTarget::CpuScalar | ComputeTarget::CpuSimd => {}
                }
            }
            DispatchOp::Synchronize { target, node_id } => {
                if *target != ComputeTarget::Gpu
                    || plan.assignment.get(node_id) != Some(target)
                    || !pending_gpu_nodes.remove(node_id)
                {
                    return Err(MetalEmitError::InvalidDispatchPlan {
                        reason: format!(
                            "sync for {node_id} is not paired with one preceding GPU launch"
                        ),
                    });
                }
            }
            DispatchOp::CpuFallback { node_id, .. } => {
                if graph.node(*node_id).is_none() {
                    return Err(MetalEmitError::MissingPlanNode { node_id: *node_id });
                }
                if plan.assignment.get(node_id) != Some(&ComputeTarget::CpuScalar) {
                    return Err(MetalEmitError::PlanAssignmentMismatch { node_id: *node_id });
                }
            }
        }
    }

    if !pending_gpu_nodes.is_empty() {
        return Err(MetalEmitError::InvalidDispatchPlan {
            reason: "one or more GPU launches have no matching synchronization".to_string(),
        });
    }
    let assigned_gpu_nodes = plan
        .assignment
        .iter()
        .filter_map(|(node, target)| (*target == ComputeTarget::Gpu).then_some(*node))
        .collect::<HashSet<_>>();
    if assigned_gpu_nodes != launched_gpu_nodes {
        return Err(MetalEmitError::InvalidDispatchPlan {
            reason: "GPU assignments and launches are not one-to-one".to_string(),
        });
    }
    Ok(())
}

fn emit_exact_buffer_bindings(
    encoder_index: usize,
    node_id: ComputeNodeId,
    lhs: TrustIrValueId,
    rhs: TrustIrValueId,
    result: TrustIrValueId,
) -> String {
    let lhs = lhs.stable_key();
    let rhs = rhs.stable_key();
    let result = result.stable_key();
    format!(
        "    NSCAssert(buffers[@({lhs}ULL)] && buffers[@({rhs}ULL)] && buffers[@({result}ULL)], @\"missing function-scoped TrustIR buffer binding for {node_id}\");\n\
         [enc_{encoder_index} setBuffer:buffers[@({lhs}ULL)] offset:0 atIndex:0];\n\
         [enc_{encoder_index} setBuffer:buffers[@({rhs}ULL)] offset:0 atIndex:1];\n\
         [enc_{encoder_index} setBuffer:buffers[@({result}ULL)] offset:0 atIndex:2];\n"
    )
}

pub fn emit_dispatch_code(
    plan: &DispatchPlan,
    graph: &trust_cg_lower::compute_graph::ComputeGraph,
) -> Result<String, MetalEmitError> {
    validate_metal_plan(plan, graph)?;
    let mut out = String::new();

    out.push_str("// Generated by Trust Codegen — Metal dispatch code\n");
    out.push_str(&format!(
        "// Dispatch plan: {} ops ({} launches, {} transfers)\n\n",
        plan.len(),
        plan.count_launches(),
        plan.count_transfers(),
    ));

    out.push_str(
        "- (void)executeDispatchPlanWithBuffers:(NSDictionary<NSNumber *, id<MTLBuffer>> *)buffers {\n",
    );
    out.push_str("    id<MTLCommandBuffer> cmdBuf = [_queue commandBuffer];\n\n");

    for (i, op) in plan.ops.iter().enumerate() {
        match op {
            DispatchOp::DataTransfer {
                src,
                dst,
                size_bytes,
                edge_from,
                edge_to,
                ..
            } => {
                out.push_str(&format!(
                    "    // Op {}: Transfer {} bytes ({:?} -> {:?})\n",
                    i, size_bytes, src, dst,
                ));
                // On Apple UMA, shared memory means no explicit copy for CPU<->GPU.
                if (*src == ComputeTarget::CpuScalar || *src == ComputeTarget::CpuSimd)
                    && *dst == ComputeTarget::Gpu
                {
                    out.push_str("    // UMA: no explicit copy needed (shared memory)\n");
                } else if *src == ComputeTarget::Gpu
                    && (*dst == ComputeTarget::CpuScalar || *dst == ComputeTarget::CpuSimd)
                {
                    out.push_str("    // UMA: coherent after command buffer completion\n");
                } else {
                    out.push_str(&format!(
                        "    id<MTLBuffer> xfer_{i} = [_device newBufferWithLength:{size} options:MTLResourceStorageModeShared];\n",
                        i = i, size = size_bytes,
                    ));
                }
                let _ = (edge_from, edge_to); // suppress unused warnings in doc
                out.push('\n');
            }

            DispatchOp::KernelLaunch {
                target,
                node_id,
                estimated_cycles,
            } => {
                let node_id_str = format!("{}", node_id);
                let kernel_name = if *target == ComputeTarget::Gpu {
                    format!("trust_cg_map2_{}", node_id_str)
                } else {
                    format!("trust_cg_cpu_{}", node_id_str)
                };

                out.push_str(&format!(
                    "    // Op {}: Launch {:?} kernel '{}' (est. {} cycles)\n",
                    i, target, kernel_name, estimated_cycles,
                ));

                if *target == ComputeTarget::Gpu {
                    out.push_str(&format!(
                        "    id<MTLFunction> fn_{i} = [_library newFunctionWithName:@\"{name}\"];\n",
                        i = i, name = kernel_name,
                    ));
                    out.push_str(&format!(
                        "    id<MTLComputePipelineState> pso_{i} = [_device newComputePipelineStateWithFunction:fn_{i} error:nil];\n",
                        i = i,
                    ));
                    out.push_str(&format!(
                        "    id<MTLComputeCommandEncoder> enc_{i} = [cmdBuf computeCommandEncoder];\n",
                        i = i,
                    ));
                    out.push_str(&format!(
                        "    [enc_{i} setComputePipelineState:pso_{i}];\n",
                        i = i,
                    ));

                    let node = graph
                        .node(*node_id)
                        .ok_or(MetalEmitError::MissingPlanNode { node_id: *node_id })?;
                    let exact = exact_metal_map(node)?;
                    out.push_str(&emit_exact_buffer_bindings(
                        i,
                        *node_id,
                        exact.lhs,
                        exact.rhs,
                        exact.result,
                    ));
                    let params =
                        MetalDispatchParams::for_1d(exact.element_count, DEFAULT_THREADGROUP_SIZE);
                    out.push_str(&format!(
                        "    [enc_{i} dispatchThreads:MTLSizeMake({w}, 1, 1) threadsPerThreadgroup:MTLSizeMake({tw}, 1, 1)];\n",
                        i = i,
                        w = params.grid_size.width,
                        tw = params.threadgroup_size.width,
                    ));

                    out.push_str(&format!("    [enc_{i} endEncoding];\n", i = i));
                } else {
                    out.push_str(&format!(
                        "    // CPU execution for {} (not a Metal kernel)\n",
                        node_id,
                    ));
                }
                out.push('\n');
            }

            DispatchOp::Synchronize { target, .. } => {
                out.push_str(&format!("    // Op {}: Synchronize {:?}\n", i, target,));
                if *target == ComputeTarget::Gpu {
                    out.push_str("    [cmdBuf commit];\n");
                    out.push_str("    [cmdBuf waitUntilCompleted];\n");
                    out.push_str("    cmdBuf = [_queue commandBuffer];\n");
                }
                out.push('\n');
            }

            DispatchOp::CpuFallback { node_id, reason } => {
                out.push_str(&format!(
                    "    // Op {}: CPU fallback for {} ({})\n",
                    i, node_id, reason,
                ));
                out.push('\n');
            }
        }
    }

    out.push_str("    [cmdBuf commit];\n");
    out.push_str("    [cmdBuf waitUntilCompleted];\n");
    out.push_str("}\n");

    Ok(out)
}

// ---------------------------------------------------------------------------
// Kernel function name generation
// ---------------------------------------------------------------------------

/// Return the MSL kernel function name for a given node and pattern.
pub fn kernel_function_name(node_id: &str, kernel: &MslKernel) -> String {
    match kernel {
        MslKernel::ParallelMap { input_count, .. } => {
            if *input_count <= 1 {
                format!("trust_cg_map_{}", node_id)
            } else {
                format!("trust_cg_map2_{}", node_id)
            }
        }
        MslKernel::ParallelReduce { use_simd, .. } => {
            if *use_simd {
                format!("trust_cg_reduce_simd_{}", node_id)
            } else {
                format!("trust_cg_reduce_{}", node_id)
            }
        }
        MslKernel::MapReduce { .. } => format!("trust_cg_map_reduce_{}", node_id),
        MslKernel::MatMul { .. } => format!("trust_cg_matmul_{}", node_id),
    }
}

// ---------------------------------------------------------------------------
// MetalOutput — aggregated output from Metal kernel generation pipeline
// ---------------------------------------------------------------------------

/// A named MSL kernel source: function name + source text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedKernel {
    /// The MSL kernel function name (e.g., `trust_cg_map_node_42`).
    pub name: String,
    /// Complete MSL source text for this kernel.
    pub source: String,
    /// The compute node ID that produced this kernel.
    pub node_id: ComputeNodeId,
}

/// Aggregated output from Metal kernel generation for a dispatch plan.
///
/// Contains all generated MSL kernel sources, the host-side dispatch code,
/// and metadata about buffer requirements. This is the output of
/// [`emit_metal_kernels`] and the primary integration point between the
/// Metal emission pipeline and the compilation pipeline.
#[derive(Debug, Clone)]
pub struct MetalOutput {
    /// Generated MSL kernel sources, one per GPU-targeted node.
    pub kernels: Vec<NamedKernel>,
    /// Host-side Objective-C dispatch code (complete function body).
    pub dispatch_code: String,
    /// Total number of Metal buffers required across all kernels.
    ///
    /// Computed as the sum of per-kernel buffer counts:
    /// - Unary map: 2 (input + output)
    /// - Binary map: 3 (a + b + output)
    /// - Reduce: 2 (input + partial_results)
    /// - MapReduce: 3 (a + b + partial_results)
    /// - MatMul: 3 (A + B + C)
    pub buffer_count: usize,
}

// ---------------------------------------------------------------------------
// VNN BN+ReLU fused Metal source boundary
// ---------------------------------------------------------------------------

/// First Metal GPU fusion target for VNN tensor trust_ir.
pub const GPU_METAL_MSL_TARGET: &str = "gpu.metal.msl";

/// Canonical fusion name for `trust_ir.vnn.batch_norm` -> `trust_ir.vnn.relu`.
pub const BATCH_NORM_RELU_FUSION: &str = "batch_norm_relu";

/// Canonical certified pass name for `trust_ir.vnn.conv2d|linear` -> BatchNorm.
pub const CONV_BATCH_NORM_FUSION: &str = "conv-bn-fusion";

/// Canonical fusion name for QK^T -> scale -> softmax -> V attention.
pub const ATTENTION_QK_SOFTMAX_V_FUSION: &str = "attention_qk_softmax_v";

/// Options for selecting and emitting the BN+ReLU VNN fusion.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct VnnBatchNormReluOptions {
    /// Certified mode requires #557 ReLU relaxation metadata and fails closed
    /// when the current VNN payload does not carry it.
    pub certified: bool,
}

/// Options for selecting and emitting fused attention source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VnnFusedAttentionOptions {
    /// Maximum supported static sequence length for this bounded source
    /// emission path.
    pub max_sequence: u64,
    /// Maximum supported static head dimension for this bounded source
    /// emission path.
    pub max_head_dim: u64,
}

impl Default for VnnFusedAttentionOptions {
    fn default() -> Self {
        Self {
            max_sequence: 512,
            max_head_dim: 256,
        }
    }
}

/// Reason code for fail-closed GPU fusion rejection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuFusionUnsupportedReason {
    UnsupportedTargetBackend,
    UnsupportedDtype,
    UnsupportedLayout,
    DynamicShape,
    ShapeMismatch,
    MissingInitializer,
    TrainingModeBatchNorm,
    MultipleConsumers,
    MissingRelaxationMetadata,
    UnsupportedSoftmaxAxis,
    UnsupportedAttentionMask,
    MissingTransposeMetadata,
}

impl GpuFusionUnsupportedReason {
    pub fn as_str(self) -> &'static str {
        match self {
            GpuFusionUnsupportedReason::UnsupportedTargetBackend => "unsupported_target_backend",
            GpuFusionUnsupportedReason::UnsupportedDtype => "unsupported_dtype",
            GpuFusionUnsupportedReason::UnsupportedLayout => "unsupported_layout",
            GpuFusionUnsupportedReason::DynamicShape => "dynamic_shape",
            GpuFusionUnsupportedReason::ShapeMismatch => "shape_mismatch",
            GpuFusionUnsupportedReason::MissingInitializer => "missing_initializer",
            GpuFusionUnsupportedReason::TrainingModeBatchNorm => "training_mode_batch_norm",
            GpuFusionUnsupportedReason::MultipleConsumers => "multiple_consumers",
            GpuFusionUnsupportedReason::MissingRelaxationMetadata => "missing_relaxation_metadata",
            GpuFusionUnsupportedReason::UnsupportedSoftmaxAxis => "unsupported_softmax_axis",
            GpuFusionUnsupportedReason::UnsupportedAttentionMask => "unsupported_attention_mask",
            GpuFusionUnsupportedReason::MissingTransposeMetadata => "missing_transpose_metadata",
        }
    }
}

impl fmt::Display for GpuFusionUnsupportedReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Structured fail-closed diagnostic for unsupported GPU fusion candidates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GpuFusionUnsupportedDiagnostic {
    pub code: &'static str,
    pub phase: &'static str,
    pub fusion: &'static str,
    pub target: &'static str,
    pub reason: GpuFusionUnsupportedReason,
    pub source_ops: Vec<String>,
    pub blocked_by: &'static str,
}

impl GpuFusionUnsupportedDiagnostic {
    fn new(reason: GpuFusionUnsupportedReason, source_ops: Vec<String>) -> Self {
        Self::new_for_fusion(BATCH_NORM_RELU_FUSION, reason, source_ops)
    }

    fn new_for_fusion(
        fusion: &'static str,
        reason: GpuFusionUnsupportedReason,
        source_ops: Vec<String>,
    ) -> Self {
        Self {
            code: "gpu.fusion.unsupported",
            phase: "select_gpu_fusion",
            fusion,
            target: GPU_METAL_MSL_TARGET,
            reason,
            source_ops,
            blocked_by: "#480",
        }
    }
}

impl fmt::Display for GpuFusionUnsupportedDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} phase={} fusion={} target={} reason={} source_ops={:?} blocked_by={}",
            self.code,
            self.phase,
            self.fusion,
            self.target,
            self.reason,
            self.source_ops,
            self.blocked_by
        )
    }
}

impl std::error::Error for GpuFusionUnsupportedDiagnostic {}

/// Provenance copied from source VNN ops into a fused compile unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VnnSourceProvenance {
    pub gamma_layer_id: String,
    pub gamma_layer_type: String,
    pub onnx_node_name: String,
    pub onnx_op_type: String,
    pub onnx_outputs: Vec<String>,
}

/// MSL source plus the metadata required by the later launch/runtime boundary.
#[derive(Debug, Clone, PartialEq)]
pub struct MetalBatchNormReluCompileUnit {
    pub fusion: &'static str,
    pub target: &'static str,
    pub kernel_name: String,
    pub source: String,
    pub dispatch: MetalDispatchParams,
    pub element_count: u64,
    pub source_ops: Vec<String>,
    pub source_provenance: Vec<VnnSourceProvenance>,
    pub input_tensor: String,
    pub preactivation_tensor: String,
    pub output_tensor: String,
    pub fused_gamma_layer_ids: Vec<String>,
    /// Certified-pass run emitted by the real fusion selector when certified
    /// mode succeeds. Non-certified emission leaves this empty.
    pub certified_pass_run: Option<CertifiedPassRunRecord>,
}

/// Certified Conv/Linear + BatchNorm fusion record emitted by the VNN selector.
#[derive(Debug, Clone, PartialEq)]
pub struct ConvBatchNormCertifiedFusionUnit {
    pub fusion: &'static str,
    pub target: &'static str,
    pub source_ops: Vec<String>,
    pub source_provenance: Vec<VnnSourceProvenance>,
    pub input_tensor: String,
    pub pre_batch_norm_tensor: String,
    pub output_tensor: String,
    pub fused_gamma_layer_ids: Vec<String>,
    pub certified_pass_run: CertifiedPassRunRecord,
}

/// MSL source plus the metadata required by the fused attention launch boundary.
#[derive(Debug, Clone, PartialEq)]
pub struct MetalFusedAttentionCompileUnit {
    pub fusion: &'static str,
    pub target: &'static str,
    pub kernel_name: String,
    pub source: String,
    pub dispatch: MetalDispatchParams,
    pub batch: u64,
    pub sequence: u64,
    pub head_dim: u64,
    pub output_element_count: u64,
    pub scale: f64,
    pub source_ops: Vec<String>,
    pub source_provenance: Vec<VnnSourceProvenance>,
    pub query_tensor: String,
    pub key_tensor: String,
    pub value_tensor: String,
    pub scores_tensor: String,
    pub probability_tensor: String,
    pub output_tensor: String,
    pub fused_gamma_layer_ids: Vec<String>,
}

/// Emit a fail-closed Metal MSL source compile unit for a VNN
/// `trust_ir.vnn.batch_norm` -> single-consumer `trust_ir.vnn.relu` pattern.
///
/// This boundary intentionally accepts the serialized VNN JSON shape rather
/// than depending on the importer crate. That keeps codegen focused on the VNN
/// contract and also lets tests cover malformed/dynamic payloads that the
/// current importer rejects before codegen can see them.
pub fn emit_vnn_batch_norm_relu_msl(
    module: &serde_json::Value,
    options: VnnBatchNormReluOptions,
) -> Result<MetalBatchNormReluCompileUnit, GpuFusionUnsupportedDiagnostic> {
    let ops = module
        .get("ops")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| {
            GpuFusionUnsupportedDiagnostic::new(
                GpuFusionUnsupportedReason::ShapeMismatch,
                Vec::new(),
            )
        })?;

    let (bn_index, relu_index, source_ops) = find_batch_norm_relu_pair(ops)?;
    let bn = &ops[bn_index];
    let relu = &ops[relu_index];

    let input_tensor = first_string_array_item(bn, "inputs")
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops))?;
    let preactivation_tensor = first_string_array_item(bn, "outputs")
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops))?;
    let relu_input = first_string_array_item(relu, "inputs")
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops))?;
    let output_tensor = first_string_array_item(relu, "outputs")
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops))?;
    if relu_input != preactivation_tensor {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }

    let input_shape = read_tensor_shape(module, &input_tensor, &source_ops)?;
    let preactivation_shape = read_tensor_shape(module, &preactivation_tensor, &source_ops)?;
    let output_shape = read_tensor_shape(module, &output_tensor, &source_ops)?;
    if input_shape.len() != 4
        || preactivation_shape != input_shape
        || output_shape != input_shape
        || input_shape.contains(&0)
    {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }

    for tensor in [&input_tensor, &preactivation_tensor, &output_tensor] {
        if read_tensor_string(module, tensor, "dtype", &source_ops)? != "f32" {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::UnsupportedDtype,
                &source_ops,
            ));
        }
        if read_tensor_string(module, tensor, "layout", &source_ops)? != "nchw" {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::UnsupportedLayout,
                &source_ops,
            ));
        }
    }

    if is_training_batch_norm(bn) {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::TrainingModeBatchNorm,
            &source_ops,
        ));
    }

    let epsilon = bn
        .pointer("/attrs/epsilon")
        .and_then(serde_json::Value::as_f64)
        .unwrap_or(0.00001);
    if !epsilon.is_finite() || epsilon <= 0.0 {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }

    let channels = input_shape[1];
    let weights = bn
        .get("weights")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::MissingInitializer, &source_ops))?;
    if weights.len() < 4 {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::MissingInitializer,
            &source_ops,
        ));
    }
    let mut batch_norm_weights = Vec::with_capacity(4);
    for weight in weights.iter().take(4) {
        let Some(name) = weight.as_str() else {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::MissingInitializer,
                &source_ops,
            ));
        };
        validate_bn_initializer(module, name, channels, &source_ops)?;
        batch_norm_weights.push(name.to_string());
    }

    let relaxation_metadata = if options.certified {
        Some(read_relu_relaxation_metadata(module, relu, &source_ops)?)
    } else {
        None
    };

    let source_provenance = vec![read_provenance(bn), read_provenance(relu)];
    let fused_gamma_layer_ids = source_provenance
        .iter()
        .map(|provenance| provenance.gamma_layer_id.clone())
        .collect::<Vec<_>>();
    let element_count = input_shape.iter().product::<u64>();
    let kernel_name = format!(
        "trust_cg_batch_norm_relu_{}",
        sanitize_kernel_suffix(&source_ops.join("_"))
    );
    let source = emit_batch_norm_relu_source(
        &kernel_name,
        &source_ops,
        &fused_gamma_layer_ids,
        &input_shape,
        element_count,
        epsilon,
    );
    let dispatch = MetalDispatchParams::for_1d(element_count, DEFAULT_THREADGROUP_SIZE);
    let certified_pass_run = relaxation_metadata.as_ref().map(|relaxation| {
        bn_relu_certified_pass_run(
            module,
            &source_ops,
            &source_provenance,
            &input_tensor,
            &preactivation_tensor,
            &output_tensor,
            &fused_gamma_layer_ids,
            &batch_norm_weights,
            &input_shape,
            element_count,
            epsilon,
            &kernel_name,
            relaxation,
        )
    });

    Ok(MetalBatchNormReluCompileUnit {
        fusion: BATCH_NORM_RELU_FUSION,
        target: GPU_METAL_MSL_TARGET,
        kernel_name,
        source,
        dispatch,
        element_count,
        source_ops,
        source_provenance,
        input_tensor,
        preactivation_tensor,
        output_tensor,
        fused_gamma_layer_ids,
        certified_pass_run,
    })
}

/// Emit a certified-pass run record for a VNN `Conv2d|Linear -> BatchNorm`
/// affine fold. The source payload remains JSON-shaped trust_ir so the selector can
/// fail closed on malformed or dynamic VNN fixtures before any backend fallback.
pub fn emit_vnn_conv_batch_norm_certified_fusion(
    module: &serde_json::Value,
) -> Result<ConvBatchNormCertifiedFusionUnit, GpuFusionUnsupportedDiagnostic> {
    let ops = module
        .get("ops")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| {
            GpuFusionUnsupportedDiagnostic::new_for_fusion(
                CONV_BATCH_NORM_FUSION,
                GpuFusionUnsupportedReason::ShapeMismatch,
                Vec::new(),
            )
        })?;

    let candidate = find_conv_batch_norm_pair(ops)?;
    let op = &ops[candidate.source_index];
    let bn = &ops[candidate.batch_norm_index];
    let source_ops = candidate.source_ops;

    let input_tensor = first_string_array_item(op, "inputs").ok_or_else(|| {
        conv_bn_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops)
    })?;
    let pre_batch_norm_tensor = first_string_array_item(op, "outputs").ok_or_else(|| {
        conv_bn_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops)
    })?;
    let bn_input = first_string_array_item(bn, "inputs").ok_or_else(|| {
        conv_bn_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops)
    })?;
    let output_tensor = first_string_array_item(bn, "outputs").ok_or_else(|| {
        conv_bn_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops)
    })?;
    if bn_input != pre_batch_norm_tensor {
        return Err(conv_bn_diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }

    if is_training_batch_norm(bn) {
        return Err(conv_bn_diagnostic(
            GpuFusionUnsupportedReason::TrainingModeBatchNorm,
            &source_ops,
        ));
    }

    let kind = op
        .get("op")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| {
            conv_bn_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &source_ops)
        })?;
    let (activation_layout, weight_layout, expected_rank) = match kind {
        "trust_ir.vnn.conv2d" => ("nchw", "oihw", 4),
        "trust_ir.vnn.linear" => ("nc", "oi", 2),
        _ => {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &source_ops,
            ));
        }
    };

    let input_shape = read_conv_bn_tensor_shape(module, &input_tensor, &source_ops)?;
    let pre_bn_shape = read_conv_bn_tensor_shape(module, &pre_batch_norm_tensor, &source_ops)?;
    let output_shape = read_conv_bn_tensor_shape(module, &output_tensor, &source_ops)?;
    if input_shape.len() != expected_rank
        || pre_bn_shape.len() != expected_rank
        || output_shape != pre_bn_shape
        || pre_bn_shape.contains(&0)
    {
        return Err(conv_bn_diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }
    for tensor in [&input_tensor, &pre_batch_norm_tensor, &output_tensor] {
        if read_conv_bn_tensor_string(module, tensor, "dtype", &source_ops)? != "f32" {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::UnsupportedDtype,
                &source_ops,
            ));
        }
        if read_conv_bn_tensor_string(module, tensor, "layout", &source_ops)? != activation_layout {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::UnsupportedLayout,
                &source_ops,
            ));
        }
    }

    let channels = pre_bn_shape[1];
    let weights = op
        .get("weights")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| {
            conv_bn_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, &source_ops)
        })?;
    let weight_name = weights
        .first()
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| {
            conv_bn_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, &source_ops)
        })?;
    validate_initializer(
        module,
        weight_name,
        "f32",
        weight_layout,
        Some(channels),
        &source_ops,
        CONV_BATCH_NORM_FUSION,
    )?;
    let bias_name = weights.get(1).and_then(serde_json::Value::as_str);
    if let Some(name) = bias_name {
        validate_initializer(
            module,
            name,
            "f32",
            "vector",
            Some(channels),
            &source_ops,
            CONV_BATCH_NORM_FUSION,
        )?;
    }

    let bn_weights = bn
        .get("weights")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| {
            conv_bn_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, &source_ops)
        })?;
    if bn_weights.len() < 4 {
        return Err(conv_bn_diagnostic(
            GpuFusionUnsupportedReason::MissingInitializer,
            &source_ops,
        ));
    }
    let mut batch_norm_weights = Vec::with_capacity(4);
    for weight in bn_weights.iter().take(4) {
        let name = weight.as_str().ok_or_else(|| {
            conv_bn_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, &source_ops)
        })?;
        validate_initializer(
            module,
            name,
            "f32",
            "vector",
            Some(channels),
            &source_ops,
            CONV_BATCH_NORM_FUSION,
        )?;
        batch_norm_weights.push(name.to_string());
    }

    let epsilon = bn
        .pointer("/attrs/epsilon")
        .and_then(serde_json::Value::as_f64)
        .unwrap_or(0.00001);
    if !epsilon.is_finite() || epsilon <= 0.0 {
        return Err(conv_bn_diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }

    let source_provenance = vec![read_provenance(op), read_provenance(bn)];
    let fused_gamma_layer_ids = source_provenance
        .iter()
        .map(|provenance| provenance.gamma_layer_id.clone())
        .collect::<Vec<_>>();
    let run = conv_bn_certified_pass_run(
        module,
        kind,
        &source_ops,
        &source_provenance,
        &input_tensor,
        &pre_batch_norm_tensor,
        &output_tensor,
        &fused_gamma_layer_ids,
        weight_name,
        bias_name,
        &batch_norm_weights,
        &input_shape,
        &pre_bn_shape,
        epsilon,
    )?;

    Ok(ConvBatchNormCertifiedFusionUnit {
        fusion: CONV_BATCH_NORM_FUSION,
        target: GPU_METAL_MSL_TARGET,
        source_ops,
        source_provenance,
        input_tensor,
        pre_batch_norm_tensor,
        output_tensor,
        fused_gamma_layer_ids,
        certified_pass_run: run,
    })
}

/// Emit a fail-closed Metal MSL source compile unit for a bounded single-head
/// VNN attention pattern:
///
/// `QK MatMul -> Scale -> Softmax -> PV MatMul`.
///
/// The emitted kernel consumes already-projected Q/K/V tensors and fuses score
/// matmul, scale, row-wise softmax, and value matmul into one Metal kernel.
/// Projection emission remains outside this bounded source-emission slice.
pub fn emit_vnn_fused_attention_msl(
    module: &serde_json::Value,
    options: VnnFusedAttentionOptions,
) -> Result<MetalFusedAttentionCompileUnit, GpuFusionUnsupportedDiagnostic> {
    let ops = module
        .get("ops")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| attention_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, &[]))?;

    let attention = find_attention_qk_softmax_v(ops)?;
    let source_ops = attention.source_ops.clone();

    let softmax = &ops[attention.softmax_index];
    let scale = &ops[attention.scale_index];
    let transpose = &ops[attention.transpose_index];

    reject_attention_multiple_consumers(
        ops,
        &[
            attention.transposed_key_tensor.as_str(),
            attention.scores_tensor.as_str(),
            attention.scaled_scores_tensor.as_str(),
            attention.probability_tensor.as_str(),
        ],
        &source_ops,
    )?;

    if !softmax_axis_is_last_json(
        module,
        softmax,
        &attention.scaled_scores_tensor,
        &source_ops,
    )? {
        return Err(attention_diagnostic(
            GpuFusionUnsupportedReason::UnsupportedSoftmaxAxis,
            &source_ops,
        ));
    }

    if !transpose_swaps_last_two_dims_json(transpose) {
        return Err(attention_diagnostic(
            GpuFusionUnsupportedReason::MissingTransposeMetadata,
            &source_ops,
        ));
    }

    let query_shape = read_attention_tensor_shape(module, &attention.query_tensor, &source_ops)?;
    let key_shape = read_attention_tensor_shape(module, &attention.key_tensor, &source_ops)?;
    let value_shape = read_attention_tensor_shape(module, &attention.value_tensor, &source_ops)?;
    let scores_shape = read_attention_tensor_shape(module, &attention.scores_tensor, &source_ops)?;
    let prob_shape =
        read_attention_tensor_shape(module, &attention.probability_tensor, &source_ops)?;
    let output_shape = read_attention_tensor_shape(module, &attention.output_tensor, &source_ops)?;

    let [batch, sequence, head_dim] = match query_shape.as_slice() {
        [batch, sequence, head_dim] => [*batch, *sequence, *head_dim],
        _ => {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &source_ops,
            ));
        }
    };

    if key_shape != query_shape
        || value_shape != query_shape
        || output_shape != query_shape
        || scores_shape != [batch, sequence, sequence]
        || prob_shape != scores_shape
        || sequence > options.max_sequence
        || head_dim > options.max_head_dim
    {
        return Err(attention_diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }

    for tensor in [
        &attention.query_tensor,
        &attention.key_tensor,
        &attention.value_tensor,
        &attention.scores_tensor,
        &attention.scaled_scores_tensor,
        &attention.probability_tensor,
        &attention.output_tensor,
    ] {
        if read_attention_tensor_string(module, tensor, "dtype", &source_ops)? != "f32" {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::UnsupportedDtype,
                &source_ops,
            ));
        }
    }

    for tensor in [
        &attention.query_tensor,
        &attention.key_tensor,
        &attention.value_tensor,
        &attention.output_tensor,
    ] {
        if read_attention_tensor_string(module, tensor, "layout", &source_ops)? != "nld" {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::UnsupportedLayout,
                &source_ops,
            ));
        }
    }

    for tensor in [
        &attention.scores_tensor,
        &attention.scaled_scores_tensor,
        &attention.probability_tensor,
    ] {
        let layout = read_attention_tensor_string(module, tensor, "layout", &source_ops)?;
        if layout != "nss" && layout != "nld" {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::UnsupportedLayout,
                &source_ops,
            ));
        }
    }

    if read_attention_tensor_string(
        module,
        &attention.transposed_key_tensor,
        "dtype",
        &source_ops,
    )? != "f32"
    {
        return Err(attention_diagnostic(
            GpuFusionUnsupportedReason::UnsupportedDtype,
            &source_ops,
        ));
    }

    let transposed_key_shape =
        read_attention_tensor_shape(module, &attention.transposed_key_tensor, &source_ops)?;
    if transposed_key_shape != [batch, head_dim, sequence] {
        return Err(attention_diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }

    let scale_value = read_attention_scale(module, scale, &source_ops)?;
    if !scale_value.is_finite() || scale_value <= 0.0 {
        return Err(attention_diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            &source_ops,
        ));
    }

    let source_indices = [
        attention.query_linear_index,
        attention.key_linear_index,
        attention.value_linear_index,
        Some(attention.transpose_index),
        Some(attention.scores_matmul_index),
        Some(attention.scale_index),
        Some(attention.softmax_index),
        Some(attention.context_matmul_index),
    ];
    let source_provenance = source_indices
        .into_iter()
        .flatten()
        .map(|index| read_provenance(&ops[index]))
        .collect::<Vec<_>>();
    let fused_gamma_layer_ids = source_provenance
        .iter()
        .map(|provenance| provenance.gamma_layer_id.clone())
        .filter(|id: &String| !id.is_empty())
        .collect::<Vec<_>>();
    let kernel_name = format!(
        "trust_cg_attention_qk_softmax_v_{}",
        sanitize_kernel_suffix(&source_ops.join("_"))
    );
    let output_element_count = batch * sequence * head_dim;
    let source = emit_fused_attention_source(
        &kernel_name,
        &source_ops,
        &fused_gamma_layer_ids,
        batch,
        sequence,
        head_dim,
        scale_value,
    );
    let dispatch = MetalDispatchParams::for_2d(batch * sequence, head_dim, DEFAULT_MATMUL_TILE);

    Ok(MetalFusedAttentionCompileUnit {
        fusion: ATTENTION_QK_SOFTMAX_V_FUSION,
        target: GPU_METAL_MSL_TARGET,
        kernel_name,
        source,
        dispatch,
        batch,
        sequence,
        head_dim,
        output_element_count,
        scale: scale_value,
        source_ops,
        source_provenance,
        query_tensor: attention.query_tensor,
        key_tensor: attention.key_tensor,
        value_tensor: attention.value_tensor,
        scores_tensor: attention.scores_tensor,
        probability_tensor: attention.probability_tensor,
        output_tensor: attention.output_tensor,
        fused_gamma_layer_ids,
    })
}

fn diagnostic(
    reason: GpuFusionUnsupportedReason,
    source_ops: &[String],
) -> GpuFusionUnsupportedDiagnostic {
    GpuFusionUnsupportedDiagnostic::new(reason, source_ops.to_vec())
}

fn attention_diagnostic(
    reason: GpuFusionUnsupportedReason,
    source_ops: &[String],
) -> GpuFusionUnsupportedDiagnostic {
    GpuFusionUnsupportedDiagnostic::new_for_fusion(
        ATTENTION_QK_SOFTMAX_V_FUSION,
        reason,
        source_ops.to_vec(),
    )
}

#[derive(Debug, Clone)]
struct AttentionJsonMatch {
    context_matmul_index: usize,
    softmax_index: usize,
    scale_index: usize,
    scores_matmul_index: usize,
    transpose_index: usize,
    query_linear_index: Option<usize>,
    key_linear_index: Option<usize>,
    value_linear_index: Option<usize>,
    query_tensor: String,
    key_tensor: String,
    transposed_key_tensor: String,
    value_tensor: String,
    scores_tensor: String,
    scaled_scores_tensor: String,
    probability_tensor: String,
    output_tensor: String,
    source_ops: Vec<String>,
}

fn find_attention_qk_softmax_v(
    ops: &[serde_json::Value],
) -> Result<AttentionJsonMatch, GpuFusionUnsupportedDiagnostic> {
    for (context_matmul_index, context_matmul) in ops.iter().enumerate() {
        if context_matmul.get("op").and_then(serde_json::Value::as_str)
            != Some("trust_ir.vnn.matmul")
        {
            continue;
        }

        let Some(probability_tensor) = string_array_item(context_matmul, "inputs", 0) else {
            continue;
        };
        let Some(value_tensor) = string_array_item(context_matmul, "inputs", 1) else {
            continue;
        };
        let Some(output_tensor) = string_array_item(context_matmul, "outputs", 0) else {
            continue;
        };

        let Some(softmax_index) = producer_index_for_tensor(ops, &probability_tensor) else {
            continue;
        };
        let softmax = &ops[softmax_index];
        if softmax.get("op").and_then(serde_json::Value::as_str) != Some("trust_ir.vnn.softmax") {
            continue;
        }
        let Some(scaled_scores_tensor) = string_array_item(softmax, "inputs", 0) else {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &[op_id(softmax)],
            ));
        };

        let Some(scale_index) = producer_index_for_tensor(ops, &scaled_scores_tensor) else {
            continue;
        };
        let scale = &ops[scale_index];
        if scale.get("op").and_then(serde_json::Value::as_str) == Some("trust_ir.vnn.add") {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::UnsupportedAttentionMask,
                &[op_id(scale), op_id(softmax), op_id(context_matmul)],
            ));
        }
        if scale.get("op").and_then(serde_json::Value::as_str) != Some("trust_ir.vnn.scale") {
            continue;
        }
        let Some(scores_tensor) = string_array_item(scale, "inputs", 0) else {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &[op_id(scale), op_id(softmax), op_id(context_matmul)],
            ));
        };

        let Some(scores_matmul_index) = producer_index_for_tensor(ops, &scores_tensor) else {
            continue;
        };
        let scores_matmul = &ops[scores_matmul_index];
        if scores_matmul.get("op").and_then(serde_json::Value::as_str) == Some("trust_ir.vnn.add") {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::UnsupportedAttentionMask,
                &[
                    op_id(scores_matmul),
                    op_id(scale),
                    op_id(softmax),
                    op_id(context_matmul),
                ],
            ));
        }
        if scores_matmul.get("op").and_then(serde_json::Value::as_str)
            != Some("trust_ir.vnn.matmul")
        {
            continue;
        }
        let Some(query_tensor) = string_array_item(scores_matmul, "inputs", 0) else {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &[op_id(scores_matmul), op_id(scale), op_id(softmax)],
            ));
        };
        let Some(transposed_key_tensor) = string_array_item(scores_matmul, "inputs", 1) else {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &[op_id(scores_matmul), op_id(scale), op_id(softmax)],
            ));
        };

        let Some(transpose_index) = producer_index_for_tensor(ops, &transposed_key_tensor) else {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::MissingTransposeMetadata,
                &[op_id(scores_matmul), op_id(scale), op_id(softmax)],
            ));
        };
        let transpose = &ops[transpose_index];
        if transpose.get("op").and_then(serde_json::Value::as_str) != Some("trust_ir.vnn.transpose")
        {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::MissingTransposeMetadata,
                &[
                    op_id(transpose),
                    op_id(scores_matmul),
                    op_id(scale),
                    op_id(softmax),
                ],
            ));
        }
        let Some(key_tensor) = string_array_item(transpose, "inputs", 0) else {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::MissingTransposeMetadata,
                &[
                    op_id(transpose),
                    op_id(scores_matmul),
                    op_id(scale),
                    op_id(softmax),
                ],
            ));
        };

        let query_linear_index = producer_index_for_tensor(ops, &query_tensor)
            .filter(|index| op_is(ops, *index, "trust_ir.vnn.linear"));
        let key_linear_index = producer_index_for_tensor(ops, &key_tensor)
            .filter(|index| op_is(ops, *index, "trust_ir.vnn.linear"));
        let value_linear_index = producer_index_for_tensor(ops, &value_tensor)
            .filter(|index| op_is(ops, *index, "trust_ir.vnn.linear"));

        let mut source_ops = Vec::new();
        for index in [
            query_linear_index,
            key_linear_index,
            value_linear_index,
            Some(transpose_index),
            Some(scores_matmul_index),
            Some(scale_index),
            Some(softmax_index),
            Some(context_matmul_index),
        ]
        .into_iter()
        .flatten()
        {
            push_unique(&mut source_ops, op_id(&ops[index]));
        }

        return Ok(AttentionJsonMatch {
            context_matmul_index,
            softmax_index,
            scale_index,
            scores_matmul_index,
            transpose_index,
            query_linear_index,
            key_linear_index,
            value_linear_index,
            query_tensor,
            key_tensor,
            transposed_key_tensor,
            value_tensor,
            scores_tensor,
            scaled_scores_tensor,
            probability_tensor,
            output_tensor,
            source_ops,
        });
    }

    Err(GpuFusionUnsupportedDiagnostic::new_for_fusion(
        ATTENTION_QK_SOFTMAX_V_FUSION,
        GpuFusionUnsupportedReason::ShapeMismatch,
        Vec::new(),
    ))
}

fn op_is(ops: &[serde_json::Value], index: usize, expected: &str) -> bool {
    ops.get(index)
        .and_then(|op| op.get("op"))
        .and_then(serde_json::Value::as_str)
        == Some(expected)
}

fn producer_index_for_tensor(ops: &[serde_json::Value], tensor: &str) -> Option<usize> {
    ops.iter()
        .enumerate()
        .find(|(_, op)| {
            op.get("outputs")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|outputs| {
                    outputs
                        .iter()
                        .any(|output| output.as_str().is_some_and(|value| value == tensor))
                })
        })
        .map(|(index, _)| index)
}

fn reject_attention_multiple_consumers(
    ops: &[serde_json::Value],
    tensors: &[&str],
    source_ops: &[String],
) -> Result<(), GpuFusionUnsupportedDiagnostic> {
    for tensor in tensors {
        let consumer_count = ops
            .iter()
            .filter(|op| op_inputs_contain(op, tensor))
            .count();
        if consumer_count != 1 {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::MultipleConsumers,
                source_ops,
            ));
        }
    }
    Ok(())
}

fn softmax_axis_is_last_json(
    module: &serde_json::Value,
    softmax: &serde_json::Value,
    input_tensor: &str,
    source_ops: &[String],
) -> Result<bool, GpuFusionUnsupportedDiagnostic> {
    let rank = read_attention_tensor_shape(module, input_tensor, source_ops)?.len() as i64;
    let Some(axis) = softmax
        .pointer("/attrs/axis")
        .and_then(serde_json::Value::as_i64)
    else {
        return Ok(false);
    };
    Ok(axis == -1 || axis == rank - 1)
}

fn transpose_swaps_last_two_dims_json(transpose: &serde_json::Value) -> bool {
    let Some(perm) = transpose
        .pointer("/attrs/perm")
        .and_then(serde_json::Value::as_array)
    else {
        return false;
    };
    let actual = perm
        .iter()
        .map(serde_json::Value::as_u64)
        .collect::<Option<Vec<_>>>();
    actual.as_deref() == Some(&[0, 2, 1])
}

fn read_attention_scale(
    module: &serde_json::Value,
    scale: &serde_json::Value,
    source_ops: &[String],
) -> Result<f64, GpuFusionUnsupportedDiagnostic> {
    if let Some(scale_value) = scale
        .pointer("/attrs/scale_value")
        .and_then(serde_json::Value::as_f64)
    {
        return Ok(scale_value);
    }

    let initializer_name = scale
        .pointer("/attrs/scale_initializer")
        .and_then(serde_json::Value::as_str)
        .map(str::to_string)
        .or_else(|| string_array_item(scale, "weights", 0))
        .ok_or_else(|| {
            attention_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, source_ops)
        })?;
    let initializer = read_initializer(module, &initializer_name, source_ops)?;
    if initializer.get("dtype").and_then(serde_json::Value::as_str) != Some("f32") {
        return Err(attention_diagnostic(
            GpuFusionUnsupportedReason::UnsupportedDtype,
            source_ops,
        ));
    }
    let shape = initializer
        .get("shape")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| {
            attention_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, source_ops)
        })?;
    if !(shape.is_empty() || shape.len() == 1 && shape[0].as_u64() == Some(1)) {
        return Err(attention_diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            source_ops,
        ));
    }
    initializer
        .get("values")
        .and_then(serde_json::Value::as_array)
        .and_then(|values| values.first())
        .and_then(serde_json::Value::as_f64)
        .ok_or_else(|| {
            attention_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, source_ops)
        })
}

fn read_initializer<'a>(
    module: &'a serde_json::Value,
    name: &str,
    source_ops: &[String],
) -> Result<&'a serde_json::Value, GpuFusionUnsupportedDiagnostic> {
    let initializers = module.get("initializers").ok_or_else(|| {
        attention_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, source_ops)
    })?;
    if let Some(object) = initializers.as_object() {
        return object.get(name).ok_or_else(|| {
            attention_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, source_ops)
        });
    }
    initializers
        .as_array()
        .and_then(|items| {
            items.iter().find(|item| {
                item.get("name")
                    .and_then(serde_json::Value::as_str)
                    .is_some_and(|value| value == name)
            })
        })
        .ok_or_else(|| {
            attention_diagnostic(GpuFusionUnsupportedReason::MissingInitializer, source_ops)
        })
}

fn push_unique(items: &mut Vec<String>, item: String) {
    if !items.iter().any(|existing| existing == &item) {
        items.push(item);
    }
}

fn read_attention_tensor<'a>(
    module: &'a serde_json::Value,
    tensor: &str,
    source_ops: &[String],
) -> Result<&'a serde_json::Value, GpuFusionUnsupportedDiagnostic> {
    module
        .get("tensors")
        .and_then(|tensors| tensors.get(tensor))
        .ok_or_else(|| attention_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, source_ops))
}

fn read_attention_tensor_string(
    module: &serde_json::Value,
    tensor: &str,
    field: &str,
    source_ops: &[String],
) -> Result<String, GpuFusionUnsupportedDiagnostic> {
    read_attention_tensor(module, tensor, source_ops)?
        .get(field)
        .and_then(serde_json::Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| attention_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, source_ops))
}

fn read_attention_tensor_shape(
    module: &serde_json::Value,
    tensor: &str,
    source_ops: &[String],
) -> Result<Vec<u64>, GpuFusionUnsupportedDiagnostic> {
    let shape = read_attention_tensor(module, tensor, source_ops)?
        .get("shape")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| {
            attention_diagnostic(GpuFusionUnsupportedReason::DynamicShape, source_ops)
        })?;
    let mut dims = Vec::with_capacity(shape.len());
    for dim in shape {
        let Some(value) = dim.as_u64() else {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::DynamicShape,
                source_ops,
            ));
        };
        if value == 0 {
            return Err(attention_diagnostic(
                GpuFusionUnsupportedReason::DynamicShape,
                source_ops,
            ));
        }
        dims.push(value);
    }
    Ok(dims)
}

fn find_batch_norm_relu_pair(
    ops: &[serde_json::Value],
) -> Result<(usize, usize, Vec<String>), GpuFusionUnsupportedDiagnostic> {
    for (bn_index, bn) in ops.iter().enumerate() {
        if bn.get("op").and_then(serde_json::Value::as_str) != Some("trust_ir.vnn.batch_norm") {
            continue;
        }
        let bn_id = op_id(bn);
        let source_ops = vec![bn_id.clone()];
        let Some(output) = first_string_array_item(bn, "outputs") else {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &source_ops,
            ));
        };
        let consumers = ops
            .iter()
            .enumerate()
            .filter(|(_, op)| op_inputs_contain(op, &output))
            .collect::<Vec<_>>();
        if consumers.len() != 1 {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::MultipleConsumers,
                &source_ops,
            ));
        }
        let (relu_index, relu) = consumers[0];
        let relu_id = op_id(relu);
        let source_ops = vec![bn_id, relu_id];
        if relu.get("op").and_then(serde_json::Value::as_str) != Some("trust_ir.vnn.relu") {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &source_ops,
            ));
        }
        if relu_index <= bn_index {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &source_ops,
            ));
        }
        return Ok((bn_index, relu_index, source_ops));
    }
    Err(GpuFusionUnsupportedDiagnostic::new(
        GpuFusionUnsupportedReason::ShapeMismatch,
        Vec::new(),
    ))
}

struct ConvBatchNormCandidate {
    source_index: usize,
    batch_norm_index: usize,
    source_ops: Vec<String>,
}

fn find_conv_batch_norm_pair(
    ops: &[serde_json::Value],
) -> Result<ConvBatchNormCandidate, GpuFusionUnsupportedDiagnostic> {
    for (source_index, op) in ops.iter().enumerate() {
        let Some(kind) = op.get("op").and_then(serde_json::Value::as_str) else {
            continue;
        };
        if !matches!(kind, "trust_ir.vnn.conv2d" | "trust_ir.vnn.linear") {
            continue;
        }
        let source_id = op_id(op);
        let source_ops = vec![source_id.clone()];
        let Some(output) = first_string_array_item(op, "outputs") else {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &source_ops,
            ));
        };
        let consumers = ops
            .iter()
            .enumerate()
            .filter(|(_, candidate)| op_inputs_contain(candidate, &output))
            .collect::<Vec<_>>();
        if consumers.len() != 1 {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::MultipleConsumers,
                &source_ops,
            ));
        }
        let (batch_norm_index, bn) = consumers[0];
        let bn_id = op_id(bn);
        let source_ops = vec![source_id, bn_id];
        if bn.get("op").and_then(serde_json::Value::as_str) != Some("trust_ir.vnn.batch_norm") {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &source_ops,
            ));
        }
        if batch_norm_index <= source_index {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::ShapeMismatch,
                &source_ops,
            ));
        }
        return Ok(ConvBatchNormCandidate {
            source_index,
            batch_norm_index,
            source_ops,
        });
    }
    Err(GpuFusionUnsupportedDiagnostic::new_for_fusion(
        CONV_BATCH_NORM_FUSION,
        GpuFusionUnsupportedReason::ShapeMismatch,
        Vec::new(),
    ))
}

fn op_id(op: &serde_json::Value) -> String {
    op.get("id")
        .and_then(serde_json::Value::as_str)
        .unwrap_or("<unknown>")
        .to_string()
}

fn op_inputs_contain(op: &serde_json::Value, tensor: &str) -> bool {
    op.get("inputs")
        .and_then(serde_json::Value::as_array)
        .is_some_and(|inputs| {
            inputs
                .iter()
                .any(|input| input.as_str().is_some_and(|value| value == tensor))
        })
}

fn first_string_array_item(op: &serde_json::Value, field: &str) -> Option<String> {
    string_array_item(op, field, 0)
}

fn string_array_item(op: &serde_json::Value, field: &str, index: usize) -> Option<String> {
    op.get(field)?
        .as_array()?
        .get(index)?
        .as_str()
        .map(str::to_string)
}

fn conv_bn_diagnostic(
    reason: GpuFusionUnsupportedReason,
    source_ops: &[String],
) -> GpuFusionUnsupportedDiagnostic {
    GpuFusionUnsupportedDiagnostic::new_for_fusion(
        CONV_BATCH_NORM_FUSION,
        reason,
        source_ops.to_vec(),
    )
}

fn read_tensor<'a>(
    module: &'a serde_json::Value,
    tensor: &str,
    source_ops: &[String],
) -> Result<&'a serde_json::Value, GpuFusionUnsupportedDiagnostic> {
    module
        .get("tensors")
        .and_then(|tensors| tensors.get(tensor))
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, source_ops))
}

fn read_tensor_string(
    module: &serde_json::Value,
    tensor: &str,
    field: &str,
    source_ops: &[String],
) -> Result<String, GpuFusionUnsupportedDiagnostic> {
    read_tensor(module, tensor, source_ops)?
        .get(field)
        .and_then(serde_json::Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, source_ops))
}

fn read_tensor_shape(
    module: &serde_json::Value,
    tensor: &str,
    source_ops: &[String],
) -> Result<Vec<u64>, GpuFusionUnsupportedDiagnostic> {
    let shape = read_tensor(module, tensor, source_ops)?
        .get("shape")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::DynamicShape, source_ops))?;
    let mut dims = Vec::with_capacity(shape.len());
    for dim in shape {
        let Some(value) = dim.as_u64() else {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::DynamicShape,
                source_ops,
            ));
        };
        if value == 0 {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::DynamicShape,
                source_ops,
            ));
        }
        dims.push(value);
    }
    Ok(dims)
}

fn read_conv_bn_tensor<'a>(
    module: &'a serde_json::Value,
    tensor: &str,
    source_ops: &[String],
) -> Result<&'a serde_json::Value, GpuFusionUnsupportedDiagnostic> {
    module
        .get("tensors")
        .and_then(|tensors| tensors.get(tensor))
        .ok_or_else(|| conv_bn_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, source_ops))
}

fn read_conv_bn_tensor_string(
    module: &serde_json::Value,
    tensor: &str,
    field: &str,
    source_ops: &[String],
) -> Result<String, GpuFusionUnsupportedDiagnostic> {
    read_conv_bn_tensor(module, tensor, source_ops)?
        .get(field)
        .and_then(serde_json::Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| conv_bn_diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, source_ops))
}

fn read_conv_bn_tensor_shape(
    module: &serde_json::Value,
    tensor: &str,
    source_ops: &[String],
) -> Result<Vec<u64>, GpuFusionUnsupportedDiagnostic> {
    let shape = read_conv_bn_tensor(module, tensor, source_ops)?
        .get("shape")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| conv_bn_diagnostic(GpuFusionUnsupportedReason::DynamicShape, source_ops))?;
    let mut dims = Vec::with_capacity(shape.len());
    for dim in shape {
        let Some(value) = dim.as_u64() else {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::DynamicShape,
                source_ops,
            ));
        };
        if value == 0 {
            return Err(conv_bn_diagnostic(
                GpuFusionUnsupportedReason::DynamicShape,
                source_ops,
            ));
        }
        dims.push(value);
    }
    Ok(dims)
}

fn validate_bn_initializer(
    module: &serde_json::Value,
    name: &str,
    channels: u64,
    source_ops: &[String],
) -> Result<(), GpuFusionUnsupportedDiagnostic> {
    let initializer = module
        .get("initializers")
        .and_then(|initializers| initializers.get(name))
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::MissingInitializer, source_ops))?;
    if initializer.get("dtype").and_then(serde_json::Value::as_str) != Some("f32") {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::UnsupportedDtype,
            source_ops,
        ));
    }
    if initializer
        .get("layout")
        .and_then(serde_json::Value::as_str)
        != Some("vector")
    {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::UnsupportedLayout,
            source_ops,
        ));
    }
    let shape = initializer
        .get("shape")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch, source_ops))?;
    if shape.len() != 1 || shape[0].as_u64() != Some(channels) {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::ShapeMismatch,
            source_ops,
        ));
    }
    Ok(())
}

fn validate_initializer(
    module: &serde_json::Value,
    name: &str,
    expected_dtype: &str,
    expected_layout: &str,
    expected_first_dim: Option<u64>,
    source_ops: &[String],
    fusion: &'static str,
) -> Result<(), GpuFusionUnsupportedDiagnostic> {
    let diagnostic = |reason| {
        GpuFusionUnsupportedDiagnostic::new_for_fusion(fusion, reason, source_ops.to_vec())
    };
    let initializer = module
        .get("initializers")
        .and_then(|initializers| initializers.get(name))
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::MissingInitializer))?;
    if initializer.get("dtype").and_then(serde_json::Value::as_str) != Some(expected_dtype) {
        return Err(diagnostic(GpuFusionUnsupportedReason::UnsupportedDtype));
    }
    if initializer
        .get("layout")
        .and_then(serde_json::Value::as_str)
        != Some(expected_layout)
    {
        return Err(diagnostic(GpuFusionUnsupportedReason::UnsupportedLayout));
    }
    let shape = initializer
        .get("shape")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch))?;
    let mut dims = Vec::with_capacity(shape.len());
    for dim in shape {
        let Some(value) = dim.as_u64() else {
            return Err(diagnostic(GpuFusionUnsupportedReason::DynamicShape));
        };
        if value == 0 {
            return Err(diagnostic(GpuFusionUnsupportedReason::DynamicShape));
        }
        dims.push(value);
    }
    if expected_layout == "vector" && dims.len() != 1 {
        return Err(diagnostic(GpuFusionUnsupportedReason::ShapeMismatch));
    }
    if let Some(expected) = expected_first_dim
        && dims.first().copied() != Some(expected)
    {
        return Err(diagnostic(GpuFusionUnsupportedReason::ShapeMismatch));
    }
    if let Some(values) = initializer.get("values") {
        let values = values
            .as_array()
            .ok_or_else(|| diagnostic(GpuFusionUnsupportedReason::ShapeMismatch))?;
        let expected_len = dims.iter().try_fold(1usize, |acc, dim| {
            usize::try_from(*dim)
                .ok()
                .and_then(|dim| acc.checked_mul(dim))
        });
        if expected_len != Some(values.len())
            || values
                .iter()
                .any(|value| !value.as_f64().is_some_and(f64::is_finite))
        {
            return Err(diagnostic(GpuFusionUnsupportedReason::ShapeMismatch));
        }
    }
    Ok(())
}

fn is_training_batch_norm(op: &serde_json::Value) -> bool {
    let Some(attrs) = op.get("attrs") else {
        return false;
    };
    attrs
        .get("training_mode")
        .and_then(serde_json::Value::as_bool)
        .unwrap_or(false)
        || attrs
            .get("training_mode")
            .and_then(serde_json::Value::as_i64)
            .is_some_and(|value| value != 0)
        || attrs
            .get("mode")
            .and_then(serde_json::Value::as_str)
            .is_some_and(|value| value == "training")
        || attrs
            .get("is_test")
            .and_then(serde_json::Value::as_i64)
            .is_some_and(|value| value == 0)
}

fn read_relu_relaxation_metadata(
    module: &serde_json::Value,
    relu: &serde_json::Value,
    source_ops: &[String],
) -> Result<serde_json::Value, GpuFusionUnsupportedDiagnostic> {
    if let Some(relaxation) = relu.pointer("/attrs/relaxation") {
        let source = relaxation.get("source").unwrap_or(relaxation);
        let rewrite = relaxation.get("rewrite").unwrap_or(source);
        return build_relu_relaxation_metadata(
            "relu.attrs.relaxation",
            relaxation.get("relation"),
            source,
            rewrite,
            source_ops,
        );
    }

    if let (Some(source), Some(rewrite)) = (
        module.pointer("/relaxation/source"),
        module.pointer("/relaxation/rewrite"),
    ) {
        return build_relu_relaxation_metadata(
            "module.relaxation",
            module.pointer("/relaxation/relation"),
            source,
            rewrite,
            source_ops,
        );
    }

    Err(diagnostic(
        GpuFusionUnsupportedReason::MissingRelaxationMetadata,
        source_ops,
    ))
}

fn build_relu_relaxation_metadata(
    metadata_source: &'static str,
    relation: Option<&serde_json::Value>,
    source: &serde_json::Value,
    rewrite: &serde_json::Value,
    source_ops: &[String],
) -> Result<serde_json::Value, GpuFusionUnsupportedDiagnostic> {
    validate_relu_relaxation_payload(source, source_ops)?;
    validate_relu_relaxation_payload(rewrite, source_ops)?;

    let relation = relation
        .and_then(serde_json::Value::as_str)
        .unwrap_or("same");
    if !matches!(relation, "same" | "tighter") {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::MissingRelaxationMetadata,
            source_ops,
        ));
    }
    if relation == "same" && source != rewrite {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::MissingRelaxationMetadata,
            source_ops,
        ));
    }

    Ok(serde_json::json!({
        "metadata_source": metadata_source,
        "relation": relation,
        "source": source,
        "rewrite": rewrite,
    }))
}

fn validate_relu_relaxation_payload(
    payload: &serde_json::Value,
    source_ops: &[String],
) -> Result<(), GpuFusionUnsupportedDiagnostic> {
    validate_interval_bounds(payload.get("preactivation_bounds"), source_ops)?;
    validate_interval_bounds(payload.get("output_bounds"), source_ops)?;
    for field in ["lower_slope", "upper_slope", "upper_intercept"] {
        validate_number_array(payload.get(field), source_ops)?;
    }
    Ok(())
}

fn validate_interval_bounds(
    bounds: Option<&serde_json::Value>,
    source_ops: &[String],
) -> Result<(), GpuFusionUnsupportedDiagnostic> {
    let Some(bounds) = bounds else {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::MissingRelaxationMetadata,
            source_ops,
        ));
    };
    let lower = bounds.get("lower").and_then(serde_json::Value::as_array);
    let upper = bounds.get("upper").and_then(serde_json::Value::as_array);
    let (Some(lower), Some(upper)) = (lower, upper) else {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::MissingRelaxationMetadata,
            source_ops,
        ));
    };
    if lower.is_empty() || lower.len() != upper.len() {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::MissingRelaxationMetadata,
            source_ops,
        ));
    }
    for value in lower.iter().chain(upper.iter()) {
        if !value.as_f64().is_some_and(f64::is_finite) {
            return Err(diagnostic(
                GpuFusionUnsupportedReason::MissingRelaxationMetadata,
                source_ops,
            ));
        }
    }
    Ok(())
}

fn validate_number_array(
    value: Option<&serde_json::Value>,
    source_ops: &[String],
) -> Result<(), GpuFusionUnsupportedDiagnostic> {
    let Some(values) = value.and_then(serde_json::Value::as_array) else {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::MissingRelaxationMetadata,
            source_ops,
        ));
    };
    if values.is_empty()
        || values
            .iter()
            .any(|value| !value.as_f64().is_some_and(f64::is_finite))
    {
        return Err(diagnostic(
            GpuFusionUnsupportedReason::MissingRelaxationMetadata,
            source_ops,
        ));
    }
    Ok(())
}

fn bn_relu_certified_pass_run(
    module: &serde_json::Value,
    source_ops: &[String],
    source_provenance: &[VnnSourceProvenance],
    input_tensor: &str,
    preactivation_tensor: &str,
    output_tensor: &str,
    fused_gamma_layer_ids: &[String],
    batch_norm_weights: &[String],
    input_shape: &[u64],
    element_count: u64,
    epsilon: f64,
    kernel_name: &str,
    relaxation: &serde_json::Value,
) -> CertifiedPassRunRecord {
    let summary = bn_relu_certified_pass_summary(
        module,
        source_ops,
        source_provenance,
        input_tensor,
        preactivation_tensor,
        output_tensor,
        fused_gamma_layer_ids,
        batch_norm_weights,
        input_shape,
        element_count,
        epsilon,
        kernel_name,
        relaxation,
    );
    let obligation_hash = bn_relu_certified_obligation_hash(&summary);
    CertifiedPassRunRecord {
        format_version: "trust-cg.opt.certified_pass_run.v1".to_string(),
        pass_name: "bn-relu-relaxation-fusion".to_string(),
        pass_version: 1,
        pass_instance_id: format!("bn-relu-relaxation-fusion:{}:v1", source_ops.join("+")),
        function_name: module_entry_name(module),
        changed: true,
        status: CertifiedPassRunStatus::Verified,
        certificate_count: 1,
        failure_count: 0,
        obligation_hash,
        local_checker: CertifiedPassCheckerRecord {
            kind: "trust-cg-codegen-local".to_string(),
            name: "metal BN+ReLU relaxation metadata checker".to_string(),
            version: "1".to_string(),
            status: CertifiedPassRunStatus::Verified,
        },
        summary,
    }
}

fn bn_relu_certified_pass_summary(
    module: &serde_json::Value,
    source_ops: &[String],
    source_provenance: &[VnnSourceProvenance],
    input_tensor: &str,
    preactivation_tensor: &str,
    output_tensor: &str,
    fused_gamma_layer_ids: &[String],
    batch_norm_weights: &[String],
    input_shape: &[u64],
    element_count: u64,
    epsilon: f64,
    kernel_name: &str,
    relaxation: &serde_json::Value,
) -> serde_json::Value {
    serde_json::json!({
        "format_version": "trust-cg.gamma.bn_relu_fusion_run.v1",
        "fusion": BATCH_NORM_RELU_FUSION,
        "target": GPU_METAL_MSL_TARGET,
        "source": {
            "op_kinds": ["trust_ir.vnn.batch_norm", "trust_ir.vnn.relu"],
            "op_ids": source_ops,
            "input_tensor": input_tensor,
            "preactivation_tensor": preactivation_tensor,
            "output_tensor": output_tensor,
            "dtype": "f32",
            "layout": "nchw",
            "shape": input_shape,
            "provenance": provenance_summary(source_provenance),
        },
        "rewrite": {
            "op": "trust_ir.vnn.batch_norm_relu",
            "kernel_name": kernel_name,
            "fused_gamma_layer_ids": fused_gamma_layer_ids,
            "element_count": element_count,
        },
        "batch_norm": {
            "mode": "inference",
            "axis": 1,
            "epsilon": epsilon,
            "weights": batch_norm_weight_summary(module, batch_norm_weights),
        },
        "relaxation": relaxation,
        "semantic_policy": {
            "float": {
                "rounding": "exact_real",
                "nan": "disallowed",
                "signed_zero": "disallowed",
                "denormals": "disallowed"
            },
            "fail_closed": true
        },
        "certification": {
            "proof_family": "gamma-bn-relu-fusion-relaxation-v1",
            "local_checker": "metal-bn-relu-relaxation-metadata-v1"
        }
    })
}

fn conv_bn_certified_pass_run(
    module: &serde_json::Value,
    source_kind: &str,
    source_ops: &[String],
    source_provenance: &[VnnSourceProvenance],
    input_tensor: &str,
    pre_batch_norm_tensor: &str,
    output_tensor: &str,
    fused_gamma_layer_ids: &[String],
    weight_name: &str,
    bias_name: Option<&str>,
    batch_norm_weights: &[String],
    input_shape: &[u64],
    output_shape: &[u64],
    epsilon: f64,
) -> Result<CertifiedPassRunRecord, GpuFusionUnsupportedDiagnostic> {
    let summary = conv_bn_certified_pass_summary(
        module,
        source_kind,
        source_ops,
        source_provenance,
        input_tensor,
        pre_batch_norm_tensor,
        output_tensor,
        fused_gamma_layer_ids,
        weight_name,
        bias_name,
        batch_norm_weights,
        input_shape,
        output_shape,
        epsilon,
    )?;
    let obligation_hash = conv_bn_certified_obligation_hash(&summary);
    Ok(CertifiedPassRunRecord {
        format_version: "trust-cg.opt.certified_pass_run.v1".to_string(),
        pass_name: CONV_BATCH_NORM_FUSION.to_string(),
        pass_version: 1,
        pass_instance_id: format!("conv-bn-fusion:{}:v1", source_ops.join("+")),
        function_name: module_entry_name(module),
        changed: true,
        status: CertifiedPassRunStatus::Verified,
        certificate_count: 1,
        failure_count: 0,
        obligation_hash,
        local_checker: CertifiedPassCheckerRecord {
            kind: "trust-cg-codegen-local".to_string(),
            name: "conv/linear batch-norm affine fold checker".to_string(),
            version: "1".to_string(),
            status: CertifiedPassRunStatus::Verified,
        },
        summary,
    })
}

fn conv_bn_certified_pass_summary(
    module: &serde_json::Value,
    source_kind: &str,
    source_ops: &[String],
    source_provenance: &[VnnSourceProvenance],
    input_tensor: &str,
    pre_batch_norm_tensor: &str,
    output_tensor: &str,
    fused_gamma_layer_ids: &[String],
    weight_name: &str,
    bias_name: Option<&str>,
    batch_norm_weights: &[String],
    input_shape: &[u64],
    output_shape: &[u64],
    epsilon: f64,
) -> Result<serde_json::Value, GpuFusionUnsupportedDiagnostic> {
    let source_layout = if source_kind == "trust_ir.vnn.conv2d" {
        "nchw"
    } else {
        "nc"
    };
    let weight_layout = if source_kind == "trust_ir.vnn.conv2d" {
        "oihw"
    } else {
        "oi"
    };
    let fused_parameters = conv_bn_fused_parameter_summary(
        module,
        weight_name,
        bias_name,
        batch_norm_weights,
        epsilon,
    )
    .map_err(|reason| conv_bn_diagnostic(reason, source_ops))?;

    Ok(serde_json::json!({
        "format_version": "trust-cg.gamma.conv_bn_fusion_run.v1",
        "fusion": CONV_BATCH_NORM_FUSION,
        "target": GPU_METAL_MSL_TARGET,
        "source": {
            "op_kinds": [source_kind, "trust_ir.vnn.batch_norm"],
            "op_ids": source_ops,
            "input_tensor": input_tensor,
            "pre_batch_norm_tensor": pre_batch_norm_tensor,
            "output_tensor": output_tensor,
            "dtype": "f32",
            "layout": source_layout,
            "input_shape": input_shape,
            "output_shape": output_shape,
            "provenance": provenance_summary(source_provenance),
        },
        "rewrite": {
            "op": if source_kind == "trust_ir.vnn.conv2d" {
                "trust_ir.vnn.conv2d"
            } else {
                "trust_ir.vnn.linear"
            },
            "fused_gamma_layer_ids": fused_gamma_layer_ids,
            "fused_weight": fused_parameters["fused_weight"].clone(),
            "fused_bias": fused_parameters["fused_bias"].clone(),
        },
        "parameters": {
            "source_weight": initializer_summary(module, weight_name),
            "source_bias": bias_name
                .map(|name| initializer_summary(module, name))
                .unwrap_or_else(|| serde_json::json!({"kind": "implicit_zero", "shape": [output_shape[1]]})),
            "weight_layout": weight_layout,
            "batch_norm": {
                "mode": "inference",
                "axis": 1,
                "epsilon": epsilon,
                "weights": batch_norm_weight_summary(module, batch_norm_weights),
            }
        },
        "contract": {
            "mode": "epsilon_equivalence",
            "metric": "absolute_per_element",
            "epsilon": 0.000001
        },
        "semantic_policy": {
            "dtype": "f32",
            "rounding": "rne",
            "nan": "disallowed",
            "signed_zero": "preserved",
            "denormals": "ieee",
            "fail_closed": true
        },
        "certification": {
            "proof_family": "gamma-conv-bn-fusion-affine-v1",
            "local_checker": "conv-bn-affine-parameter-fold-v1"
        }
    }))
}

fn conv_bn_fused_parameter_summary(
    module: &serde_json::Value,
    weight_name: &str,
    bias_name: Option<&str>,
    batch_norm_weights: &[String],
    epsilon: f64,
) -> Result<serde_json::Value, GpuFusionUnsupportedReason> {
    let weight = initializer_summary(module, weight_name);
    let bias = bias_name.map(|name| initializer_summary(module, name));
    let bn = batch_norm_weight_summary(module, batch_norm_weights);
    let channels = weight
        .get("shape")
        .and_then(serde_json::Value::as_array)
        .and_then(|shape| shape.first())
        .and_then(serde_json::Value::as_u64)
        .ok_or(GpuFusionUnsupportedReason::ShapeMismatch)? as usize;

    let maybe_values = (
        initializer_values(module, weight_name)?,
        bias_name
            .map(|name| initializer_values(module, name))
            .transpose()?,
        initializer_values(module, &batch_norm_weights[0])?,
        initializer_values(module, &batch_norm_weights[1])?,
        initializer_values(module, &batch_norm_weights[2])?,
        initializer_values(module, &batch_norm_weights[3])?,
    );

    if let (Some(weight_values), bias_values, Some(scale), Some(beta), Some(mean), Some(var)) =
        maybe_values
    {
        if scale.len() != channels
            || beta.len() != channels
            || mean.len() != channels
            || var.len() != channels
        {
            return Err(GpuFusionUnsupportedReason::ShapeMismatch);
        }
        let bias_values = bias_values.flatten().unwrap_or_else(|| vec![0.0; channels]);
        if bias_values.len() != channels || weight_values.len() % channels != 0 {
            return Err(GpuFusionUnsupportedReason::ShapeMismatch);
        }
        let values_per_channel = weight_values.len() / channels;
        let mut fused_weight = Vec::with_capacity(weight_values.len());
        let mut fused_bias = Vec::with_capacity(channels);
        for channel in 0..channels {
            let affine_scale = scale[channel] / (var[channel] + epsilon).sqrt();
            let start = channel * values_per_channel;
            let end = start + values_per_channel;
            fused_weight.extend(
                weight_values[start..end]
                    .iter()
                    .map(|value| value * affine_scale),
            );
            fused_bias.push(beta[channel] + (bias_values[channel] - mean[channel]) * affine_scale);
        }
        return Ok(serde_json::json!({
            "fused_weight": {
                "kind": "inline_values",
                "dtype": "f32",
                "layout": weight["layout"].clone(),
                "shape": weight["shape"].clone(),
                "values": fused_weight,
            },
            "fused_bias": {
                "kind": "inline_values",
                "dtype": "f32",
                "layout": "vector",
                "shape": [channels],
                "values": fused_bias,
            }
        }));
    }

    Ok(serde_json::json!({
        "fused_weight": {
            "kind": "derived_initializer",
            "formula": "source_weight[o,...] * bn.scale[o] / sqrt(bn.variance[o] + epsilon)",
            "source_weight": weight,
            "batch_norm": bn,
            "epsilon": epsilon
        },
        "fused_bias": {
            "kind": "derived_initializer",
            "formula": "bn.bias[o] + ((source_bias[o] or 0) - bn.mean[o]) * bn.scale[o] / sqrt(bn.variance[o] + epsilon)",
            "source_bias": bias.unwrap_or_else(|| serde_json::json!({"kind": "implicit_zero", "shape": [channels]})),
            "batch_norm": bn,
            "epsilon": epsilon
        }
    }))
}

fn initializer_values(
    module: &serde_json::Value,
    name: &str,
) -> Result<Option<Vec<f64>>, GpuFusionUnsupportedReason> {
    let Some(values) = module
        .get("initializers")
        .and_then(|initializers| initializers.get(name))
        .and_then(|initializer| initializer.get("values"))
    else {
        return Ok(None);
    };
    let values = values
        .as_array()
        .ok_or(GpuFusionUnsupportedReason::ShapeMismatch)?;
    values
        .iter()
        .map(|value| {
            value
                .as_f64()
                .filter(|value| value.is_finite())
                .ok_or(GpuFusionUnsupportedReason::ShapeMismatch)
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Some)
}

fn provenance_summary(source_provenance: &[VnnSourceProvenance]) -> Vec<serde_json::Value> {
    source_provenance
        .iter()
        .map(|provenance| {
            serde_json::json!({
                "gamma_layer_id": provenance.gamma_layer_id,
                "gamma_layer_type": provenance.gamma_layer_type,
                "onnx_node_name": provenance.onnx_node_name,
                "onnx_op_type": provenance.onnx_op_type,
                "onnx_outputs": provenance.onnx_outputs,
            })
        })
        .collect()
}

fn batch_norm_weight_summary(
    module: &serde_json::Value,
    batch_norm_weights: &[String],
) -> serde_json::Value {
    let mut weights = serde_json::Map::new();
    for (role, name) in ["scale", "bias", "mean", "variance"]
        .into_iter()
        .zip(batch_norm_weights)
    {
        weights.insert(role.to_string(), initializer_summary(module, name));
    }
    serde_json::Value::Object(weights)
}

fn initializer_summary(module: &serde_json::Value, name: &str) -> serde_json::Value {
    let initializer = module
        .get("initializers")
        .and_then(|initializers| initializers.get(name))
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "name": name,
        "dtype": initializer.get("dtype").cloned().unwrap_or(serde_json::Value::Null),
        "layout": initializer.get("layout").cloned().unwrap_or(serde_json::Value::Null),
        "shape": initializer.get("shape").cloned().unwrap_or(serde_json::Value::Null),
        "storage": initializer.get("storage").cloned().unwrap_or(serde_json::Value::Null),
        "sha256": initializer.get("sha256").cloned().unwrap_or(serde_json::Value::Null),
    })
}

fn module_entry_name(module: &serde_json::Value) -> String {
    module
        .get("entry")
        .and_then(serde_json::Value::as_str)
        .unwrap_or("vnn-module")
        .to_string()
}

fn bn_relu_certified_obligation_hash(summary: &serde_json::Value) -> String {
    let mut h = StableHasher::new();
    h.write_str("trust-cg.bn-relu-relaxation-fusion.certified-run.v1");
    h.write_framed(summary.to_string().as_bytes());
    format!("trust-cg-opt-certified-pass-run-v1:{:032x}", h.finish128())
}

fn conv_bn_certified_obligation_hash(summary: &serde_json::Value) -> String {
    let mut h = StableHasher::new();
    h.write_str("trust-cg.conv-bn-fusion.certified-run.v1");
    h.write_framed(summary.to_string().as_bytes());
    format!("trust-cg-opt-certified-pass-run-v1:{:032x}", h.finish128())
}

fn read_provenance(op: &serde_json::Value) -> VnnSourceProvenance {
    let provenance = op.get("provenance").unwrap_or(&serde_json::Value::Null);
    VnnSourceProvenance {
        gamma_layer_id: provenance
            .get("gamma_layer_id")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("")
            .to_string(),
        gamma_layer_type: provenance
            .get("gamma_layer_type")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("")
            .to_string(),
        onnx_node_name: provenance
            .get("onnx_node_name")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("")
            .to_string(),
        onnx_op_type: provenance
            .get("onnx_op_type")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("")
            .to_string(),
        onnx_outputs: provenance
            .get("onnx_outputs")
            .and_then(serde_json::Value::as_array)
            .map(|outputs| {
                outputs
                    .iter()
                    .filter_map(serde_json::Value::as_str)
                    .map(str::to_string)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default(),
    }
}

fn sanitize_kernel_suffix(input: &str) -> String {
    let mut suffix = String::with_capacity(input.len());
    for ch in input.chars() {
        if ch.is_ascii_alphanumeric() {
            suffix.push(ch);
        } else {
            suffix.push('_');
        }
    }
    while suffix.contains("__") {
        suffix = suffix.replace("__", "_");
    }
    suffix.trim_matches('_').to_string()
}

fn emit_batch_norm_relu_source(
    kernel_name: &str,
    source_ops: &[String],
    fused_gamma_layer_ids: &[String],
    shape: &[u64],
    element_count: u64,
    epsilon: f64,
) -> String {
    format!(
        "#include <metal_stdlib>\n\
         using namespace metal;\n\n\
         // Generated by Trust Codegen for VNN fused GPU source emission.\n\
         // Fusion: {fusion}\n\
         // Source ops: {source_ops}\n\
         // Fused gamma layer IDs: {gamma_ids}\n\n\
         kernel void {kernel_name}(\n\
         \x20   const device float* input    [[buffer(0)]],\n\
         \x20   device float* output         [[buffer(1)]],\n\
         \x20   const device float* scale    [[buffer(2)]],\n\
         \x20   const device float* bias     [[buffer(3)]],\n\
         \x20   const device float* mean     [[buffer(4)]],\n\
         \x20   const device float* variance [[buffer(5)]],\n\
         \x20   constant float& epsilon      [[buffer(6)]],\n\
         \x20   uint tid [[thread_position_in_grid]])\n\
         {{\n\
         \x20   const uint N = {n}u;\n\
         \x20   const uint C = {c}u;\n\
         \x20   const uint H = {h}u;\n\
         \x20   const uint W = {w}u;\n\
         \x20   const uint HW = H * W;\n\
         \x20   const uint element_count = {element_count}u;\n\
         \x20   (void)N;\n\
         \x20   if (tid >= element_count) return;\n\
         \x20   uint channel = (tid / HW) % C;\n\
         \x20   float y = scale[channel] * (input[tid] - mean[channel]) / sqrt(variance[channel] + epsilon) + bias[channel];\n\
         \x20   output[tid] = max(y, 0.0f);\n\
         }}\n\
         // Static epsilon accepted at selection time: {epsilon:.9}\n",
        fusion = BATCH_NORM_RELU_FUSION,
        source_ops = source_ops.join(" -> "),
        gamma_ids = fused_gamma_layer_ids.join(", "),
        kernel_name = kernel_name,
        n = shape[0],
        c = shape[1],
        h = shape[2],
        w = shape[3],
        element_count = element_count,
        epsilon = epsilon,
    )
}

fn emit_fused_attention_source(
    kernel_name: &str,
    source_ops: &[String],
    fused_gamma_layer_ids: &[String],
    batch: u64,
    sequence: u64,
    head_dim: u64,
    scale: f64,
) -> String {
    format!(
        "#include <metal_stdlib>\n\
         using namespace metal;\n\n\
         // Generated by Trust Codegen for VNN fused GPU source emission.\n\
         // Fusion: {fusion}\n\
         // Source ops: {source_ops}\n\
         // Fused gamma layer IDs: {gamma_ids}\n\n\
         kernel void {kernel_name}(\n\
         \x20   const device float* query  [[buffer(0)]],\n\
         \x20   const device float* key    [[buffer(1)]],\n\
         \x20   const device float* value  [[buffer(2)]],\n\
         \x20   device float* output       [[buffer(3)]],\n\
         \x20   constant float& scale      [[buffer(4)]],\n\
         \x20   uint2 gid [[thread_position_in_grid]])\n\
         {{\n\
         \x20   const uint B = {batch}u;\n\
         \x20   const uint S = {sequence}u;\n\
         \x20   const uint D = {head_dim}u;\n\
         \x20   uint dim = gid.x;\n\
         \x20   uint row = gid.y;\n\
         \x20   if (row >= B * S || dim >= D) return;\n\
         \x20   uint batch = row / S;\n\
         \x20   uint q_pos = row % S;\n\
         \x20   uint base = batch * S * D;\n\
         \x20   uint q_base = base + q_pos * D;\n\
         \x20   float max_score = -INFINITY;\n\
         \x20   for (uint k_pos = 0; k_pos < S; ++k_pos) {{\n\
         \x20       uint k_base = base + k_pos * D;\n\
         \x20       float dot = 0.0f;\n\
         \x20       for (uint kk = 0; kk < D; ++kk) {{\n\
         \x20           dot += query[q_base + kk] * key[k_base + kk];\n\
         \x20       }}\n\
         \x20       max_score = max(max_score, dot * scale);\n\
         \x20   }}\n\
         \x20   float denom = 0.0f;\n\
         \x20   float acc = 0.0f;\n\
         \x20   for (uint k_pos = 0; k_pos < S; ++k_pos) {{\n\
         \x20       uint k_base = base + k_pos * D;\n\
         \x20       float dot = 0.0f;\n\
         \x20       for (uint kk = 0; kk < D; ++kk) {{\n\
         \x20           dot += query[q_base + kk] * key[k_base + kk];\n\
         \x20       }}\n\
         \x20       float weight = exp((dot * scale) - max_score);\n\
         \x20       denom += weight;\n\
         \x20       acc += weight * value[k_base + dim];\n\
         \x20   }}\n\
         \x20   output[q_base + dim] = acc / denom;\n\
         }}\n\
         // Static scale accepted at selection time: {scale:.9}\n",
        fusion = ATTENTION_QK_SOFTMAX_V_FUSION,
        source_ops = source_ops.join(" -> "),
        gamma_ids = fused_gamma_layer_ids.join(", "),
        kernel_name = kernel_name,
        batch = batch,
        sequence = sequence,
        head_dim = head_dim,
        scale = scale,
    )
}

/// Count the number of Metal buffers a kernel requires based on node kind
/// and operation pattern.
fn count_buffers_for_node(node: &ComputeNode) -> Result<usize, MetalEmitError> {
    exact_metal_map(node)?;
    Ok(3) // exact lhs + rhs + result
}

/// Generate Metal kernel sources and dispatch code for a dispatch plan.
///
/// Iterates over GPU-targeted kernel launch operations in the plan, generates
/// an MSL kernel source for each corresponding compute graph node, and
/// generates the host-side dispatch code that drives execution.
///
/// # Arguments
///
/// * `plan` - The dispatch plan containing GPU kernel launches.
/// * `graph` - The compute graph with node metadata (kind, dominant_op, data_size).
///
/// # Returns
///
/// A [`MetalOutput`] containing kernel sources, dispatch code, and buffer metadata.
///
/// # Errors
///
/// Returns [`MetalEmitError`] if any GPU-targeted node cannot be converted to
/// an MSL kernel (e.g., unsuitable node kind, zero data size).
pub fn emit_metal_kernels(
    plan: &DispatchPlan,
    graph: &trust_cg_lower::compute_graph::ComputeGraph,
) -> Result<MetalOutput, MetalEmitError> {
    validate_metal_plan(plan, graph)?;
    let mut kernels = Vec::new();
    let mut total_buffer_count: usize = 0;

    // Iterate over GPU-targeted kernel launches in the plan
    for op in &plan.ops {
        if let DispatchOp::KernelLaunch {
            target, node_id, ..
        } = op
        {
            if *target != ComputeTarget::Gpu {
                continue;
            }

            // Look up the node in the compute graph
            let node = graph
                .node(*node_id)
                .ok_or(MetalEmitError::MissingPlanNode { node_id: *node_id })?;

            // Generate the MSL kernel source
            let source = emit_kernel_from_node(node)?;

            // Determine the kernel function name
            let node_id_str = format!("{}", node.id);

            let kernel_name = format!("trust_cg_map2_{}", node_id_str);

            let buf_count = count_buffers_for_node(node)?;
            total_buffer_count += buf_count;

            kernels.push(NamedKernel {
                name: kernel_name,
                source,
                node_id: *node_id,
            });
        }
    }

    // Generate the host-side dispatch code
    let dispatch_code = emit_dispatch_code(plan, graph)?;

    Ok(MetalOutput {
        kernels,
        dispatch_code,
        buffer_count: total_buffer_count,
    })
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_msl_element_type_display() {
        assert_eq!(MslElementType::Float.to_string(), "float");
        assert_eq!(MslElementType::Half.to_string(), "half");
        assert_eq!(MslElementType::Int.to_string(), "int");
        assert_eq!(MslElementType::Uint.to_string(), "uint");
    }

    #[test]
    fn test_msl_op_emit_binary() {
        assert_eq!(MslOp::Add.emit("x", "y", ""), "x + y");
        assert_eq!(MslOp::Mul.emit("a", "b", ""), "a * b");
        assert_eq!(MslOp::Min.emit("a", "b", ""), "min(a, b)");
    }

    #[test]
    fn test_msl_op_emit_ternary() {
        assert_eq!(MslOp::Fma.emit("a", "b", "c"), "fma(a, b, c)");
        assert_eq!(MslOp::Clamp.emit("x", "lo", "hi"), "clamp(x, lo, hi)");
        assert_eq!(MslOp::Select.emit("t", "f", "c"), "select(f, t, c)");
    }

    #[test]
    fn test_msl_op_arity() {
        assert_eq!(MslOp::Neg.arity(), 1);
        assert_eq!(MslOp::Add.arity(), 2);
        assert_eq!(MslOp::Fma.arity(), 3);
    }

    #[test]
    fn test_dispatch_params_1d() {
        let params = MetalDispatchParams::for_1d(1000, 256);
        // Rounds up: ceil(1000/256) * 256 = 4 * 256 = 1024
        assert_eq!(params.grid_size.width, 1024);
        assert_eq!(params.grid_size.height, 1);
        assert_eq!(params.threadgroup_size.width, 256);
    }

    #[test]
    fn test_dispatch_params_2d() {
        let params = MetalDispatchParams::for_2d(100, 200, 16);
        // ceil(200/16)*16 = 208, ceil(100/16)*16 = 112
        assert_eq!(params.grid_size.width, 208);
        assert_eq!(params.grid_size.height, 112);
        assert_eq!(params.threadgroup_size.width, 16);
        assert_eq!(params.threadgroup_size.height, 16);
    }

    #[test]
    fn test_emit_parallel_map_contains_kernel_decl() {
        let emitter = MetalKernelEmitter::new("node_1", MslElementType::Float);
        let kernel = MslKernel::parallel_map("-input[tid]", 1024, 256);
        let source = emitter.emit(&kernel);

        assert!(source.contains("kernel void trust_cg_map_node_1("));
        assert!(source.contains("const device float* input"));
        assert!(source.contains("if (tid >= 1024u) return;"));
        assert!(source.contains("output[tid] = -input[tid];"));
        assert!(source.contains("#include <metal_stdlib>"));
    }

    #[test]
    fn test_emit_parallel_reduce_tree() {
        let emitter = MetalKernelEmitter::new("node_3", MslElementType::Float);
        let kernel = MslKernel::parallel_reduce(MslReduceOp::Add, false, 2048, 256);
        let source = emitter.emit(&kernel);

        assert!(source.contains("kernel void trust_cg_reduce_node_3("));
        assert!(source.contains("threadgroup float* shared"));
        assert!(source.contains("threadgroup_barrier"));
        assert!(source.contains("partial_results[tgid] = shared[0];"));
    }

    #[test]
    fn test_emit_matmul_aligned_uses_scalar_until_tile_dispatch_exists() {
        let emitter = MetalKernelEmitter::new("node_7", MslElementType::Float);
        let kernel = MslKernel::matmul(64, 32, 64);
        let source = emitter.emit(&kernel);

        assert!(source.contains("kernel void trust_cg_matmul_node_7("));
        assert!(source.contains("const uint M = 64u;"));
        assert!(source.contains("const uint K = 32u;"));
        assert!(source.contains("const uint N = 64u;"));
        assert!(source.contains("for (uint kk = 0; kk < K; ++kk)"));
        assert!(source.contains("acc += A[row * K + kk] * B[kk * N + col];"));
        assert!(source.contains("C[row * N + col] = acc;"));
        // Grid bounds early-return MUST be present for rounded-up dispatch
        // grids. Issue #403.
        assert!(
            source.contains("if (row >= M || col >= N) return;"),
            "aligned matmul kernel must emit grid bounds check, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_matrix"),
            "aligned matmul must stay on scalar path until tile dispatch is wired, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_load"),
            "aligned matmul must not use tile loads with per-element dispatch, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_multiply_accumulate"),
            "aligned matmul must not use simdgroup MAC with per-element dispatch, got:\n{}",
            source
        );
    }

    /// Issue #403: matmul emitter MUST handle K not divisible by the 8-element
    /// tile size. When any of M, K, N is unaligned, we fall back to a scalar
    /// per-thread accumulator loop that reads exactly `K` elements per thread,
    /// avoiding the out-of-bounds `simdgroup_load` that the legacy simdgroup
    /// template would perform on the final partial K tile.
    #[test]
    fn test_emit_matmul_k_not_multiple_of_tile() {
        let emitter = MetalKernelEmitter::new("node_8", MslElementType::Float);
        // K=10 is not a multiple of 8 — must trigger the scalar fallback.
        let kernel = MslKernel::matmul(16, 10, 16);
        let source = emitter.emit(&kernel);

        // Scalar fallback characteristics.
        assert!(
            source.contains("kernel void trust_cg_matmul_node_8("),
            "expected matmul kernel name, got:\n{}",
            source
        );
        assert!(
            source.contains("const uint K = 10u;"),
            "expected K=10, got:\n{}",
            source
        );
        assert!(
            source.contains("if (row >= M || col >= N) return;"),
            "scalar fallback must emit grid bounds check, got:\n{}",
            source
        );
        assert!(
            source.contains("for (uint kk = 0; kk < K; ++kk)"),
            "scalar fallback must emit scalar accumulator loop, got:\n{}",
            source
        );
        assert!(
            source.contains("A[row * K + kk] * B[kk * N + col]"),
            "scalar fallback must emit element-wise multiply-add, got:\n{}",
            source
        );
        assert!(
            source.contains("C[row * N + col] = acc;"),
            "scalar fallback must emit scalar store, got:\n{}",
            source
        );
        // The scalar fallback must NOT use simdgroup_matrix (which would do
        // out-of-bounds 8x8 loads on the K=10 tail).
        assert!(
            !source.contains("simdgroup_load"),
            "scalar fallback must not emit simdgroup_load, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_multiply_accumulate"),
            "scalar fallback must not emit simdgroup_multiply_accumulate, got:\n{}",
            source
        );
    }

    /// Issue #403: even when the matmul is shape-unaligned, the grid bounds
    /// early-return guards against `MetalDispatchParams::for_2d`-style dispatch
    /// grids that round up to a multiple of the tile size. Here M=7 is smaller
    /// than the 8-wide tile, so any rounded-up grid will spawn threads with
    /// `row >= M` that must bail out cleanly.
    #[test]
    fn test_emit_matmul_m_smaller_than_tile_has_grid_bounds() {
        let emitter = MetalKernelEmitter::new("node_9", MslElementType::Float);
        let kernel = MslKernel::matmul(7, 8, 8);
        let source = emitter.emit(&kernel);

        assert!(
            source.contains("kernel void trust_cg_matmul_node_9("),
            "expected matmul kernel name, got:\n{}",
            source
        );
        assert!(
            source.contains("const uint M = 7u;"),
            "expected M=7, got:\n{}",
            source
        );
        assert!(
            source.contains("if (row >= M || col >= N) return;"),
            "unaligned-M matmul must emit grid bounds check, got:\n{}",
            source
        );
        // M=7 forces the scalar fallback (7 % 8 != 0).
        assert!(
            source.contains("for (uint kk = 0; kk < K; ++kk)"),
            "M<8 must trigger scalar fallback, got:\n{}",
            source
        );
    }

    /// Issue #403 regression guard: for the pre-existing aligned square case
    /// (M=K=N=64), the emitted kernel must still be bounded under the current
    /// per-output-element dispatch path.
    #[test]
    fn test_emit_matmul_aligned_square_uses_scalar_safe_path() {
        let emitter = MetalKernelEmitter::new("node_10", MslElementType::Float);
        let kernel = MslKernel::matmul(64, 64, 64);
        let source = emitter.emit(&kernel);

        // Current correctness path: one thread computes one output element.
        assert!(
            source.contains("for (uint kk = 0; kk < K; ++kk)"),
            "aligned 64x64x64 must use scalar K loop until tile dispatch is wired, got:\n{}",
            source
        );
        assert!(
            source.contains("acc += A[row * K + kk] * B[kk * N + col];"),
            "aligned path must emit scalar multiply-add, got:\n{}",
            source
        );
        assert!(
            source.contains("C[row * N + col] = acc;"),
            "aligned path must emit scalar store, got:\n{}",
            source
        );
        assert!(
            !source.contains("#include <metal_simdgroup_matrix>"),
            "aligned path must not include simdgroup header under per-element dispatch, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_matrix"),
            "aligned path must not declare simdgroup tiles under per-element dispatch, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_load"),
            "aligned path must not use simdgroup loads under per-element dispatch, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_store"),
            "aligned path must not use simdgroup stores under per-element dispatch, got:\n{}",
            source
        );
        assert!(
            !source.contains("for (uint kk = 0; kk < K; kk += 8)"),
            "aligned path must not use tile-stride K loop under per-element dispatch, got:\n{}",
            source
        );

        // #403: grid bounds early-return.
        assert!(
            source.contains("if (row >= M || col >= N) return;"),
            "aligned path must now emit grid bounds early-return, got:\n{}",
            source
        );
    }

    /// Issue #403 AC #4: explicit repro from the issue body.
    ///
    /// `MslKernel::matmul(10, 10, 10)` was the original out-of-bounds repro.
    /// All three dims are unaligned (10 % 8 = 2), so the emitter must:
    /// 1. Trigger the scalar fallback (no simdgroup_load / simdgroup_matrix).
    /// 2. Emit a grid-bounds early-return for M=10, N=10 padded dispatch.
    /// 3. Loop the full K=10 elements per thread with a bounded index.
    /// 4. Produce a single deterministic kernel (string-match friendly).
    ///
    /// The final AC criterion ("compiles under `xcrun metal`") is not
    /// verifiable on CI-less developer machines without the Metal toolchain;
    /// this test guarantees the emitted MSL is *structurally* correct so a
    /// downstream `xcrun metal -c` pass can be run manually on an Apple
    /// Silicon machine with Xcode installed.
    #[test]
    fn test_emit_matmul_10_10_10_issue_403_repro() {
        let emitter = MetalKernelEmitter::new("repro_403", MslElementType::Float);
        let kernel = MslKernel::matmul(10, 10, 10);
        let source = emitter.emit(&kernel);

        // Kernel signature uses the expected node id.
        assert!(
            source.contains("kernel void trust_cg_matmul_repro_403("),
            "expected matmul kernel signature, got:\n{}",
            source
        );

        // Declared shape.
        assert!(
            source.contains("const uint M = 10u;"),
            "expected M=10, got:\n{}",
            source
        );
        assert!(
            source.contains("const uint K = 10u;"),
            "expected K=10, got:\n{}",
            source
        );
        assert!(
            source.contains("const uint N = 10u;"),
            "expected N=10, got:\n{}",
            source
        );

        // Grid bounds early-return is mandatory under rounded-up dispatch.
        assert!(
            source.contains("if (row >= M || col >= N) return;"),
            "matmul(10,10,10) must emit grid bounds check, got:\n{}",
            source
        );

        // Must NOT use simdgroup_matrix / simdgroup_load / simdgroup_store:
        // any of these on K=10 would read 4 elements OOB on the final tile.
        assert!(
            !source.contains("simdgroup_matrix"),
            "matmul(10,10,10) must not use simdgroup_matrix, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_load"),
            "matmul(10,10,10) must not use simdgroup_load, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_multiply_accumulate"),
            "matmul(10,10,10) must not use simdgroup_multiply_accumulate, got:\n{}",
            source
        );
        assert!(
            !source.contains("simdgroup_store"),
            "matmul(10,10,10) must not use simdgroup_store, got:\n{}",
            source
        );
        assert!(
            !source.contains("<metal_simdgroup_matrix>"),
            "matmul(10,10,10) must not include simdgroup_matrix header, got:\n{}",
            source
        );

        // Scalar fallback body: element-wise MAC over the full K range,
        // single per-thread accumulator store.
        assert!(
            source.contains("for (uint kk = 0; kk < K; ++kk)"),
            "matmul(10,10,10) must use scalar K loop, got:\n{}",
            source
        );
        assert!(
            source.contains("acc += A[row * K + kk] * B[kk * N + col];"),
            "matmul(10,10,10) must emit scalar multiply-add, got:\n{}",
            source
        );
        assert!(
            source.contains("C[row * N + col] = acc;"),
            "matmul(10,10,10) must emit scalar store, got:\n{}",
            source
        );
    }

    #[test]
    fn test_kernel_function_name() {
        let map = MslKernel::parallel_map("x", 100, 32);
        assert_eq!(kernel_function_name("n1", &map), "trust_cg_map_n1");

        let map2 = MslKernel::parallel_map2("a+b", 100, 32);
        assert_eq!(kernel_function_name("n1", &map2), "trust_cg_map2_n1");

        let red = MslKernel::parallel_reduce(MslReduceOp::Add, true, 100, 256);
        assert_eq!(kernel_function_name("n2", &red), "trust_cg_reduce_simd_n2");

        let mm = MslKernel::matmul(8, 8, 8);
        assert_eq!(kernel_function_name("n3", &mm), "trust_cg_matmul_n3");
    }

    // -----------------------------------------------------------------------
    // Sealed ComputeGraph -> Metal boundary tests
    // -----------------------------------------------------------------------

    fn forged_node(id: u32, target: ComputeTarget, dominant_op: &str) -> ComputeNode {
        let mut costs = HashMap::new();
        costs.insert(
            target,
            trust_cg_lower::compute_graph::ComputeCost {
                latency_cycles: 7,
                throughput_ops_per_kcycle: 1,
            },
        );
        ComputeNode {
            id: ComputeNodeId(id),
            instructions: vec![],
            costs,
            legal_targets: vec![target],
            kind: NodeKind::DataParallel,
            data_size_bytes: 1 << 20,
            produced_values: vec![],
            consumed_values: vec![],
            dominant_op: dominant_op.to_string(),
            target_legality: None,
            matmul_shape: None,
        }
    }

    fn gpu_plan(node_id: ComputeNodeId) -> DispatchPlan {
        DispatchPlan {
            ops: vec![
                DispatchOp::KernelLaunch {
                    target: ComputeTarget::Gpu,
                    node_id,
                    estimated_cycles: 7,
                },
                DispatchOp::Synchronize {
                    target: ComputeTarget::Gpu,
                    node_id,
                },
            ],
            assignment: HashMap::from([(node_id, ComputeTarget::Gpu)]),
            estimated_total_cycles: 7,
        }
    }

    fn graphbuilder_exact_u32x4_graph_in_function_one()
    -> trust_cg_lower::compute_graph::ComputeGraph {
        use trust_cg_lower::adapter::Proof;
        use trust_cg_lower::compute_graph::GraphBuilder;
        use trust_cg_lower::instructions::Value;
        use trust_cg_lower::target_analysis::{
            CostConfig, ProofAnalyzer, SubgraphId, SubgraphProof, TargetProofContext,
        };
        use trust_ir::{
            BinOp, Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
        };

        let mut module = Module::new("exact_u32x4_metal");
        let dummy_ty = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut dummy = Function::new(FuncId::new(0), "dummy", dummy_ty, BlockId::new(0));
        dummy.blocks.push(Block::new(BlockId::new(0)));
        module.add_function(dummy);

        let vector_ty = Ty::Vector(Box::new(Ty::U32), 4);
        let exact_ty = module.add_func_type(FuncTy {
            params: vec![vector_ty.clone(), vector_ty.clone()],
            returns: vec![vector_ty.clone()],
            is_vararg: false,
        });
        let mut exact = Function::new(FuncId::new(1), "map2", exact_ty, BlockId::new(0));
        exact.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![
                (ValueId::new(0), vector_ty.clone()),
                (ValueId::new(1), vector_ty.clone()),
            ],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: vector_ty,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(2)],
                }),
            ],
        });
        module.add_function(exact);

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
        GraphBuilder::new(analyzer, proof_ctx).build_from_module(&module)
    }

    /// Cross-crate authority frontier: lower's internal `cfg(test)` structural
    /// model validates the canonical recipe, digest, and exact U32 operation.
    /// Here `trust-cg-lower` is a normal dependency, so the production policy
    /// must retain that genuinely GraphBuilder-derived recipe while refusing
    /// emission until validator-issued target replay authority is wired.
    #[test]
    fn graphbuilder_scoped_u32_recipe_fails_closed_without_validator_authority() {
        use trust_cg_lower::compute_graph::AcceleratorBindingError;

        let graph = graphbuilder_exact_u32x4_graph_in_function_one();
        let [node] = graph.nodes.as_slice() else {
            panic!(
                "expected one GraphBuilder node, got {:?}",
                graph.nodes.len()
            );
        };
        assert!(
            node.instructions
                .iter()
                .all(|instruction| instruction.func_idx == 1)
        );
        assert_eq!(
            node.consumed_values,
            vec![
                TrustIrValueId::new(1, trust_ir::ValueId::new(0)),
                TrustIrValueId::new(1, trust_ir::ValueId::new(1)),
                TrustIrValueId::new(1, trust_ir::ValueId::new(2)),
            ]
        );
        assert_eq!(
            node.produced_values,
            vec![TrustIrValueId::new(1, trust_ir::ValueId::new(2))]
        );

        assert!(matches!(
            node.validated_accelerator_recipe(AcceleratorBackend::Metal),
            Err(AcceleratorBindingError::TargetNotAuthorized {
                node_id: ComputeNodeId(0),
                target: ComputeTarget::Gpu,
            })
        ));
        let error = emit_kernel_from_node(node)
            .expect_err("production must reject emission without validator replay authority");
        let MetalEmitError::SemanticBinding { node_id, reason } = error else {
            panic!("expected semantic binding rejection, got {error:?}");
        };
        assert_eq!(node_id, ComputeNodeId(0));
        assert!(
            reason.contains("did not authorize target GPU"),
            "unexpected reason: {reason}"
        );
    }

    #[test]
    fn caller_labels_and_legal_targets_cannot_mint_metal_semantics() {
        for op in [
            "ADD",
            "FADD",
            "FDIV",
            "REDUCE_INT_ADD",
            "GEMM",
            "MATMUL",
            "UNKNOWN",
        ] {
            let node = forged_node(9, ComputeTarget::Gpu, op);
            let error = emit_kernel_from_node(&node)
                .expect_err("manual node must not gain Metal authority");
            assert!(matches!(error, MetalEmitError::SemanticBinding { .. }));

            let mut graph = trust_cg_lower::compute_graph::ComputeGraph::new();
            graph.nodes.push(node);
            let error = emit_metal_kernels(&gpu_plan(ComputeNodeId(9)), &graph)
                .expect_err("manual plan and node must not emit accelerator code");
            assert!(matches!(error, MetalEmitError::SemanticBinding { .. }));
        }
    }

    #[test]
    fn public_operand_and_instruction_vectors_are_not_semantic_recipes() {
        let mut node = forged_node(10, ComputeTarget::Gpu, "ADD");
        node.instructions = vec![
            trust_cg_lower::compute_graph::TrustIrInstId {
                func_idx: 0,
                block_id: 0,
                inst_idx: 0,
            },
            trust_cg_lower::compute_graph::TrustIrInstId {
                func_idx: 0,
                block_id: 0,
                inst_idx: 1,
            },
        ];
        node.consumed_values = vec![TrustIrValueId::new(0, trust_ir::ValueId::new(1))];
        node.produced_values = vec![TrustIrValueId::new(0, trust_ir::ValueId::new(2))];
        assert!(matches!(
            emit_kernel_from_node(&node),
            Err(MetalEmitError::SemanticBinding { .. })
        ));
    }

    #[test]
    fn metal_buffer_keys_include_function_identity_for_reused_value_ids() {
        let local = |func_idx, value| TrustIrValueId::new(func_idx, trust_ir::ValueId::new(value));
        let first =
            emit_exact_buffer_bindings(0, ComputeNodeId(0), local(0, 0), local(0, 1), local(0, 2));
        let second =
            emit_exact_buffer_bindings(1, ComputeNodeId(1), local(1, 0), local(1, 1), local(1, 2));

        assert_ne!(first, second);
        assert!(first.contains("buffers[@(0ULL)]"));
        assert!(first.contains("buffers[@(1ULL)]"));
        assert!(first.contains("buffers[@(2ULL)]"));
        assert!(second.contains("buffers[@(4294967296ULL)]"));
        assert!(second.contains("buffers[@(4294967297ULL)]"));
        assert!(second.contains("buffers[@(4294967298ULL)]"));
        assert!(
            !second.contains("buffers[@(0ULL)]"),
            "function 1 must not reuse function 0's local SSA buffer key"
        );
    }

    #[test]
    fn missing_plan_node_is_an_error_not_a_skip() {
        let graph = trust_cg_lower::compute_graph::ComputeGraph::new();
        let error = emit_metal_kernels(&gpu_plan(ComputeNodeId(404)), &graph)
            .expect_err("missing plan node must fail");
        assert_eq!(
            error,
            MetalEmitError::MissingPlanNode {
                node_id: ComputeNodeId(404)
            }
        );
    }

    #[test]
    fn transfer_must_match_exact_graph_edge_and_assignments() {
        use trust_cg_lower::compute_graph::{DataEdge, TransferCost};

        let mut graph = trust_cg_lower::compute_graph::ComputeGraph::new();
        graph
            .nodes
            .push(forged_node(0, ComputeTarget::CpuScalar, "CPU"));
        graph.nodes.push(forged_node(1, ComputeTarget::Gpu, "ADD"));
        graph.edges.push(DataEdge {
            from: ComputeNodeId(0),
            to: ComputeNodeId(1),
            transfer_bytes: 64,
            transfer_cost: TransferCost::zero(),
        });
        let plan = DispatchPlan {
            ops: vec![DispatchOp::DataTransfer {
                src: ComputeTarget::CpuScalar,
                dst: ComputeTarget::Gpu,
                size_bytes: 63,
                cost: estimate_transfer_cost(63, ComputeTarget::CpuScalar, ComputeTarget::Gpu),
                edge_from: ComputeNodeId(0),
                edge_to: ComputeNodeId(1),
            }],
            assignment: HashMap::from([
                (ComputeNodeId(0), ComputeTarget::CpuScalar),
                (ComputeNodeId(1), ComputeTarget::Gpu),
            ]),
            estimated_total_cycles: 0,
        };
        assert!(matches!(
            emit_dispatch_code(&plan, &graph),
            Err(MetalEmitError::InvalidDispatchPlan { .. })
        ));
    }

    #[test]
    fn sync_requires_one_preceding_matching_gpu_launch() {
        let mut graph = trust_cg_lower::compute_graph::ComputeGraph::new();
        graph.nodes.push(forged_node(1, ComputeTarget::Gpu, "ADD"));
        let plan = DispatchPlan {
            ops: vec![DispatchOp::Synchronize {
                target: ComputeTarget::Gpu,
                node_id: ComputeNodeId(1),
            }],
            assignment: HashMap::from([(ComputeNodeId(1), ComputeTarget::Gpu)]),
            estimated_total_cycles: 0,
        };
        assert!(matches!(
            emit_dispatch_code(&plan, &graph),
            Err(MetalEmitError::InvalidDispatchPlan { .. })
        ));
    }

    #[test]
    fn cpu_only_plan_remains_a_live_fallback() {
        let mut graph = trust_cg_lower::compute_graph::ComputeGraph::new();
        graph
            .nodes
            .push(forged_node(3, ComputeTarget::CpuScalar, "ADD"));
        let plan = DispatchPlan {
            ops: vec![DispatchOp::KernelLaunch {
                target: ComputeTarget::CpuScalar,
                node_id: ComputeNodeId(3),
                estimated_cycles: 7,
            }],
            assignment: HashMap::from([(ComputeNodeId(3), ComputeTarget::CpuScalar)]),
            estimated_total_cycles: 7,
        };
        let output = emit_metal_kernels(&plan, &graph).expect("CPU fallback is not Metal emission");
        assert!(output.kernels.is_empty());
        assert_eq!(output.buffer_count, 0);
        assert!(output.dispatch_code.contains("CPU execution"));
    }

    #[test]
    fn empty_plan_emits_only_a_host_shell() {
        let graph = trust_cg_lower::compute_graph::ComputeGraph::new();
        let plan = DispatchPlan {
            ops: vec![],
            assignment: HashMap::new(),
            estimated_total_cycles: 0,
        };
        let output = emit_metal_kernels(&plan, &graph).unwrap();
        assert!(output.kernels.is_empty());
        assert!(
            output
                .dispatch_code
                .contains("executeDispatchPlanWithBuffers")
        );
    }

    #[test]
    fn test_metal_output_struct_fields() {
        // Verify MetalOutput struct is correctly constructed
        let output = MetalOutput {
            kernels: vec![NamedKernel {
                name: "test_kernel".to_string(),
                source: "kernel void test_kernel() {}".to_string(),
                node_id: ComputeNodeId(42),
            }],
            dispatch_code: "dispatch code here".to_string(),
            buffer_count: 3,
        };

        assert_eq!(output.kernels.len(), 1);
        assert_eq!(output.kernels[0].name, "test_kernel");
        assert_eq!(output.kernels[0].node_id, ComputeNodeId(42));
        assert_eq!(output.dispatch_code, "dispatch code here");
        assert_eq!(output.buffer_count, 3);
    }
}
