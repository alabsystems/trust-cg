// trust-cg-gpu/kernel_extract.rs - Extract parallel regions as kernels
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-gpu-passes-pipeline.md (Pass 1).

//! Pass 1: `KernelExtract`.
//!
//! Walks the compute graph, selects nodes whose workload classification is
//! GPU-eligible (DataParallel, MatrixHeavy), and groups contiguous
//! compatible nodes into [`KernelRegion`]s.
//!
//! # GPU eligibility gate (trust_ir#39, Trust Codegen#428/#433)
//!
//! The GPU gate in this pass is the **composed** predicate — the workload
//! classification (`NodeKind::DataParallel | NodeKind::MatrixHeavy`) AND the
//! function-level `trust_ir::Function::is_gpu_eligible()` predicate supplied by
//! the caller. That trust_ir predicate is intentionally frozen as:
//!
//! 1. `is_safe_for_gpu()` — `Pure + NoPanic + Deterministic` (trust_ir#39 contract
//!    frozen; **Trust Codegen must not tighten this gate on its own**).
//! 2. `ParallelMap` proof is present.
//! 3. `DivergenceClass` is `Uniform` or `Low` (missing or `High` disqualifies).
//!
//! Trust Codegen must **not** add its own divergence check, parallel-map re-inference,
//! or Pure/NoPanic/Deterministic enforcement — the authoritative source is the
//! trust_ir `is_gpu_eligible()` composition. See trust_ir `Function::is_gpu_eligible`
//! docstring and `designs/2026-04-18-ty-supremacy-trust_ir-scope.md` §3.2.
//!
//! Callers that don't have per-node trust_ir function handles can use [`run`] (the
//! pre-#433 behavior, no function-level gate — tests and fixtures). Callers
//! that do have trust_ir functions should call [`run_with_gpu_gate`] with a
//! closure that returns `function.is_gpu_eligible()` for the owning function
//! of each node.

use std::fmt;

use serde::{Deserialize, Serialize};

use trust_cg_lower::compute_graph::{
    AcceleratorBackend, AcceleratorOperation, ComputeGraph, ComputeNodeId, NodeKind,
};

use crate::region::{BufferId, KernelRegion, RegionId};

// ---------------------------------------------------------------------------
// KernelPattern
// ---------------------------------------------------------------------------

/// Hint describing the shape of a kernel region.
///
/// Maps directly to one of the patterns supported by
/// [`trust_cg_codegen::metal_emitter::MslKernel`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum KernelPattern {
    /// Element-wise `output[i] = f(input[i])`.
    ParallelMap,
    /// Tree reduction across the input.
    ParallelReduce,
    /// Fused map-reduce (avoids materializing the intermediate).
    MapReduce,
    /// Tiled matrix multiply.
    MatMul,
}

impl fmt::Display for KernelPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelPattern::ParallelMap => write!(f, "ParallelMap"),
            KernelPattern::ParallelReduce => write!(f, "ParallelReduce"),
            KernelPattern::MapReduce => write!(f, "MapReduce"),
            KernelPattern::MatMul => write!(f, "MatMul"),
        }
    }
}

impl KernelPattern {
    /// Derive the default kernel pattern from a `NodeKind`.
    pub fn from_kind(kind: NodeKind) -> Option<Self> {
        match kind {
            NodeKind::DataParallel => Some(KernelPattern::ParallelMap),
            NodeKind::MatrixHeavy => Some(KernelPattern::MatMul),
            NodeKind::Scalar => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// Pass 1: extract GPU-eligible regions from a [`ComputeGraph`].
#[derive(Debug, Default, Clone)]
pub struct KernelExtract;

impl KernelExtract {
    /// Run the pass without a function-level GPU gate.
    ///
    /// Returns one [`KernelRegion`] per node whose `NodeKind` is GPU-eligible
    /// (`DataParallel` or `MatrixHeavy`). Callers that have trust_ir function
    /// handles should prefer [`Self::run_with_gpu_gate`], which additionally
    /// consults `trust_ir::Function::is_gpu_eligible()` per node (trust_ir#39 frozen
    /// composition — see module docstring).
    ///
    /// The scaffolding keeps one node per region. A future depth pass can
    /// merge adjacent compatible regions; merging is safe only when
    /// address space, element type, and divergence class agree.
    pub fn run(&self, graph: &ComputeGraph) -> Vec<KernelRegion> {
        // `|_| true` here means "no function-level gate" — fixtures and
        // pre-trust_ir#39 call sites. Production call sites that own a
        // `trust_ir::Function` must pass the real `is_gpu_eligible` predicate.
        self.run_with_gpu_gate(graph, |_| true)
    }

    /// Run the pass, consulting a caller-supplied function-level GPU gate
    /// for each compute node.
    ///
    /// `gpu_eligible(node) -> bool` should return `true` iff the trust_ir
    /// function owning `node` satisfies `trust_ir::Function::is_gpu_eligible()`.
    /// See the module docstring for the exact composed predicate. Trust Codegen does
    /// NOT compose divergence / parallel-map / purity here — it defers to
    /// the frozen trust_ir predicate.
    ///
    /// A node is extracted as a [`KernelRegion`] iff:
    ///
    /// 1. Its [`NodeKind`] has a [`KernelPattern`] mapping (DataParallel or
    ///    MatrixHeavy), AND
    /// 2. `gpu_eligible(node)` returns `true`.
    pub fn run_with_gpu_gate<F>(
        &self,
        graph: &ComputeGraph,
        mut gpu_eligible: F,
    ) -> Vec<KernelRegion>
    where
        F: FnMut(&trust_cg_lower::compute_graph::ComputeNode) -> bool,
    {
        let mut regions = Vec::new();
        let mut next_region = 0u32;
        let mut next_buf = 0u32;

        for node in &graph.nodes {
            let Ok(recipe) = node.validated_accelerator_recipe(AcceleratorBackend::Metal) else {
                continue;
            };
            // trust_ir#39 composed-predicate gate. Trust Codegen must NOT add its own
            // divergence / purity / ParallelMap checks here — defer to the
            // frozen `trust_ir::Function::is_gpu_eligible` predicate.
            if !gpu_eligible(node) {
                continue;
            }

            let (input_values, output_values, element_count, pattern) = match recipe.operation() {
                AcceleratorOperation::ElementwiseBinary {
                    lhs,
                    rhs,
                    result,
                    element_count,
                    ..
                } => (
                    vec![*lhs, *rhs],
                    vec![*result],
                    *element_count,
                    KernelPattern::ParallelMap,
                ),
            };

            // Buffer arity and order come only from the sealed operation.
            // `ComputeNode::consumed_values` also contains control/Return
            // uses and is not a kernel-argument list.
            let (Ok(input_count), Ok(output_count)) = (
                u32::try_from(input_values.len()),
                u32::try_from(output_values.len()),
            ) else {
                continue;
            };

            let mut inputs = Vec::with_capacity(input_count as usize);
            for _ in 0..input_count {
                inputs.push(BufferId(next_buf));
                next_buf += 1;
            }
            let mut outputs = Vec::with_capacity(output_count as usize);
            for _ in 0..output_count {
                outputs.push(BufferId(next_buf));
                next_buf += 1;
            }

            let mut region = KernelRegion::new(
                RegionId(next_region),
                format!("kernel_{}", node.id),
                vec![node.id],
                element_count,
                recipe.data_size_bytes(),
                pattern,
                inputs,
                outputs,
            );
            region.input_values = input_values;
            region.output_values = output_values;
            region.bind_semantic_recipe(recipe.clone());
            regions.push(region);
            next_region += 1;
        }

        regions
    }

    /// Convenience: sum of `data_size_bytes` across extracted regions.
    pub fn total_bytes(regions: &[KernelRegion]) -> u64 {
        regions.iter().map(|r| r.data_size_bytes).sum()
    }

    /// Convenience: list all compute nodes referenced by the regions.
    pub fn covered_nodes(regions: &[KernelRegion]) -> Vec<ComputeNodeId> {
        let mut out = Vec::new();
        for r in regions {
            out.extend_from_slice(&r.nodes);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use trust_cg_lower::compute_graph::{ComputeCost, ComputeNode, ComputeNodeId, NodeKind};
    use trust_cg_lower::target_analysis::ComputeTarget;

    fn mk_node(id: u32, kind: NodeKind, bytes: u64) -> ComputeNode {
        let mut costs = HashMap::new();
        costs.insert(
            ComputeTarget::CpuScalar,
            ComputeCost {
                latency_cycles: 10,
                throughput_ops_per_kcycle: 1000,
            },
        );
        costs.insert(
            ComputeTarget::Gpu,
            ComputeCost {
                latency_cycles: 100,
                throughput_ops_per_kcycle: 5000,
            },
        );
        ComputeNode {
            id: ComputeNodeId(id),
            instructions: vec![],
            costs,
            legal_targets: vec![ComputeTarget::CpuScalar, ComputeTarget::Gpu],
            kind,
            data_size_bytes: bytes,
            produced_values: vec![],
            consumed_values: vec![],
            dominant_op: "ADD".to_string(),
            target_legality: None,
            matmul_shape: None,
        }
    }

    #[test]
    fn manual_data_parallel_node_has_no_extraction_authority() {
        let mut graph = ComputeGraph::new();
        graph.add_node(mk_node(0, NodeKind::DataParallel, 4096));
        let regions = KernelExtract.run(&graph);
        assert!(regions.is_empty());
    }

    #[test]
    fn skips_scalar_node() {
        let mut graph = ComputeGraph::new();
        graph.add_node(mk_node(0, NodeKind::Scalar, 8));
        assert!(KernelExtract.run(&graph).is_empty());
    }

    #[test]
    fn heuristic_matrix_kind_has_no_extraction_authority() {
        let mut graph = ComputeGraph::new();
        graph.add_node(mk_node(0, NodeKind::MatrixHeavy, 65536));
        assert!(KernelExtract.run(&graph).is_empty());
    }

    #[test]
    fn total_bytes_and_covered_nodes() {
        let mut graph = ComputeGraph::new();
        graph.add_node(mk_node(0, NodeKind::DataParallel, 2048));
        graph.add_node(mk_node(1, NodeKind::DataParallel, 4096));
        graph.add_node(mk_node(2, NodeKind::Scalar, 8));
        let regions = KernelExtract.run(&graph);
        assert!(regions.is_empty());
        assert_eq!(KernelExtract::total_bytes(&regions), 0);
        assert!(KernelExtract::covered_nodes(&regions).is_empty());
    }

    // trust_ir#39 composed-predicate gate (Trust Codegen#428/#433). The caller-supplied
    // `gpu_eligible` closure stands in for `trust_ir::Function::is_gpu_eligible()`.
    #[test]
    fn gpu_gate_rejects_ineligible_function() {
        let mut graph = ComputeGraph::new();
        graph.add_node(mk_node(0, NodeKind::DataParallel, 4096));
        graph.add_node(mk_node(1, NodeKind::DataParallel, 4096));

        // Only node 1 is GPU-eligible per the trust_ir function predicate.
        let regions = KernelExtract.run_with_gpu_gate(&graph, |n| n.id.0 == 1);
        assert!(
            regions.is_empty(),
            "function-level labels cannot replace the sealed semantic recipe"
        );
    }

    #[test]
    fn gpu_gate_rejects_all_when_gate_false() {
        let mut graph = ComputeGraph::new();
        graph.add_node(mk_node(0, NodeKind::DataParallel, 4096));
        graph.add_node(mk_node(1, NodeKind::MatrixHeavy, 65536));

        let regions = KernelExtract.run_with_gpu_gate(&graph, |_| false);
        assert!(regions.is_empty(), "gate=false must prune every node");
    }

    #[test]
    fn gpu_gate_true_matches_bare_run() {
        let mut graph = ComputeGraph::new();
        graph.add_node(mk_node(0, NodeKind::DataParallel, 2048));
        graph.add_node(mk_node(1, NodeKind::MatrixHeavy, 65536));
        graph.add_node(mk_node(2, NodeKind::Scalar, 8));

        let bare = KernelExtract.run(&graph);
        let gated = KernelExtract.run_with_gpu_gate(&graph, |_| true);
        assert_eq!(
            bare.iter().map(|r| r.nodes.clone()).collect::<Vec<_>>(),
            gated.iter().map(|r| r.nodes.clone()).collect::<Vec<_>>(),
            "gate=true must match the bare run"
        );
    }
}
