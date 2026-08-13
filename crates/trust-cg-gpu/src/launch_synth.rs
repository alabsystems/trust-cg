// trust-cg-gpu/launch_synth.rs - Synthesize Metal launch glue
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-gpu-passes-pipeline.md (Pass 6).

//! Pass 6: `LaunchSynth`.
//!
//! Produces Metal launch descriptors — grid/threadgroup dimensions plus
//! an ordered argument table — for every region that HeteroPartition
//! assigned to the GPU.

use std::collections::{HashMap, HashSet};
use std::fmt;

use thiserror::Error;
use trust_cg_codegen::metal_emitter::{MetalDispatchParams, MtlStorageMode};
use trust_cg_lower::compute_graph::{
    AcceleratorBackend, AcceleratorOperation, ComputeNodeId, TargetRecommendation, TrustIrValueId,
};
use trust_cg_lower::target_analysis::ComputeTarget;

use crate::address_space::AddressSpace;
use crate::memory_partition::{BufferPlan, BufferRole};
use crate::region::{BufferId, KernelRegion, RegionId};

/// Default threadgroup size (threads per group) for 1D kernels.
///
/// 256 is a common sweet spot on Apple Silicon and matches the existing
/// `DEFAULT_THREADGROUP_SIZE` used in `trust_cg_codegen::metal_emitter`
/// tests.
pub const DEFAULT_THREADGROUP_SIZE: u32 = 256;

/// A structural or authority failure that prevents an exact Metal launch.
///
/// Launch synthesis is an all-or-nothing operation. Returning an error means
/// that no launch from the input batch is authorized for dispatch.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum LaunchSynthError {
    #[error("Metal threadgroup size must be greater than zero")]
    InvalidThreadgroupSize,
    #[error("duplicate kernel region id {region_id}")]
    DuplicateRegionId { region_id: RegionId },
    #[error("kernel region {region_id} has no compute node")]
    EmptyRegion { region_id: RegionId },
    #[error("compute node {node_id} is the dispatch identity of multiple kernel regions")]
    DuplicateRegionNode { node_id: ComputeNodeId },
    #[error("compute node {node_id} has multiple target recommendations")]
    DuplicateRecommendation { node_id: ComputeNodeId },
    #[error("kernel region {region_id} for compute node {node_id} has no target recommendation")]
    MissingRecommendation {
        region_id: RegionId,
        node_id: ComputeNodeId,
    },
    #[error("target recommendation for compute node {node_id} has no kernel region")]
    RecommendationWithoutRegion { node_id: ComputeNodeId },
    #[error(
        "target recommendation for compute node {node_id} selects {target:?}, which is absent from its legal target set"
    )]
    IllegalRecommendation {
        node_id: ComputeNodeId,
        target: ComputeTarget,
    },
    #[error("GPU-recommended kernel region {region_id} has no sealed Metal semantic recipe")]
    MissingSemanticRecipe { region_id: RegionId },
    #[error("GPU-recommended kernel region {region_id} does not match its sealed recipe: {detail}")]
    RecipeMismatch {
        region_id: RegionId,
        detail: &'static str,
    },
    #[error("GPU-recommended kernel region {region_id} reuses buffer id {buffer}")]
    DuplicateBufferId {
        region_id: RegionId,
        buffer: BufferId,
    },
    #[error("GPU-recommended kernel region {region_id} has no {role} plan for buffer {buffer}")]
    MissingBufferPlan {
        region_id: RegionId,
        buffer: BufferId,
        role: BufferRole,
    },
    #[error(
        "GPU-recommended kernel region {region_id} has multiple {role} plans for buffer {buffer}"
    )]
    DuplicateBufferPlan {
        region_id: RegionId,
        buffer: BufferId,
        role: BufferRole,
    },
    #[error(
        "GPU-recommended kernel region {region_id} has an unexpected {role} plan for buffer {buffer}"
    )]
    UnexpectedBufferPlan {
        region_id: RegionId,
        buffer: BufferId,
        role: BufferRole,
    },
    #[error(
        "GPU-recommended kernel region {region_id} has an invalid {role} plan for buffer {buffer}: {detail}"
    )]
    BufferPlanMismatch {
        region_id: RegionId,
        buffer: BufferId,
        role: BufferRole,
        detail: &'static str,
    },
    #[error("kernel region {region_id} has too many Metal buffer bindings")]
    BindingIndexOverflow { region_id: RegionId },
}

// ---------------------------------------------------------------------------
// LaunchArgument
// ---------------------------------------------------------------------------

/// A single entry in a Metal argument table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaunchArgument {
    /// Binding slot index (0..N in order of appearance).
    pub binding: u32,
    /// Which buffer this argument carries.
    pub buffer: BufferId,
    /// Exact TrustIR SSA value carried by this buffer binding.
    pub value: TrustIrValueId,
    /// Metal storage mode for the buffer.
    pub storage: MtlStorageMode,
    /// Address space qualifier in the kernel signature.
    pub address_space: AddressSpace,
    /// Buffer role (input or output).
    pub role: BufferRole,
}

impl fmt::Display for LaunchArgument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "arg[{}] = {} ({} {}, {})",
            self.binding, self.buffer, self.address_space, self.role, self.storage
        )
    }
}

// ---------------------------------------------------------------------------
// MetalLaunch
// ---------------------------------------------------------------------------

/// Everything the host side needs to launch one Metal kernel.
#[derive(Debug, Clone)]
pub struct MetalLaunch {
    /// Region id this launch corresponds to.
    pub region_id: RegionId,
    /// Kernel function name (matches what the MSL emitter produces).
    pub kernel_name: String,
    /// Grid + threadgroup dimensions.
    pub dispatch: MetalDispatchParams,
    /// Ordered argument table.
    pub arguments: Vec<LaunchArgument>,
    /// Whether the dispatch requires a synchronize after it completes
    /// (derived from region consumer topology; populated by pipeline).
    pub requires_sync: bool,
}

impl MetalLaunch {
    /// Number of arguments.
    pub fn arg_count(&self) -> usize {
        self.arguments.len()
    }

    /// Iterate input-only arguments.
    pub fn inputs(&self) -> impl Iterator<Item = &LaunchArgument> {
        self.arguments
            .iter()
            .filter(|a| a.role == BufferRole::Input)
    }

    /// Iterate output-only arguments.
    pub fn outputs(&self) -> impl Iterator<Item = &LaunchArgument> {
        self.arguments
            .iter()
            .filter(|a| a.role == BufferRole::Output)
    }
}

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// Pass 6: launch glue synthesis.
#[derive(Debug, Clone)]
pub struct LaunchSynth {
    /// Threadgroup size used for 1D launches (defaults to
    /// [`DEFAULT_THREADGROUP_SIZE`]).
    pub threadgroup_size: u32,
}

impl Default for LaunchSynth {
    fn default() -> Self {
        Self {
            threadgroup_size: DEFAULT_THREADGROUP_SIZE,
        }
    }
}

impl LaunchSynth {
    /// Build a launch descriptor per GPU-bound region.
    ///
    /// Regions recommended for CPU (by [`crate::HeteroPartition`]) are
    /// skipped — the caller continues to run them via the existing
    /// dispatch plan's CPU fallback. Every region and recommendation must
    /// still participate in a one-to-one identity mapping. If any GPU region
    /// cannot produce its exact launch, the entire batch fails.
    pub fn run(
        &self,
        regions: &[KernelRegion],
        recommendations: &[TargetRecommendation],
    ) -> Result<Vec<MetalLaunch>, LaunchSynthError> {
        if self.threadgroup_size == 0 {
            return Err(LaunchSynthError::InvalidThreadgroupSize);
        }

        let mut seen_region_ids = HashSet::with_capacity(regions.len());
        let mut regions_by_node = HashMap::with_capacity(regions.len());
        for region in regions {
            if !seen_region_ids.insert(region.id) {
                return Err(LaunchSynthError::DuplicateRegionId {
                    region_id: region.id,
                });
            }
            let Some(node_id) = region.nodes.first().copied() else {
                return Err(LaunchSynthError::EmptyRegion {
                    region_id: region.id,
                });
            };
            if regions_by_node.insert(node_id, region).is_some() {
                return Err(LaunchSynthError::DuplicateRegionNode { node_id });
            }
        }

        let mut recommendations_by_node = HashMap::with_capacity(recommendations.len());
        for recommendation in recommendations {
            if recommendations_by_node
                .insert(recommendation.node_id, recommendation)
                .is_some()
            {
                return Err(LaunchSynthError::DuplicateRecommendation {
                    node_id: recommendation.node_id,
                });
            }
            if !regions_by_node.contains_key(&recommendation.node_id) {
                return Err(LaunchSynthError::RecommendationWithoutRegion {
                    node_id: recommendation.node_id,
                });
            }
            if !recommendation
                .legal_targets
                .contains(&recommendation.recommended_target)
            {
                return Err(LaunchSynthError::IllegalRecommendation {
                    node_id: recommendation.node_id,
                    target: recommendation.recommended_target,
                });
            }
        }

        let mut launches = Vec::new();
        for region in regions {
            let node_id = region.nodes[0];
            let rec = recommendations_by_node.get(&node_id).copied().ok_or(
                LaunchSynthError::MissingRecommendation {
                    region_id: region.id,
                    node_id,
                },
            )?;
            if rec.recommended_target != ComputeTarget::Gpu {
                continue;
            }

            let recipe =
                region
                    .semantic_recipe()
                    .ok_or(LaunchSynthError::MissingSemanticRecipe {
                        region_id: region.id,
                    })?;
            if recipe.backend() != AcceleratorBackend::Metal {
                return Err(recipe_mismatch(region, "recipe backend is not Metal"));
            }
            if region.nodes.as_slice() != [recipe.node_id()] || recipe.node_id() != rec.node_id {
                return Err(recipe_mismatch(
                    region,
                    "recipe, region, and recommendation node identities differ",
                ));
            }
            if region.data_size_bytes != recipe.data_size_bytes() {
                return Err(recipe_mismatch(
                    region,
                    "region byte size differs from the sealed recipe",
                ));
            }
            let (input_values, output_values, element_count) = match recipe.operation() {
                AcceleratorOperation::ElementwiseBinary {
                    lhs,
                    rhs,
                    result,
                    element_count,
                    ..
                } => (vec![*lhs, *rhs], vec![*result], *element_count),
            };
            if region.pattern != crate::kernel_extract::KernelPattern::ParallelMap {
                return Err(recipe_mismatch(region, "unsupported kernel pattern"));
            }
            if region.element_count != element_count {
                return Err(recipe_mismatch(
                    region,
                    "element count differs from the sealed recipe",
                ));
            }
            if region.input_values != input_values || region.output_values != output_values {
                return Err(recipe_mismatch(
                    region,
                    "TrustIR value bindings differ from the sealed recipe",
                ));
            }
            if region.input_buffers.len() != input_values.len()
                || region.output_buffers.len() != output_values.len()
            {
                return Err(recipe_mismatch(
                    region,
                    "buffer arity differs from the sealed operation",
                ));
            }

            let mut seen_buffers = HashSet::with_capacity(region.buffer_count());
            for buffer in region
                .input_buffers
                .iter()
                .chain(region.output_buffers.iter())
                .copied()
            {
                if !seen_buffers.insert(buffer) {
                    return Err(LaunchSynthError::DuplicateBufferId {
                        region_id: region.id,
                        buffer,
                    });
                }
            }
            if region.address_space.len() != seen_buffers.len() {
                return Err(recipe_mismatch(
                    region,
                    "address-space annotation cardinality differs from buffer cardinality",
                ));
            }

            // Grid = element_count rounded up to threadgroup size. We
            // reuse the existing metal_emitter helper so grid math is
            // identical between host and kernel.
            let dispatch = MetalDispatchParams::for_1d(region.element_count, self.threadgroup_size);

            let mut arguments = Vec::with_capacity(region.buffer_count());
            for (buf, value) in region
                .input_buffers
                .iter()
                .copied()
                .zip(input_values.iter().copied())
            {
                let plan = find_unique_plan(region, buf, BufferRole::Input)?;
                validate_buffer_plan(region, plan, BufferRole::Input)?;
                let binding = u32::try_from(arguments.len()).map_err(|_| {
                    LaunchSynthError::BindingIndexOverflow {
                        region_id: region.id,
                    }
                })?;
                arguments.push(LaunchArgument {
                    binding,
                    buffer: buf,
                    value,
                    storage: plan.storage,
                    address_space: plan.address_space,
                    role: BufferRole::Input,
                });
            }
            for (buf, value) in region
                .output_buffers
                .iter()
                .copied()
                .zip(output_values.iter().copied())
            {
                let plan = find_unique_plan(region, buf, BufferRole::Output)?;
                validate_buffer_plan(region, plan, BufferRole::Output)?;
                let binding = u32::try_from(arguments.len()).map_err(|_| {
                    LaunchSynthError::BindingIndexOverflow {
                        region_id: region.id,
                    }
                })?;
                arguments.push(LaunchArgument {
                    binding,
                    buffer: buf,
                    value,
                    storage: plan.storage,
                    address_space: plan.address_space,
                    role: BufferRole::Output,
                });
            }

            for plan in &region.buffer_plans {
                let expected = match plan.role {
                    BufferRole::Input => region.input_buffers.contains(&plan.id),
                    BufferRole::Output => region.output_buffers.contains(&plan.id),
                };
                if !expected {
                    return Err(LaunchSynthError::UnexpectedBufferPlan {
                        region_id: region.id,
                        buffer: plan.id,
                        role: plan.role,
                    });
                }
            }

            launches.push(MetalLaunch {
                region_id: region.id,
                kernel_name: format!("trust_cg_map2_{}", recipe.node_id()),
                dispatch,
                arguments,
                // Scaffolding marks every GPU launch as requiring a sync
                // before its results are visible on the CPU. A depth pass
                // can elide this when consumers are also on the GPU.
                requires_sync: true,
            });
        }
        Ok(launches)
    }
}

fn recipe_mismatch(region: &KernelRegion, detail: &'static str) -> LaunchSynthError {
    LaunchSynthError::RecipeMismatch {
        region_id: region.id,
        detail,
    }
}

fn find_unique_plan(
    region: &KernelRegion,
    buf: BufferId,
    role: BufferRole,
) -> Result<&BufferPlan, LaunchSynthError> {
    let mut plans = region
        .buffer_plans
        .iter()
        .filter(|plan| plan.id == buf && plan.role == role);
    let plan = plans.next().ok_or(LaunchSynthError::MissingBufferPlan {
        region_id: region.id,
        buffer: buf,
        role,
    })?;
    if plans.next().is_some() {
        return Err(LaunchSynthError::DuplicateBufferPlan {
            region_id: region.id,
            buffer: buf,
            role,
        });
    }
    Ok(plan)
}

fn validate_buffer_plan(
    region: &KernelRegion,
    plan: &BufferPlan,
    role: BufferRole,
) -> Result<(), LaunchSynthError> {
    let mismatch = |detail| LaunchSynthError::BufferPlanMismatch {
        region_id: region.id,
        buffer: plan.id,
        role,
        detail,
    };
    if region.address_space.get(plan.id) != Some(plan.address_space) {
        return Err(mismatch(
            "plan address space differs from the address-space pass",
        ));
    }
    if plan.address_space != AddressSpace::Device {
        return Err(mismatch(
            "current exact Metal emitter supports only device buffer arguments",
        ));
    }
    if plan.storage == MtlStorageMode::Memoryless {
        return Err(mismatch(
            "memoryless storage is render-only and invalid for Metal compute buffers",
        ));
    }
    let expected_size = region.data_size_bytes
        / u64::try_from(region.buffer_count()).map_err(|_| mismatch("buffer count overflow"))?;
    if plan.size_bytes != expected_size {
        return Err(mismatch(
            "allocation size differs from the memory-partition result",
        ));
    }
    match role {
        BufferRole::Input => {
            if plan
                .consumer_regions
                .iter()
                .filter(|candidate| **candidate == region.id)
                .count()
                != 1
            {
                return Err(mismatch(
                    "input plan does not name this region exactly once as a consumer",
                ));
            }
        }
        BufferRole::Output => {
            if plan.producer_region != Some(region.id) {
                return Err(mismatch("output plan is not produced by this region"));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::address_space::AddressSpaceInfer;
    use crate::kernel_extract::KernelPattern;
    use crate::memory_partition::MemoryPartition;
    use crate::region::RegionId;
    use trust_cg_lower::compute_graph::ComputeNodeId;
    use trust_ir::ValueId;

    fn mk_region() -> KernelRegion {
        KernelRegion::new(
            RegionId(0),
            "kernel_0".into(),
            vec![ComputeNodeId(0)],
            1024,
            4096,
            KernelPattern::ParallelMap,
            vec![BufferId(0)],
            vec![BufferId(1)],
        )
    }

    #[test]
    fn gpu_recommendation_without_sealed_region_is_typed_error() {
        let mut regions = vec![mk_region()];
        AddressSpaceInfer.run(&mut regions);
        MemoryPartition.run(&mut regions);

        let recs = vec![TargetRecommendation {
            node_id: ComputeNodeId(0),
            recommended_target: ComputeTarget::Gpu,
            legal_targets: vec![ComputeTarget::CpuScalar, ComputeTarget::Gpu],
            reason: "test".to_string(),
            parallel_reduction_legal: true,
        }];

        assert!(matches!(
            LaunchSynth::default().run(&regions, &recs),
            Err(LaunchSynthError::MissingSemanticRecipe {
                region_id: RegionId(0)
            })
        ));
    }

    #[test]
    fn cpu_recommendation_produces_no_launch() {
        let mut regions = vec![mk_region()];
        AddressSpaceInfer.run(&mut regions);
        MemoryPartition.run(&mut regions);
        let recs = vec![TargetRecommendation {
            node_id: ComputeNodeId(0),
            recommended_target: ComputeTarget::CpuScalar,
            legal_targets: vec![ComputeTarget::CpuScalar],
            reason: "test".to_string(),
            parallel_reduction_legal: false,
        }];
        let launches = LaunchSynth::default()
            .run(&regions, &recs)
            .expect("CPU-only recommendation needs no Metal launch");
        assert!(launches.is_empty());
    }

    #[test]
    fn public_buffer_vectors_cannot_mint_launch_arguments() {
        let mut regions = vec![KernelRegion::new(
            RegionId(0),
            "kernel_0".into(),
            vec![ComputeNodeId(0)],
            1024,
            4096,
            KernelPattern::ParallelMap,
            vec![BufferId(0), BufferId(1)],
            vec![BufferId(2)],
        )];
        AddressSpaceInfer.run(&mut regions);
        MemoryPartition.run(&mut regions);
        let recs = vec![TargetRecommendation {
            node_id: ComputeNodeId(0),
            recommended_target: ComputeTarget::Gpu,
            legal_targets: vec![ComputeTarget::Gpu],
            reason: "test".to_string(),
            parallel_reduction_legal: true,
        }];
        assert!(matches!(
            LaunchSynth::default().run(&regions, &recs),
            Err(LaunchSynthError::MissingSemanticRecipe {
                region_id: RegionId(0)
            })
        ));
    }

    #[test]
    fn zero_threadgroup_size_is_rejected_before_dispatch_math() {
        assert!(matches!(
            LaunchSynth {
                threadgroup_size: 0
            }
            .run(&[], &[]),
            Err(LaunchSynthError::InvalidThreadgroupSize)
        ));
    }

    #[test]
    fn missing_memory_partition_plan_is_typed_error() {
        let region = mk_region();
        assert!(matches!(
            find_unique_plan(&region, BufferId(0), BufferRole::Input),
            Err(LaunchSynthError::MissingBufferPlan {
                region_id: RegionId(0),
                buffer: BufferId(0),
                role: BufferRole::Input,
            })
        ));
    }

    #[test]
    fn duplicate_memory_partition_plan_is_typed_error() {
        let mut regions = vec![mk_region()];
        AddressSpaceInfer.run(&mut regions);
        MemoryPartition.run(&mut regions);
        let duplicate = regions[0].buffer_plans[0].clone();
        regions[0].buffer_plans.push(duplicate);

        assert!(matches!(
            find_unique_plan(&regions[0], BufferId(0), BufferRole::Input),
            Err(LaunchSynthError::DuplicateBufferPlan {
                region_id: RegionId(0),
                buffer: BufferId(0),
                role: BufferRole::Input,
            })
        ));
    }

    #[test]
    fn memory_plan_without_address_space_pass_is_rejected() {
        let mut regions = vec![mk_region()];
        MemoryPartition.run(&mut regions);
        let plan = find_unique_plan(&regions[0], BufferId(0), BufferRole::Input)
            .expect("memory pass created an input plan");

        assert!(matches!(
            validate_buffer_plan(&regions[0], plan, BufferRole::Input),
            Err(LaunchSynthError::BufferPlanMismatch {
                region_id: RegionId(0),
                buffer: BufferId(0),
                role: BufferRole::Input,
                ..
            })
        ));
    }

    #[test]
    fn memoryless_compute_buffer_plan_is_rejected() {
        let mut regions = vec![mk_region()];
        AddressSpaceInfer.run(&mut regions);
        MemoryPartition.run(&mut regions);
        regions[0].buffer_plans[0].storage = MtlStorageMode::Memoryless;
        let plan = &regions[0].buffer_plans[0];

        assert!(matches!(
            validate_buffer_plan(&regions[0], plan, BufferRole::Input),
            Err(LaunchSynthError::BufferPlanMismatch {
                region_id: RegionId(0),
                buffer: BufferId(0),
                role: BufferRole::Input,
                ..
            })
        ));
    }

    #[test]
    fn launch_arguments_preserve_function_scope_for_reused_local_values() {
        let argument = |func_idx| LaunchArgument {
            binding: 0,
            buffer: BufferId(func_idx),
            value: TrustIrValueId::new(func_idx, ValueId::new(7)),
            storage: MtlStorageMode::Shared,
            address_space: AddressSpace::Device,
            role: BufferRole::Input,
        };
        let first = argument(0);
        let second = argument(1);

        assert_ne!(first.value, second.value);
        assert_ne!(first.value.stable_key(), second.value.stable_key());
    }
}
