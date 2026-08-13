// trust-cg-gpu/pipeline.rs - Orchestrates the six GPU passes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-gpu-passes-pipeline.md

//! The orchestrator that runs the six GPU passes in order and returns
//! a single bundle that carries everything downstream consumers
//! (dispatch-plan generation, MSL emission, test harnesses) need.

use thiserror::Error;
use trust_cg_lower::compute_graph::{ComputeGraph, ComputeNodeId, TargetRecommendation};
use trust_cg_lower::target_analysis::ComputeTarget;

use crate::address_space::AddressSpaceInfer;
use crate::divergence_flatten::{DivergenceFlatten, DivergenceStats};
use crate::hetero_partition::HeteroPartition;
use crate::kernel_extract::KernelExtract;
use crate::launch_synth::{LaunchSynth, LaunchSynthError, MetalLaunch};
use crate::memory_partition::{BufferPlan, MemoryPartition};
use crate::region::KernelRegion;

// ---------------------------------------------------------------------------
// GpuPipelineConfig
// ---------------------------------------------------------------------------

/// Per-pass opt-in toggles.
///
/// Each toggle defaults to `true`, matching the scaffolding's "run all
/// six passes" expectation. Depth experiments can disable individual
/// passes for A/B comparisons without rewiring the code.
#[derive(Debug, Clone)]
pub struct GpuPipelineConfig {
    pub kernel_extract: bool,
    pub address_space: bool,
    pub memory_partition: bool,
    pub divergence_flatten: bool,
    pub hetero_partition: bool,
    pub launch_synth: bool,
    /// Threadgroup size passed to [`LaunchSynth`].
    pub threadgroup_size: u32,
}

impl Default for GpuPipelineConfig {
    fn default() -> Self {
        Self {
            kernel_extract: true,
            address_space: true,
            memory_partition: true,
            divergence_flatten: true,
            hetero_partition: true,
            launch_synth: true,
            threadgroup_size: crate::launch_synth::DEFAULT_THREADGROUP_SIZE,
        }
    }
}

impl GpuPipelineConfig {
    /// A configuration with every pass disabled except KernelExtract.
    /// Useful for pure pattern-detection experiments.
    pub fn extract_only() -> Self {
        Self {
            kernel_extract: true,
            address_space: false,
            memory_partition: false,
            divergence_flatten: false,
            hetero_partition: false,
            launch_synth: false,
            threadgroup_size: crate::launch_synth::DEFAULT_THREADGROUP_SIZE,
        }
    }
}

// ---------------------------------------------------------------------------
// GpuPipelineOutput
// ---------------------------------------------------------------------------

/// What the pipeline produces.
#[derive(Debug, Clone)]
pub struct GpuPipelineOutput {
    /// All kernel regions extracted from the compute graph (annotated
    /// with address-space / buffer-plan / divergence metadata).
    pub regions: Vec<KernelRegion>,
    /// Flat buffer plan view (also attached per-region).
    pub buffer_plans: Vec<BufferPlan>,
    /// Per-region target recommendation (compatible with
    /// [`trust_cg_lower::dispatch::generate_dispatch_plan`]).
    pub recommendations: Vec<TargetRecommendation>,
    /// Metal launch descriptors for GPU-bound regions.
    pub launches: Vec<MetalLaunch>,
    /// Aggregated divergence stats.
    pub divergence_stats: DivergenceStats,
}

/// A pass required to turn a GPU recommendation into an exact launch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuPipelinePass {
    AddressSpaceInfer,
    MemoryPartition,
    LaunchSynth,
}

impl std::fmt::Display for GpuPipelinePass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AddressSpaceInfer => write!(f, "AddressSpaceInfer"),
            Self::MemoryPartition => write!(f, "MemoryPartition"),
            Self::LaunchSynth => write!(f, "LaunchSynth"),
        }
    }
}

impl GpuPipelineOutput {
    /// Whether any launch was synthesized.
    pub fn has_gpu_work(&self) -> bool {
        !self.launches.is_empty()
    }

    /// Number of extracted regions.
    pub fn region_count(&self) -> usize {
        self.regions.len()
    }
}

/// A fail-closed GPU pipeline orchestration error.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum GpuPipelineError {
    #[error(transparent)]
    LaunchSynthesis(#[from] LaunchSynthError),
    #[error("compute node {node_id} was recommended for GPU dispatch while {pass} was disabled")]
    GpuRecommendationRequiresPass {
        node_id: ComputeNodeId,
        pass: GpuPipelinePass,
    },
    #[error(
        "GPU recommendation/Metal launch cardinality mismatch: {gpu_recommendations} recommendations, {launches} launches"
    )]
    LaunchCardinalityMismatch {
        gpu_recommendations: usize,
        launches: usize,
    },
    #[error("GPU recommendation for compute node {node_id} has no exact one-to-one Metal launch")]
    GpuRecommendationLaunchMismatch { node_id: ComputeNodeId },
    #[error("Metal launch for {region_id} has no exact GPU recommendation")]
    LaunchWithoutGpuRecommendation { region_id: crate::region::RegionId },
}

// ---------------------------------------------------------------------------
// GpuPipeline
// ---------------------------------------------------------------------------

/// The six-pass GPU pipeline.
#[derive(Debug, Default, Clone)]
pub struct GpuPipeline {
    pub config: GpuPipelineConfig,
}

impl GpuPipeline {
    /// Construct with an explicit config.
    pub fn new(config: GpuPipelineConfig) -> Self {
        Self { config }
    }

    /// Run the pipeline over a [`ComputeGraph`].
    pub fn run(&self, graph: &ComputeGraph) -> Result<GpuPipelineOutput, GpuPipelineError> {
        // 1. KernelExtract.
        let mut regions = if self.config.kernel_extract {
            KernelExtract.run(graph)
        } else {
            Vec::new()
        };

        // 2. AddressSpaceInfer.
        if self.config.address_space {
            AddressSpaceInfer.run(&mut regions);
        }

        // 3. MemoryPartition.
        let buffer_plans = if self.config.memory_partition {
            MemoryPartition.run(&mut regions)
        } else {
            Vec::new()
        };

        // 4. DivergenceFlatten.
        let divergence_stats = if self.config.divergence_flatten {
            DivergenceFlatten.run(&mut regions)
        } else {
            DivergenceStats::default()
        };

        // 5. HeteroPartition.
        let mut recommendations = if self.config.hetero_partition {
            HeteroPartition.run(graph, &regions)
        } else {
            Vec::new()
        };

        // 6. LaunchSynth.
        let launches = self.synthesize_or_downgrade(&regions, &mut recommendations)?;

        validate_gpu_launch_bijection(&regions, &recommendations, &launches)?;

        Ok(GpuPipelineOutput {
            regions,
            buffer_plans,
            recommendations,
            launches,
            divergence_stats,
        })
    }

    fn synthesize_or_downgrade(
        &self,
        regions: &[KernelRegion],
        recommendations: &mut [TargetRecommendation],
    ) -> Result<Vec<MetalLaunch>, GpuPipelineError> {
        let Some(first_gpu) = recommendations
            .iter()
            .find(|recommendation| recommendation.recommended_target == ComputeTarget::Gpu)
        else {
            return Ok(Vec::new());
        };

        let disabled_pass = if !self.config.address_space {
            Some(GpuPipelinePass::AddressSpaceInfer)
        } else if !self.config.memory_partition {
            Some(GpuPipelinePass::MemoryPartition)
        } else if !self.config.launch_synth {
            Some(GpuPipelinePass::LaunchSynth)
        } else {
            None
        };
        if let Some(pass) = disabled_pass {
            let error = GpuPipelineError::GpuRecommendationRequiresPass {
                node_id: first_gpu.node_id,
                pass,
            };
            return downgrade_gpu_recommendations(recommendations, error);
        }

        let synthesis = LaunchSynth {
            threadgroup_size: self.config.threadgroup_size,
        }
        .run(regions, recommendations)
        .map_err(GpuPipelineError::from);
        match synthesis {
            Ok(launches) => Ok(launches),
            Err(error) => downgrade_gpu_recommendations(recommendations, error),
        }
    }
}

fn downgrade_gpu_recommendations(
    recommendations: &mut [TargetRecommendation],
    error: GpuPipelineError,
) -> Result<Vec<MetalLaunch>, GpuPipelineError> {
    let fallbacks = recommendations
        .iter()
        .enumerate()
        .filter(|(_, recommendation)| recommendation.recommended_target == ComputeTarget::Gpu)
        .map(|(index, recommendation)| {
            recommendation
                .legal_targets
                .contains(&ComputeTarget::CpuScalar)
                .then_some(ComputeTarget::CpuScalar)
                .or_else(|| {
                    recommendation
                        .legal_targets
                        .contains(&ComputeTarget::CpuSimd)
                        .then_some(ComputeTarget::CpuSimd)
                })
                .map(|target| (index, target))
        })
        .collect::<Option<Vec<_>>>();
    let Some(fallbacks) = fallbacks else {
        return Err(error);
    };

    let cause = error.to_string();
    for (index, target) in fallbacks {
        let recommendation = &mut recommendations[index];
        recommendation.recommended_target = target;
        recommendation
            .legal_targets
            .retain(|candidate| *candidate != ComputeTarget::Gpu);
        recommendation.reason =
            format!("atomic CPU fallback to {target}: exact GPU launch unavailable ({cause})");
    }
    Ok(Vec::new())
}

fn validate_gpu_launch_bijection(
    regions: &[KernelRegion],
    recommendations: &[TargetRecommendation],
    launches: &[MetalLaunch],
) -> Result<(), GpuPipelineError> {
    let gpu_recommendations = recommendations
        .iter()
        .filter(|recommendation| recommendation.recommended_target == ComputeTarget::Gpu)
        .collect::<Vec<_>>();
    if gpu_recommendations.len() != launches.len() {
        return Err(GpuPipelineError::LaunchCardinalityMismatch {
            gpu_recommendations: gpu_recommendations.len(),
            launches: launches.len(),
        });
    }

    for recommendation in gpu_recommendations {
        let mut matching_regions = regions
            .iter()
            .filter(|region| region.nodes.first().copied() == Some(recommendation.node_id));
        let Some(region) = matching_regions.next() else {
            return Err(GpuPipelineError::GpuRecommendationLaunchMismatch {
                node_id: recommendation.node_id,
            });
        };
        if matching_regions.next().is_some()
            || launches
                .iter()
                .filter(|launch| launch.region_id == region.id)
                .count()
                != 1
        {
            return Err(GpuPipelineError::GpuRecommendationLaunchMismatch {
                node_id: recommendation.node_id,
            });
        }
    }

    for launch in launches {
        let Some(region) = regions.iter().find(|region| region.id == launch.region_id) else {
            return Err(GpuPipelineError::LaunchWithoutGpuRecommendation {
                region_id: launch.region_id,
            });
        };
        let Some(node_id) = region.nodes.first().copied() else {
            return Err(GpuPipelineError::LaunchWithoutGpuRecommendation {
                region_id: launch.region_id,
            });
        };
        if recommendations
            .iter()
            .filter(|recommendation| {
                recommendation.node_id == node_id
                    && recommendation.recommended_target == ComputeTarget::Gpu
            })
            .count()
            != 1
        {
            return Err(GpuPipelineError::LaunchWithoutGpuRecommendation {
                region_id: launch.region_id,
            });
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use trust_cg_lower::compute_graph::{ComputeCost, ComputeNode, ComputeNodeId, NodeKind};

    use crate::kernel_extract::KernelPattern;
    use crate::region::{BufferId, RegionId};

    fn mk_graph() -> ComputeGraph {
        let mut costs = HashMap::new();
        costs.insert(
            ComputeTarget::CpuScalar,
            ComputeCost {
                latency_cycles: 100,
                throughput_ops_per_kcycle: 1000,
            },
        );
        costs.insert(
            ComputeTarget::Gpu,
            ComputeCost {
                latency_cycles: 20,
                throughput_ops_per_kcycle: 5000,
            },
        );
        let mut g = ComputeGraph::new();
        g.add_node(ComputeNode {
            id: ComputeNodeId(0),
            instructions: vec![],
            costs,
            legal_targets: vec![ComputeTarget::CpuScalar, ComputeTarget::Gpu],
            kind: NodeKind::DataParallel,
            data_size_bytes: 4096,
            produced_values: vec![],
            consumed_values: vec![],
            dominant_op: "ADD".to_string(),
            target_legality: None,
            matmul_shape: None,
        });
        g
    }

    fn mk_region(id: u32, node_id: u32) -> KernelRegion {
        KernelRegion::new(
            RegionId(id),
            format!("kernel_{id}"),
            vec![ComputeNodeId(node_id)],
            1024,
            4096,
            KernelPattern::ParallelMap,
            vec![BufferId(id * 2)],
            vec![BufferId(id * 2 + 1)],
        )
    }

    fn gpu_recommendation(
        node_id: u32,
        cpu_fallback: Option<ComputeTarget>,
    ) -> TargetRecommendation {
        let mut legal_targets = vec![ComputeTarget::Gpu];
        if let Some(cpu_fallback) = cpu_fallback {
            legal_targets.insert(0, cpu_fallback);
        }
        TargetRecommendation {
            node_id: ComputeNodeId(node_id),
            recommended_target: ComputeTarget::Gpu,
            legal_targets,
            reason: "test GPU recommendation".to_string(),
            parallel_reduction_legal: false,
        }
    }

    #[test]
    fn full_pipeline_rejects_manual_accelerator_metadata() {
        let graph = mk_graph();
        let out = GpuPipeline::default()
            .run(&graph)
            .expect("manual metadata has no accelerator region to reject atomically");
        assert_eq!(out.region_count(), 0);
        assert!(out.buffer_plans.is_empty());
        assert!(out.recommendations.is_empty());
        assert!(!out.has_gpu_work());
        assert!(out.launches.is_empty());
    }

    #[test]
    fn extract_only_config_skips_later_passes() {
        let graph = mk_graph();
        let out = GpuPipeline::new(GpuPipelineConfig::extract_only())
            .run(&graph)
            .expect("extract-only configuration has no dispatch recommendations");
        assert_eq!(out.region_count(), 0);
        assert!(out.buffer_plans.is_empty());
        assert!(out.recommendations.is_empty());
        assert!(out.launches.is_empty());
    }

    #[test]
    fn empty_graph_produces_empty_output() {
        let graph = ComputeGraph::new();
        let out = GpuPipeline::default()
            .run(&graph)
            .expect("empty pipeline input");
        assert!(out.regions.is_empty());
        assert!(out.buffer_plans.is_empty());
        assert!(out.recommendations.is_empty());
        assert!(out.launches.is_empty());
    }

    #[test]
    fn memory_partition_disabled_atomically_downgrades_legal_gpu_work() {
        let pipeline = GpuPipeline::new(GpuPipelineConfig {
            memory_partition: false,
            ..GpuPipelineConfig::default()
        });
        let mut recommendations = vec![gpu_recommendation(0, Some(ComputeTarget::CpuScalar))];
        let launches = pipeline
            .synthesize_or_downgrade(&[mk_region(0, 0)], &mut recommendations)
            .expect("legal CPU fallback makes the disabled pass atomic");

        assert!(launches.is_empty());
        assert_eq!(
            recommendations[0].recommended_target,
            ComputeTarget::CpuScalar
        );
        assert!(
            !recommendations[0]
                .legal_targets
                .contains(&ComputeTarget::Gpu)
        );
        assert!(recommendations[0].reason.contains("MemoryPartition"));
    }

    #[test]
    fn address_space_disabled_atomically_downgrades_legal_gpu_work() {
        let pipeline = GpuPipeline::new(GpuPipelineConfig {
            address_space: false,
            ..GpuPipelineConfig::default()
        });
        let mut recommendations = vec![gpu_recommendation(0, Some(ComputeTarget::CpuScalar))];
        let launches = pipeline
            .synthesize_or_downgrade(&[mk_region(0, 0)], &mut recommendations)
            .expect("legal CPU fallback makes the disabled pass atomic");

        assert!(launches.is_empty());
        assert_eq!(
            recommendations[0].recommended_target,
            ComputeTarget::CpuScalar
        );
        assert!(recommendations[0].reason.contains("AddressSpaceInfer"));
    }

    #[test]
    fn launch_synth_disabled_cannot_retain_gpu_recommendation() {
        let pipeline = GpuPipeline::new(GpuPipelineConfig {
            launch_synth: false,
            ..GpuPipelineConfig::default()
        });
        let mut recommendations = vec![gpu_recommendation(0, Some(ComputeTarget::CpuSimd))];
        let launches = pipeline
            .synthesize_or_downgrade(&[mk_region(0, 0)], &mut recommendations)
            .expect("legal SIMD fallback makes the disabled pass atomic");

        assert!(launches.is_empty());
        assert_eq!(
            recommendations[0].recommended_target,
            ComputeTarget::CpuSimd
        );
        assert!(recommendations[0].reason.contains("LaunchSynth"));
    }

    #[test]
    fn disabled_required_pass_is_error_for_gpu_only_recommendation() {
        let pipeline = GpuPipeline::new(GpuPipelineConfig {
            memory_partition: false,
            ..GpuPipelineConfig::default()
        });
        let mut recommendations = vec![gpu_recommendation(0, None)];

        assert!(matches!(
            pipeline.synthesize_or_downgrade(&[mk_region(0, 0)], &mut recommendations),
            Err(GpuPipelineError::GpuRecommendationRequiresPass {
                node_id: ComputeNodeId(0),
                pass: GpuPipelinePass::MemoryPartition,
            })
        ));
        assert_eq!(
            recommendations[0].recommended_target,
            ComputeTarget::Gpu,
            "an error must not partially rewrite the caller's recommendation set"
        );
    }

    #[test]
    fn fallback_is_all_or_nothing_across_gpu_batch() {
        let pipeline = GpuPipeline::new(GpuPipelineConfig {
            launch_synth: false,
            ..GpuPipelineConfig::default()
        });
        let mut recommendations = vec![
            gpu_recommendation(0, Some(ComputeTarget::CpuScalar)),
            gpu_recommendation(1, None),
        ];

        assert!(
            pipeline
                .synthesize_or_downgrade(&[mk_region(0, 0), mk_region(1, 1)], &mut recommendations,)
                .is_err()
        );
        assert!(
            recommendations
                .iter()
                .all(|recommendation| recommendation.recommended_target == ComputeTarget::Gpu)
        );
    }

    #[test]
    fn synthesis_error_atomically_downgrades_legal_gpu_work() {
        let pipeline = GpuPipeline::default();
        let mut region = mk_region(0, 0);
        AddressSpaceInfer.run(std::slice::from_mut(&mut region));
        MemoryPartition.run(std::slice::from_mut(&mut region));
        let mut recommendations = vec![gpu_recommendation(0, Some(ComputeTarget::CpuScalar))];

        let launches = pipeline
            .synthesize_or_downgrade(&[region], &mut recommendations)
            .expect("missing sealed recipe must downgrade the entire legal batch");
        assert!(launches.is_empty());
        assert_eq!(
            recommendations[0].recommended_target,
            ComputeTarget::CpuScalar
        );
        assert!(
            recommendations[0]
                .reason
                .contains("sealed Metal semantic recipe")
        );
    }

    #[test]
    fn synthesis_error_is_typed_for_gpu_only_recommendation() {
        let pipeline = GpuPipeline::default();
        let mut region = mk_region(0, 0);
        AddressSpaceInfer.run(std::slice::from_mut(&mut region));
        MemoryPartition.run(std::slice::from_mut(&mut region));
        let mut recommendations = vec![gpu_recommendation(0, None)];

        assert!(matches!(
            pipeline.synthesize_or_downgrade(&[region], &mut recommendations),
            Err(GpuPipelineError::LaunchSynthesis(
                LaunchSynthError::MissingSemanticRecipe {
                    region_id: RegionId(0)
                }
            ))
        ));
    }

    #[test]
    fn recommendation_region_identity_mismatch_is_typed_error() {
        let region = mk_region(0, 0);
        let recommendations = vec![gpu_recommendation(99, Some(ComputeTarget::CpuScalar))];

        assert!(matches!(
            LaunchSynth::default().run(&[region], &recommendations),
            Err(LaunchSynthError::RecommendationWithoutRegion {
                node_id: ComputeNodeId(99)
            })
        ));
    }

    #[test]
    fn successful_output_invariant_rejects_gpu_without_launch() {
        let recommendations = vec![gpu_recommendation(0, Some(ComputeTarget::CpuScalar))];
        assert!(matches!(
            validate_gpu_launch_bijection(&[mk_region(0, 0)], &recommendations, &[]),
            Err(GpuPipelineError::LaunchCardinalityMismatch {
                gpu_recommendations: 1,
                launches: 0,
            })
        ));
    }
}
