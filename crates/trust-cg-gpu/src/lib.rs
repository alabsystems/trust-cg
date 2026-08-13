// trust-cg-gpu - GPU passes (Metal first)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-gpu-passes-pipeline.md
// Issue: alabsystems/trust-cg#394 (Part of #390, ty supremacy blocker 5)

//! GPU pass pipeline for Trust Codegen (Metal first).
//!
//! This crate implements six structural passes that sit between the
//! existing [`trust_cg_lower::compute_graph`] heterogeneous compute analysis
//! and the existing [`trust_cg_codegen::metal_emitter`] MSL emitter:
//!
//! 1. [`kernel_extract::KernelExtract`] — identify parallel regions and
//!    extract them as self-contained kernels.
//! 2. [`address_space::AddressSpaceInfer`] — tag buffers with MSL
//!    address spaces (`device`, `threadgroup`, `constant`, `thread`).
//! 3. [`memory_partition::MemoryPartition`] — split host/device/shared
//!    allocations and pick Metal storage modes.
//! 4. [`divergence_flatten::DivergenceFlatten`] — flatten warp-divergent
//!    control flow into predicated arithmetic.
//! 5. [`hetero_partition::HeteroPartition`] — pick CPU vs GPU per region
//!    using the cost-model profitability analyzer.
//! 6. [`launch_synth::LaunchSynth`] — synthesize Metal launch glue
//!    (grid/threadgroup dims, argument tables, storage modes).
//!
//! The passes run in the order above. Each is idempotent. Each is opt-in via
//! [`GpuPipelineConfig`] toggles.
//!
//! Note on wiring: nothing in the workspace depends on this crate yet, so the
//! passes run only when driven directly rather than as part of the main
//! optimization pipeline.
//!
//! See [`pipeline::GpuPipeline`] for the orchestrator and
//! [`sample_bfs`] for the end-to-end BFS-style parallel_map sample that
//! wires KernelExtract -> LaunchSynth -> MSL emission.

pub mod address_space;
pub mod divergence_flatten;
pub mod fusion_bench;
pub mod hetero_partition;
pub mod kernel_extract;
pub mod launch_synth;
pub mod memory_partition;
pub mod metal_runtime;
pub mod pipeline;
pub mod region;
pub mod sample_bfs;

pub use address_space::{AddressSpace, AddressSpaceInfer, AddressSpaceMap};
pub use divergence_flatten::{DivergenceFlatten, DivergenceStats};
pub use fusion_bench::{
    AttentionBenchRecord, AttentionBenchShape, AttentionBenchTimings, AttentionInput,
    AttentionReferenceError, BatchNormReluInput, BenchCorrectness, BenchDevice, BenchResult,
    BenchStatus, FusionBenchRecord, FusionBenchShape, FusionBenchTimings,
    GPU_FUSION_BENCH_SCHEMA_VERSION, GPU_FUSION_SPEEDUP_BAR, attention_records_to_jsonl,
    cpu_batch_norm_relu_f32_nchw, cpu_fused_attention_f32_nld, cpu_naive_attention_f32_nld,
    records_to_jsonl,
};
pub use hetero_partition::HeteroPartition;
pub use kernel_extract::{KernelExtract, KernelPattern};
pub use launch_synth::{LaunchArgument, LaunchSynth, LaunchSynthError, MetalLaunch};
pub use memory_partition::{BufferPlan, MemoryPartition};
pub use metal_runtime::{
    MetalAttentionBenchmarkConfig, MetalAttentionBenchmarkEvidence, MetalAttentionBenchmarkOutcome,
    MetalBatchNormReluBenchmarkConfig, MetalBatchNormReluBenchmarkEvidence,
    MetalBatchNormReluBenchmarkOutcome, MetalBatchNormReluKernel, MetalBufferBinding,
    MetalBufferRole, MetalCompileOutcome, MetalCompileReport, MetalCompileRequest,
    MetalCompiledLibrary, MetalF32Buffer, MetalF32KernelRunOutcome, MetalF32KernelRunReport,
    MetalF32KernelSequenceInvocation, MetalFusedAttentionKernel, MetalKernelDispatch,
    MetalKernelInvocation, MetalLaunchOutcome, MetalLibraryCompileOutcome, MetalRuntimeConfig,
    MetalRuntimeHarness, MetalRuntimeUnavailable, MetalToolchain,
};
pub use pipeline::{
    GpuPipeline, GpuPipelineConfig, GpuPipelineError, GpuPipelineOutput, GpuPipelinePass,
};
pub use region::{BufferId, KernelRegion, RegionId};
pub use sample_bfs::{SampleBfsSpec, emit_msl_for_region, run_sample_bfs, run_sample_map2};
