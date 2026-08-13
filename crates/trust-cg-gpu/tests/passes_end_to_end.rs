// trust-cg-gpu/tests/passes_end_to_end.rs - GPU pass authority integration
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_gpu::sample_bfs::{SampleBfsSpec, count_gpu_launches, run_sample_map2, validate};
use trust_cg_gpu::{GpuPipeline, GpuPipelineConfig};

#[test]
fn synthetic_map2_labels_do_not_create_regions_launches_or_msl() {
    let result = run_sample_map2(SampleBfsSpec::default()).expect("sample pipeline");

    assert_eq!(result.pipeline.region_count(), 0);
    assert!(result.pipeline.buffer_plans.is_empty());
    assert!(result.pipeline.recommendations.is_empty());
    assert!(result.pipeline.launches.is_empty());
    assert!(result.msl_source.is_empty());
    assert_eq!(count_gpu_launches(&result.dispatch), 0);
    validate(&result.graph, &result.dispatch).expect("CPU fallback dispatch validates");
}

#[test]
fn disabled_recommendation_and_launch_passes_emit_no_dispatch_authority() {
    let sample = run_sample_map2(SampleBfsSpec::default()).expect("sample pipeline");
    let pipeline = GpuPipeline::new(GpuPipelineConfig {
        kernel_extract: true,
        address_space: true,
        memory_partition: true,
        divergence_flatten: false,
        hetero_partition: false,
        launch_synth: false,
        threadgroup_size: 256,
    });
    let output = pipeline
        .run(&sample.graph)
        .expect("no recommendation means no launch authority");

    assert!(output.regions.is_empty());
    assert!(output.buffer_plans.is_empty());
    assert!(output.recommendations.is_empty());
    assert!(output.launches.is_empty());
}

#[test]
fn extract_only_configuration_remains_cpu_only() {
    let sample = run_sample_map2(SampleBfsSpec::default()).expect("sample pipeline");
    let output = GpuPipeline::new(GpuPipelineConfig::extract_only())
        .run(&sample.graph)
        .expect("extract-only configuration");

    assert!(output.regions.is_empty());
    assert!(output.recommendations.is_empty());
    assert!(output.launches.is_empty());
}
