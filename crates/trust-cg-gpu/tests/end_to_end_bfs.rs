// trust-cg-gpu/tests/end_to_end_bfs.rs - End-to-end BFS-style parallel_map test
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-gpu-passes-pipeline.md
// Issue: alabsystems/trust-cg#394

use trust_cg_gpu::sample_bfs::{SampleBfsSpec, count_gpu_launches, run_sample_bfs, validate};

#[test]
fn synthetic_bfs_metadata_cannot_mint_gpu_pipeline_authority() {
    let result = run_sample_bfs(SampleBfsSpec::default()).expect("sample pipeline");
    assert_eq!(result.pipeline.region_count(), 0);
    assert!(result.pipeline.buffer_plans.is_empty());
    assert!(result.pipeline.recommendations.is_empty());
    assert!(result.pipeline.launches.is_empty());
    assert!(result.msl_source.is_empty());
}

#[test]
fn synthetic_bfs_dispatch_is_cpu_only_and_validates() {
    let result = run_sample_bfs(SampleBfsSpec::default()).expect("sample pipeline");
    assert_eq!(count_gpu_launches(&result.dispatch), 0);
    validate(&result.graph, &result.dispatch).expect("plan validates");
}
