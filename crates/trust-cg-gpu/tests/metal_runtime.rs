// trust-cg-gpu/tests/metal_runtime.rs - Metal harness and JSONL schema tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Issue: alabsystems/trust-cg#561

use std::path::PathBuf;

use serde_json::{Value, json};
use trust_cg_codegen::metal_emitter::{
    VnnBatchNormReluOptions, VnnFusedAttentionOptions, emit_vnn_batch_norm_relu_msl,
    emit_vnn_fused_attention_msl,
};
use trust_cg_gpu::{
    AttentionBenchRecord, AttentionBenchShape, AttentionInput, BatchNormReluInput, BenchDevice,
    BenchResult, BenchStatus, FusionBenchRecord, FusionBenchShape, GPU_FUSION_BENCH_SCHEMA_VERSION,
    MetalAttentionBenchmarkConfig, MetalAttentionBenchmarkOutcome,
    MetalBatchNormReluBenchmarkConfig, MetalBatchNormReluBenchmarkOutcome,
    MetalBatchNormReluKernel, MetalBufferBinding, MetalBufferRole, MetalCompileOutcome,
    MetalCompileRequest, MetalFusedAttentionKernel, MetalKernelInvocation, MetalLaunchOutcome,
    MetalRuntimeConfig, MetalRuntimeHarness, attention_records_to_jsonl,
    cpu_batch_norm_relu_f32_nchw, cpu_fused_attention_f32_nld, cpu_naive_attention_f32_nld,
    records_to_jsonl,
};

const SIMPLE_MSL: &str = r#"
#include <metal_stdlib>
using namespace metal;

kernel void trust_cg_copy(
    const device float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    uint tid [[thread_position_in_grid]]
) {
    if (tid >= 4u) return;
    output[tid] = input[tid];
}
"#;

#[test]
fn missing_xcrun_is_typed_environmental_unavailable() {
    let harness = MetalRuntimeHarness::new(MetalRuntimeConfig {
        xcrun_path: PathBuf::from("/definitely/not/a/real/xcrun"),
        sdk: "macosx".to_string(),
        temp_dir: std::env::temp_dir(),
    });

    let outcome = harness.compile_msl(&MetalCompileRequest {
        kernel_name: "trust_cg_copy".to_string(),
        source: SIMPLE_MSL.to_string(),
    });

    match outcome {
        MetalCompileOutcome::Unavailable { unavailable } => {
            assert_eq!(unavailable.phase, "detect_toolchain");
            assert_eq!(unavailable.reason, "tool_unavailable");
            assert_eq!(unavailable.tool.as_deref(), Some("xcrun"));
        }
        other => panic!("expected typed unavailable result, got {other:?}"),
    }
}

#[test]
fn compile_msl_compiles_when_platform_toolchain_exists_or_reports_unavailable() {
    let harness = MetalRuntimeHarness::default();
    let kernel_name = "trust_cg_copy".to_string();
    let outcome = harness.compile_msl(&MetalCompileRequest {
        kernel_name: kernel_name.clone(),
        source: SIMPLE_MSL.to_string(),
    });

    match outcome {
        MetalCompileOutcome::Compiled { report } => {
            assert_eq!(report.kernel_name, kernel_name);
            assert_eq!(report.source_bytes, SIMPLE_MSL.len());
            assert!(report.air_bytes > 0);
            assert!(report.metallib_bytes > 0);
            assert!(report.cold_compile_us > 0);
            assert!(!report.toolchain.metal_path.is_empty());
            assert!(!report.toolchain.metallib_path.is_empty());
        }
        MetalCompileOutcome::Unavailable { unavailable } => {
            assert_eq!(unavailable.phase, "detect_toolchain");
            assert_eq!(unavailable.reason, "tool_unavailable");
        }
        MetalCompileOutcome::Failed { error } => {
            panic!("platform Metal compile failed unexpectedly: {error:?}");
        }
    }
}

fn valid_invocation() -> MetalKernelInvocation {
    MetalKernelInvocation {
        kernel_name: "batch_norm_relu_f32_nchw".to_string(),
        grid_size: [1024, 1, 1],
        threadgroup_size: [256, 1, 1],
        buffers: vec![
            MetalBufferBinding {
                binding: 0,
                byte_len: 4096,
                role: MetalBufferRole::Input,
            },
            MetalBufferBinding {
                binding: 1,
                byte_len: 4096,
                role: MetalBufferRole::Output,
            },
        ],
        synchronize: true,
    }
}

#[test]
fn host_runtime_probe_reports_runtime_separately_from_compiler_tools() {
    let harness = MetalRuntimeHarness::default();
    match harness.detect_host_runtime() {
        Ok(report) => {
            assert_eq!(report.api, "Metal.framework");
            assert!(report.default_device_available);
            assert!(report.command_queue_available);
        }
        Err(unavailable) => {
            assert_eq!(unavailable.phase, "detect_host_runtime");
            assert!(matches!(
                unavailable.reason.as_str(),
                "unsupported_os"
                    | "default_device_unavailable"
                    | "command_queue_unavailable"
                    | "objc_selector_unavailable"
            ));
        }
    }
}

#[test]
fn launch_descriptor_probes_host_runtime_then_reports_missing_library_layer() {
    let harness = MetalRuntimeHarness::default();
    let runtime_probe = harness.detect_host_runtime();
    let outcome = harness.launch(&valid_invocation());

    match (runtime_probe, outcome) {
        (Ok(_), MetalLaunchOutcome::Unavailable { unavailable }) => {
            assert_eq!(unavailable.phase, "load_kernel_library");
            assert_eq!(unavailable.reason, "compiled_kernel_library_missing");
            assert_ne!(unavailable.reason, "host_metal_runtime_unimplemented");
        }
        (Err(runtime_unavailable), MetalLaunchOutcome::Unavailable { unavailable }) => {
            assert_eq!(unavailable.phase, runtime_unavailable.phase);
            assert_eq!(unavailable.reason, runtime_unavailable.reason);
        }
        (_, other) => panic!("expected typed unavailable result, got {other:?}"),
    }
}

#[test]
fn launch_descriptor_validation_fails_before_runtime_probe() {
    let harness = MetalRuntimeHarness::default();
    let mut invocation = valid_invocation();
    invocation.grid_size = [0, 1, 1];
    match harness.launch(&invocation) {
        MetalLaunchOutcome::Failed { error } => {
            assert_eq!(error.phase, "launch_kernel");
            assert_eq!(error.reason, "invalid_grid_size");
        }
        other => panic!("expected invalid grid failure, got {other:?}"),
    }

    let mut invocation = valid_invocation();
    invocation.buffers.push(MetalBufferBinding {
        binding: 1,
        byte_len: 1024,
        role: MetalBufferRole::Constant,
    });
    match harness.launch(&invocation) {
        MetalLaunchOutcome::Failed { error } => {
            assert_eq!(error.phase, "launch_kernel");
            assert_eq!(error.reason, "duplicate_buffer_binding");
        }
        other => panic!("expected duplicate binding failure, got {other:?}"),
    }
}

#[test]
fn launch_descriptor_with_missing_buffers_is_typed_failure() {
    let harness = MetalRuntimeHarness::default();
    let mut invocation = valid_invocation();
    invocation.buffers.clear();

    match harness.launch(&invocation) {
        MetalLaunchOutcome::Unavailable { unavailable } => {
            panic!("expected validation failure, got unavailable result {unavailable:?}");
        }
        MetalLaunchOutcome::Failed { error } => {
            assert_eq!(error.phase, "launch_kernel");
            assert_eq!(error.reason, "missing_buffers");
        }
        other => panic!("expected missing buffer failure, got {other:?}"),
    }
}

#[test]
fn benchmark_jsonl_record_has_480_schema_and_null_timings_when_environmental() {
    let shape = FusionBenchShape {
        n: 1,
        c: 2,
        h: 2,
        w: 2,
    };
    let record = FusionBenchRecord::environmental_bn_relu(
        "bn_relu_n1_c2_h2_w2_f32",
        "metal-runtime",
        BenchDevice::metal_unknown("test-commit"),
        shape,
        20,
        100,
        BenchResult::environmental(
            "detect_toolchain",
            "tool_unavailable",
            "xcrun was not available",
        ),
    );
    let jsonl = records_to_jsonl(&[record]).expect("serialize JSONL");
    assert!(jsonl.ends_with('\n'));

    let value: Value = serde_json::from_str(jsonl.trim()).expect("valid JSON object");
    assert_eq!(value["schema_version"], GPU_FUSION_BENCH_SCHEMA_VERSION);
    assert_eq!(value["issue"], 480);
    assert_eq!(value["fusion"], "batch_norm_relu");
    assert_eq!(value["backend"], "metal-runtime");
    assert_eq!(value["baseline"], "naive_gpu_two_kernel");
    assert_eq!(value["warmup_iters"], 20);
    assert_eq!(value["measure_iters"], 100);
    assert!(value["cold_compile_us"].is_null());
    assert!(value["baseline_cold_compile_us"].is_null());
    assert!(value["median_us"].is_null());
    assert!(value["p95_us"].is_null());
    assert!(value["baseline_median_us"].is_null());
    assert!(value["baseline_p95_us"].is_null());
    assert!(value["speedup_vs_baseline"].is_null());
    assert_eq!(value["speedup_bar"], 5.0);
    assert!(value["speedup_bar_met"].is_null());
    assert_eq!(value["correctness"], "unavailable");
    assert_eq!(value["result"]["status"], "environmental");
}

#[test]
fn cpu_batch_norm_relu_reference_matches_nchw_channel_indexing() {
    let shape = FusionBenchShape {
        n: 1,
        c: 2,
        h: 1,
        w: 2,
    };
    let output = cpu_batch_norm_relu_f32_nchw(BatchNormReluInput {
        input: &[-1.0, 1.0, 2.0, -2.0],
        scale: &[2.0, 0.5],
        bias: &[0.0, 1.0],
        mean: &[0.0, 2.0],
        variance: &[3.0, 1.0],
        epsilon: 1.0,
        shape,
    })
    .expect("reference succeeds");

    assert_eq!(output.len(), 4);
    assert_eq!(output[0], 0.0);
    assert_eq!(output[1], 1.0);
    assert_eq!(output[2], 1.0);
    assert_eq!(output[3], 0.0);
}

#[test]
fn bounded_bn_relu_runtime_benchmarks_or_reports_typed_environmental() {
    let module = valid_bn_relu_module_json();
    let unit = emit_vnn_batch_norm_relu_msl(&module, VnnBatchNormReluOptions::default()).unwrap();
    let shape = FusionBenchShape {
        n: 1,
        c: 2,
        h: 3,
        w: 4,
    };
    let kernel = MetalBatchNormReluKernel {
        kernel_name: unit.kernel_name,
        source: unit.source,
        shape,
        epsilon: 1.0e-5,
        grid_size: [
            unit.dispatch.grid_size.width,
            unit.dispatch.grid_size.height,
            unit.dispatch.grid_size.depth,
        ],
        threadgroup_size: [
            unit.dispatch.threadgroup_size.width,
            unit.dispatch.threadgroup_size.height,
            unit.dispatch.threadgroup_size.depth,
        ],
    };
    let input_values = deterministic_bn_relu_input(shape);
    let scale = vec![1.25, 0.75];
    let bias = vec![-0.125, 0.25];
    let mean = vec![0.5, -0.5];
    let variance = vec![1.5, 2.0];
    let input = BatchNormReluInput {
        input: &input_values,
        scale: &scale,
        bias: &bias,
        mean: &mean,
        variance: &variance,
        epsilon: kernel.epsilon,
        shape,
    };
    let config = MetalBatchNormReluBenchmarkConfig {
        warmup_iters: 1,
        measure_iters: 3,
        tolerance: 1.0e-4,
        speedup_bar: 5.0,
        ..MetalBatchNormReluBenchmarkConfig::default()
    };

    let outcome =
        MetalRuntimeHarness::default().benchmark_batch_norm_relu_f32(&kernel, input, &config);
    match outcome {
        MetalBatchNormReluBenchmarkOutcome::Completed { evidence } => {
            eprintln!("BN+ReLU benchmark JSONL: {}", evidence.jsonl.trim());
            assert_eq!(
                evidence.record.correctness,
                trust_cg_gpu::BenchCorrectness::Passed
            );
            assert_eq!(
                evidence.fused_output.len(),
                shape.element_count().expect("shape fits usize")
            );
            assert_eq!(
                evidence.naive_output.len(),
                shape.element_count().expect("shape fits usize")
            );
            assert!(evidence.record.median_us.is_some());
            assert!(evidence.record.p95_us.is_some());
            assert!(evidence.record.cold_compile_us.is_some());
            assert!(evidence.record.baseline_cold_compile_us.is_some());
            assert!(evidence.record.baseline_median_us.is_some());
            assert!(evidence.record.baseline_p95_us.is_some());
            assert!(evidence.record.speedup_vs_baseline.is_some());
            assert!(evidence.record.speedup_bar_met.is_some());
            assert!(
                evidence
                    .record
                    .max_abs_error
                    .is_some_and(|error| error <= config.tolerance)
            );
            assert!(evidence.jsonl.contains("\"fusion\":\"batch_norm_relu\""));
            assert!(
                evidence
                    .jsonl
                    .contains("\"baseline\":\"naive_gpu_two_kernel\"")
            );
        }
        MetalBatchNormReluBenchmarkOutcome::Unavailable {
            unavailable,
            record,
            jsonl,
        } => {
            eprintln!("BN+ReLU benchmark environmental JSONL: {}", jsonl.trim());
            assert!(!unavailable.phase.is_empty());
            assert!(!unavailable.reason.is_empty());
            assert_eq!(
                record.result.status,
                trust_cg_gpu::BenchStatus::Environmental
            );
            assert!(record.cold_compile_us.is_none());
            assert!(record.baseline_cold_compile_us.is_none());
            assert!(record.median_us.is_none());
            assert!(record.baseline_median_us.is_none());
            assert!(record.speedup_bar_met.is_none());
            assert!(jsonl.contains("\"status\":\"environmental\""));
        }
        MetalBatchNormReluBenchmarkOutcome::Failed { error, jsonl, .. } => {
            panic!("BN+ReLU runtime failed unexpectedly: {error:?}\n{jsonl}");
        }
    }
}

#[test]
fn benchmark_status_serializes_as_snake_case() {
    let status = serde_json::to_value(BenchStatus::Environmental).expect("serialize status");
    assert_eq!(status, Value::String("environmental".to_string()));
}

#[test]
fn attention_jsonl_record_states_speedup_bar_result() {
    let shape = AttentionBenchShape {
        batch: 1,
        sequence: 2,
        head_dim: 2,
    };
    let record = AttentionBenchRecord::environmental_attention(
        "attention_qk_softmax_v_b1_s2_d2_f32",
        "metal-runtime",
        BenchDevice::metal_unknown("test-commit"),
        shape,
        20,
        100,
        1.0e-4,
        BenchResult::environmental(
            "detect_host_runtime",
            "unsupported_os",
            "host Metal runtime APIs are only available on macOS",
        ),
    );
    let jsonl = attention_records_to_jsonl(&[record]).expect("serialize attention JSONL");
    let value: Value = serde_json::from_str(jsonl.trim()).expect("valid JSON object");
    assert_eq!(value["schema_version"], GPU_FUSION_BENCH_SCHEMA_VERSION);
    assert_eq!(value["issue"], 480);
    assert_eq!(value["task_issue"], 876);
    assert_eq!(value["fusion"], "attention_qk_softmax_v");
    assert_eq!(value["baseline"], "naive_gpu_three_kernel");
    assert_eq!(value["speedup_bar"], 5.0);
    assert!(value["fused_median_us"].is_null());
    assert!(value["naive_median_us"].is_null());
    assert!(value["speedup_bar_met"].is_null());
    assert_eq!(value["result"]["status"], "environmental");
}

#[test]
fn cpu_attention_references_match_for_bounded_fixture() {
    let shape = AttentionBenchShape {
        batch: 1,
        sequence: 2,
        head_dim: 2,
    };
    let (query, key, value) = deterministic_attention_inputs(shape);
    let spec = AttentionInput {
        query: &query,
        key: &key,
        value: &value,
        scale: std::f32::consts::FRAC_1_SQRT_2,
        shape,
    };

    let fused = cpu_fused_attention_f32_nld(spec).expect("fused reference succeeds");
    let naive = cpu_naive_attention_f32_nld(spec).expect("naive reference succeeds");
    assert_eq!(fused.len(), 4);
    for (actual, expected) in fused.iter().zip(naive.iter()) {
        assert!(
            (actual - expected).abs() <= 1.0e-6,
            "actual={actual} expected={expected}"
        );
    }
}

#[test]
fn bounded_fused_attention_runtime_benchmarks_or_reports_typed_environmental() {
    let module = valid_attention_module_json();
    let unit = emit_vnn_fused_attention_msl(&module, VnnFusedAttentionOptions::default()).unwrap();
    let kernel = MetalFusedAttentionKernel {
        kernel_name: unit.kernel_name,
        source: unit.source,
        batch: unit.batch,
        sequence: unit.sequence,
        head_dim: unit.head_dim,
        scale: unit.scale as f32,
        grid_size: [
            unit.dispatch.grid_size.width,
            unit.dispatch.grid_size.height,
            unit.dispatch.grid_size.depth,
        ],
        threadgroup_size: [
            unit.dispatch.threadgroup_size.width,
            unit.dispatch.threadgroup_size.height,
            unit.dispatch.threadgroup_size.depth,
        ],
    };
    let shape = kernel.shape();
    let (query, key, value) = deterministic_attention_inputs(shape);
    let input = AttentionInput {
        query: &query,
        key: &key,
        value: &value,
        scale: kernel.scale,
        shape,
    };
    let config = MetalAttentionBenchmarkConfig {
        warmup_iters: 1,
        measure_iters: 3,
        tolerance: 1.0e-4,
        speedup_bar: 5.0,
        ..MetalAttentionBenchmarkConfig::default()
    };

    let outcome =
        MetalRuntimeHarness::default().benchmark_fused_attention_f32(&kernel, input, &config);
    match outcome {
        MetalAttentionBenchmarkOutcome::Completed { evidence } => {
            eprintln!("attention benchmark JSONL: {}", evidence.jsonl.trim());
            assert_eq!(
                evidence.record.correctness,
                trust_cg_gpu::BenchCorrectness::Passed
            );
            assert_eq!(
                evidence.fused_output.len(),
                shape.output_element_count().unwrap()
            );
            assert_eq!(
                evidence.naive_output.len(),
                shape.output_element_count().unwrap()
            );
            assert!(evidence.record.fused_median_us.is_some());
            assert!(evidence.record.naive_median_us.is_some());
            assert!(evidence.record.speedup_vs_baseline.is_some());
            assert!(evidence.record.speedup_bar_met.is_some());
            assert!(
                evidence
                    .record
                    .max_abs_error
                    .is_some_and(|error| error <= config.tolerance)
            );
            assert!(
                evidence
                    .jsonl
                    .contains("\"fusion\":\"attention_qk_softmax_v\"")
            );
        }
        MetalAttentionBenchmarkOutcome::Unavailable {
            unavailable,
            record,
            jsonl,
        } => {
            eprintln!("attention benchmark environmental JSONL: {}", jsonl.trim());
            assert!(!unavailable.phase.is_empty());
            assert!(!unavailable.reason.is_empty());
            assert_eq!(
                record.result.status,
                trust_cg_gpu::BenchStatus::Environmental
            );
            assert!(record.fused_median_us.is_none());
            assert!(record.naive_median_us.is_none());
            assert!(jsonl.contains("\"status\":\"environmental\""));
        }
        MetalAttentionBenchmarkOutcome::Failed { error, jsonl, .. } => {
            panic!("attention runtime failed unexpectedly: {error:?}\n{jsonl}");
        }
    }
}

fn valid_attention_module_json() -> Value {
    json!({
        "version": 1,
        "dialect": "trust_ir.vnn",
        "entry": "attention",
        "tensors": {
            "%hidden": {"shape": [1, 4, 8], "dtype": "f32", "layout": "nld", "role": "input"},
            "%q": {"shape": [1, 4, 8], "dtype": "f32", "layout": "nld", "role": "activation"},
            "%k": {"shape": [1, 4, 8], "dtype": "f32", "layout": "nld", "role": "activation"},
            "%v": {"shape": [1, 4, 8], "dtype": "f32", "layout": "nld", "role": "activation"},
            "%kt": {"shape": [1, 8, 4], "dtype": "f32", "layout": "strided", "role": "activation"},
            "%scores": {"shape": [1, 4, 4], "dtype": "f32", "layout": "nld", "role": "activation"},
            "%scaled_scores": {"shape": [1, 4, 4], "dtype": "f32", "layout": "nld", "role": "activation"},
            "%prob": {"shape": [1, 4, 4], "dtype": "f32", "layout": "nld", "role": "activation"},
            "%ctx": {"shape": [1, 4, 8], "dtype": "f32", "layout": "nld", "role": "output"}
        },
        "initializers": {
            "q.weight": {"shape": [8, 8], "dtype": "f32", "layout": "oi", "values": [0.1]},
            "k.weight": {"shape": [8, 8], "dtype": "f32", "layout": "oi", "values": [0.1]},
            "v.weight": {"shape": [8, 8], "dtype": "f32", "layout": "oi", "values": [0.1]},
            "inv_sqrt_d": {
                "shape": [],
                "dtype": "f32",
                "layout": "scalar",
                "values": [0.3535533905932738]
            }
        },
        "ops": [
            attention_op("vnn.q", "trust_ir.vnn.linear", &["%hidden"], &["%q"], &["q.weight"], "layer.q"),
            attention_op("vnn.k", "trust_ir.vnn.linear", &["%hidden"], &["%k"], &["k.weight"], "layer.k"),
            attention_op("vnn.v", "trust_ir.vnn.linear", &["%hidden"], &["%v"], &["v.weight"], "layer.v"),
            {
                "id": "vnn.transpose",
                "op": "trust_ir.vnn.transpose",
                "inputs": ["%k"],
                "outputs": ["%kt"],
                "weights": [],
                "attrs": {"perm": [0, 2, 1]},
                "provenance": attention_provenance("layer.transpose")
            },
            attention_op("vnn.scores", "trust_ir.vnn.matmul", &["%q", "%kt"], &["%scores"], &[], "layer.scores"),
            {
                "id": "vnn.scale",
                "op": "trust_ir.vnn.scale",
                "inputs": ["%scores"],
                "outputs": ["%scaled_scores"],
                "weights": ["inv_sqrt_d"],
                "attrs": {"scale_initializer": "inv_sqrt_d"},
                "provenance": attention_provenance("layer.scale")
            },
            {
                "id": "vnn.softmax",
                "op": "trust_ir.vnn.softmax",
                "inputs": ["%scaled_scores"],
                "outputs": ["%prob"],
                "weights": [],
                "attrs": {"axis": -1},
                "provenance": attention_provenance("layer.softmax")
            },
            attention_op("vnn.context", "trust_ir.vnn.matmul", &["%prob", "%v"], &["%ctx"], &[], "layer.context")
        ]
    })
}

fn valid_bn_relu_module_json() -> Value {
    json!({
        "version": 1,
        "dialect": "trust_ir.vnn",
        "entry": "bn_relu",
        "tensors": {
            "%input": {"shape": [1, 2, 3, 4], "dtype": "f32", "layout": "nchw", "role": "input"},
            "%bn0": {"shape": [1, 2, 3, 4], "dtype": "f32", "layout": "nchw", "role": "activation"},
            "%relu0": {"shape": [1, 2, 3, 4], "dtype": "f32", "layout": "nchw", "role": "output"}
        },
        "initializers": {
            "bn.scale": {"shape": [2], "dtype": "f32", "layout": "vector", "storage": {"kind": "external", "name": "bn.scale"}, "sha256": "00"},
            "bn.bias": {"shape": [2], "dtype": "f32", "layout": "vector", "storage": {"kind": "external", "name": "bn.bias"}, "sha256": "00"},
            "bn.mean": {"shape": [2], "dtype": "f32", "layout": "vector", "storage": {"kind": "external", "name": "bn.mean"}, "sha256": "00"},
            "bn.var": {"shape": [2], "dtype": "f32", "layout": "vector", "storage": {"kind": "external", "name": "bn.var"}, "sha256": "00"}
        },
        "ops": [
            {
                "id": "vnn.0",
                "op": "trust_ir.vnn.batch_norm",
                "inputs": ["%input"],
                "outputs": ["%bn0"],
                "weights": ["bn.scale", "bn.bias", "bn.mean", "bn.var"],
                "attrs": {"epsilon": 0.00001},
                "provenance": {
                    "gamma_layer_id": "layer.0",
                    "gamma_layer_type": "BatchNorm",
                    "onnx_node_name": "BatchNormalization_0",
                    "onnx_op_type": "BatchNormalization",
                    "onnx_outputs": ["bn0"]
                }
            },
            {
                "id": "vnn.1",
                "op": "trust_ir.vnn.relu",
                "inputs": ["%bn0"],
                "outputs": ["%relu0"],
                "weights": [],
                "attrs": {},
                "provenance": {
                    "gamma_layer_id": "layer.1",
                    "gamma_layer_type": "ReLU",
                    "onnx_node_name": "Relu_1",
                    "onnx_op_type": "Relu",
                    "onnx_outputs": ["relu0"]
                }
            }
        ],
        "edges": [
            {"from": "%bn0", "to": "vnn.1", "from_layer": "layer.0", "to_layer": "layer.1", "onnx_tensor": "bn0"}
        ]
    })
}

fn deterministic_bn_relu_input(shape: FusionBenchShape) -> Vec<f32> {
    let len = shape.element_count().expect("static fixture fits usize");
    (0..len)
        .map(|idx| ((idx % 17) as f32 - 8.0) * 0.125)
        .collect()
}

fn deterministic_attention_inputs(shape: AttentionBenchShape) -> (Vec<f32>, Vec<f32>, Vec<f32>) {
    let len = shape
        .output_element_count()
        .expect("static fixture fits usize");
    let query = (0..len)
        .map(|idx| ((idx % 11) as f32 - 5.0) * 0.03125)
        .collect::<Vec<_>>();
    let key = (0..len)
        .map(|idx| ((idx % 7) as f32 - 3.0) * 0.046875)
        .collect::<Vec<_>>();
    let value = (0..len)
        .map(|idx| ((idx % 13) as f32 - 6.0) * 0.0625)
        .collect::<Vec<_>>();
    (query, key, value)
}

fn attention_op(
    id: &str,
    op: &str,
    inputs: &[&str],
    outputs: &[&str],
    weights: &[&str],
    layer_id: &str,
) -> Value {
    json!({
        "id": id,
        "op": op,
        "inputs": inputs,
        "outputs": outputs,
        "weights": weights,
        "attrs": {},
        "provenance": attention_provenance(layer_id)
    })
}

fn attention_provenance(layer_id: &str) -> Value {
    json!({
        "gamma_layer_id": layer_id,
        "gamma_layer_type": "Attention",
        "onnx_node_name": layer_id,
        "onnx_op_type": "Attention",
        "onnx_outputs": [layer_id]
    })
}
