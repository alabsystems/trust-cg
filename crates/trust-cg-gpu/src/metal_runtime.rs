// trust-cg-gpu/metal_runtime.rs - Metal fused-kernel runtime harness
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: reports/2026-04-25-480-fused-gpu-kernel-plan.md
// Issue: alabsystems/trust-cg#561 (Part of #480)

//! Narrow host-side harness for Metal fused-kernel validation.
//!
//! This module deliberately separates platform MSL compilation from host GPU
//! execution. Compilation is attempted through the platform `xcrun` Metal
//! toolchain when available. Kernel launch probes the host Metal runtime
//! independently so missing compiler tools and missing runtime APIs remain
//! distinct environmental results.

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

use crate::fusion_bench::{
    AttentionBenchRecord, AttentionBenchShape, AttentionBenchTimings, AttentionInput,
    BatchNormReluInput, BenchCorrectness, BenchDevice, BenchResult, FusionBenchRecord,
    FusionBenchShape, FusionBenchTimings, GPU_FUSION_SPEEDUP_BAR, attention_records_to_jsonl,
    cpu_batch_norm_relu_f32_nchw, cpu_naive_attention_f32_nld, records_to_jsonl,
};

/// Harness configuration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetalRuntimeConfig {
    pub xcrun_path: PathBuf,
    pub sdk: String,
    pub temp_dir: PathBuf,
}

impl Default for MetalRuntimeConfig {
    fn default() -> Self {
        Self {
            xcrun_path: PathBuf::from("xcrun"),
            sdk: "macosx".to_string(),
            temp_dir: std::env::temp_dir(),
        }
    }
}

/// Located platform Metal toolchain.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalToolchain {
    pub xcrun_path: String,
    pub sdk: String,
    pub metal_path: String,
    pub metallib_path: String,
}

/// Typed environmental unavailable result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalRuntimeUnavailable {
    pub phase: String,
    pub reason: String,
    pub message: String,
    pub tool: Option<String>,
}

impl MetalRuntimeUnavailable {
    fn tool_unavailable(tool: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            phase: "detect_toolchain".to_string(),
            reason: "tool_unavailable".to_string(),
            message: message.into(),
            tool: Some(tool.into()),
        }
    }

    fn host_runtime_unavailable(reason: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            phase: "detect_host_runtime".to_string(),
            reason: reason.into(),
            message: message.into(),
            tool: None,
        }
    }

    fn kernel_library_missing(message: impl Into<String>) -> Self {
        Self {
            phase: "load_kernel_library".to_string(),
            reason: "compiled_kernel_library_missing".to_string(),
            message: message.into(),
            tool: None,
        }
    }
}

/// MSL source compilation request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetalCompileRequest {
    pub kernel_name: String,
    pub source: String,
}

/// Successful MSL compile/validate report. Timing is cold compile time for
/// `metal` plus `metallib`; it is intentionally separate from kernel timing.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalCompileReport {
    pub kernel_name: String,
    pub source_bytes: usize,
    pub air_bytes: u64,
    pub metallib_bytes: u64,
    pub cold_compile_us: u128,
    pub toolchain: MetalToolchain,
}

/// Retained compiled MSL library artifact for a later runtime launch.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalCompiledLibrary {
    pub report: MetalCompileReport,
    pub metallib_path: PathBuf,
}

/// Toolchain compilation outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum MetalCompileOutcome {
    Compiled {
        report: MetalCompileReport,
    },
    Unavailable {
        unavailable: MetalRuntimeUnavailable,
    },
    Failed {
        error: MetalRuntimeError,
    },
}

/// Toolchain compilation outcome that keeps the `.metallib` on disk.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum MetalLibraryCompileOutcome {
    Compiled {
        library: MetalCompiledLibrary,
    },
    Unavailable {
        unavailable: MetalRuntimeUnavailable,
    },
    Failed {
        error: MetalRuntimeError,
    },
}

/// Runtime or toolchain failure after required tooling was available.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalRuntimeError {
    pub phase: String,
    pub reason: String,
    pub message: String,
    pub tool: Option<String>,
    pub status: Option<i32>,
}

impl MetalRuntimeError {
    fn invalid_source(reason: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            phase: "compile_msl".to_string(),
            reason: reason.into(),
            message: message.into(),
            tool: None,
            status: None,
        }
    }

    fn io(phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            phase: phase.into(),
            reason: "io_error".to_string(),
            message: message.into(),
            tool: None,
            status: None,
        }
    }

    fn invalid_launch(reason: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            phase: "launch_kernel".to_string(),
            reason: reason.into(),
            message: message.into(),
            tool: None,
            status: None,
        }
    }

    fn runtime(
        phase: impl Into<String>,
        reason: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            phase: phase.into(),
            reason: reason.into(),
            message: message.into(),
            tool: None,
            status: None,
        }
    }

    fn tool_failed(
        phase: impl Into<String>,
        tool: impl Into<String>,
        status: Option<i32>,
        stderr: impl Into<String>,
    ) -> Self {
        Self {
            phase: phase.into(),
            reason: "tool_failed".to_string(),
            message: stderr.into(),
            tool: Some(tool.into()),
            status,
        }
    }
}

/// Host Metal runtime availability report. This covers runtime APIs only; it
/// says nothing about `metal` or `metallib` compiler tool availability.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalHostRuntimeReport {
    pub api: String,
    pub default_device_available: bool,
    pub command_queue_available: bool,
}

/// Host-side buffer binding descriptor. Callers can validate launch descriptor
/// shape before the harness has a compiled library to dispatch.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalBufferBinding {
    pub binding: u32,
    pub byte_len: usize,
    pub role: MetalBufferRole,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MetalBufferRole {
    Input,
    Output,
    Constant,
}

/// Host-side launch descriptor for a compiled kernel.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalKernelInvocation {
    pub kernel_name: String,
    pub grid_size: [u64; 3],
    pub threadgroup_size: [u64; 3],
    pub buffers: Vec<MetalBufferBinding>,
    pub synchronize: bool,
}

/// Launch outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum MetalLaunchOutcome {
    Completed,
    Unavailable {
        unavailable: MetalRuntimeUnavailable,
    },
    Failed {
        error: MetalRuntimeError,
    },
}

/// Kernel dispatch entry used by the f32 runtime path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetalKernelDispatch {
    pub kernel_name: String,
    pub grid_size: [u64; 3],
    pub threadgroup_size: [u64; 3],
}

/// Host f32 buffer payload for a Metal launch sequence.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MetalF32Buffer {
    pub binding: u32,
    pub role: MetalBufferRole,
    pub values: Vec<f32>,
}

/// A same-library f32 dispatch sequence sharing one buffer table.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MetalF32KernelSequenceInvocation {
    pub metallib_path: PathBuf,
    pub dispatches: Vec<MetalKernelDispatch>,
    pub buffers: Vec<MetalF32Buffer>,
    pub output_binding: u32,
    pub synchronize: bool,
}

/// Successful f32 launch sequence report.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MetalF32KernelRunReport {
    pub elapsed_us: u128,
    pub output_binding: u32,
    pub output: Vec<f32>,
}

/// Runtime outcome for the actual f32 Metal execution path.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum MetalF32KernelRunOutcome {
    Completed {
        report: MetalF32KernelRunReport,
    },
    Unavailable {
        unavailable: MetalRuntimeUnavailable,
    },
    Failed {
        error: MetalRuntimeError,
    },
}

/// Bounded fused-attention kernel emitted by #872 plus dispatch metadata.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MetalFusedAttentionKernel {
    pub kernel_name: String,
    pub source: String,
    pub batch: u64,
    pub sequence: u64,
    pub head_dim: u64,
    pub scale: f32,
    pub grid_size: [u64; 3],
    pub threadgroup_size: [u64; 3],
}

impl MetalFusedAttentionKernel {
    pub fn shape(&self) -> AttentionBenchShape {
        AttentionBenchShape {
            batch: self.batch,
            sequence: self.sequence,
            head_dim: self.head_dim,
        }
    }
}

/// Bounded f32 NCHW BN+ReLU kernel emitted by the Metal VNN fusion path.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MetalBatchNormReluKernel {
    pub kernel_name: String,
    pub source: String,
    pub shape: FusionBenchShape,
    pub epsilon: f32,
    pub grid_size: [u64; 3],
    pub threadgroup_size: [u64; 3],
}

impl MetalBatchNormReluKernel {
    pub fn case_id(&self) -> String {
        bn_relu_case_id(self.shape)
    }
}

/// Runtime benchmark controls for the #876 attention slice.
#[derive(Debug, Clone, PartialEq)]
pub struct MetalAttentionBenchmarkConfig {
    pub warmup_iters: u32,
    pub measure_iters: u32,
    pub tolerance: f64,
    pub speedup_bar: f64,
    pub trust_cg_commit: String,
}

impl Default for MetalAttentionBenchmarkConfig {
    fn default() -> Self {
        Self {
            warmup_iters: 20,
            measure_iters: 100,
            tolerance: 1.0e-4,
            speedup_bar: GPU_FUSION_SPEEDUP_BAR,
            trust_cg_commit: std::env::var("TRUST_CG_COMMIT")
                .unwrap_or_else(|_| "unknown".to_string()),
        }
    }
}

/// Runtime benchmark controls for the #561 BN+ReLU slice.
#[derive(Debug, Clone, PartialEq)]
pub struct MetalBatchNormReluBenchmarkConfig {
    pub warmup_iters: u32,
    pub measure_iters: u32,
    pub tolerance: f64,
    pub speedup_bar: f64,
    pub trust_cg_commit: String,
}

impl Default for MetalBatchNormReluBenchmarkConfig {
    fn default() -> Self {
        Self {
            warmup_iters: 20,
            measure_iters: 100,
            tolerance: 1.0e-4,
            speedup_bar: GPU_FUSION_SPEEDUP_BAR,
            trust_cg_commit: std::env::var("TRUST_CG_COMMIT")
                .unwrap_or_else(|_| "unknown".to_string()),
        }
    }
}

/// Completed runtime evidence for #876.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MetalAttentionBenchmarkEvidence {
    pub record: AttentionBenchRecord,
    pub jsonl: String,
    pub fused_output: Vec<f32>,
    pub naive_output: Vec<f32>,
    pub reference_output: Vec<f32>,
}

/// Completed runtime evidence for #561.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MetalBatchNormReluBenchmarkEvidence {
    pub record: FusionBenchRecord,
    pub jsonl: String,
    pub fused_output: Vec<f32>,
    pub naive_output: Vec<f32>,
    pub reference_output: Vec<f32>,
}

/// End-to-end attention benchmark outcome.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum MetalAttentionBenchmarkOutcome {
    Completed {
        evidence: MetalAttentionBenchmarkEvidence,
    },
    Unavailable {
        unavailable: MetalRuntimeUnavailable,
        record: AttentionBenchRecord,
        jsonl: String,
    },
    Failed {
        error: MetalRuntimeError,
        record: AttentionBenchRecord,
        jsonl: String,
    },
}

/// End-to-end BN+ReLU benchmark outcome.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum MetalBatchNormReluBenchmarkOutcome {
    Completed {
        evidence: MetalBatchNormReluBenchmarkEvidence,
    },
    Unavailable {
        unavailable: MetalRuntimeUnavailable,
        record: FusionBenchRecord,
        jsonl: String,
    },
    Failed {
        error: MetalRuntimeError,
        record: FusionBenchRecord,
        jsonl: String,
    },
}

/// Metal runtime harness.
#[derive(Debug, Clone)]
pub struct MetalRuntimeHarness {
    config: MetalRuntimeConfig,
}

impl Default for MetalRuntimeHarness {
    fn default() -> Self {
        Self::new(MetalRuntimeConfig::default())
    }
}

impl MetalRuntimeHarness {
    pub fn new(config: MetalRuntimeConfig) -> Self {
        Self { config }
    }

    pub fn config(&self) -> &MetalRuntimeConfig {
        &self.config
    }

    /// Locate `metal` and `metallib` via `xcrun`.
    pub fn detect_toolchain(&self) -> Result<MetalToolchain, MetalRuntimeUnavailable> {
        let metal_path = self.find_tool("metal")?;
        let metallib_path = self.find_tool("metallib")?;
        Ok(MetalToolchain {
            xcrun_path: self.config.xcrun_path.display().to_string(),
            sdk: self.config.sdk.clone(),
            metal_path,
            metallib_path,
        })
    }

    /// Probe host Metal runtime APIs without invoking compiler tools.
    pub fn detect_host_runtime(&self) -> Result<MetalHostRuntimeReport, MetalRuntimeUnavailable> {
        platform::detect_host_runtime()
    }

    /// Compile MSL source to AIR, archive it to a `.metallib`, and return a
    /// cold compile timing report. Missing tooling is an environmental result,
    /// not a benchmark success.
    pub fn compile_msl(&self, request: &MetalCompileRequest) -> MetalCompileOutcome {
        match self.compile_msl_library(request) {
            MetalLibraryCompileOutcome::Compiled { library } => {
                cleanup_files([&library.metallib_path]);
                MetalCompileOutcome::Compiled {
                    report: library.report,
                }
            }
            MetalLibraryCompileOutcome::Unavailable { unavailable } => {
                MetalCompileOutcome::Unavailable { unavailable }
            }
            MetalLibraryCompileOutcome::Failed { error } => MetalCompileOutcome::Failed { error },
        }
    }

    /// Compile MSL and retain the `.metallib` for a later launch.
    pub fn compile_msl_library(&self, request: &MetalCompileRequest) -> MetalLibraryCompileOutcome {
        if request.source.trim().is_empty() {
            return MetalLibraryCompileOutcome::Failed {
                error: MetalRuntimeError::invalid_source("empty_source", "MSL source is empty"),
            };
        }
        if !request.source.contains(&request.kernel_name) {
            return MetalLibraryCompileOutcome::Failed {
                error: MetalRuntimeError::invalid_source(
                    "missing_kernel_name",
                    format!(
                        "MSL source does not contain kernel name `{}`",
                        request.kernel_name
                    ),
                ),
            };
        }

        let toolchain = match self.detect_toolchain() {
            Ok(toolchain) => toolchain,
            Err(unavailable) => return MetalLibraryCompileOutcome::Unavailable { unavailable },
        };

        let stem = unique_stem(&request.kernel_name);
        let source_path = self.config.temp_dir.join(format!("{stem}.metal"));
        let air_path = self.config.temp_dir.join(format!("{stem}.air"));
        let metallib_path = self.config.temp_dir.join(format!("{stem}.metallib"));

        if let Err(err) = fs::create_dir_all(&self.config.temp_dir) {
            return MetalLibraryCompileOutcome::Failed {
                error: MetalRuntimeError::io(
                    "prepare_temp_dir",
                    format!(
                        "failed to create temp dir {}: {err}",
                        self.config.temp_dir.display()
                    ),
                ),
            };
        }
        if let Err(err) = fs::write(&source_path, request.source.as_bytes()) {
            return MetalLibraryCompileOutcome::Failed {
                error: MetalRuntimeError::io(
                    "write_msl_source",
                    format!("failed to write {}: {err}", source_path.display()),
                ),
            };
        }

        let started = Instant::now();
        let metal_status = self.run_xcrun_tool(
            "compile_msl",
            "metal",
            [
                OsString::from("-c"),
                source_path.as_os_str().to_os_string(),
                OsString::from("-o"),
                air_path.as_os_str().to_os_string(),
            ],
        );
        if let Err(error) = metal_status {
            cleanup_files([&source_path, &air_path, &metallib_path]);
            return MetalLibraryCompileOutcome::Failed { error };
        }

        let metallib_status = self.run_xcrun_tool(
            "archive_metallib",
            "metallib",
            [
                air_path.as_os_str().to_os_string(),
                OsString::from("-o"),
                metallib_path.as_os_str().to_os_string(),
            ],
        );
        if let Err(error) = metallib_status {
            cleanup_files([&source_path, &air_path, &metallib_path]);
            return MetalLibraryCompileOutcome::Failed { error };
        }
        let cold_compile_us = started.elapsed().as_micros();

        let air_bytes = match fs::metadata(&air_path) {
            Ok(metadata) => metadata.len(),
            Err(err) => {
                cleanup_files([&source_path, &air_path, &metallib_path]);
                return MetalLibraryCompileOutcome::Failed {
                    error: MetalRuntimeError::io(
                        "stat_air",
                        format!("failed to stat {}: {err}", air_path.display()),
                    ),
                };
            }
        };
        let metallib_bytes = match fs::metadata(&metallib_path) {
            Ok(metadata) => metadata.len(),
            Err(err) => {
                cleanup_files([&source_path, &air_path, &metallib_path]);
                return MetalLibraryCompileOutcome::Failed {
                    error: MetalRuntimeError::io(
                        "stat_metallib",
                        format!("failed to stat {}: {err}", metallib_path.display()),
                    ),
                };
            }
        };
        cleanup_files([&source_path, &air_path]);

        MetalLibraryCompileOutcome::Compiled {
            library: MetalCompiledLibrary {
                metallib_path,
                report: MetalCompileReport {
                    kernel_name: request.kernel_name.clone(),
                    source_bytes: request.source.len(),
                    air_bytes,
                    metallib_bytes,
                    cold_compile_us,
                    toolchain,
                },
            },
        }
    }

    /// Validate launch descriptor shape, prove host Metal runtime APIs are
    /// usable, and report the next concrete launch blocker.
    pub fn launch(&self, invocation: &MetalKernelInvocation) -> MetalLaunchOutcome {
        if let Err(error) = validate_invocation(invocation) {
            return MetalLaunchOutcome::Failed { error };
        }

        if let Err(unavailable) = self.detect_host_runtime() {
            return MetalLaunchOutcome::Unavailable { unavailable };
        }

        MetalLaunchOutcome::Unavailable {
            unavailable: MetalRuntimeUnavailable::kernel_library_missing(format!(
                "host Metal runtime is available for `{}`, but trust-cg-gpu launch descriptors do \
                 not yet carry a compiled MTL library or metallib path to load before binding \
                 buffers and dispatching",
                invocation.kernel_name
            )),
        }
    }

    /// Execute one or more f32 kernels from a retained `.metallib`.
    pub fn run_f32_kernel_sequence(
        &self,
        invocation: &MetalF32KernelSequenceInvocation,
    ) -> MetalF32KernelRunOutcome {
        if let Err(error) = validate_f32_sequence_invocation(invocation) {
            return MetalF32KernelRunOutcome::Failed { error };
        }
        if let Err(unavailable) = self.detect_host_runtime() {
            return MetalF32KernelRunOutcome::Unavailable { unavailable };
        }
        match platform::run_f32_kernel_sequence(invocation) {
            Ok(report) => MetalF32KernelRunOutcome::Completed { report },
            Err(error) => MetalF32KernelRunOutcome::Failed { error },
        }
    }

    /// Compile, execute, validate, and benchmark the bounded f32 BN+ReLU slice.
    pub fn benchmark_batch_norm_relu_f32(
        &self,
        kernel: &MetalBatchNormReluKernel,
        input: BatchNormReluInput<'_>,
        config: &MetalBatchNormReluBenchmarkConfig,
    ) -> MetalBatchNormReluBenchmarkOutcome {
        if config.measure_iters == 0 {
            return self.bn_relu_failed_outcome(
                kernel,
                config,
                MetalRuntimeError::runtime(
                    "benchmark_bn_relu",
                    "invalid_measure_iters",
                    "BN+ReLU benchmark requires at least one measured iteration",
                ),
            );
        }
        if input.shape != kernel.shape {
            return self.bn_relu_failed_outcome(
                kernel,
                config,
                MetalRuntimeError::runtime(
                    "prepare_bn_relu_inputs",
                    "shape_mismatch",
                    format!(
                        "input shape {:?} does not match kernel shape {:?}",
                        input.shape, kernel.shape
                    ),
                ),
            );
        }

        let reference_output = match cpu_batch_norm_relu_f32_nchw(input) {
            Ok(output) => output,
            Err(err) => {
                return self.bn_relu_failed_outcome(
                    kernel,
                    config,
                    MetalRuntimeError::runtime(
                        "prepare_bn_relu_reference",
                        "reference_error",
                        err.to_string(),
                    ),
                );
            }
        };

        let fused_library = match self.compile_msl_library(&MetalCompileRequest {
            kernel_name: kernel.kernel_name.clone(),
            source: kernel.source.clone(),
        }) {
            MetalLibraryCompileOutcome::Compiled { library } => library,
            MetalLibraryCompileOutcome::Unavailable { unavailable } => {
                return self.bn_relu_unavailable_outcome(kernel, config, unavailable);
            }
            MetalLibraryCompileOutcome::Failed { error } => {
                return self.bn_relu_failed_outcome(kernel, config, error);
            }
        };

        let naive_source = emit_naive_bn_relu_source(kernel.shape);
        let naive_library = match self.compile_msl_library(&MetalCompileRequest {
            kernel_name: "trust_cg_bn_relu_naive_batch_norm".to_string(),
            source: naive_source,
        }) {
            MetalLibraryCompileOutcome::Compiled { library } => library,
            MetalLibraryCompileOutcome::Unavailable { unavailable } => {
                cleanup_files([&fused_library.metallib_path]);
                return self.bn_relu_unavailable_outcome(kernel, config, unavailable);
            }
            MetalLibraryCompileOutcome::Failed { error } => {
                cleanup_files([&fused_library.metallib_path]);
                return self.bn_relu_failed_outcome(kernel, config, error);
            }
        };

        let fused_invocation = fused_bn_relu_invocation(&fused_library, kernel, input);
        let naive_invocation = naive_bn_relu_invocation(&naive_library, kernel, input);

        for _ in 0..config.warmup_iters {
            if let Err(outcome) = self.run_bn_relu_sequence(kernel, config, &fused_invocation) {
                cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);
                return outcome;
            }
            if let Err(outcome) = self.run_bn_relu_sequence(kernel, config, &naive_invocation) {
                cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);
                return outcome;
            }
        }

        let mut fused_samples = Vec::with_capacity(config.measure_iters as usize);
        let mut naive_samples = Vec::with_capacity(config.measure_iters as usize);
        let mut fused_output = Vec::new();
        let mut naive_output = Vec::new();

        for _ in 0..config.measure_iters {
            match self.run_bn_relu_sequence(kernel, config, &fused_invocation) {
                Ok(report) => {
                    fused_samples.push(report.elapsed_us as f64);
                    fused_output = report.output;
                }
                Err(outcome) => {
                    cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);
                    return outcome;
                }
            }
        }
        for _ in 0..config.measure_iters {
            match self.run_bn_relu_sequence(kernel, config, &naive_invocation) {
                Ok(report) => {
                    naive_samples.push(report.elapsed_us as f64);
                    naive_output = report.output;
                }
                Err(outcome) => {
                    cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);
                    return outcome;
                }
            }
        }

        cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);

        let fused_max_abs_error = max_abs_error(&fused_output, &reference_output);
        let naive_max_abs_error = max_abs_error(&naive_output, &reference_output);
        let max_abs_error = fused_max_abs_error.max(naive_max_abs_error);
        let correctness = if max_abs_error <= config.tolerance {
            BenchCorrectness::Passed
        } else {
            BenchCorrectness::Failed
        };
        let fused_median_us = percentile_us(&fused_samples, 0.50);
        let fused_p95_us = percentile_us(&fused_samples, 0.95);
        let naive_median_us = percentile_us(&naive_samples, 0.50);
        let naive_p95_us = percentile_us(&naive_samples, 0.95);
        let speedup_vs_baseline = if fused_median_us > 0.0 {
            naive_median_us / fused_median_us
        } else {
            0.0
        };
        let speedup_bar_met = speedup_vs_baseline >= config.speedup_bar;
        let result = if correctness == BenchCorrectness::Passed {
            BenchResult::passed_at(
                "benchmark_bn_relu",
                format!(
                    "fused median {fused_median_us:.3}us vs naive median {naive_median_us:.3}us; \
                     speedup {speedup_vs_baseline:.3}x, #480 bar {bar:.1}x met={speedup_bar_met}",
                    bar = config.speedup_bar,
                ),
            )
        } else {
            BenchResult::failed(
                "compare_bn_relu_output",
                "correctness_mismatch",
                format!(
                    "fused max_abs_error {fused_max_abs_error:.6} and naive max_abs_error \
                     {naive_max_abs_error:.6} with tolerance {tol:.6}",
                    tol = config.tolerance,
                ),
            )
        };
        let record = FusionBenchRecord::measured_bn_relu(
            kernel.case_id(),
            "metal-runtime",
            BenchDevice::metal_default(config.trust_cg_commit.clone()),
            kernel.shape,
            config.warmup_iters,
            config.measure_iters,
            FusionBenchTimings {
                cold_compile_us: fused_library.report.cold_compile_us as f64,
                baseline_cold_compile_us: naive_library.report.cold_compile_us as f64,
                median_us: fused_median_us,
                p95_us: fused_p95_us,
                baseline_median_us: naive_median_us,
                baseline_p95_us: naive_p95_us,
                speedup_vs_baseline,
                speedup_bar: config.speedup_bar,
                speedup_bar_met,
                max_abs_error,
            },
            correctness,
            result,
        );
        let jsonl = records_to_jsonl(std::slice::from_ref(&record))
            .unwrap_or_else(|err| format!("{{\"serialization_error\":\"{err}\"}}\n"));

        MetalBatchNormReluBenchmarkOutcome::Completed {
            evidence: MetalBatchNormReluBenchmarkEvidence {
                record,
                jsonl,
                fused_output,
                naive_output,
                reference_output,
            },
        }
    }

    /// Compile, execute, validate, and benchmark the bounded f32 attention slice.
    pub fn benchmark_fused_attention_f32(
        &self,
        kernel: &MetalFusedAttentionKernel,
        input: AttentionInput<'_>,
        config: &MetalAttentionBenchmarkConfig,
    ) -> MetalAttentionBenchmarkOutcome {
        if config.measure_iters == 0 {
            return self.attention_failed_outcome(
                kernel,
                config,
                MetalRuntimeError::runtime(
                    "benchmark_attention",
                    "invalid_measure_iters",
                    "attention benchmark requires at least one measured iteration",
                ),
            );
        }

        let shape = kernel.shape();
        if input.shape != shape {
            return self.attention_failed_outcome(
                kernel,
                config,
                MetalRuntimeError::runtime(
                    "prepare_attention_inputs",
                    "shape_mismatch",
                    format!(
                        "input shape {:?} does not match kernel shape {:?}",
                        input.shape, shape
                    ),
                ),
            );
        }

        let reference_output = match cpu_naive_attention_f32_nld(input) {
            Ok(output) => output,
            Err(err) => {
                return self.attention_failed_outcome(
                    kernel,
                    config,
                    MetalRuntimeError::runtime(
                        "prepare_attention_reference",
                        "reference_error",
                        err.to_string(),
                    ),
                );
            }
        };

        let fused_library = match self.compile_msl_library(&MetalCompileRequest {
            kernel_name: kernel.kernel_name.clone(),
            source: kernel.source.clone(),
        }) {
            MetalLibraryCompileOutcome::Compiled { library } => library,
            MetalLibraryCompileOutcome::Unavailable { unavailable } => {
                return self.attention_unavailable_outcome(kernel, config, unavailable);
            }
            MetalLibraryCompileOutcome::Failed { error } => {
                return self.attention_failed_outcome(kernel, config, error);
            }
        };

        let naive_source = emit_naive_attention_source(shape);
        let naive_kernel_name = "trust_cg_attention_naive_scores".to_string();
        let naive_library = match self.compile_msl_library(&MetalCompileRequest {
            kernel_name: naive_kernel_name,
            source: naive_source,
        }) {
            MetalLibraryCompileOutcome::Compiled { library } => library,
            MetalLibraryCompileOutcome::Unavailable { unavailable } => {
                cleanup_files([&fused_library.metallib_path]);
                return self.attention_unavailable_outcome(kernel, config, unavailable);
            }
            MetalLibraryCompileOutcome::Failed { error } => {
                cleanup_files([&fused_library.metallib_path]);
                return self.attention_failed_outcome(kernel, config, error);
            }
        };

        let fused_invocation = fused_attention_invocation(&fused_library, kernel, input);
        let naive_invocation = naive_attention_invocation(&naive_library, kernel, input);

        for _ in 0..config.warmup_iters {
            if let Err(outcome) = self.run_attention_sequence(kernel, config, &fused_invocation) {
                cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);
                return outcome;
            }
            if let Err(outcome) = self.run_attention_sequence(kernel, config, &naive_invocation) {
                cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);
                return outcome;
            }
        }

        let mut fused_samples = Vec::with_capacity(config.measure_iters as usize);
        let mut naive_samples = Vec::with_capacity(config.measure_iters as usize);
        let mut fused_output = Vec::new();
        let mut naive_output = Vec::new();

        for _ in 0..config.measure_iters {
            match self.run_attention_sequence(kernel, config, &fused_invocation) {
                Ok(report) => {
                    fused_samples.push(report.elapsed_us as f64);
                    fused_output = report.output;
                }
                Err(outcome) => {
                    cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);
                    return outcome;
                }
            }
        }
        for _ in 0..config.measure_iters {
            match self.run_attention_sequence(kernel, config, &naive_invocation) {
                Ok(report) => {
                    naive_samples.push(report.elapsed_us as f64);
                    naive_output = report.output;
                }
                Err(outcome) => {
                    cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);
                    return outcome;
                }
            }
        }

        cleanup_files([&fused_library.metallib_path, &naive_library.metallib_path]);

        let fused_max_abs_error = max_abs_error(&fused_output, &reference_output);
        let naive_max_abs_error = max_abs_error(&naive_output, &reference_output);
        let correctness =
            if fused_max_abs_error <= config.tolerance && naive_max_abs_error <= config.tolerance {
                BenchCorrectness::Passed
            } else {
                BenchCorrectness::Failed
            };

        let fused_median_us = percentile_us(&fused_samples, 0.50);
        let fused_p95_us = percentile_us(&fused_samples, 0.95);
        let naive_median_us = percentile_us(&naive_samples, 0.50);
        let naive_p95_us = percentile_us(&naive_samples, 0.95);
        let speedup_vs_baseline = if fused_median_us > 0.0 {
            naive_median_us / fused_median_us
        } else {
            0.0
        };
        let speedup_bar_met = speedup_vs_baseline >= config.speedup_bar;
        let result = if correctness == BenchCorrectness::Passed {
            BenchResult::passed(format!(
                "fused median {fused_median_us:.3}us vs naive median {naive_median_us:.3}us; \
                 speedup {speedup_vs_baseline:.3}x, #480 bar {bar:.1}x met={speedup_bar_met}",
                bar = config.speedup_bar,
            ))
        } else {
            BenchResult::failed(
                "compare_attention_output",
                "correctness_mismatch",
                format!(
                    "fused max_abs_error {fused_max_abs_error:.6} and naive max_abs_error \
                     {naive_max_abs_error:.6} with tolerance {tol:.6}",
                    tol = config.tolerance,
                ),
            )
        };
        let record = AttentionBenchRecord::measured_attention(
            attention_case_id(shape),
            "metal-runtime",
            BenchDevice::metal_default(config.trust_cg_commit.clone()),
            shape,
            config.warmup_iters,
            config.measure_iters,
            AttentionBenchTimings {
                fused_cold_compile_us: fused_library.report.cold_compile_us as f64,
                naive_cold_compile_us: naive_library.report.cold_compile_us as f64,
                fused_median_us,
                fused_p95_us,
                naive_median_us,
                naive_p95_us,
                speedup_vs_baseline,
                speedup_bar: config.speedup_bar,
                speedup_bar_met,
                max_abs_error: fused_max_abs_error,
                tolerance: config.tolerance,
            },
            correctness,
            result,
        );
        let jsonl = attention_records_to_jsonl(std::slice::from_ref(&record))
            .unwrap_or_else(|err| format!("{{\"serialization_error\":\"{err}\"}}\n"));

        MetalAttentionBenchmarkOutcome::Completed {
            evidence: MetalAttentionBenchmarkEvidence {
                record,
                jsonl,
                fused_output,
                naive_output,
                reference_output,
            },
        }
    }

    #[allow(clippy::result_large_err)] // The error is the complete evidence-bearing outcome.
    fn run_bn_relu_sequence(
        &self,
        kernel: &MetalBatchNormReluKernel,
        config: &MetalBatchNormReluBenchmarkConfig,
        invocation: &MetalF32KernelSequenceInvocation,
    ) -> Result<MetalF32KernelRunReport, MetalBatchNormReluBenchmarkOutcome> {
        match self.run_f32_kernel_sequence(invocation) {
            MetalF32KernelRunOutcome::Completed { report } => Ok(report),
            MetalF32KernelRunOutcome::Unavailable { unavailable } => {
                Err(self.bn_relu_unavailable_outcome(kernel, config, unavailable))
            }
            MetalF32KernelRunOutcome::Failed { error } => {
                Err(self.bn_relu_failed_outcome(kernel, config, error))
            }
        }
    }

    fn bn_relu_unavailable_outcome(
        &self,
        kernel: &MetalBatchNormReluKernel,
        config: &MetalBatchNormReluBenchmarkConfig,
        unavailable: MetalRuntimeUnavailable,
    ) -> MetalBatchNormReluBenchmarkOutcome {
        let record = FusionBenchRecord::environmental_bn_relu(
            kernel.case_id(),
            "metal-runtime",
            BenchDevice::metal_unknown(config.trust_cg_commit.clone()),
            kernel.shape,
            config.warmup_iters,
            config.measure_iters,
            BenchResult::environmental(
                unavailable.phase.clone(),
                unavailable.reason.clone(),
                unavailable.message.clone(),
            ),
        );
        let jsonl = records_to_jsonl(std::slice::from_ref(&record))
            .unwrap_or_else(|err| format!("{{\"serialization_error\":\"{err}\"}}\n"));
        MetalBatchNormReluBenchmarkOutcome::Unavailable {
            unavailable,
            record,
            jsonl,
        }
    }

    fn bn_relu_failed_outcome(
        &self,
        kernel: &MetalBatchNormReluKernel,
        config: &MetalBatchNormReluBenchmarkConfig,
        error: MetalRuntimeError,
    ) -> MetalBatchNormReluBenchmarkOutcome {
        let record = FusionBenchRecord::environmental_bn_relu(
            kernel.case_id(),
            "metal-runtime",
            BenchDevice::metal_default(config.trust_cg_commit.clone()),
            kernel.shape,
            config.warmup_iters,
            config.measure_iters,
            BenchResult::failed(
                error.phase.clone(),
                error.reason.clone(),
                error.message.clone(),
            ),
        );
        let jsonl = records_to_jsonl(std::slice::from_ref(&record))
            .unwrap_or_else(|err| format!("{{\"serialization_error\":\"{err}\"}}\n"));
        MetalBatchNormReluBenchmarkOutcome::Failed {
            error,
            record,
            jsonl,
        }
    }

    #[allow(clippy::result_large_err)] // The error is the complete evidence-bearing outcome.
    fn run_attention_sequence(
        &self,
        kernel: &MetalFusedAttentionKernel,
        config: &MetalAttentionBenchmarkConfig,
        invocation: &MetalF32KernelSequenceInvocation,
    ) -> Result<MetalF32KernelRunReport, MetalAttentionBenchmarkOutcome> {
        match self.run_f32_kernel_sequence(invocation) {
            MetalF32KernelRunOutcome::Completed { report } => Ok(report),
            MetalF32KernelRunOutcome::Unavailable { unavailable } => {
                Err(self.attention_unavailable_outcome(kernel, config, unavailable))
            }
            MetalF32KernelRunOutcome::Failed { error } => {
                Err(self.attention_failed_outcome(kernel, config, error))
            }
        }
    }

    fn attention_unavailable_outcome(
        &self,
        kernel: &MetalFusedAttentionKernel,
        config: &MetalAttentionBenchmarkConfig,
        unavailable: MetalRuntimeUnavailable,
    ) -> MetalAttentionBenchmarkOutcome {
        let record = AttentionBenchRecord::environmental_attention(
            attention_case_id(kernel.shape()),
            "metal-runtime",
            BenchDevice::metal_unknown(config.trust_cg_commit.clone()),
            kernel.shape(),
            config.warmup_iters,
            config.measure_iters,
            config.tolerance,
            BenchResult::environmental(
                unavailable.phase.clone(),
                unavailable.reason.clone(),
                unavailable.message.clone(),
            ),
        );
        let jsonl = attention_records_to_jsonl(std::slice::from_ref(&record))
            .unwrap_or_else(|err| format!("{{\"serialization_error\":\"{err}\"}}\n"));
        MetalAttentionBenchmarkOutcome::Unavailable {
            unavailable,
            record,
            jsonl,
        }
    }

    fn attention_failed_outcome(
        &self,
        kernel: &MetalFusedAttentionKernel,
        config: &MetalAttentionBenchmarkConfig,
        error: MetalRuntimeError,
    ) -> MetalAttentionBenchmarkOutcome {
        let record = AttentionBenchRecord::environmental_attention(
            attention_case_id(kernel.shape()),
            "metal-runtime",
            BenchDevice::metal_default(config.trust_cg_commit.clone()),
            kernel.shape(),
            config.warmup_iters,
            config.measure_iters,
            config.tolerance,
            BenchResult::failed(
                error.phase.clone(),
                error.reason.clone(),
                error.message.clone(),
            ),
        );
        let jsonl = attention_records_to_jsonl(std::slice::from_ref(&record))
            .unwrap_or_else(|err| format!("{{\"serialization_error\":\"{err}\"}}\n"));
        MetalAttentionBenchmarkOutcome::Failed {
            error,
            record,
            jsonl,
        }
    }

    fn find_tool(&self, tool: &str) -> Result<String, MetalRuntimeUnavailable> {
        let output = Command::new(&self.config.xcrun_path)
            .arg("-sdk")
            .arg(&self.config.sdk)
            .arg("--find")
            .arg(tool)
            .output()
            .map_err(|err| {
                MetalRuntimeUnavailable::tool_unavailable(
                    "xcrun",
                    format!("failed to run {}: {err}", self.config.xcrun_path.display()),
                )
            })?;
        if !output.status.success() {
            return Err(MetalRuntimeUnavailable::tool_unavailable(
                tool,
                String::from_utf8_lossy(&output.stderr).trim().to_string(),
            ));
        }
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    }

    fn run_xcrun_tool<I>(&self, phase: &str, tool: &str, args: I) -> Result<(), MetalRuntimeError>
    where
        I: IntoIterator<Item = OsString>,
    {
        let output = Command::new(&self.config.xcrun_path)
            .arg("-sdk")
            .arg(&self.config.sdk)
            .arg(tool)
            .args(args)
            .output()
            .map_err(|err| {
                MetalRuntimeError::io(
                    phase,
                    format!(
                        "failed to run {} {tool}: {err}",
                        self.config.xcrun_path.display()
                    ),
                )
            })?;
        if output.status.success() {
            Ok(())
        } else {
            Err(MetalRuntimeError::tool_failed(
                phase,
                tool,
                output.status.code(),
                String::from_utf8_lossy(&output.stderr).trim().to_string(),
            ))
        }
    }
}

fn validate_f32_sequence_invocation(
    invocation: &MetalF32KernelSequenceInvocation,
) -> Result<(), MetalRuntimeError> {
    if invocation.metallib_path.as_os_str().is_empty() {
        return Err(MetalRuntimeError::invalid_launch(
            "missing_metallib_path",
            "f32 kernel sequence has no metallib path",
        ));
    }
    if !invocation.metallib_path.is_file() {
        return Err(MetalRuntimeError::runtime(
            "load_kernel_library",
            "metallib_path_missing",
            format!(
                "metallib path does not exist: {}",
                invocation.metallib_path.display()
            ),
        ));
    }
    if invocation.dispatches.is_empty() {
        return Err(MetalRuntimeError::invalid_launch(
            "missing_dispatches",
            "f32 kernel sequence has no dispatch entries",
        ));
    }
    if invocation.buffers.is_empty() {
        return Err(MetalRuntimeError::invalid_launch(
            "missing_buffers",
            "f32 kernel sequence has no buffer bindings",
        ));
    }

    for dispatch in &invocation.dispatches {
        if dispatch.kernel_name.trim().is_empty() {
            return Err(MetalRuntimeError::invalid_launch(
                "missing_kernel_name",
                "f32 kernel sequence has an empty kernel name",
            ));
        }
        if dispatch.grid_size.contains(&0) {
            return Err(MetalRuntimeError::invalid_launch(
                "invalid_grid_size",
                format!(
                    "kernel `{}` grid_size must be non-zero in every dimension, got {:?}",
                    dispatch.kernel_name, dispatch.grid_size
                ),
            ));
        }
        if dispatch.threadgroup_size.contains(&0) {
            return Err(MetalRuntimeError::invalid_launch(
                "invalid_threadgroup_size",
                format!(
                    "kernel `{}` threadgroup_size must be non-zero in every dimension, got {:?}",
                    dispatch.kernel_name, dispatch.threadgroup_size
                ),
            ));
        }
    }

    let mut seen = BTreeSet::new();
    let mut output_found = false;
    for buffer in &invocation.buffers {
        if buffer.values.is_empty() {
            return Err(MetalRuntimeError::invalid_launch(
                "empty_buffer_binding",
                format!("buffer binding {} has no f32 values", buffer.binding),
            ));
        }
        if !seen.insert(buffer.binding) {
            return Err(MetalRuntimeError::invalid_launch(
                "duplicate_buffer_binding",
                format!(
                    "buffer binding {} is specified more than once",
                    buffer.binding
                ),
            ));
        }
        if buffer.binding == invocation.output_binding {
            output_found = true;
            if buffer.role != MetalBufferRole::Output {
                return Err(MetalRuntimeError::invalid_launch(
                    "output_binding_role_mismatch",
                    format!(
                        "output binding {} must have output role",
                        invocation.output_binding
                    ),
                ));
            }
        }
    }
    if !output_found {
        return Err(MetalRuntimeError::invalid_launch(
            "missing_output_binding",
            format!(
                "output binding {} is not present in the f32 buffer table",
                invocation.output_binding
            ),
        ));
    }
    Ok(())
}

fn validate_invocation(invocation: &MetalKernelInvocation) -> Result<(), MetalRuntimeError> {
    if invocation.kernel_name.trim().is_empty() {
        return Err(MetalRuntimeError::invalid_launch(
            "missing_kernel_name",
            "kernel invocation has an empty kernel name",
        ));
    }
    if invocation.buffers.is_empty() {
        return Err(MetalRuntimeError::invalid_launch(
            "missing_buffers",
            "kernel invocation has no buffer bindings",
        ));
    }
    if invocation.grid_size.contains(&0) {
        return Err(MetalRuntimeError::invalid_launch(
            "invalid_grid_size",
            format!(
                "kernel invocation grid_size must be non-zero in every dimension, got {:?}",
                invocation.grid_size
            ),
        ));
    }
    if invocation.threadgroup_size.contains(&0) {
        return Err(MetalRuntimeError::invalid_launch(
            "invalid_threadgroup_size",
            format!(
                "kernel invocation threadgroup_size must be non-zero in every dimension, got {:?}",
                invocation.threadgroup_size
            ),
        ));
    }

    let mut seen = BTreeSet::new();
    for buffer in &invocation.buffers {
        if buffer.byte_len == 0 {
            return Err(MetalRuntimeError::invalid_launch(
                "empty_buffer_binding",
                format!("buffer binding {} has zero byte length", buffer.binding),
            ));
        }
        if !seen.insert(buffer.binding) {
            return Err(MetalRuntimeError::invalid_launch(
                "duplicate_buffer_binding",
                format!(
                    "buffer binding {} is specified more than once",
                    buffer.binding
                ),
            ));
        }
    }

    Ok(())
}

fn fused_bn_relu_invocation(
    library: &MetalCompiledLibrary,
    kernel: &MetalBatchNormReluKernel,
    input: BatchNormReluInput<'_>,
) -> MetalF32KernelSequenceInvocation {
    let output_len = kernel.shape.element_count().unwrap_or(1);
    MetalF32KernelSequenceInvocation {
        metallib_path: library.metallib_path.clone(),
        dispatches: vec![MetalKernelDispatch {
            kernel_name: kernel.kernel_name.clone(),
            grid_size: kernel.grid_size,
            threadgroup_size: kernel.threadgroup_size,
        }],
        buffers: bn_relu_buffers(input, output_len, 0),
        output_binding: 1,
        synchronize: true,
    }
}

fn naive_bn_relu_invocation(
    library: &MetalCompiledLibrary,
    kernel: &MetalBatchNormReluKernel,
    input: BatchNormReluInput<'_>,
) -> MetalF32KernelSequenceInvocation {
    let output_len = kernel.shape.element_count().unwrap_or(1);
    MetalF32KernelSequenceInvocation {
        metallib_path: library.metallib_path.clone(),
        dispatches: vec![
            MetalKernelDispatch {
                kernel_name: "trust_cg_bn_relu_naive_batch_norm".to_string(),
                grid_size: kernel.grid_size,
                threadgroup_size: kernel.threadgroup_size,
            },
            MetalKernelDispatch {
                kernel_name: "trust_cg_bn_relu_naive_relu".to_string(),
                grid_size: kernel.grid_size,
                threadgroup_size: kernel.threadgroup_size,
            },
        ],
        buffers: bn_relu_buffers(input, output_len, output_len),
        output_binding: 1,
        synchronize: true,
    }
}

fn bn_relu_buffers(
    input: BatchNormReluInput<'_>,
    output_len: usize,
    tmp_len: usize,
) -> Vec<MetalF32Buffer> {
    let mut buffers = vec![
        MetalF32Buffer {
            binding: 0,
            role: MetalBufferRole::Input,
            values: input.input.to_vec(),
        },
        MetalF32Buffer {
            binding: 1,
            role: MetalBufferRole::Output,
            values: vec![0.0; output_len],
        },
        MetalF32Buffer {
            binding: 2,
            role: MetalBufferRole::Input,
            values: input.scale.to_vec(),
        },
        MetalF32Buffer {
            binding: 3,
            role: MetalBufferRole::Input,
            values: input.bias.to_vec(),
        },
        MetalF32Buffer {
            binding: 4,
            role: MetalBufferRole::Input,
            values: input.mean.to_vec(),
        },
        MetalF32Buffer {
            binding: 5,
            role: MetalBufferRole::Input,
            values: input.variance.to_vec(),
        },
        MetalF32Buffer {
            binding: 6,
            role: MetalBufferRole::Constant,
            values: vec![input.epsilon],
        },
    ];
    if tmp_len > 0 {
        buffers.push(MetalF32Buffer {
            binding: 7,
            role: MetalBufferRole::Output,
            values: vec![0.0; tmp_len],
        });
    }
    buffers
}

fn fused_attention_invocation(
    library: &MetalCompiledLibrary,
    kernel: &MetalFusedAttentionKernel,
    input: AttentionInput<'_>,
) -> MetalF32KernelSequenceInvocation {
    let output_len = kernel.shape().output_element_count().unwrap_or(1);
    MetalF32KernelSequenceInvocation {
        metallib_path: library.metallib_path.clone(),
        dispatches: vec![MetalKernelDispatch {
            kernel_name: kernel.kernel_name.clone(),
            grid_size: kernel.grid_size,
            threadgroup_size: kernel.threadgroup_size,
        }],
        buffers: vec![
            MetalF32Buffer {
                binding: 0,
                role: MetalBufferRole::Input,
                values: input.query.to_vec(),
            },
            MetalF32Buffer {
                binding: 1,
                role: MetalBufferRole::Input,
                values: input.key.to_vec(),
            },
            MetalF32Buffer {
                binding: 2,
                role: MetalBufferRole::Input,
                values: input.value.to_vec(),
            },
            MetalF32Buffer {
                binding: 3,
                role: MetalBufferRole::Output,
                values: vec![0.0; output_len],
            },
            MetalF32Buffer {
                binding: 4,
                role: MetalBufferRole::Constant,
                values: vec![input.scale],
            },
        ],
        output_binding: 3,
        synchronize: true,
    }
}

fn naive_attention_invocation(
    library: &MetalCompiledLibrary,
    kernel: &MetalFusedAttentionKernel,
    input: AttentionInput<'_>,
) -> MetalF32KernelSequenceInvocation {
    let shape = kernel.shape();
    let output_len = shape.output_element_count().unwrap_or(1);
    let scores_len = shape.score_element_count().unwrap_or(1);
    let row_count = shape.batch * shape.sequence;
    MetalF32KernelSequenceInvocation {
        metallib_path: library.metallib_path.clone(),
        dispatches: vec![
            MetalKernelDispatch {
                kernel_name: "trust_cg_attention_naive_scores".to_string(),
                grid_size: [shape.sequence, row_count, 1],
                threadgroup_size: [8, 8, 1],
            },
            MetalKernelDispatch {
                kernel_name: "trust_cg_attention_naive_softmax".to_string(),
                grid_size: [row_count, 1, 1],
                threadgroup_size: [64, 1, 1],
            },
            MetalKernelDispatch {
                kernel_name: "trust_cg_attention_naive_context".to_string(),
                grid_size: [shape.head_dim, row_count, 1],
                threadgroup_size: [8, 8, 1],
            },
        ],
        buffers: vec![
            MetalF32Buffer {
                binding: 0,
                role: MetalBufferRole::Input,
                values: input.query.to_vec(),
            },
            MetalF32Buffer {
                binding: 1,
                role: MetalBufferRole::Input,
                values: input.key.to_vec(),
            },
            MetalF32Buffer {
                binding: 2,
                role: MetalBufferRole::Input,
                values: input.value.to_vec(),
            },
            MetalF32Buffer {
                binding: 3,
                role: MetalBufferRole::Output,
                values: vec![0.0; output_len],
            },
            MetalF32Buffer {
                binding: 4,
                role: MetalBufferRole::Constant,
                values: vec![input.scale],
            },
            MetalF32Buffer {
                binding: 5,
                role: MetalBufferRole::Output,
                values: vec![0.0; scores_len],
            },
            MetalF32Buffer {
                binding: 6,
                role: MetalBufferRole::Output,
                values: vec![0.0; scores_len],
            },
        ],
        output_binding: 3,
        synchronize: true,
    }
}

fn emit_naive_bn_relu_source(shape: FusionBenchShape) -> String {
    let element_count = shape
        .element_count()
        .and_then(|count| u64::try_from(count).ok())
        .unwrap_or(u64::MAX);
    format!(
        "#include <metal_stdlib>\n\
         using namespace metal;\n\n\
         kernel void trust_cg_bn_relu_naive_batch_norm(\n\
         \x20   const device float* input    [[buffer(0)]],\n\
         \x20   device float* preactivation  [[buffer(7)]],\n\
         \x20   const device float* scale    [[buffer(2)]],\n\
         \x20   const device float* bias     [[buffer(3)]],\n\
         \x20   const device float* mean     [[buffer(4)]],\n\
         \x20   const device float* variance [[buffer(5)]],\n\
         \x20   constant float& epsilon      [[buffer(6)]],\n\
         \x20   uint tid [[thread_position_in_grid]])\n\
         {{\n\
         \x20   const uint C = {c}u;\n\
         \x20   const uint H = {h}u;\n\
         \x20   const uint W = {w}u;\n\
         \x20   const uint HW = H * W;\n\
         \x20   const uint element_count = {element_count}u;\n\
         \x20   if (tid >= element_count) return;\n\
         \x20   uint channel = (tid / HW) % C;\n\
         \x20   preactivation[tid] = scale[channel] * (input[tid] - mean[channel]) / sqrt(variance[channel] + epsilon) + bias[channel];\n\
         }}\n\n\
         kernel void trust_cg_bn_relu_naive_relu(\n\
         \x20   const device float* preactivation [[buffer(7)]],\n\
         \x20   device float* output              [[buffer(1)]],\n\
         \x20   uint tid [[thread_position_in_grid]])\n\
         {{\n\
         \x20   const uint element_count = {element_count}u;\n\
         \x20   if (tid >= element_count) return;\n\
         \x20   output[tid] = max(preactivation[tid], 0.0f);\n\
         }}\n",
        c = shape.c,
        h = shape.h,
        w = shape.w,
        element_count = element_count,
    )
}

fn emit_naive_attention_source(shape: AttentionBenchShape) -> String {
    format!(
        "#include <metal_stdlib>\n\
         using namespace metal;\n\n\
         kernel void trust_cg_attention_naive_scores(\n\
         \x20   const device float* query [[buffer(0)]],\n\
         \x20   const device float* key [[buffer(1)]],\n\
         \x20   constant float& scale [[buffer(4)]],\n\
         \x20   device float* scores [[buffer(5)]],\n\
         \x20   uint2 gid [[thread_position_in_grid]])\n\
         {{\n\
         \x20   const uint B = {batch}u;\n\
         \x20   const uint S = {sequence}u;\n\
         \x20   const uint D = {head_dim}u;\n\
         \x20   uint k_pos = gid.x;\n\
         \x20   uint row = gid.y;\n\
         \x20   if (row >= B * S || k_pos >= S) return;\n\
         \x20   uint batch = row / S;\n\
         \x20   uint q_pos = row % S;\n\
         \x20   uint base = batch * S * D;\n\
         \x20   uint q_base = base + q_pos * D;\n\
         \x20   uint k_base = base + k_pos * D;\n\
         \x20   float dot = 0.0f;\n\
         \x20   for (uint d = 0; d < D; ++d) {{\n\
         \x20       dot += query[q_base + d] * key[k_base + d];\n\
         \x20   }}\n\
         \x20   scores[row * S + k_pos] = dot * scale;\n\
         }}\n\n\
         kernel void trust_cg_attention_naive_softmax(\n\
         \x20   const device float* scores [[buffer(5)]],\n\
         \x20   device float* probabilities [[buffer(6)]],\n\
         \x20   uint row [[thread_position_in_grid]])\n\
         {{\n\
         \x20   const uint B = {batch}u;\n\
         \x20   const uint S = {sequence}u;\n\
         \x20   if (row >= B * S) return;\n\
         \x20   uint row_base = row * S;\n\
         \x20   float max_score = -INFINITY;\n\
         \x20   for (uint k_pos = 0; k_pos < S; ++k_pos) {{\n\
         \x20       max_score = max(max_score, scores[row_base + k_pos]);\n\
         \x20   }}\n\
         \x20   float denom = 0.0f;\n\
         \x20   for (uint k_pos = 0; k_pos < S; ++k_pos) {{\n\
         \x20       float weight = exp(scores[row_base + k_pos] - max_score);\n\
         \x20       probabilities[row_base + k_pos] = weight;\n\
         \x20       denom += weight;\n\
         \x20   }}\n\
         \x20   for (uint k_pos = 0; k_pos < S; ++k_pos) {{\n\
         \x20       probabilities[row_base + k_pos] /= denom;\n\
         \x20   }}\n\
         }}\n\n\
         kernel void trust_cg_attention_naive_context(\n\
         \x20   const device float* value [[buffer(2)]],\n\
         \x20   device float* output [[buffer(3)]],\n\
         \x20   const device float* probabilities [[buffer(6)]],\n\
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
         \x20   uint prob_base = row * S;\n\
         \x20   float acc = 0.0f;\n\
         \x20   for (uint k_pos = 0; k_pos < S; ++k_pos) {{\n\
         \x20       uint v_base = base + k_pos * D;\n\
         \x20       acc += probabilities[prob_base + k_pos] * value[v_base + dim];\n\
         \x20   }}\n\
         \x20   output[base + q_pos * D + dim] = acc;\n\
         }}\n",
        batch = shape.batch,
        sequence = shape.sequence,
        head_dim = shape.head_dim,
    )
}

fn bn_relu_case_id(shape: FusionBenchShape) -> String {
    format!(
        "bn_relu_n{}_c{}_h{}_w{}_f32",
        shape.n, shape.c, shape.h, shape.w
    )
}

fn attention_case_id(shape: AttentionBenchShape) -> String {
    format!(
        "attention_qk_softmax_v_b{}_s{}_d{}_f32",
        shape.batch, shape.sequence, shape.head_dim
    )
}

fn max_abs_error(actual: &[f32], expected: &[f32]) -> f64 {
    if actual.len() != expected.len() {
        return f64::INFINITY;
    }
    actual
        .iter()
        .zip(expected.iter())
        .map(|(actual, expected)| f64::from((actual - expected).abs()))
        .fold(0.0, f64::max)
}

fn percentile_us(samples: &[f64], percentile: f64) -> f64 {
    if samples.is_empty() {
        return 0.0;
    }
    let mut sorted = samples.to_vec();
    sorted.sort_by(|left, right| left.total_cmp(right));
    let rank = ((sorted.len() as f64 * percentile).ceil() as usize).saturating_sub(1);
    sorted[rank.min(sorted.len() - 1)]
}

fn unique_stem(kernel_name: &str) -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    let safe_kernel: String = kernel_name
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect();
    format!("trust_cg_{safe_kernel}_{}_{}", std::process::id(), nanos)
}

fn cleanup_files<I, P>(paths: I)
where
    I: IntoIterator<Item = P>,
    P: AsRef<Path>,
{
    for path in paths {
        let _ = fs::remove_file(path.as_ref());
    }
}

#[cfg(target_os = "macos")]
mod platform {
    use std::ffi::{CStr, CString, c_char, c_void};
    use std::ptr;
    use std::time::Instant;

    use super::{
        MetalF32KernelRunReport, MetalF32KernelSequenceInvocation, MetalHostRuntimeReport,
        MetalRuntimeError, MetalRuntimeUnavailable,
    };

    type ObjcId = *mut c_void;
    type ObjcSel = *mut c_void;

    #[repr(C)]
    #[derive(Debug, Clone, Copy)]
    struct MtlSizeC {
        width: usize,
        height: usize,
        depth: usize,
    }

    const NEW_COMMAND_QUEUE_SELECTOR: &[u8] = b"newCommandQueue\0";
    const NEW_LIBRARY_WITH_FILE_SELECTOR: &[u8] = b"newLibraryWithFile:error:\0";
    const NEW_FUNCTION_WITH_NAME_SELECTOR: &[u8] = b"newFunctionWithName:\0";
    const NEW_PIPELINE_SELECTOR: &[u8] = b"newComputePipelineStateWithFunction:error:\0";
    const NEW_BUFFER_WITH_BYTES_SELECTOR: &[u8] = b"newBufferWithBytes:length:options:\0";
    const COMMAND_BUFFER_SELECTOR: &[u8] = b"commandBuffer\0";
    const COMPUTE_COMMAND_ENCODER_SELECTOR: &[u8] = b"computeCommandEncoder\0";
    const SET_PIPELINE_SELECTOR: &[u8] = b"setComputePipelineState:\0";
    const SET_BUFFER_SELECTOR: &[u8] = b"setBuffer:offset:atIndex:\0";
    const DISPATCH_THREADS_SELECTOR: &[u8] = b"dispatchThreads:threadsPerThreadgroup:\0";
    const END_ENCODING_SELECTOR: &[u8] = b"endEncoding\0";
    const COMMIT_SELECTOR: &[u8] = b"commit\0";
    const WAIT_UNTIL_COMPLETED_SELECTOR: &[u8] = b"waitUntilCompleted\0";
    const STATUS_SELECTOR: &[u8] = b"status\0";
    const ERROR_SELECTOR: &[u8] = b"error\0";
    const CONTENTS_SELECTOR: &[u8] = b"contents\0";
    const NSSTRING_CLASS: &[u8] = b"NSString\0";
    const STRING_WITH_UTF8_SELECTOR: &[u8] = b"stringWithUTF8String:\0";
    const LOCALIZED_DESCRIPTION_SELECTOR: &[u8] = b"localizedDescription\0";
    const UTF8_STRING_SELECTOR: &[u8] = b"UTF8String\0";
    const RELEASE_SELECTOR: &[u8] = b"release\0";
    const MTL_COMMAND_BUFFER_STATUS_COMPLETED: usize = 4;

    #[link(name = "Metal", kind = "framework")]
    unsafe extern "C" {
        fn MTLCreateSystemDefaultDevice() -> ObjcId;
    }

    #[allow(clashing_extern_declarations)]
    #[link(name = "objc")]
    unsafe extern "C" {
        fn sel_registerName(name: *const c_char) -> ObjcSel;
        #[link_name = "objc_getClass"]
        fn objc_get_class(name: *const c_char) -> ObjcId;
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_id(receiver: ObjcId, selector: ObjcSel) -> ObjcId;
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_id_id(receiver: ObjcId, selector: ObjcSel, arg: ObjcId) -> ObjcId;
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_id_cstr(receiver: ObjcId, selector: ObjcSel, arg: *const c_char)
        -> ObjcId;
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_id_id_error(
            receiver: ObjcId,
            selector: ObjcSel,
            arg: ObjcId,
            error: *mut ObjcId,
        ) -> ObjcId;
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_id_bytes_len_options(
            receiver: ObjcId,
            selector: ObjcSel,
            bytes: *const c_void,
            length: usize,
            options: usize,
        ) -> ObjcId;
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_void(receiver: ObjcId, selector: ObjcSel);
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_void_id(receiver: ObjcId, selector: ObjcSel, arg: ObjcId);
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_void_buffer(
            receiver: ObjcId,
            selector: ObjcSel,
            buffer: ObjcId,
            offset: usize,
            index: usize,
        );
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_void_mtlsize(
            receiver: ObjcId,
            selector: ObjcSel,
            grid: MtlSizeC,
            threads_per_threadgroup: MtlSizeC,
        );
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_usize(receiver: ObjcId, selector: ObjcSel) -> usize;
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_ptr(receiver: ObjcId, selector: ObjcSel) -> *mut c_void;
        #[link_name = "objc_msgSend"]
        fn objc_msg_send_const_char(receiver: ObjcId, selector: ObjcSel) -> *const c_char;
    }

    pub(super) fn detect_host_runtime() -> Result<MetalHostRuntimeReport, MetalRuntimeUnavailable> {
        let device = unsafe { MTLCreateSystemDefaultDevice() };
        if device.is_null() {
            return Err(MetalRuntimeUnavailable::host_runtime_unavailable(
                "default_device_unavailable",
                "Metal.framework is present but MTLCreateSystemDefaultDevice returned no device",
            ));
        }

        let command_queue_selector = selector(NEW_COMMAND_QUEUE_SELECTOR)?;
        let command_queue = unsafe { objc_msg_send_id(device, command_queue_selector) };
        if command_queue.is_null() {
            release_obj(device);
            return Err(MetalRuntimeUnavailable::host_runtime_unavailable(
                "command_queue_unavailable",
                "default Metal device could not create a command queue",
            ));
        }

        release_obj(command_queue);
        release_obj(device);

        Ok(MetalHostRuntimeReport {
            api: "Metal.framework".to_string(),
            default_device_available: true,
            command_queue_available: true,
        })
    }

    pub(super) fn run_f32_kernel_sequence(
        invocation: &MetalF32KernelSequenceInvocation,
    ) -> Result<MetalF32KernelRunReport, MetalRuntimeError> {
        if !invocation.synchronize {
            return Err(MetalRuntimeError::runtime(
                "launch_kernel",
                "async_output_readback_unsupported",
                "f32 Metal launches must synchronize before output readback",
            ));
        }

        let device = Retained::new(
            unsafe { MTLCreateSystemDefaultDevice() },
            "detect_host_runtime",
            "default_device_unavailable",
            "Metal.framework returned no default device during launch",
        )?;
        let command_queue_selector =
            selector_runtime(NEW_COMMAND_QUEUE_SELECTOR, "detect_host_runtime")?;
        let command_queue = Retained::new(
            unsafe { objc_msg_send_id(device.id(), command_queue_selector) },
            "detect_host_runtime",
            "command_queue_unavailable",
            "default Metal device could not create a command queue during launch",
        )?;

        let library_path = ns_string(
            &invocation.metallib_path.to_string_lossy(),
            "load_kernel_library",
        )?;
        let library_selector =
            selector_runtime(NEW_LIBRARY_WITH_FILE_SELECTOR, "load_kernel_library")?;
        let mut library_error = ptr::null_mut();
        let library = Retained::new_with_error(
            unsafe {
                objc_msg_send_id_id_error(
                    device.id(),
                    library_selector,
                    library_path,
                    &mut library_error,
                )
            },
            "load_kernel_library",
            "new_library_failed",
            library_error,
        )?;

        let mut pipelines = Vec::with_capacity(invocation.dispatches.len());
        for dispatch in &invocation.dispatches {
            let function_name = ns_string(&dispatch.kernel_name, "load_kernel_function")?;
            let function_selector =
                selector_runtime(NEW_FUNCTION_WITH_NAME_SELECTOR, "load_kernel_function")?;
            let function = Retained::new(
                unsafe { objc_msg_send_id_id(library.id(), function_selector, function_name) },
                "load_kernel_function",
                "kernel_function_missing",
                format!(
                    "metallib does not contain kernel `{}`",
                    dispatch.kernel_name
                ),
            )?;
            let pipeline_selector = selector_runtime(NEW_PIPELINE_SELECTOR, "build_pipeline")?;
            let mut pipeline_error = ptr::null_mut();
            let pipeline = Retained::new_with_error(
                unsafe {
                    objc_msg_send_id_id_error(
                        device.id(),
                        pipeline_selector,
                        function.id(),
                        &mut pipeline_error,
                    )
                },
                "build_pipeline",
                "compute_pipeline_failed",
                pipeline_error,
            )?;
            pipelines.push(PipelineDispatch {
                pipeline,
                grid: mtl_size(dispatch.grid_size, "grid_size")?,
                threadgroup: mtl_size(dispatch.threadgroup_size, "threadgroup_size")?,
            });
        }

        let buffer_selector = selector_runtime(NEW_BUFFER_WITH_BYTES_SELECTOR, "allocate_buffers")?;
        let mut buffers = Vec::with_capacity(invocation.buffers.len());
        for buffer in &invocation.buffers {
            let byte_len = buffer
                .values
                .len()
                .checked_mul(std::mem::size_of::<f32>())
                .ok_or_else(|| {
                    MetalRuntimeError::runtime(
                        "allocate_buffers",
                        "buffer_size_overflow",
                        format!("buffer binding {} byte size overflowed", buffer.binding),
                    )
                })?;
            let object = Retained::new(
                unsafe {
                    objc_msg_send_id_bytes_len_options(
                        device.id(),
                        buffer_selector,
                        buffer.values.as_ptr().cast(),
                        byte_len,
                        0,
                    )
                },
                "allocate_buffers",
                "new_buffer_failed",
                format!("Metal failed to allocate buffer binding {}", buffer.binding),
            )?;
            buffers.push(BufferObject {
                binding: buffer.binding,
                len: buffer.values.len(),
                object,
            });
        }

        let command_buffer_selector =
            selector_runtime(COMMAND_BUFFER_SELECTOR, "create_command_buffer")?;
        let command_buffer =
            unsafe { objc_msg_send_id(command_queue.id(), command_buffer_selector) };
        if command_buffer.is_null() {
            return Err(MetalRuntimeError::runtime(
                "create_command_buffer",
                "command_buffer_unavailable",
                "Metal command queue returned no command buffer",
            ));
        }
        let encoder_selector =
            selector_runtime(COMPUTE_COMMAND_ENCODER_SELECTOR, "create_command_encoder")?;
        let encoder = unsafe { objc_msg_send_id(command_buffer, encoder_selector) };
        if encoder.is_null() {
            return Err(MetalRuntimeError::runtime(
                "create_command_encoder",
                "compute_encoder_unavailable",
                "Metal command buffer returned no compute encoder",
            ));
        }

        let set_pipeline_selector = selector_runtime(SET_PIPELINE_SELECTOR, "encode_dispatch")?;
        let set_buffer_selector = selector_runtime(SET_BUFFER_SELECTOR, "encode_dispatch")?;
        let dispatch_selector = selector_runtime(DISPATCH_THREADS_SELECTOR, "encode_dispatch")?;
        let end_encoding_selector = selector_runtime(END_ENCODING_SELECTOR, "encode_dispatch")?;
        let commit_selector = selector_runtime(COMMIT_SELECTOR, "commit_dispatch")?;
        let wait_selector = selector_runtime(WAIT_UNTIL_COMPLETED_SELECTOR, "wait_dispatch")?;

        let started = Instant::now();
        for pipeline in &pipelines {
            unsafe {
                objc_msg_send_void_id(encoder, set_pipeline_selector, pipeline.pipeline.id());
            }
            for buffer in &buffers {
                unsafe {
                    objc_msg_send_void_buffer(
                        encoder,
                        set_buffer_selector,
                        buffer.object.id(),
                        0,
                        buffer.binding as usize,
                    );
                }
            }
            unsafe {
                objc_msg_send_void_mtlsize(
                    encoder,
                    dispatch_selector,
                    pipeline.grid,
                    pipeline.threadgroup,
                );
            }
        }
        unsafe {
            objc_msg_send_void(encoder, end_encoding_selector);
            objc_msg_send_void(command_buffer, commit_selector);
            objc_msg_send_void(command_buffer, wait_selector);
        }
        let elapsed_us = started.elapsed().as_micros();

        let status_selector = selector_runtime(STATUS_SELECTOR, "wait_dispatch")?;
        let status = unsafe { objc_msg_send_usize(command_buffer, status_selector) };
        if status != MTL_COMMAND_BUFFER_STATUS_COMPLETED {
            return Err(MetalRuntimeError::runtime(
                "wait_dispatch",
                "command_buffer_failed",
                format!(
                    "Metal command buffer finished with status {status}: {}",
                    command_buffer_error(command_buffer)
                ),
            ));
        }

        let output = buffers
            .iter()
            .find(|buffer| buffer.binding == invocation.output_binding)
            .ok_or_else(|| {
                MetalRuntimeError::runtime(
                    "read_output",
                    "missing_output_binding",
                    format!("output binding {} is missing", invocation.output_binding),
                )
            })?;
        let contents_selector = selector_runtime(CONTENTS_SELECTOR, "read_output")?;
        let contents = unsafe { objc_msg_send_ptr(output.object.id(), contents_selector) };
        if contents.is_null() {
            return Err(MetalRuntimeError::runtime(
                "read_output",
                "buffer_contents_unavailable",
                format!(
                    "output binding {} has null contents",
                    invocation.output_binding
                ),
            ));
        }
        let output_values =
            unsafe { std::slice::from_raw_parts(contents.cast::<f32>(), output.len) }.to_vec();

        Ok(MetalF32KernelRunReport {
            elapsed_us,
            output_binding: invocation.output_binding,
            output: output_values,
        })
    }

    fn selector(name: &'static [u8]) -> Result<ObjcSel, MetalRuntimeUnavailable> {
        let selector = unsafe { sel_registerName(name.as_ptr().cast()) };
        if selector.is_null() {
            Err(MetalRuntimeUnavailable::host_runtime_unavailable(
                "objc_selector_unavailable",
                format!(
                    "Objective-C runtime could not register selector `{}`",
                    String::from_utf8_lossy(&name[..name.len() - 1])
                ),
            ))
        } else {
            Ok(selector)
        }
    }

    fn selector_runtime(
        name: &'static [u8],
        phase: &'static str,
    ) -> Result<ObjcSel, MetalRuntimeError> {
        let selector = unsafe { sel_registerName(name.as_ptr().cast()) };
        if selector.is_null() {
            Err(MetalRuntimeError::runtime(
                phase,
                "objc_selector_unavailable",
                format!(
                    "Objective-C runtime could not register selector `{}`",
                    String::from_utf8_lossy(&name[..name.len() - 1])
                ),
            ))
        } else {
            Ok(selector)
        }
    }

    fn ns_string(value: &str, phase: &'static str) -> Result<ObjcId, MetalRuntimeError> {
        let c_value = CString::new(value).map_err(|_| {
            MetalRuntimeError::runtime(
                phase,
                "invalid_nsstring",
                "string contained an interior NUL byte",
            )
        })?;
        let class = unsafe { objc_get_class(NSSTRING_CLASS.as_ptr().cast()) };
        if class.is_null() {
            return Err(MetalRuntimeError::runtime(
                phase,
                "nsstring_class_unavailable",
                "Objective-C NSString class is unavailable",
            ));
        }
        let selector = selector_runtime(STRING_WITH_UTF8_SELECTOR, phase)?;
        let object = unsafe { objc_msg_send_id_cstr(class, selector, c_value.as_ptr()) };
        if object.is_null() {
            Err(MetalRuntimeError::runtime(
                phase,
                "nsstring_create_failed",
                "NSString stringWithUTF8String returned null",
            ))
        } else {
            Ok(object)
        }
    }

    fn mtl_size(values: [u64; 3], name: &'static str) -> Result<MtlSizeC, MetalRuntimeError> {
        Ok(MtlSizeC {
            width: values[0].try_into().map_err(|_| {
                MetalRuntimeError::runtime(
                    "launch_kernel",
                    "dispatch_size_overflow",
                    format!("{name}.width does not fit NSUInteger"),
                )
            })?,
            height: values[1].try_into().map_err(|_| {
                MetalRuntimeError::runtime(
                    "launch_kernel",
                    "dispatch_size_overflow",
                    format!("{name}.height does not fit NSUInteger"),
                )
            })?,
            depth: values[2].try_into().map_err(|_| {
                MetalRuntimeError::runtime(
                    "launch_kernel",
                    "dispatch_size_overflow",
                    format!("{name}.depth does not fit NSUInteger"),
                )
            })?,
        })
    }

    fn command_buffer_error(command_buffer: ObjcId) -> String {
        let error_selector = unsafe { sel_registerName(ERROR_SELECTOR.as_ptr().cast()) };
        if error_selector.is_null() {
            return "command buffer error selector unavailable".to_string();
        }
        let error = unsafe { objc_msg_send_id(command_buffer, error_selector) };
        ns_error_message(error)
    }

    fn ns_error_message(error: ObjcId) -> String {
        if error.is_null() {
            return "no NSError details available".to_string();
        }
        let description_selector =
            unsafe { sel_registerName(LOCALIZED_DESCRIPTION_SELECTOR.as_ptr().cast()) };
        if description_selector.is_null() {
            return "NSError localizedDescription selector unavailable".to_string();
        }
        let description = unsafe { objc_msg_send_id(error, description_selector) };
        if description.is_null() {
            return "NSError localizedDescription returned null".to_string();
        }
        let utf8_selector = unsafe { sel_registerName(UTF8_STRING_SELECTOR.as_ptr().cast()) };
        if utf8_selector.is_null() {
            return "NSString UTF8String selector unavailable".to_string();
        }
        let bytes = unsafe { objc_msg_send_const_char(description, utf8_selector) };
        if bytes.is_null() {
            "NSError description UTF8String returned null".to_string()
        } else {
            unsafe { CStr::from_ptr(bytes) }
                .to_string_lossy()
                .into_owned()
        }
    }

    fn release_obj(object: ObjcId) {
        if object.is_null() {
            return;
        }
        let selector = unsafe { sel_registerName(RELEASE_SELECTOR.as_ptr().cast()) };
        if !selector.is_null() {
            unsafe {
                objc_msg_send_void(object, selector);
            }
        }
    }

    struct Retained(ObjcId);

    impl Retained {
        fn new(
            object: ObjcId,
            phase: impl Into<String>,
            reason: impl Into<String>,
            message: impl Into<String>,
        ) -> Result<Self, MetalRuntimeError> {
            if object.is_null() {
                Err(MetalRuntimeError::runtime(phase, reason, message))
            } else {
                Ok(Self(object))
            }
        }

        fn new_with_error(
            object: ObjcId,
            phase: impl Into<String>,
            reason: impl Into<String>,
            error: ObjcId,
        ) -> Result<Self, MetalRuntimeError> {
            if object.is_null() {
                Err(MetalRuntimeError::runtime(
                    phase,
                    reason,
                    ns_error_message(error),
                ))
            } else {
                Ok(Self(object))
            }
        }

        fn id(&self) -> ObjcId {
            self.0
        }
    }

    impl Drop for Retained {
        fn drop(&mut self) {
            release_obj(self.0);
        }
    }

    struct PipelineDispatch {
        pipeline: Retained,
        grid: MtlSizeC,
        threadgroup: MtlSizeC,
    }

    struct BufferObject {
        binding: u32,
        len: usize,
        object: Retained,
    }
}

#[cfg(not(target_os = "macos"))]
mod platform {
    use super::{
        MetalF32KernelRunReport, MetalF32KernelSequenceInvocation, MetalHostRuntimeReport,
        MetalRuntimeError, MetalRuntimeUnavailable,
    };

    pub(super) fn detect_host_runtime() -> Result<MetalHostRuntimeReport, MetalRuntimeUnavailable> {
        Err(MetalRuntimeUnavailable::host_runtime_unavailable(
            "unsupported_os",
            "host Metal runtime APIs are only available on macOS",
        ))
    }

    pub(super) fn run_f32_kernel_sequence(
        _invocation: &MetalF32KernelSequenceInvocation,
    ) -> Result<MetalF32KernelRunReport, MetalRuntimeError> {
        Err(MetalRuntimeError::runtime(
            "detect_host_runtime",
            "unsupported_os",
            "host Metal runtime APIs are only available on macOS",
        ))
    }
}
