// trust-cg-gpu/fusion_bench.rs - Fused GPU benchmark JSONL schema
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: reports/2026-04-25-480-fused-gpu-kernel-plan.md
// Issue: alabsystems/trust-cg#561 (Part of #480)

//! JSONL records and reference helpers for fused GPU kernel benchmarks.
//!
//! The schema is intentionally host-runtime agnostic so Metal, naive GPU,
//! CPU-reference, and future WGSL runs can be compared without changing
//! downstream report readers. When the Metal runtime is unavailable, timing
//! fields stay present as JSON `null` and [`BenchResult`] carries the typed
//! environmental reason.

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Schema tag required by #480.
pub const GPU_FUSION_BENCH_SCHEMA_VERSION: &str = "trust-cg.gpu_fusion_bench.v1";

/// #480 acceptance floor for fused GPU kernels against the naive GPU baseline.
pub const GPU_FUSION_SPEEDUP_BAR: f64 = 5.0;

/// Device and build identity attached to every benchmark row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BenchDevice {
    pub name: String,
    pub os: String,
    pub driver: String,
    pub trust_cg_commit: String,
}

impl BenchDevice {
    /// Generic Metal device placeholder used before the host runtime can
    /// enumerate a concrete `MTLDevice`.
    pub fn metal_unknown(trust_cg_commit: impl Into<String>) -> Self {
        Self {
            name: "unavailable".to_string(),
            os: std::env::consts::OS.to_string(),
            driver: "metal".to_string(),
            trust_cg_commit: trust_cg_commit.into(),
        }
    }

    pub fn metal_default(trust_cg_commit: impl Into<String>) -> Self {
        Self {
            name: "default_metal_device".to_string(),
            os: std::env::consts::OS.to_string(),
            driver: "metal".to_string(),
            trust_cg_commit: trust_cg_commit.into(),
        }
    }
}

/// NCHW tensor shape used by the first fused BN+ReLU benchmark slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct FusionBenchShape {
    pub n: u64,
    pub c: u64,
    pub h: u64,
    pub w: u64,
}

impl FusionBenchShape {
    pub fn element_count(&self) -> Option<usize> {
        self.n
            .checked_mul(self.c)?
            .checked_mul(self.h)?
            .checked_mul(self.w)?
            .try_into()
            .ok()
    }

    pub fn channel_count(&self) -> Option<usize> {
        self.c.try_into().ok()
    }
}

/// Static single-head attention shape for the bounded f32 [B,S,D] slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttentionBenchShape {
    pub batch: u64,
    pub sequence: u64,
    pub head_dim: u64,
}

impl AttentionBenchShape {
    pub fn output_element_count(&self) -> Option<usize> {
        self.batch
            .checked_mul(self.sequence)?
            .checked_mul(self.head_dim)?
            .try_into()
            .ok()
    }

    pub fn score_element_count(&self) -> Option<usize> {
        self.batch
            .checked_mul(self.sequence)?
            .checked_mul(self.sequence)?
            .try_into()
            .ok()
    }
}

/// High-level correctness result for the emitted row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BenchCorrectness {
    Passed,
    Failed,
    Unavailable,
}

/// Machine-readable result class.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BenchStatus {
    Passed,
    Environmental,
    Failed,
    Unsupported,
}

/// Typed status payload carried by every benchmark record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BenchResult {
    pub status: BenchStatus,
    pub phase: String,
    pub reason: String,
    pub message: String,
}

impl BenchResult {
    pub fn passed(message: impl Into<String>) -> Self {
        Self {
            status: BenchStatus::Passed,
            phase: "benchmark_attention".to_string(),
            reason: "ok".to_string(),
            message: message.into(),
        }
    }

    pub fn passed_at(phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            status: BenchStatus::Passed,
            phase: phase.into(),
            reason: "ok".to_string(),
            message: message.into(),
        }
    }

    pub fn environmental(
        phase: impl Into<String>,
        reason: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            status: BenchStatus::Environmental,
            phase: phase.into(),
            reason: reason.into(),
            message: message.into(),
        }
    }

    pub fn failed(
        phase: impl Into<String>,
        reason: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            status: BenchStatus::Failed,
            phase: phase.into(),
            reason: reason.into(),
            message: message.into(),
        }
    }
}

/// One JSONL row for the #480 fused-kernel microbenchmark schema.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FusionBenchRecord {
    pub schema_version: String,
    pub issue: u32,
    pub case_id: String,
    pub fusion: String,
    pub backend: String,
    pub device: BenchDevice,
    pub shape: FusionBenchShape,
    pub dtype: String,
    pub layout: String,
    pub baseline: String,
    pub warmup_iters: u32,
    pub measure_iters: u32,
    pub cold_compile_us: Option<f64>,
    pub baseline_cold_compile_us: Option<f64>,
    pub median_us: Option<f64>,
    pub p95_us: Option<f64>,
    pub baseline_median_us: Option<f64>,
    pub baseline_p95_us: Option<f64>,
    pub speedup_vs_baseline: Option<f64>,
    pub speedup_bar: f64,
    pub speedup_bar_met: Option<bool>,
    pub max_abs_error: Option<f64>,
    pub correctness: BenchCorrectness,
    pub result: BenchResult,
}

/// One JSONL row for bounded f32 [B,S,D] fused attention runtime evidence.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AttentionBenchRecord {
    pub schema_version: String,
    pub issue: u32,
    pub task_issue: u32,
    pub case_id: String,
    pub fusion: String,
    pub backend: String,
    pub device: BenchDevice,
    pub shape: AttentionBenchShape,
    pub dtype: String,
    pub layout: String,
    pub baseline: String,
    pub warmup_iters: u32,
    pub measure_iters: u32,
    pub speedup_bar: f64,
    pub cold_compile_us: Option<f64>,
    pub naive_cold_compile_us: Option<f64>,
    pub fused_median_us: Option<f64>,
    pub fused_p95_us: Option<f64>,
    pub naive_median_us: Option<f64>,
    pub naive_p95_us: Option<f64>,
    pub speedup_vs_baseline: Option<f64>,
    pub speedup_bar_met: Option<bool>,
    pub max_abs_error: Option<f64>,
    pub tolerance: f64,
    pub correctness: BenchCorrectness,
    pub result: BenchResult,
}

impl AttentionBenchRecord {
    #[allow(clippy::too_many_arguments)] // Constructor mirrors the persisted benchmark record.
    pub fn environmental_attention(
        case_id: impl Into<String>,
        backend: impl Into<String>,
        device: BenchDevice,
        shape: AttentionBenchShape,
        warmup_iters: u32,
        measure_iters: u32,
        tolerance: f64,
        result: BenchResult,
    ) -> Self {
        Self {
            schema_version: GPU_FUSION_BENCH_SCHEMA_VERSION.to_string(),
            issue: 480,
            task_issue: 876,
            case_id: case_id.into(),
            fusion: "attention_qk_softmax_v".to_string(),
            backend: backend.into(),
            device,
            shape,
            dtype: "f32".to_string(),
            layout: "nld".to_string(),
            baseline: "naive_gpu_three_kernel".to_string(),
            warmup_iters,
            measure_iters,
            speedup_bar: GPU_FUSION_SPEEDUP_BAR,
            cold_compile_us: None,
            naive_cold_compile_us: None,
            fused_median_us: None,
            fused_p95_us: None,
            naive_median_us: None,
            naive_p95_us: None,
            speedup_vs_baseline: None,
            speedup_bar_met: None,
            max_abs_error: None,
            tolerance,
            correctness: BenchCorrectness::Unavailable,
            result,
        }
    }

    #[allow(clippy::too_many_arguments)] // Constructor mirrors the persisted benchmark record.
    pub fn measured_attention(
        case_id: impl Into<String>,
        backend: impl Into<String>,
        device: BenchDevice,
        shape: AttentionBenchShape,
        warmup_iters: u32,
        measure_iters: u32,
        timings: AttentionBenchTimings,
        correctness: BenchCorrectness,
        result: BenchResult,
    ) -> Self {
        Self {
            schema_version: GPU_FUSION_BENCH_SCHEMA_VERSION.to_string(),
            issue: 480,
            task_issue: 876,
            case_id: case_id.into(),
            fusion: "attention_qk_softmax_v".to_string(),
            backend: backend.into(),
            device,
            shape,
            dtype: "f32".to_string(),
            layout: "nld".to_string(),
            baseline: "naive_gpu_three_kernel".to_string(),
            warmup_iters,
            measure_iters,
            speedup_bar: timings.speedup_bar,
            cold_compile_us: Some(timings.fused_cold_compile_us),
            naive_cold_compile_us: Some(timings.naive_cold_compile_us),
            fused_median_us: Some(timings.fused_median_us),
            fused_p95_us: Some(timings.fused_p95_us),
            naive_median_us: Some(timings.naive_median_us),
            naive_p95_us: Some(timings.naive_p95_us),
            speedup_vs_baseline: Some(timings.speedup_vs_baseline),
            speedup_bar_met: Some(timings.speedup_bar_met),
            max_abs_error: Some(timings.max_abs_error),
            tolerance: timings.tolerance,
            correctness,
            result,
        }
    }

    /// Compact JSON object suitable for one JSONL line.
    pub fn to_jsonl_line(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AttentionBenchTimings {
    pub fused_cold_compile_us: f64,
    pub naive_cold_compile_us: f64,
    pub fused_median_us: f64,
    pub fused_p95_us: f64,
    pub naive_median_us: f64,
    pub naive_p95_us: f64,
    pub speedup_vs_baseline: f64,
    pub speedup_bar: f64,
    pub speedup_bar_met: bool,
    pub max_abs_error: f64,
    pub tolerance: f64,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FusionBenchTimings {
    pub cold_compile_us: f64,
    pub baseline_cold_compile_us: f64,
    pub median_us: f64,
    pub p95_us: f64,
    pub baseline_median_us: f64,
    pub baseline_p95_us: f64,
    pub speedup_vs_baseline: f64,
    pub speedup_bar: f64,
    pub speedup_bar_met: bool,
    pub max_abs_error: f64,
}

impl FusionBenchRecord {
    /// Environmental BN+ReLU row. This is the fail-closed path used when
    /// Metal tooling or host execution is unavailable.
    pub fn environmental_bn_relu(
        case_id: impl Into<String>,
        backend: impl Into<String>,
        device: BenchDevice,
        shape: FusionBenchShape,
        warmup_iters: u32,
        measure_iters: u32,
        result: BenchResult,
    ) -> Self {
        Self {
            schema_version: GPU_FUSION_BENCH_SCHEMA_VERSION.to_string(),
            issue: 480,
            case_id: case_id.into(),
            fusion: "batch_norm_relu".to_string(),
            backend: backend.into(),
            device,
            shape,
            dtype: "f32".to_string(),
            layout: "nchw".to_string(),
            baseline: "naive_gpu_two_kernel".to_string(),
            warmup_iters,
            measure_iters,
            cold_compile_us: None,
            baseline_cold_compile_us: None,
            median_us: None,
            p95_us: None,
            baseline_median_us: None,
            baseline_p95_us: None,
            speedup_vs_baseline: None,
            speedup_bar: GPU_FUSION_SPEEDUP_BAR,
            speedup_bar_met: None,
            max_abs_error: None,
            correctness: BenchCorrectness::Unavailable,
            result,
        }
    }

    #[allow(clippy::too_many_arguments)] // Constructor mirrors the persisted benchmark record.
    pub fn measured_bn_relu(
        case_id: impl Into<String>,
        backend: impl Into<String>,
        device: BenchDevice,
        shape: FusionBenchShape,
        warmup_iters: u32,
        measure_iters: u32,
        timings: FusionBenchTimings,
        correctness: BenchCorrectness,
        result: BenchResult,
    ) -> Self {
        Self {
            schema_version: GPU_FUSION_BENCH_SCHEMA_VERSION.to_string(),
            issue: 480,
            case_id: case_id.into(),
            fusion: "batch_norm_relu".to_string(),
            backend: backend.into(),
            device,
            shape,
            dtype: "f32".to_string(),
            layout: "nchw".to_string(),
            baseline: "naive_gpu_two_kernel".to_string(),
            warmup_iters,
            measure_iters,
            cold_compile_us: Some(timings.cold_compile_us),
            baseline_cold_compile_us: Some(timings.baseline_cold_compile_us),
            median_us: Some(timings.median_us),
            p95_us: Some(timings.p95_us),
            baseline_median_us: Some(timings.baseline_median_us),
            baseline_p95_us: Some(timings.baseline_p95_us),
            speedup_vs_baseline: Some(timings.speedup_vs_baseline),
            speedup_bar: timings.speedup_bar,
            speedup_bar_met: Some(timings.speedup_bar_met),
            max_abs_error: Some(timings.max_abs_error),
            correctness,
            result,
        }
    }

    /// Compact JSON object suitable for one JSONL line.
    pub fn to_jsonl_line(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// Serialize benchmark records as JSONL with a trailing newline.
pub fn records_to_jsonl(records: &[FusionBenchRecord]) -> Result<String, serde_json::Error> {
    let mut out = String::new();
    for record in records {
        out.push_str(&record.to_jsonl_line()?);
        out.push('\n');
    }
    Ok(out)
}

/// Serialize attention benchmark records as JSONL with a trailing newline.
pub fn attention_records_to_jsonl(
    records: &[AttentionBenchRecord],
) -> Result<String, serde_json::Error> {
    let mut out = String::new();
    for record in records {
        out.push_str(&record.to_jsonl_line()?);
        out.push('\n');
    }
    Ok(out)
}

/// Inputs for the unfused CPU BN+ReLU correctness reference.
#[derive(Debug, Clone, Copy)]
pub struct BatchNormReluInput<'a> {
    pub input: &'a [f32],
    pub scale: &'a [f32],
    pub bias: &'a [f32],
    pub mean: &'a [f32],
    pub variance: &'a [f32],
    pub epsilon: f32,
    pub shape: FusionBenchShape,
}

/// Validation failures for the CPU BN+ReLU reference.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum BenchReferenceError {
    #[error("NCHW element count overflows usize")]
    ElementCountOverflow,
    #[error("input length {actual} does not match shape element count {expected}")]
    InputLengthMismatch { expected: usize, actual: usize },
    #[error("{name} length {actual} does not match channel count {expected}")]
    ChannelLengthMismatch {
        name: &'static str,
        expected: usize,
        actual: usize,
    },
    #[error("epsilon must be positive and finite")]
    InvalidEpsilon,
    #[error("variance[{index}] + epsilon is not positive and finite")]
    InvalidVariance { index: usize },
}

/// Unfused CPU reference for inference-mode BN+ReLU over f32 NCHW tensors.
pub fn cpu_batch_norm_relu_f32_nchw(
    spec: BatchNormReluInput<'_>,
) -> Result<Vec<f32>, BenchReferenceError> {
    let elements = spec
        .shape
        .element_count()
        .ok_or(BenchReferenceError::ElementCountOverflow)?;
    let channels = spec
        .shape
        .channel_count()
        .ok_or(BenchReferenceError::ElementCountOverflow)?;
    if spec.input.len() != elements {
        return Err(BenchReferenceError::InputLengthMismatch {
            expected: elements,
            actual: spec.input.len(),
        });
    }
    check_channels("scale", channels, spec.scale)?;
    check_channels("bias", channels, spec.bias)?;
    check_channels("mean", channels, spec.mean)?;
    check_channels("variance", channels, spec.variance)?;
    if !spec.epsilon.is_finite() || spec.epsilon <= 0.0 {
        return Err(BenchReferenceError::InvalidEpsilon);
    }

    let hw = spec
        .shape
        .h
        .checked_mul(spec.shape.w)
        .and_then(|v| usize::try_from(v).ok())
        .ok_or(BenchReferenceError::ElementCountOverflow)?;
    let mut output = Vec::with_capacity(elements);
    for (idx, x) in spec.input.iter().copied().enumerate() {
        let c = (idx / hw) % channels;
        let denom_sq = spec.variance[c] + spec.epsilon;
        if !denom_sq.is_finite() || denom_sq <= 0.0 {
            return Err(BenchReferenceError::InvalidVariance { index: c });
        }
        let y = spec.scale[c] * (x - spec.mean[c]) / denom_sq.sqrt() + spec.bias[c];
        output.push(y.max(0.0));
    }
    Ok(output)
}

fn check_channels(
    name: &'static str,
    expected: usize,
    values: &[f32],
) -> Result<(), BenchReferenceError> {
    if values.len() == expected {
        Ok(())
    } else {
        Err(BenchReferenceError::ChannelLengthMismatch {
            name,
            expected,
            actual: values.len(),
        })
    }
}

/// Inputs for the bounded single-head f32 attention CPU references.
#[derive(Debug, Clone, Copy)]
pub struct AttentionInput<'a> {
    pub query: &'a [f32],
    pub key: &'a [f32],
    pub value: &'a [f32],
    pub scale: f32,
    pub shape: AttentionBenchShape,
}

/// Validation failures for f32 [B,S,D] attention references.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum AttentionReferenceError {
    #[error("attention output element count overflows usize")]
    ElementCountOverflow,
    #[error("attention score element count overflows usize")]
    ScoreCountOverflow,
    #[error("{name} length {actual} does not match attention element count {expected}")]
    InputLengthMismatch {
        name: &'static str,
        expected: usize,
        actual: usize,
    },
    #[error("scale must be positive and finite")]
    InvalidScale,
}

/// Fused-loop CPU reference matching the bounded Metal fused attention kernel.
pub fn cpu_fused_attention_f32_nld(
    spec: AttentionInput<'_>,
) -> Result<Vec<f32>, AttentionReferenceError> {
    let (batch, sequence, dim, elements, _) = validate_attention_input(spec)?;
    let mut output = vec![0.0; elements];
    for b in 0..batch {
        for q_pos in 0..sequence {
            for d in 0..dim {
                let base = b * sequence * dim;
                let q_base = base + q_pos * dim;
                let mut max_score = f32::NEG_INFINITY;
                for k_pos in 0..sequence {
                    let k_base = base + k_pos * dim;
                    let dot = (0..dim)
                        .map(|kk| spec.query[q_base + kk] * spec.key[k_base + kk])
                        .sum::<f32>();
                    max_score = max_score.max(dot * spec.scale);
                }

                let mut denom = 0.0;
                let mut acc = 0.0;
                for k_pos in 0..sequence {
                    let k_base = base + k_pos * dim;
                    let dot = (0..dim)
                        .map(|kk| spec.query[q_base + kk] * spec.key[k_base + kk])
                        .sum::<f32>();
                    let weight = ((dot * spec.scale) - max_score).exp();
                    denom += weight;
                    acc += weight * spec.value[k_base + d];
                }
                output[q_base + d] = acc / denom;
            }
        }
    }
    Ok(output)
}

/// Naive CPU reference for QK^T, row softmax, then probability*V.
pub fn cpu_naive_attention_f32_nld(
    spec: AttentionInput<'_>,
) -> Result<Vec<f32>, AttentionReferenceError> {
    let (batch, sequence, dim, elements, scores_len) = validate_attention_input(spec)?;
    let mut output = vec![0.0; elements];
    let mut scores = vec![0.0; scores_len];
    for b in 0..batch {
        for q_pos in 0..sequence {
            for k_pos in 0..sequence {
                let base = b * sequence * dim;
                let q_base = base + q_pos * dim;
                let k_base = base + k_pos * dim;
                let dot = (0..dim)
                    .map(|kk| spec.query[q_base + kk] * spec.key[k_base + kk])
                    .sum::<f32>();
                scores[(b * sequence + q_pos) * sequence + k_pos] = dot * spec.scale;
            }
        }
    }

    for b in 0..batch {
        for q_pos in 0..sequence {
            let row_base = (b * sequence + q_pos) * sequence;
            let row = &mut scores[row_base..row_base + sequence];
            let max_score = row.iter().copied().fold(f32::NEG_INFINITY, f32::max);
            let denom = row
                .iter_mut()
                .map(|score| {
                    *score = (*score - max_score).exp();
                    *score
                })
                .sum::<f32>();
            for score in row.iter_mut() {
                *score /= denom;
            }
            for d in 0..dim {
                let mut acc = 0.0;
                for (k_pos, &weight) in row.iter().enumerate() {
                    let base = b * sequence * dim;
                    let k_base = base + k_pos * dim;
                    acc += weight * spec.value[k_base + d];
                }
                output[b * sequence * dim + q_pos * dim + d] = acc;
            }
        }
    }
    Ok(output)
}

fn validate_attention_input(
    spec: AttentionInput<'_>,
) -> Result<(usize, usize, usize, usize, usize), AttentionReferenceError> {
    let elements = spec
        .shape
        .output_element_count()
        .ok_or(AttentionReferenceError::ElementCountOverflow)?;
    let scores = spec
        .shape
        .score_element_count()
        .ok_or(AttentionReferenceError::ScoreCountOverflow)?;
    if !spec.scale.is_finite() || spec.scale <= 0.0 {
        return Err(AttentionReferenceError::InvalidScale);
    }
    check_attention_len("query", elements, spec.query)?;
    check_attention_len("key", elements, spec.key)?;
    check_attention_len("value", elements, spec.value)?;
    let batch = spec
        .shape
        .batch
        .try_into()
        .map_err(|_| AttentionReferenceError::ElementCountOverflow)?;
    let sequence = spec
        .shape
        .sequence
        .try_into()
        .map_err(|_| AttentionReferenceError::ElementCountOverflow)?;
    let dim = spec
        .shape
        .head_dim
        .try_into()
        .map_err(|_| AttentionReferenceError::ElementCountOverflow)?;
    Ok((batch, sequence, dim, elements, scores))
}

fn check_attention_len(
    name: &'static str,
    expected: usize,
    actual: &[f32],
) -> Result<(), AttentionReferenceError> {
    if actual.len() == expected {
        Ok(())
    } else {
        Err(AttentionReferenceError::InputLengthMismatch {
            name,
            expected,
            actual: actual.len(),
        })
    }
}
