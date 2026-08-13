// trust-cg-codegen/error.rs - Unified error types for the codegen crate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Unified error types for the trust-cg-codegen crate.
//!
//! Provides a top-level [`CodegenError`] that aggregates errors from all
//! codegen subsystems: encoding, frame lowering, branch relaxation,
//! relocations, and the compilation pipeline.

use thiserror::Error;

use crate::aarch64::encode::EncodeError;
use crate::async_compile_service::{AsyncCompileState, AsyncSubmitReject, AsyncSubmitRejectCode};
use crate::compile_service::CompileRequestId;
use crate::compiler::CompileError;
use crate::jit::JitError;
use crate::jit_contract::ArtifactContractError;
use crate::lower::LowerError;
use crate::macho::FixupError;
use crate::macho::linker::LinkerError;
use crate::pipeline::PipelineError;
use crate::relax::RelaxError;

/// Top-level error type for the trust-cg-codegen crate.
///
/// Wraps errors from all codegen subsystems into a single error type
/// for callers that use multiple codegen facilities.
#[derive(Debug, Error)]
pub enum CodegenError {
    /// Instruction encoding error (AArch64 encoder).
    #[error("encoding error: {0}")]
    Encoding(#[from] EncodeError),

    /// Machine code lowering error (instruction selection to binary).
    #[error("lowering error: {0}")]
    Lowering(#[from] LowerError),

    /// Branch relaxation error (out-of-range branches).
    #[error("relaxation error: {0}")]
    Relaxation(#[from] RelaxError),

    /// Compilation pipeline error.
    #[error("pipeline error: {0}")]
    Pipeline(#[from] PipelineError),
}

/// Embedder-facing error facade for public trust-cg-codegen paths.
///
/// This facade preserves the crate's typed public errors while giving
/// embedders a single error type for codegen, JIT, pipeline, Mach-O, artifact
/// contract, and async submit boundaries.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TrustCgError {
    /// General codegen subsystem error.
    #[error("codegen error: {0}")]
    Codegen(#[from] CodegenError),

    /// High-level compiler API error.
    #[error("compile error: {0}")]
    Compile(#[from] CompileError),

    /// JIT compilation or executable memory error.
    #[error("JIT error: {0}")]
    Jit(#[from] JitError),

    /// Compilation pipeline error.
    #[error("pipeline error: {0}")]
    Pipeline(#[from] PipelineError),

    /// Mach-O fixup resolution error.
    #[error("Mach-O fixup error: {0}")]
    MachOFixup(#[from] FixupError),

    /// Mach-O linker error.
    #[error("Mach-O linker error: {0}")]
    MachOLinker(#[from] LinkerError),

    /// JIT artifact contract validation error.
    #[error("artifact contract error: {0}")]
    ArtifactContract(#[from] ArtifactContractError),

    /// Immediate async compile submit rejection.
    #[error(
        "async compile submit rejected for request `{}`: {} ({state:?})",
        request_id.as_str(),
        code.as_str()
    )]
    AsyncSubmitRejected {
        /// Rejected request id.
        request_id: CompileRequestId,
        /// Stable rejection code.
        code: AsyncSubmitRejectCode,
        /// Poll state represented by this rejection.
        state: AsyncCompileState,
    },
}

impl From<AsyncSubmitReject> for TrustCgError {
    fn from(reject: AsyncSubmitReject) -> Self {
        Self::AsyncSubmitRejected {
            request_id: reject.request_id,
            code: reject.code,
            state: reject.state,
        }
    }
}
