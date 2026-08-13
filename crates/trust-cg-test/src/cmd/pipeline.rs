// WS8 — prove the rest of the pipeline: RA, scheduler, Mach-O writer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test pipeline` — planned non-ISel proof dispatchers.
//!
//! This planned WS8 dispatcher reports an explicit not-implemented status in
//! v0.1.0.

use clap::{Args, Subcommand};

use super::{GlobalArgs, not_yet_implemented};
use crate::results::ResultStatus;

/// Which stage's proof to discharge.
#[derive(Subcommand, Debug, Clone)]
pub enum PipelineCommand {
    /// Planned register-allocation proof (not implemented in v0.1.0).
    #[command(long_about = "Planned register-allocation proof stage (WS8).\n\n\
                      This stage is not implemented in trust-cg 0.1.0. It exits \
                      2 without invoking tools or writing a result artifact.")]
    Regalloc,
    /// Planned scheduler proof (not implemented in v0.1.0).
    #[command(long_about = "Planned scheduler proof stage (WS8).\n\n\
                      This stage is not implemented in trust-cg 0.1.0. It exits \
                      2 without invoking tools or writing a result artifact.")]
    Schedule,
    /// Planned object-emission proof (not implemented in v0.1.0).
    #[command(long_about = "Planned object-emission proof stage (WS8).\n\n\
                      This stage is not implemented in trust-cg 0.1.0. It exits \
                      2 without invoking tools or writing a result artifact.")]
    Emit,
}

/// Arguments for `trust-cg-test pipeline`.
#[derive(Args, Debug, Clone)]
#[command(long_about = "Planned non-ISel proof dispatcher (WS8).\n\n\
                  The register-allocation, scheduling, and object-emission \
                  stages are not implemented in this CLI in trust-cg 0.1.0. \
                  Every stage exits 2 without invoking tools or writing a \
                  result artifact.")]
pub struct PipelineArgs {
    /// Which stage to prove.
    #[command(subcommand)]
    pub cmd: PipelineCommand,
}

/// Entry point. Stub until WS8 lands.
pub fn run(_global: &GlobalArgs, _args: &PipelineArgs) -> anyhow::Result<ResultStatus> {
    not_yet_implemented("pipeline")
}
