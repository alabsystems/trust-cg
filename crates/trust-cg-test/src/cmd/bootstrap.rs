// WS5 — bootstrap rustc with Trust Codegen.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test bootstrap` — stage-1 / stage-2 rustc self-host via Trust Codegen.
//!
//! This planned WS5 dispatcher reports an explicit not-implemented status in
//! v0.1.0.

use clap::Args;

use super::{GlobalArgs, not_yet_implemented};
use crate::results::ResultStatus;

/// Arguments for `trust-cg-test bootstrap`.
#[derive(Args, Debug, Clone)]
#[command(long_about = "Planned rustc bootstrap driver (WS5).\n\n\
                  This command is not implemented in trust-cg 0.1.0. It exits \
                  2 without invoking `x.py`, reading a rustc checkout, or \
                  writing a result artifact. Its options are reserved for a \
                  future release.")]
pub struct BootstrapArgs {
    /// Planned rustc bootstrap stage; ignored in v0.1.0.
    #[arg(long, value_name = "N", default_value_t = 1)]
    pub stage: u8,

    /// Planned rustc source checkout; not read in v0.1.0.
    #[arg(long, value_name = "PATH")]
    pub rustc_src: Option<std::path::PathBuf>,
}

/// Entry point. Stub until WS5 lands.
pub fn run(_global: &GlobalArgs, _args: &BootstrapArgs) -> anyhow::Result<ResultStatus> {
    not_yet_implemented("bootstrap")
}
