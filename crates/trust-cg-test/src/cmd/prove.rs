// WS7 — discharge ay lowering obligations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test prove` — planned AY lowering-obligation dispatcher.
//!
//! This planned WS7 dispatcher reports an explicit not-implemented status in
//! v0.1.0.

use clap::{Args, ValueEnum};

use super::{GlobalArgs, not_yet_implemented};
use crate::results::ResultStatus;

/// Bitwidth target for the prove run.
#[derive(Clone, Copy, Debug, ValueEnum)]
#[value(rename_all = "lower")]
pub enum Width {
    /// 8-bit.
    W8,
    /// 16-bit.
    W16,
    /// 32-bit.
    W32,
    /// 64-bit.
    W64,
    /// Parametric width (BV theory).
    Parametric,
}

/// Arguments for `trust-cg-test prove`.
#[derive(Args, Debug, Clone)]
#[command(long_about = "Planned AY lowering-obligation dispatcher (WS7).\n\n\
                  This command is not implemented in trust-cg 0.1.0. It exits \
                  2 without invoking AY, reading a proof cache, or writing a \
                  result artifact. Its options are reserved for a future \
                  release.")]
pub struct ProveArgs {
    /// Planned proof bitwidth; ignored in v0.1.0.
    #[arg(long, value_enum, default_value_t = Width::W8)]
    pub width: Width,

    /// Planned obligation-name filter; ignored in v0.1.0.
    #[arg(long, value_name = "GLOB")]
    pub obligation: Option<String>,

    /// Planned per-query timeout; ignored in v0.1.0.
    #[arg(long, value_name = "SECS", default_value_t = 120)]
    pub timeout_per_query: u64,

    /// Planned proof-cache directory; not read in v0.1.0.
    #[arg(long, value_name = "PATH")]
    pub cache_dir: Option<std::path::PathBuf>,
}

/// Entry point. Stub until WS7 lands.
pub fn run(_global: &GlobalArgs, _args: &ProveArgs) -> anyhow::Result<ResultStatus> {
    not_yet_implemented("prove")
}
