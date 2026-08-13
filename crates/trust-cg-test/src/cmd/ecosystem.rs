// WS6 — top-100 crates.io cargo-test smoke.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test ecosystem` — planned crates.io smoke dispatcher.
//!
//! This planned WS6 dispatcher reports an explicit not-implemented status in
//! v0.1.0.

use clap::Args;

use super::{GlobalArgs, not_yet_implemented};
use crate::results::ResultStatus;

/// Arguments for `trust-cg-test ecosystem`.
#[derive(Args, Debug, Clone)]
#[command(long_about = "Planned crates.io smoke runner (WS6).\n\n\
                  This command is not implemented in trust-cg 0.1.0. It exits \
                  2 without fetching crates, invoking Cargo, modifying a \
                  cache, or writing a result artifact. Its options are \
                  reserved for a future release.")]
pub struct EcosystemArgs {
    /// Planned number of crates; ignored in v0.1.0.
    #[arg(long, value_name = "N", default_value_t = 100)]
    pub top: u32,

    /// Planned single-crate selector; ignored in v0.1.0.
    #[arg(long, value_name = "NAME")]
    pub crate_name: Option<String>,

    /// Planned source-cache directory; not read or created in v0.1.0.
    #[arg(long, value_name = "PATH")]
    pub cache_dir: Option<std::path::PathBuf>,
}

/// Entry point. Stub until WS6 lands.
pub fn run(_global: &GlobalArgs, _args: &EcosystemArgs) -> anyhow::Result<ResultStatus> {
    not_yet_implemented("ecosystem")
}
