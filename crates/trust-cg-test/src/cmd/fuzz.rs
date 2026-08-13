// WS3 — differential fuzzers (csmith, yarpgen, trust-ir-gen).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test fuzz` — differential fuzzing.
//!
//! This planned WS3 dispatcher reports an explicit not-implemented status in
//! v0.1.0; the maintained fuzz workspace remains available under `fuzz/`.

use clap::{Args, ValueEnum};

use super::{GlobalArgs, not_yet_implemented};
use crate::results::ResultStatus;

/// Which fuzz driver to run.
#[derive(Clone, Copy, Debug, ValueEnum)]
#[value(rename_all = "lower")]
pub enum Driver {
    /// Planned csmith random C program generator.
    Csmith,
    /// Planned YARPGen random C/C++ program generator.
    Yarpgen,
    /// Planned in-tree trust_ir random IR generator.
    TrustIrGen,
    /// Planned selection of every driver.
    All,
}

/// Arguments for `trust-cg-test fuzz`.
#[derive(Args, Debug, Clone)]
#[command(long_about = "Planned differential-fuzzing dispatcher (WS3).\n\n\
                  This command is not implemented in trust-cg 0.1.0. It exits \
                  2 without generating programs, invoking tools, filing \
                  issues, or writing a result artifact. Its options are \
                  reserved for a future release.")]
pub struct FuzzArgs {
    /// Planned fuzz driver; ignored in v0.1.0.
    #[arg(long, value_enum, default_value_t = Driver::All)]
    pub driver: Driver,

    /// Planned wall-clock duration; ignored in v0.1.0.
    #[arg(long, value_name = "DUR", default_value = "10m")]
    pub duration: String,

    /// Planned seed cap; ignored in v0.1.0.
    #[arg(long, value_name = "N")]
    pub seeds: Option<u64>,

    /// Planned optimization level; ignored in v0.1.0.
    #[arg(long, value_name = "N", default_value_t = 2)]
    pub optlevel: u8,

    /// Planned reduction control; no reducer runs in v0.1.0.
    #[arg(long)]
    pub reduce: bool,
}

/// Entry point. Stub until WS3 lands.
pub fn run(_global: &GlobalArgs, _args: &FuzzArgs) -> anyhow::Result<ResultStatus> {
    not_yet_implemented("fuzz")
}
