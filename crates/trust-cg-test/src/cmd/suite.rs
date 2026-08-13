// WS2 — llvm-test-suite SingleSource external corpus runner.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test suite` — external LLVM test-suite runner.
//!
//! This planned WS2 dispatcher reports an explicit not-implemented status in
//! v0.1.0; `scripts/run_llvm_test_suite.sh` remains the maintained runner.

use clap::Args;

use super::{GlobalArgs, not_yet_implemented};
use crate::results::ResultStatus;

/// Arguments for `trust-cg-test suite`.
#[derive(Args, Debug, Clone)]
#[command(
    long_about = "Planned external llvm-test-suite SingleSource runner (WS2).\n\n\
                  This command is not implemented in trust-cg 0.1.0. It exits \
                  2 without invoking tools, cloning a corpus, or writing a \
                  result artifact. Its options are reserved for a future release."
)]
pub struct SuiteArgs {
    /// Planned source-path filter; ignored in v0.1.0.
    #[arg(long, value_name = "GLOB")]
    pub filter: Option<String>,

    /// Planned Trust Codegen optimization level; ignored in v0.1.0.
    #[arg(long, value_name = "N", default_value_t = 0)]
    pub optlevel: u8,

    /// Planned corpus-clone control; no clone occurs in v0.1.0.
    #[arg(long)]
    pub clone_corpus: bool,
}

/// Entry point. Stub until WS2 lands.
pub fn run(_global: &GlobalArgs, _args: &SuiteArgs) -> anyhow::Result<ResultStatus> {
    not_yet_implemented("suite")
}
