// trust-cg-opt - Optimization passes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Individual optimization passes, each verified for correctness.
//!
//! This module re-exports the pass implementations from their dedicated
//! submodules for convenient access.

pub use crate::addr_mode::{AddrModeEarlyFormation, AddrModeFormation};
pub use crate::cfg_simplify::CfgSimplify;
pub use crate::const_fold::ConstantFolding;
pub use crate::copy_prop::CopyPropagation;
pub use crate::cse::CommonSubexprElim;
pub use crate::dce::DeadCodeElimination;
pub use crate::inline::FunctionInlining;
pub use crate::licm::LoopInvariantCodeMotion;
pub use crate::proof_opts::ProofOptimization;
pub use crate::rotate_idiom::RotateIdiom;
