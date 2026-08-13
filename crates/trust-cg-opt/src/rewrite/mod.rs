// trust-cg-opt - Declarative pattern rewrite framework
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Declarative pattern rewrite framework (PDL-style).
//!
//! Rewrite rules are declared as composable pieces: a [`Matcher`] selects
//! candidate instructions, a stack of [`Constraint`]s filters them by
//! semantic predicate, and a [`Rewriter`] produces the replacement
//! [`RewriteAction`]. A [`RewriteEngine`] drives the rule set to a fixed
//! point over a [`trust_cg_ir::MachFunction`].
//!
//! See `designs/2026-04-18-rewrite-and-interfaces.md` for the design.
//!
//! ```text
//! Engine → Rule → Matcher + Constraints + Rewriter
//!            │
//!            └── benefit: i32 (higher wins on conflict)
//! ```
//!
//! # Example
//!
//! ```
//! use trust_cg_opt::rewrite::{patterns, RewriteEngine};
//! use trust_cg_ir::{MachFunction, Signature};
//!
//! let mut func = MachFunction::new("demo".into(), Signature::new(vec![], vec![]));
//! let mut engine = RewriteEngine::new();
//! patterns::register_migrated(&mut engine);
//! let _stats = engine.run_to_fixpoint(&mut func, 16);
//! ```

pub mod admission;
pub mod constraint;
pub mod engine;
pub mod matcher;
pub mod pass;
pub mod patterns;
pub mod rewriter;
pub mod rule;

pub use admission::{
    LoadedAdmittedRewrite, REWRITE_ADMISSION_SCHEMA, REWRITE_ADMISSION_SCHEMA_VERSION,
    RewriteAdmissionLoadError, RewriteAdmissionLoadReport, RewriteAdmissionLoaderConfig,
    load_admitted_rewrites_from_json, register_admitted_rewrites_from_json,
};
pub use constraint::{
    Constraint, DefinedByCategory, DefinedByOneOf, DefinedByOpcode, DefinerImmEquals,
    DefinerImmEqualsOuterImm, DefinerImmIsPowerOfTwo, DefinerOperandEqualsOuter, ImmEquals, ImmIs,
    ImmIsPowerOfTwo, ImmNegativeNonMin, InterfacePure, OperandsEqual,
};
pub use engine::{RewriteEngine, RewriteStats};
pub use matcher::{CategoryMatcher, MatchCtx, Matcher, OpcodeMatcher};
pub use pass::DeclarativeRewritePass;
pub use rewriter::{RewriteAction, Rewriter, RewriterFn};
pub use rule::{Rule, RuleBuilder};
