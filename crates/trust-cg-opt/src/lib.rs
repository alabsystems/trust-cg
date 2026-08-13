// trust-cg-opt - Optimizations with proof and validation hooks
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

// Trust Codegen is embedded into tRust's compiler build, so rustc's internal lint set
// is applied here. These rustc query lints are not part of Trust Codegen's standalone
// API contract; deterministic optimization evidence is checked at Trust Codegen
// boundaries.
#![allow(rustc::default_hash_types)]
#![allow(rustc::potential_query_instability)]

//! Optimization passes with proof and validation hooks for Trust Codegen.
//!
//! Evidence coverage varies by pass and configuration. Unsupported
//! proof-required paths must fail closed; not every optimization in v0.1.0 has
//! a completed semantic proof.
//!
//! # Architecture
//!
//! ```text
//! PassManager { passes: [ConstFold, CopyProp, CSE, LICM, RotateIdiom, DCE, CfgSimplify] }
//!     │
//!     ├── run_once(func)              → single pass
//!     └── run_to_fixpoint(func, max)  → iterate until stable
//! ```
//!
//! # Passes
//!
//! | Pass | Description |
//! |------|-------------|
//! | [`DeadCodeElimination`](dce::DeadCodeElimination) | Remove instructions whose defs are unused |
//! | [`ConstantFolding`](const_fold::ConstantFolding) | Evaluate constant expressions at compile time |
//! | [`CopyPropagation`](copy_prop::CopyPropagation) | Replace uses of `mov dst, src` with `src` |
//! | [`RotateIdiom`](rotate_idiom::RotateIdiom) | Rotate-idiom fusion (`(x << k) \| (x >> (W-k))` → `ROR`); the other 52 hand-written peephole patterns live in the declarative [`rewrite`] framework |
//! | [`CommonSubexprElim`](cse::CommonSubexprElim) | Eliminate redundant computations (dominator-based) |
//! | [`GlobalValueNumbering`](gvn::GlobalValueNumbering) | Value-number-based redundancy elimination with load numbering |
//! | [`LoopInvariantCodeMotion`](licm::LoopInvariantCodeMotion) | Hoist loop-invariant computations to preheader |
//! | [`ProofOptimization`](proof_opts::ProofOptimization) | Consume trust_ir proof annotations to eliminate runtime checks |
//! | [`AddrModeFormation`](addr_mode::AddrModeFormation) | Fold ADD+LDR/STR into rich AArch64 addressing modes |
//! | [`CmpSelectCombine`](cmp_select::CmpSelectCombine) | Diamond CFG to CSEL/CSET conditional select formation |
//! | [`IfConversion`](if_convert::IfConversion) | General diamond/triangle CFG to CSEL/CSINC/CSNEG |
//! | [`CmpBranchFusion`](cmp_branch_fusion::CmpBranchFusion) | Fuse CMP/TST + BCond into CBZ/CBNZ/TBZ/TBNZ |
//! | [`TailCallOptimization`](tail_call::TailCallOptimization) | Replace tail calls with branches to eliminate stack growth |
//! | [`VectorizationPass`](vectorize::VectorizationPass) | NEON auto-vectorization: scalar loops to SIMD |
//! | [`CfgSimplify`](cfg_simplify::CfgSimplify) | Simplify CFG: branch folding, empty block elim, unreachable removal |
//! | [`const_materialize`] | Compact constant materialization restricted to hw0 MOVZ/MOVN seeds; MOVK and W-form MOVN proof gaps are reported by proof-required verification |
//!
//! # Memory Effects Model
//!
//! The [`effects`] module classifies each opcode as Pure, Load, Store,
//! or Call. This is used by DCE, CSE, GVN, and LICM to ensure safety.
//!
//! # Usage
//!
//! ```rust,no_run
//! use trust_cg_opt::pipeline::{OptimizationPipeline, OptLevel};
//! use trust_cg_ir::MachFunction;
//!
//! // Build and run at O2:
//! // let pipeline = OptimizationPipeline::new(OptLevel::O2);
//! // let stats = pipeline.run(&mut func);
//! ```

pub mod aarch64_bounds_check_elim;
pub mod addr_mode;
pub mod alias_hoist;
pub mod and_cmp_fuse;
pub mod cache;
pub mod cfg_simplify;
pub mod cmp_branch_fusion;
pub mod cmp_select;
pub mod const_fold;
pub mod const_materialize;
pub mod copy_prop;
pub mod cse;
pub mod dce;
pub mod dead_loop;
pub mod dom;
pub mod effects;
pub use trust_cg_process_env as env_lock;
pub mod eor_rotate_fuse;
pub mod ext_addr;
pub mod fast_hash;
pub mod generic_branch_layout;
pub mod gvn;
pub mod if_convert;
pub mod inline;
pub mod interfaces;
pub mod ir_inline;
pub mod latch_and_split;
pub mod licm;
pub mod loop_dead_pure_sink;
pub mod loop_iv;
pub mod loop_latch_layout;
pub mod loop_unroll;
pub mod loop_unswitch;
pub mod loops;
pub mod lsr_and_ubfx;
pub mod mac_reg_block;
pub mod mac_row_unroll;
pub mod mach_view;
pub mod mem_pair;
pub mod mul_shift_reduce;
pub mod neon_array;
pub mod neon_bitrev;
pub mod neon_butterfly;
pub mod neon_bytesum;
pub mod neon_condstore;
pub mod neon_farray;
pub mod neon_fill;
pub mod neon_find;
pub mod neon_fmap;
pub mod neon_fpred;
pub mod neon_iota_fill;
pub mod neon_map;
pub mod neon_minmax;
pub mod neon_predsum;
pub mod neon_reduce;
pub mod neon_stencil;
pub mod pass_manager;
pub mod passes;
pub mod pgo;
pub mod pipeline;
pub mod proof_opts;
pub mod ptr_iv_sr;
pub mod reaching_const;
pub mod recurrence_store_forward;
pub mod reduction_split;
pub mod resid_collapse;
pub mod rewrite;
pub mod rotate_idiom;
pub mod scalar_unroll;
pub mod scheduler;
pub mod select_fuse;
pub mod shift_alu_fuse;
pub mod sincos_merge;
pub mod sroa;
pub mod strength_reduce;
pub mod strided_store_unroll;
pub mod swap_range_guard;
pub mod tail_call;
pub mod unfuse_serial_fma;
pub mod vectorize;
pub mod x86_block_merge;
pub mod x86_bounds_check_elim;
pub mod x86_branch_layout;
pub mod x86_cmov_swap;
pub mod x86_const_fold;
pub mod x86_const_guard_elim;
pub mod x86_copy_prop;
pub mod x86_cse;
pub mod x86_dce;
pub mod x86_if_convert;
pub mod x86_licm;
pub mod x86_loop_unroll;
pub mod x86_pass_manager;
pub mod x86_peephole;
pub mod x86_proof_opts;
pub mod x86_rotate;
pub mod x86_sroa;
pub mod x86_strength_reduce;
pub mod x86_two_addr_expand;
pub mod x86_vectorize;
pub mod xorshift_demanded_bits;

// Re-export the most important types at crate root.
pub use aarch64_bounds_check_elim::AArch64BoundsCheckElimination;
pub use cache::{
    CACHE_KEY_VERSION, CacheBackend, CacheKey, CacheStats, FileCache, InMemoryCache,
    STABLE_HASH_SEED, STABLE_HASH_SEED_HI, StableHasher, StatsCache, stable_hash,
};
pub use dead_loop::DeadCountedLoopElimination;
pub use interfaces::{
    DivergenceClass, OpInterfaces, ProofBackedInst, ProofDiagnostic, ProofDiagnosticCode,
    ProofQuery, bounded_loop_query, divergence_class_query,
};
pub use mac_row_unroll::MacRowUnroll;
pub use pass_manager::{
    AnalysisCache, CertifiedPassCheckerRecord, CertifiedPassRunRecord, CertifiedPassRunStatus,
    MachinePass, PassManager, PassStats,
};
pub use pgo::{
    CounterInjectionPass, CounterMap, CounterSite, PipelineConfig, ProfData, ProfDataError,
    ProfileUsePass, build_profdata_from_counters, build_profdata_from_counters_with_key,
    inject_block_counters,
};
pub use pipeline::{OptLevel, OptimizationPipeline};
pub use rewrite::{
    DeclarativeRewritePass, RewriteAction, RewriteEngine, RewriteStats, Rule, RuleBuilder,
};
pub use sroa::ScalarReplacementOfAggregates;
pub use strided_store_unroll::StridedStoreUnroll;
pub use x86_block_merge::X86BlockMerge;
pub use x86_bounds_check_elim::X86BoundsCheckElimination;
pub use x86_branch_layout::{CcInversionAdmit, X86BranchLayout, X86BranchLayoutConfig};
pub use x86_cmov_swap::X86CmovSwap;
pub use x86_const_fold::X86ConstantFolding;
pub use x86_const_guard_elim::X86ConstGuardElim;
pub use x86_copy_prop::X86CopyPropagation;
pub use x86_cse::X86CommonSubexpressionElimination;
pub use x86_dce::X86DeadCodeElimination;
pub use x86_if_convert::X86IfConvert;
pub use x86_licm::X86LoopInvariantCodeMotion;
pub use x86_loop_unroll::X86LoopUnroll;
pub use x86_pass_manager::{X86MachinePass, X86PassManager, X86PassStats};
pub use x86_peephole::X86Peephole;
pub use x86_proof_opts::{X86ProofGuardElimination, X86ProofOptStats};
pub use x86_rotate::X86LoopRotate;
pub use x86_sroa::X86ScalarReplacementOfAggregates;
pub use x86_strength_reduce::{StrengthReduceAdmission, X86StrengthReduce};
pub use x86_two_addr_expand::X86TwoAddressExpand;
pub use x86_vectorize::X86Vectorize;
