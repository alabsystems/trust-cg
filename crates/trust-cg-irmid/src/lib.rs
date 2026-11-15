// trust-cg-irmid - verified trust-ir -> trust-ir mid-end
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The trust-ir → trust-ir mid-end ("irmid", layer L2 of
//! `docs/wasm32_perf_roadmap.md`).
//!
//! [`optimize_module`] returns a copy of the module with some functions
//! rewritten, and an [`IrmidReport`] of what happened. It never refuses a
//! program: every rewrite is either validated or rolled back.
//!
//! **The pass manager** (`manager.rs`) runs each pass over every eligible
//! function. For one function it keeps the current body as the snapshot, lets
//! the pass produce a candidate body and a
//! [`trust_cg_verify::trust_ir_mid_tv::PassWitness`], and keeps the candidate
//! only when
//!
//! 1. the independent witness checker
//!    ([`trust_cg_verify::trust_ir_mid_tv::check_pass`]) accepts it, and
//! 2. the interpreter differential (the same module's reference interpreter on
//!    the snapshot and the candidate, over the function's seeded inputs, with
//!    memory built for pointer, slice and aggregate parameters and its module
//!    callees run through the call, inputs on which the snapshot raises
//!    undefined behaviour excluded: `trust_cg_verify::trust_ir_mid_tv::Harness`)
//!    finds no disagreement in the results, the memory the input provided or
//!    a panic.
//!
//! Otherwise the snapshot stays and the rollback is recorded with its reason.
//! After a pass has run over every function, its proof-table transport is a
//! trust-ir `ProofTableTransformTransaction` between the module before and
//! after the pass, in which every obligation is `Preserved`; a transaction
//! trust-ir does not validate rolls the pass back on every function it changed.
//!
//! **Eligibility.** A function whose body a proof or a binding may name is
//! skipped and counted: function- or instruction-level proof annotations,
//! call-site proof context, a summary, source provenance (it digests the
//! body), a body gate, a module obligation naming the function or one of its
//! sites, an unscoped module obligation (it protects every function), or any
//! spec module (its anchors name sites). Every obligation the skipped
//! functions leave is therefore `Preserved` byte for byte, which is the only
//! disposition this mid-end produces.
//!
//! **Profiles.** [`MidProfile::Wasm32`] first respells the bridge's
//! sign-reinterpreting `copy` of an integer of another type of the same
//! width as the `bitcast` it is (and its `copy` of a thin pointer as
//! another pointer type as a `ptrtoptr`), its comparisons of typed
//! pointers as comparisons at `ptr` and its `u32` bulk-memory counts as
//! `usize`s (trust-ir's validator reports each spelling, and a splice would
//! copy the finding into a caller), then runs copy propagation, the lowering
//! of the bridge's `extractfield`/`insertfield` through a pointer to a
//! byte-offset `gep` and the load or store it is (the copy respelling
//! again after it), the pointer-chain to
//! byte-offset GEP rewrite (from a slot or a pointer already inside one, by
//! a constant or a constant expression, and the integer round trip of a
//! slot's address), copy propagation again, constant folding (which also
//! respells an integer constant spelled out of its type's range), the
//! memory-call rewrite (a call of the C library's `memmove`, `memcpy` or
//! `memset` declaration with a constant count becomes the trust-ir
//! instruction; a copy of a run-time count is withheld, OD-165), the
//! byte-copy
//! rewrite (a run of byte loads and stores copying consecutive bytes
//! between disjoint allocations becomes `memcopy`, and a `memcopy` out of a
//! non-escaping frame slot whose bytes earlier stores of its block cover
//! exactly becomes those stores into the destination), constant-branch
//! folding (with unreachable-block removal) and pure dead-code elimination;
//! the memory cleanup below over every function before any is spliced
//! (store forwarding, slot removal, scalar replacement, copy propagation and
//! dead-code elimination, so a callee whose temporary slot goes is spliced
//! without one); then call-site inlining under a wasm size budget (callees
//! first; never a callee in [`MidConfig::never_inline`], a recursive one, one
//! another definition may replace at link time, or one carrying proof
//! material, and an allocating one only with no slot on a cycle of its own,
//! into a caller off any cycle of direct calls, outside the caller's loops
//! unless its slots are return slots, and within a bound on the caller's
//! spliced slot bytes; an array the bridge passes or returns by the
//! address of its bytes bound to a `load` of them), lane-load
//! scalarization (such a `load` read lane by lane becomes a scalar load
//! per lane), field-access lowering and the copy respelling again, and the
//! cleanup again over the spliced bodies; then
//! single-dominating-store forwarding out of unobservable
//! frame slots, removal of the stores of slots nothing reads any more,
//! scalar replacement of the slots still read at constant offsets (one SSA
//! value per field, joined by block parameters; a pointer field holding an
//! address inside a fresh allocation carried as the pointer itself, the
//! bridge's field access through a pointer read as the load or store it is,
//! a word copied over narrower fields carried as one unsigned integer and
//! its parts shifted and masked, a `bool` field also read as a byte carried
//! as the byte, and a read only the `alloca` reaches given an initial zero),
//! constant-table promotion of
//! local tables still read (through a checked variable index), copy
//! propagation, by-address cloning (a call passing a pointer for an array
//! parameter that the callee copies into a slot of its own, reads only by
//! loads and writes no other memory calls a strong hidden clone that reads
//! the caller's bytes instead, the slot gone; under argument promotion's
//! clone mark and switch), argument promotion (a slot whose address escapes only into
//! calls of defined callees that load and store through it at constant
//! offsets is passed as the values those read, to a strong hidden clone of
//! the callee under a crate-private name that returns the bytes it writes
//! after its own results; the original stays for every other caller), the
//! pointer-chain rewrite, copy propagation and dead-code elimination again,
//! a second scalar replacement, copy propagation, constant folding, the
//! memory-call and byte-copy rewrites again, algebraic
//! simplification (among its rules, scalar
//! replacement's packed
//! pairs read back as their parts, a rotate whose every use is a mask
//! keeping only bits it brings round rewritten as a right shift, and the
//! difference of an address and its base read as the offset), copy
//! propagation, the select-branch rules (a `switch` or `condbr` whose
//! scrutinee a `bool` of its operand chain decides both ways becomes a
//! branch on that `bool`, an `alloca` plus a constant offset within it
//! known not null; under such a branch a `select` on its condition reads
//! its arm), the range
//! rules (the native lanes' LIR unsigned-range simplification ported to
//! trust-ir, with facts from dominating branches and block-parameter
//! intervals, loop induction ranges among them: compares, overflow flags,
//! selects, asserts, branches and `switch` cases its value intervals decide
//! are folded, and the blocks a folded branch leaves unreachable removed),
//! closed-form induction (a counted loop whose only values are affine
//! accumulators of its `+ 1` induction variable is replaced by its trip
//! count and their final values, as `trust_cg_opt::loop_iv`'s recognizer
//! lifted to trust-ir), full unrolling of the loops whose header exit the
//! passes decide on every visit within a trip count and size bound, no copy
//! keeping a call or a 128-bit operation
//! (`trust_cg_opt::loop_unroll`'s constant-trip unroll lifted to trust-ir),
//! interval-bounded unrolling (a loop whose header leaves on visit `B` by
//! the intervals of the values its exit test reads becomes `B` copies that
//! keep their exit tests), the select-branch rules again,
//! with the cleanup that turns its copies' constant induction values and
//! integer address chains into constants and `gep`s of their slots (constant
//! folding, algebraic simplification, copy propagation, branch folding,
//! address folding, copy propagation, dead-code elimination, dead block
//! parameters, dead-code elimination, block merging) and the memory passes
//! again (store forwarding, slot removal, scalar replacement, copy
//! propagation, and scalar replacement and copy propagation once more: a slot
//! read only reads of a slot the one before promoted is promotable only
//! then), the select-branch rules, the range rules and interval-bounded
//! unrolling again (a `Zip`'s state is in values only now) with that
//! cleanup and the memory passes once more, then constant folding, the
//! select-branch rules, the range rules and block merging
//! again, the CRC-table rewrite (a pure region of shift-xor diamonds over
//! one byte, the bit-serial CRC step unrolling leaves, becomes a load from
//! a 256-entry read-only table the checker evaluates exhaustively; it
//! appends static data, so [`MidConfig::promote_constant_tables`] withholds
//! it too), block merging, loop-invariant code motion (`trust_cg_opt::licm`'s
//! tiers over trust-ir: invariant header parameters become their initial
//! values, and invariant instructions that cost a wasm operation move to the
//! preheader when they cannot raise on operands that are never poison or are
//! guaranteed to execute, a load only out of a loop that calls nothing and
//! stores only to other allocations or to bytes of the load's allocation
//! disjoint from the load's, an allocation identified by its `alloca` or
//! its global's name), strength reduction of loop values linear in an
//! induction variable into new induction parameters
//! (`trust_cg_opt::strength_reduce` and `ptr_iv_sr` lifted to trust-ir), and
//! copy propagation and dead-code elimination
//! again, which remove the forwarded copies and the dead slots (a caller
//! whose memory layout cannot take new static data switches promotion off
//! with [`MidConfig::promote_constant_tables`]). A
//! function whose slots all go has no frame in the wasm32 lane: no
//! prologue, epilogue, `__stack_pointer` update or stack guard. It runs no constant
//! CSE: on wasm a shared constant lengthens a live range the engine's
//! register allocator cannot shorten, while a constant at each use is an
//! immediate.
//! [`MidProfile::Native`] is reserved: it runs nothing yet. A module with a
//! function over [`MidConfig::max_function_blocks`] blocks is returned
//! unchanged, with the reason: its caller re-validates the whole optimized
//! module, and trust-ir's validator is superlinear in a function's size.
//!
//! **Withheld fill calls.** A bare external `__trustcg_array_fill_iW`
//! declaration does not authenticate the bridge's helper loop. The default
//! profile retains those calls and reports `fill_call` as withheld; the
//! differential does not invent a body for the declaration.
//!
//! **Withheld comparison calls.** Likewise, a `memcmp` or `bcmp`
//! declaration's name and C prototype do not authenticate the C library's
//! comparison (OD-164's merge boundary): the default profile keeps those calls and reports
//! `mem_cmp` as withheld, and the differential's view gives such a
//! declaration no body.
//!
//! **CFG analysis** goes through [`cfg::TrustIrCfg`], a view of a trust-ir
//! function as trust-cg-opt's `MachIrView`, so dominators, reverse postorder
//! and loops come from `trust_cg_opt::mach_view::CfgAnalysis` rather than a
//! new implementation. **Pointer facts** — which values carry an
//! allocation's address, at which displacement, and whether it escapes —
//! come from [`escape`], the capture analysis the wasm32 lane lays out its
//! frame with, lifted here and shared with it.
//!
//! What the mid-end does not claim: the witness check is structural, per
//! rewrite; the differential covers only the inputs it draws and finishes
//! (every candidate it does not compare is counted under one reason in
//! [`TvCoverage::not_compared`]) and observes results, the bytes of the
//! memory the input provided that the source left initialised, and panics,
//! not other memory; and nothing here relates the module to the machine code
//! the lane emits from it.

pub mod cfg;
pub mod escape;
mod manager;
mod passes;
mod report;

pub use report::{IrmidReport, PassCoverage, PassStats, ProofTableStats, Rollback, TvCoverage};
pub use trust_cg_verify::trust_ir_mid_tv::{DifferentialBudget, HarnessLimits};

use std::collections::BTreeSet;

use trust_ir::Module;

/// Which target the mid-end optimizes for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MidProfile {
    /// wasm32: 32-bit pointers, no constant CSE.
    Wasm32,
    /// Reserved for the native lanes; runs nothing yet.
    Native,
}

impl MidProfile {
    /// Stable name for evidence.
    pub const fn as_str(self) -> &'static str {
        match self {
            MidProfile::Wasm32 => "wasm32",
            MidProfile::Native => "native",
        }
    }
}

/// The mid-end's configuration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MidConfig {
    pub profile: MidProfile,
    /// Seeded inputs per function for the interpreter differential.
    pub samples_per_function: usize,
    /// Bounds of one interpreter run.
    pub differential: DifferentialBudget,
    /// Bounds of the memory one input of a function with pointer, slice or
    /// aggregate parameters is built from.
    pub harness_limits: HarnessLimits,
    /// Interpreter steps the differential may spend on one module; past it a
    /// rewrite is checked by its witness alone and the shortfall is counted.
    pub module_step_budget: u64,
    /// The most blocks a function of an optimized module may have. A module
    /// with a larger function is left unchanged: the caller re-validates the
    /// whole optimized module, and trust-ir's validator is superlinear in a
    /// function's dominator tree.
    pub max_function_blocks: usize,
    /// Whether constant-table promotion and the CRC-table rewrite run. They
    /// are the passes that add to a module's static data (a read-only global
    /// per promoted table, and per distinct CRC table), so a caller whose
    /// memory layout cannot take more static data (a fixed page count whose
    /// stack the data would come out of, or a host-reserved region the data
    /// would overrun) switches them off; the report then names both in
    /// [`IrmidReport::passes_withheld`].
    pub promote_constant_tables: bool,
    /// Whether the inliner runs. Its splices copy a callee's body, findings
    /// of trust-ir's validator included, so a caller that refuses an output
    /// with a finding kind more often than its input re-runs the mid-end
    /// with this off; the report then names it in
    /// [`IrmidReport::passes_withheld`].
    pub inline: bool,
    /// Whether argument promotion runs, and by-address cloning with it.
    /// They are the passes that append functions (clones of callees with
    /// promoted parameters, or array parameters taken by address), whose
    /// bodies copy their callees', validation findings included, so a
    /// caller that refuses an output with a new finding re-runs the mid-end
    /// with this off; the report then names both in
    /// [`IrmidReport::passes_withheld`].
    pub arg_promotion: bool,
    /// Whether the loop passes run (closed-form induction, full and
    /// interval-bounded unrolling, invariant code motion, strength
    /// reduction) with block merging, field-access lowering and the
    /// select-branch rules, the passes that copy instructions, move them to
    /// another block or give a result a new type. A copied or moved
    /// instruction carries its validation findings into a new place, and a
    /// retyped result can make a use's finding appear, so a caller that
    /// refuses an output with a new finding may re-run the mid-end with
    /// this off; the report then names them in
    /// [`IrmidReport::passes_withheld`] (key `loop_passes`).
    pub loop_passes: bool,
    /// Link symbols of the callees argument promotion and by-address
    /// cloning never clone: a caller that refuses an output with a new
    /// validation finding in a clone, or in a function calling one, re-runs
    /// the mid-end with their callees here before it withdraws the passes.
    pub no_arg_promotion: BTreeSet<String>,
    /// Link symbols of the functions the inliner never splices: the
    /// producer's side table (the rustc bridge fills it with the
    /// `#[inline(never)]` and `#[cold]` items from rustc's codegen
    /// attributes; trust-ir has no inline-hint field and the bridge sets no
    /// `cold` attribute). A call of one stays a call.
    pub never_inline: BTreeSet<String>,
}

impl MidConfig {
    /// The wasm32 profile's defaults.
    pub fn wasm32() -> Self {
        Self {
            profile: MidProfile::Wasm32,
            samples_per_function: 8,
            differential: DifferentialBudget::default(),
            harness_limits: HarnessLimits::default(),
            module_step_budget: 4_000_000,
            max_function_blocks: 4096,
            promote_constant_tables: true,
            inline: true,
            arg_promotion: true,
            loop_passes: true,
            no_arg_promotion: BTreeSet::new(),
            never_inline: BTreeSet::new(),
        }
    }
}

/// Optimize `module` under `config`. The returned module differs from the
/// input only in function bodies (and the debug names of removed values),
/// in the read-only globals (with a `u8` type when the module has none)
/// that constant-table promotion appends, and in the functions (with their
/// signatures) that argument promotion appends after the input's: strong
/// hidden clones under crate-private names no other object defines.
pub fn optimize_module(module: &Module, config: &MidConfig) -> (Module, IrmidReport) {
    match config.profile {
        MidProfile::Native => {
            let report = IrmidReport::not_run(
                config.profile,
                "the native profile is reserved: no native lane calls the mid-end yet",
            );
            (module.clone(), report)
        }
        MidProfile::Wasm32 => {
            if module.pointer_bits() != 32 {
                let report = IrmidReport::not_run(
                    config.profile,
                    "the wasm32 profile needs a module with 32-bit pointers",
                );
                return (module.clone(), report);
            }
            // A declared closure frame (trust-ir v58 `Module.closure_layouts`)
            // gives `Ty::Closure` a byte size in trust-ir's layout engine,
            // which every pass here reads as plain bytes; no pass models a
            // closure environment. The lanes' shared floor refuses such a
            // module before the mid-end (OD-145); this barrier keeps a direct
            // caller from rewriting one.
            if !module.closure_layouts.is_empty() {
                let report = IrmidReport::not_run(
                    config.profile,
                    format!(
                        "the module declares {} closure layout(s) (trust-ir v58 \
                         `Module.closure_layouts`); no pass models a closure environment",
                        module.closure_layouts.len()
                    ),
                );
                return (module.clone(), report);
            }
            if let Some(func) = module
                .functions
                .iter()
                .find(|f| f.blocks.len() > config.max_function_blocks)
            {
                let report = IrmidReport::not_run(
                    config.profile,
                    format!(
                        "function `{}` has {} blocks, over the mid-end's budget of {}",
                        func.name,
                        func.blocks.len(),
                        config.max_function_blocks
                    ),
                );
                return (module.clone(), report);
            }
            let pipeline = passes::wasm32_pipeline(&config.never_inline, &config.no_arg_promotion);
            let passes: Vec<&dyn passes::MidPass> = pipeline
                .iter()
                .map(|p| p.as_ref())
                .filter(|p| {
                    config.promote_constant_tables
                        || (p.name() != passes::CTP_NAME && p.name() != passes::CRC_TABLE_NAME)
                })
                .filter(|p| config.inline || p.name() != passes::INLINE_NAME)
                .filter(|p| {
                    config.arg_promotion
                        || (p.name() != passes::ARGPROMO_NAME && p.name() != passes::BYADDR_NAME)
                })
                .filter(|p| config.loop_passes || !passes::LOOP_PASS_NAMES.contains(&p.name()))
                .collect();
            let (optimized, mut report) = manager::run(module, config, &passes);
            report.passes_withheld.insert(
                passes::FILL_CALL_NAME,
                passes::FILL_CALL_WITHHELD.to_string(),
            );
            report
                .passes_withheld
                .insert(passes::MEM_CMP_NAME, passes::MEM_CMP_WITHHELD.to_string());
            if !config.promote_constant_tables {
                report
                    .passes_withheld
                    .insert(passes::CTP_NAME, "switched off by the caller".to_string());
                report.passes_withheld.insert(
                    passes::CRC_TABLE_NAME,
                    "switched off by the caller".to_string(),
                );
            }
            if !config.inline {
                report.passes_withheld.insert(
                    passes::INLINE_NAME,
                    "switched off by the caller".to_string(),
                );
            }
            if !config.arg_promotion {
                report.passes_withheld.insert(
                    passes::ARGPROMO_NAME,
                    "switched off by the caller".to_string(),
                );
                report.passes_withheld.insert(
                    passes::BYADDR_NAME,
                    "switched off with argument promotion by the caller".to_string(),
                );
            }
            if !config.loop_passes {
                report
                    .passes_withheld
                    .insert("loop_passes", "switched off by the caller".to_string());
            }
            (optimized, report)
        }
    }
}

#[cfg(test)]
mod argpromo_tests;
#[cfg(test)]
mod call_aggregate_tests;
#[cfg(test)]
mod fill_copy_tests;
#[cfg(test)]
mod loop_tests;
#[cfg(test)]
mod mem_call_tests;
#[cfg(test)]
mod outlier_tests;
#[cfg(test)]
mod range_tests;
#[cfg(test)]
mod sroa_bool_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod unroll_tests;
