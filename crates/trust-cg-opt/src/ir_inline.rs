// trust-cg-opt - Shared trust-ir-level (LIR) function inlining (OPT-4)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared, pre-target-dispatch function inlining for the Trust-CG LIR.
//!
//! This pass runs at the SHARED `translate_module_for_arch` seam inside the
//! Compiler (`compiler.rs`), on the `Vec<(Function, ProofContext)>` the adapter
//! produced, BEFORE the per-target ISel dispatch (x86-64 / aarch64 / riscv64).
//! Because it mutates the trust-ir-level LIR and everything downstream is
//! unchanged, every existing per-instruction lowering proof and every TV gate
//! (TV-2/TV-3/TV-4) re-validates the INLINED result — the substitution is not
//! trusted, it is re-checked by the same machinery that checks any LIR.
//!
//! # Why this is the shared seam (OPT-4, roadmap §6)
//!
//! x86 has no target-specific inliner; the aarch64 machine-level inliner
//! (`inline.rs`) is a single-block `MachFunction` fallback. Implementing
//! inlining once here pays all three backends from one investment.
//!
//! # Conservative policy (two fail-safe tiers)
//!
//! The straight-line tier inlines a direct `Call { name }` to callee `C` iff
//! ALL hold:
//!   * `C` has exactly ONE basic block, terminated by `Return` (single-return);
//!   * every non-terminator instruction in `C` is a PURE, trap-free, memory-free
//!     scalar value op on the allowlist (`is_pure_inlinable_opcode`) — so `C`
//!     is a LEAF (contains no calls) and CANNOT be recursive or reach any cycle;
//!   * `C`'s parameters and returns are all "safe scalar" types
//!     (`I8/I16/I32/I64/B1/F32/F64` — no `I128`/`V128`/aggregates);
//!   * the call site's arg/result arity matches `C`'s params/returns exactly
//!     (matching-calling-convention, by-value scalar only);
//!   * `C.name != caller.name` (belt-and-suspenders self-recursion guard).
//!
//! The CFG-splicing tier admits a separately checked class of small multi-block
//! callees: safe-scalar signatures; no EH, stack slots, or discharge-bearing
//! proof carriers; no calls to functions defined in the same module; bounded
//! blocks/instructions; and a well-formed CFG with at least one return. It may
//! clone branches, loops, memory operations, and calls to external symbols.
//! See “Multi-block (CFG-splicing) inlining — OPT-4b” below for the complete
//! eligibility and splice contract.
//!
//! # Soundness (this is a trust-ir -> trust-ir TRANSFORM the per-inst proofs
//! do not cover directly)
//!
//! The single-block substitution is a value renaming + straight-line splice:
//!   1. Fresh-rename every callee value into the caller's value space (params
//!      map to the call's argument values; everything else to a fresh id).
//!   2. Splice the renamed callee body (minus its trailing `Return`) in place of
//!      the `Call` instruction, preserving effect ORDER (the body sits exactly
//!      where the call was).
//!   3. Wire each `Return` value to the corresponding call RESULT with an
//!      explicit `Copy`, so downstream caller uses stay defined.
//!      That tier leaves the caller CFG byte-identical. The multi-block tier instead
//!      fresh-renames every callee value and block, splits the call-site block, clones
//!      the callee CFG verbatim, and joins every return through a fresh continuation.
//!      It independently checks the resulting CFG, value freshness, and instruction
//!      conservation before the Compiler may continue.
//!
//! ## Structural self-check (fail-closed)
//!
//! After straight-line inlining, `verify_opcode_conservation` recomputes the
//! expected opcode multiset. The multi-block tier applies the analogous
//! block-id-agnostic multiset check plus CFG well-formedness and fresh-value
//! uniqueness checks. Any dropped/duplicated instruction, dangling edge, or
//! value collision fails the compile CLOSED ([`InlineError`]) rather than
//! emitting an unvalidated substitution.
//!
//! ## ProofContext (roadmap OPT-4 correction + soundness note #328)
//!
//! Each function keeps its OWN `ProofContext` (per-function pairing preserved).
//! Callee-synthesized `Discharged` obligation ids are NEVER merged into the
//! caller's context (that could alias ids across functions and authorize the
//! wrong elimination). The straight-line tier contains no guard carriers. The
//! multi-block tier rejects every carrier with `obligation: Some(_)`; an
//! obligation-free carrier may be cloned because the Certified-Elimination
//! Kernel must keep it as a runtime check. The caller's proof context remains
//! untouched. Any proof facts that lived on callee values are absent for fresh
//! caller values, so downstream guard elimination is at worst more conservative.
//!
//! Kill switch: `TCG_NO_INLINE` (also honors
//! `TRUST_CG_DISABLE_PASSES=irinline`). `TCG_NO_MB_INLINE` (or
//! `TRUST_CG_DISABLE_PASSES=mbinline`) disables only the CFG-splicing tier. Set
//! `TCG_INLINE_STATS` for a one-line stderr report of how many sites were
//! inlined.

use std::collections::HashMap;

use trust_cg_ir::{SourceLoc, TrustIrInstId};
use trust_cg_lower::ProofContext;
use trust_cg_lower::function::{BasicBlock, Function};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type;

/// Maximum callee (non-terminator) instruction count to consider for inlining.
/// Mirrors the aarch64 machine-level inliner's hot-callsite ceiling.
const MAX_CALLEE_INSTS: usize = 32;

/// Maximum TOTAL instruction count (across all blocks, terminators included) of a
/// MULTI-BLOCK callee considered for CFG-splicing inline (OPT-4b). Bounds compile
/// time and code-size growth; a call site whose caller would exceed
/// [`MAX_FUNCTION_INSTS`] is skipped regardless. Sized to admit the small
/// Default cap on the TOTAL instruction count (all blocks, terminators included)
/// of a multi-block callee. Kept CONSERVATIVE: on the clang-`-O1` corpus the
/// residual callees are already-optimized loop/kernel bodies, and inlining the
/// large ones (advance≈137, sort/tower helpers) perturbs register allocation and
/// block layout enough to REGRESS exec (measured: Towers +24%, Bubblesort +4%),
/// with no offsetting win — the backend's gap on these is codegen, not call
/// overhead. A small cap fires on genuinely small multi-block helpers (minimal
/// code growth) while staying clear of the regressions. Override for
/// experimentation with `TCG_MB_MAX_INSTS` (correctness is validated up to 160+).
const MAX_MB_CALLEE_INSTS_DEFAULT: usize = 40;

/// Effective multi-block callee instruction budget (env-overridable).
fn max_mb_callee_insts() -> usize {
    std::env::var("TCG_MB_MAX_INSTS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(MAX_MB_CALLEE_INSTS_DEFAULT)
}

/// Maximum basic-block count of a multi-block callee considered for inlining.
const MAX_MB_CALLEE_BLOCKS: usize = 32;

/// Cap on whole-module fixpoint rounds. Each round only inlines LEAF callees, so
/// a call chain of depth D collapses in D rounds (a leaf becomes a fresh leaf
/// once its own leaf callee is inlined); the cap bounds pathological growth.
const MAX_ROUNDS: usize = 16;

/// Absolute per-function instruction ceiling. A caller that has grown past this
/// stops accepting further inlines (compile-time + code-size guard).
const MAX_FUNCTION_INSTS: usize = 20_000;

/// Fail-closed error from the inliner's structural self-check. Mapped by the
/// Compiler to a `CompileError`, so a self-check violation fails the compile
/// rather than emitting an unvalidated substitution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlineError {
    pub detail: String,
}

impl std::fmt::Display for InlineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.detail)
    }
}

impl std::error::Error for InlineError {}

/// True when inlining is disabled by env (`TCG_NO_INLINE`, or
/// `TRUST_CG_DISABLE_PASSES=irinline`).
fn inlining_disabled() -> bool {
    if std::env::var_os("TCG_NO_INLINE").is_some() {
        return true;
    }
    crate::env_lock::var("TRUST_CG_DISABLE_PASSES")
        .map(|v| v.split(',').any(|p| p.trim() == "irinline"))
        .unwrap_or(false)
}

/// True when the MULTI-BLOCK (CFG-splicing) inline tier is disabled, while the
/// single-block straight-line tier remains active. Set `TCG_NO_MB_INLINE` (or
/// `TRUST_CG_DISABLE_PASSES=mbinline`) to fall back to single-block-only inlining
/// without disabling the whole pass. The single-block kill switches
/// (`TCG_NO_INLINE`) disable BOTH tiers.
fn multiblock_disabled() -> bool {
    if std::env::var_os("TCG_NO_MB_INLINE").is_some() {
        return true;
    }
    crate::env_lock::var("TRUST_CG_DISABLE_PASSES")
        .map(|v| v.split(',').any(|p| p.trim() == "mbinline"))
        .unwrap_or(false)
}

/// Safe-scalar type set for v1 params/returns and inlined value types. Excludes
/// `I128`/`V128` (register-pair / lane hazards) and aggregates (ABI shape).
fn is_safe_scalar_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::B1 | Type::F32 | Type::F64
    )
}

/// Allowlist of PURE, trap-free, memory-free, control-flow-free scalar value
/// opcodes whose RESULT type is exactly determinable. Any opcode NOT on this
/// list (memory, calls, guards, div/rem, control flow, vectors, i128
/// materializers, bitfield/select/float-convert ops deferred for v1) makes the
/// callee ineligible — fail-safe: new/unknown opcodes are never inlinable.
fn is_pure_inlinable_opcode(op: &Opcode) -> bool {
    match op {
        Opcode::Iconst { ty, .. } | Opcode::Fconst { ty, .. } => is_safe_scalar_type(ty),
        Opcode::Copy => true,
        // Width-preserving integer arithmetic / bitwise (no trap, no memory).
        Opcode::Iadd
        | Opcode::Isub
        | Opcode::Imul
        | Opcode::Ineg
        | Opcode::Bnot
        | Opcode::Band
        | Opcode::Bor
        | Opcode::Bxor
        | Opcode::BandNot
        | Opcode::BorNot
        | Opcode::Ishl
        | Opcode::Ushr
        | Opcode::Sshr => true,
        // Scalar floating-point (fdiv does not trap).
        Opcode::Fadd
        | Opcode::Fsub
        | Opcode::Fmul
        | Opcode::Fdiv
        | Opcode::Fneg
        | Opcode::Fabs
        | Opcode::Fmin
        | Opcode::Fmax => true,
        // Width-changing conversions with an explicit destination type.
        Opcode::Sextend { from_ty, to_ty } | Opcode::Uextend { from_ty, to_ty } => {
            is_safe_scalar_type(from_ty) && is_safe_scalar_type(to_ty)
        }
        Opcode::Trunc { to_ty } | Opcode::Bitcast { to_ty } => is_safe_scalar_type(to_ty),
        // Comparisons yield B1.
        Opcode::Icmp { .. } | Opcode::Fcmp { .. } => true,
        _ => false,
    }
}

/// The result type of an allowlisted opcode given its argument types, or `None`
/// if it cannot be determined exactly (then the value is left for ISel to infer,
/// exactly as in the standalone callee). Width-preserving ops take the type of
/// their first argument.
fn result_type_for(op: &Opcode, arg0_ty: Option<&Type>) -> Option<Type> {
    match op {
        Opcode::Iconst { ty, .. } | Opcode::Fconst { ty, .. } => Some(ty.clone()),
        Opcode::Sextend { to_ty, .. }
        | Opcode::Uextend { to_ty, .. }
        | Opcode::Trunc { to_ty }
        | Opcode::Bitcast { to_ty } => Some(to_ty.clone()),
        Opcode::Icmp { .. } | Opcode::Fcmp { .. } => Some(Type::B1),
        Opcode::Copy
        | Opcode::Iadd
        | Opcode::Isub
        | Opcode::Imul
        | Opcode::Ineg
        | Opcode::Bnot
        | Opcode::Band
        | Opcode::Bor
        | Opcode::Bxor
        | Opcode::BandNot
        | Opcode::BorNot
        | Opcode::Ishl
        | Opcode::Ushr
        | Opcode::Sshr
        | Opcode::Fadd
        | Opcode::Fsub
        | Opcode::Fmul
        | Opcode::Fdiv
        | Opcode::Fneg
        | Opcode::Fabs
        | Opcode::Fmin
        | Opcode::Fmax => arg0_ty.cloned(),
        _ => None,
    }
}

/// A snapshot of an eligible callee, taken at the start of a round so callers
/// can be mutated without borrow conflicts.
#[derive(Clone)]
struct CalleeTemplate {
    /// Parameter values (entry-block params), positional. Wired to call args.
    params: Vec<(Value, Type)>,
    /// Body instructions EXCLUDING the trailing `Return`.
    body: Vec<Instruction>,
    /// The trailing `Return`'s argument values (the returned values), positional.
    return_args: Vec<Value>,
    /// Signature return types, positional (used to pin wiring-copy types).
    return_types: Vec<Type>,
    /// Complete, soundly-derived type for every callee value we can determine
    /// (params + allowlisted results), so ISel resolves the inlined body's types
    /// identically to the standalone callee (no wrong `I64` fallback for narrow
    /// values).
    value_types: HashMap<Value, Type>,
}

/// Build a [`CalleeTemplate`] for `f` if it is v1-eligible as an inline target,
/// else `None` (ineligible — never inlined, fail-safe).
fn build_callee_template(f: &Function) -> Option<CalleeTemplate> {
    // Exactly one basic block.
    if f.blocks.len() != 1 {
        return None;
    }
    let bb = f.blocks.get(&f.entry_block)?;
    if bb.instructions.is_empty() {
        return None;
    }
    // Params == the single entry block's params, all safe-scalar, and matching
    // the signature arity.
    if bb.params.len() != f.signature.params.len() {
        return None;
    }
    if !bb.params.iter().all(|(_, ty)| is_safe_scalar_type(ty)) {
        return None;
    }
    // All returns safe-scalar.
    if !f.signature.returns.iter().all(is_safe_scalar_type) {
        return None;
    }

    let (last, body) = bb.instructions.split_last()?;
    // The single terminator must be `Return`; nothing else terminator-shaped.
    if last.opcode != Opcode::Return {
        return None;
    }
    if body.len() > MAX_CALLEE_INSTS {
        return None;
    }
    // Every body instruction must be a pure, allowlisted scalar value op — this
    // simultaneously guarantees LEAF (no calls => non-recursive, acyclic),
    // memory-free, trap-free, single-terminator.
    if !body
        .iter()
        .all(|inst| is_pure_inlinable_opcode(&inst.opcode))
    {
        return None;
    }
    // Return arity must match the signature.
    if last.args.len() != f.signature.returns.len() {
        return None;
    }
    if !last.results.is_empty() {
        return None;
    }

    // Derive a complete type map for the callee: params, its own recorded
    // value_types, then a forward pass over the body applying the exact
    // result-type rule.
    let mut value_types: HashMap<Value, Type> = HashMap::new();
    for (pv, ty) in &bb.params {
        value_types.insert(*pv, ty.clone());
    }
    for (v, ty) in &f.value_types {
        value_types.entry(*v).or_insert_with(|| ty.clone());
    }
    for inst in body {
        let arg0_ty = inst.args.first().and_then(|a| value_types.get(a)).cloned();
        if let Some(rty) = result_type_for(&inst.opcode, arg0_ty.as_ref())
            && let Some(r) = inst.results.first()
        {
            value_types.entry(*r).or_insert(rty);
        }
    }

    Some(CalleeTemplate {
        params: bb.params.clone(),
        body: body.to_vec(),
        return_args: last.args.clone(),
        return_types: f.signature.returns.clone(),
        value_types,
    })
}

/// Highest `Value` id referenced anywhere in `f`, or `None` if `f` has none.
fn max_value_id(f: &Function) -> Option<u32> {
    let mut hi: Option<u32> = None;
    let bump = |v: Value, hi: &mut Option<u32>| {
        *hi = Some(hi.map_or(v.0, |h| h.max(v.0)));
    };
    for bb in f.blocks.values() {
        for (pv, _) in &bb.params {
            bump(*pv, &mut hi);
        }
        for inst in &bb.instructions {
            for a in &inst.args {
                bump(*a, &mut hi);
            }
            for r in &inst.results {
                bump(*r, &mut hi);
            }
        }
    }
    for v in f.value_types.keys() {
        bump(*v, &mut hi);
    }
    for db in &f.debug_value_bindings {
        bump(db.value, &mut hi);
    }
    hi
}

/// Per-opcode multiset keyed by the opcode's `Debug` rendering (which embeds its
/// type/payload but NOT the args/results that renaming rewrites), so cloning a
/// callee instruction preserves its key exactly. Used by the fail-closed
/// self-check to prove no instruction was dropped or duplicated.
fn opcode_multiset(f: &Function) -> HashMap<String, i64> {
    let mut m: HashMap<String, i64> = HashMap::new();
    for bb in f.blocks.values() {
        for inst in &bb.instructions {
            *m.entry(format!("{:?}", inst.opcode)).or_insert(0) += 1;
        }
    }
    m
}

/// Statistics for a module inlining run.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct InlineStats {
    /// Number of call sites replaced by an inlined body.
    pub sites: usize,
    /// Number of fixpoint rounds executed.
    pub rounds: usize,
}

/// Run shared trust-ir-level inlining over the module's LIR functions in place.
///
/// Returns [`InlineStats`], or [`InlineError`] if the fail-closed structural
/// self-check detected a dropped/duplicated instruction (the Compiler maps this
/// to a `CompileError` — fail-closed, never emit).
pub fn inline_module(funcs: &mut [(Function, ProofContext)]) -> Result<InlineStats, InlineError> {
    run_inline_cfg(funcs, inlining_disabled(), multiblock_disabled())
}

/// Core driver with an explicit `disabled` flag (so unit tests never mutate the
/// process-global env, which would race under parallel test execution). The
/// single-block unit tests drive this entry with the multi-block tier off.
#[cfg(test)]
fn run_inline(
    funcs: &mut [(Function, ProofContext)],
    disabled: bool,
) -> Result<InlineStats, InlineError> {
    run_inline_cfg(funcs, disabled, true)
}

/// Core driver with explicit `disabled` (whole pass) and `mb_disabled`
/// (multi-block tier only) flags.
fn run_inline_cfg(
    funcs: &mut [(Function, ProofContext)],
    disabled: bool,
    mb_disabled: bool,
) -> Result<InlineStats, InlineError> {
    let mut stats = InlineStats::default();
    if disabled || funcs.is_empty() {
        return Ok(stats);
    }

    // Names of every function DEFINED in this module — the leaf / non-recursion
    // gate for multi-block templates (a callee may call external symbols only).
    let defined_names: std::collections::HashSet<String> =
        funcs.iter().map(|(f, _)| f.name.clone()).collect();

    for _round in 0..MAX_ROUNDS {
        // Snapshot eligible callees (by name) BEFORE mutating any caller this
        // round, so inlining is consistent regardless of processing order. A
        // callee is either a single-block straight-line template OR a
        // multi-block CFG-splice template (never both — routed by block count).
        let mut templates: HashMap<String, CalleeTemplate> = HashMap::new();
        let mut mb_templates: HashMap<String, MultiBlockTemplate> = HashMap::new();
        for (f, _) in funcs.iter() {
            if let Some(t) = build_callee_template(f) {
                templates.insert(f.name.clone(), t);
            } else if !mb_disabled && let Some(mb) = build_multiblock_template(f, &defined_names) {
                mb_templates.insert(f.name.clone(), mb);
            }
        }
        if templates.is_empty() && mb_templates.is_empty() {
            break;
        }

        let mut round_sites = 0usize;
        for (f, _) in funcs.iter_mut() {
            // Single-block straight-line splice first (no CFG change), then the
            // multi-block CFG splice, so a caller collapses both tiers per round.
            round_sites += inline_into_function(f, &templates)?;
            if !mb_disabled {
                round_sites += inline_multiblock_into_function(f, &mb_templates)?;
            }
        }
        stats.rounds += 1;
        stats.sites += round_sites;
        if round_sites == 0 {
            break;
        }
    }

    if std::env::var_os("TCG_INLINE_STATS").is_some() {
        eprintln!(
            "ir-inline: {} site(s) inlined across {} round(s)",
            stats.sites, stats.rounds
        );
    }
    Ok(stats)
}

/// Inline every eligible call in `caller`. Returns the number of sites inlined.
fn inline_into_function(
    caller: &mut Function,
    templates: &HashMap<String, CalleeTemplate>,
) -> Result<usize, InlineError> {
    // Cheap pre-scan: does this caller have ANY eligible call? Avoids the
    // multiset snapshot for the common no-op case.
    let has_candidate = caller.blocks.values().any(|bb| {
        bb.instructions.iter().any(|inst| match &inst.opcode {
            Opcode::Call { name } => templates.contains_key(name) && *name != caller.name,
            _ => false,
        })
    });
    if !has_candidate {
        return Ok(0);
    }

    // Expected per-opcode multiset, adjusted as we splice, for the self-check.
    let mut expected = opcode_multiset(caller);
    let adj = |m: &mut HashMap<String, i64>, key: String, delta: i64| {
        *m.entry(key).or_insert(0) += delta;
    };

    // Running fresh-value allocator (unique across all sites in this caller).
    let mut next_value = max_value_id(caller).map_or(0, |h| h + 1);
    let mut freshly_allocated: Vec<u32> = Vec::new();
    let fresh_base = next_value;

    let mut sites = 0usize;
    let mut total_insts: usize = caller.blocks.values().map(|b| b.instructions.len()).sum();

    // New value_types entries to commit after the block walk (avoid borrowing
    // caller.value_types while iterating blocks).
    let mut new_value_types: HashMap<Value, Type> = HashMap::new();

    let block_ids: Vec<Block> = caller.blocks.keys().copied().collect();
    for block_id in block_ids {
        // Snapshot the block's current instructions / provenance, then rebuild.
        let (orig_insts, orig_locs) = {
            let bb = caller.blocks.get(&block_id).expect("block present");
            (bb.instructions.clone(), bb.source_locs.clone())
        };
        let orig_origins: Vec<Option<TrustIrInstId>> = caller
            .trust_ir_origins
            .get(&block_id)
            .cloned()
            .unwrap_or_default();

        let mut changed = false;
        let mut new_insts: Vec<Instruction> = Vec::with_capacity(orig_insts.len());
        let mut new_locs: Vec<Option<SourceLoc>> = Vec::with_capacity(orig_insts.len());
        let mut new_origins: Vec<Option<TrustIrInstId>> = Vec::with_capacity(orig_insts.len());

        for (i, inst) in orig_insts.iter().enumerate() {
            let site_loc = orig_locs.get(i).copied().flatten();

            let callee_name = match &inst.opcode {
                Opcode::Call { name } if templates.contains_key(name) && *name != caller.name => {
                    Some(name.clone())
                }
                _ => None,
            };

            let Some(name) = callee_name else {
                // Keep the instruction unchanged, preserving its provenance.
                new_insts.push(inst.clone());
                new_locs.push(site_loc);
                new_origins.push(orig_origins.get(i).copied().flatten());
                continue;
            };

            let template = &templates[&name];

            // Per-call eligibility: arity match (by-value scalar, matching CC).
            if inst.args.len() != template.params.len()
                || inst.results.len() != template.return_types.len()
                || total_insts + template.body.len() + inst.results.len() > MAX_FUNCTION_INSTS
            {
                new_insts.push(inst.clone());
                new_locs.push(site_loc);
                new_origins.push(orig_origins.get(i).copied().flatten());
                continue;
            }

            // Type-pin each argument to the callee's declared param type (the
            // argument's true type by well-typedness). Skip the inline on a
            // hard type conflict with an existing caller entry (fail-safe).
            let mut arg_conflict = false;
            for (arg, (_, pty)) in inst.args.iter().zip(template.params.iter()) {
                match caller
                    .value_types
                    .get(arg)
                    .or_else(|| new_value_types.get(arg))
                {
                    Some(existing) if existing != pty => {
                        arg_conflict = true;
                        break;
                    }
                    _ => {}
                }
            }
            if arg_conflict {
                new_insts.push(inst.clone());
                new_locs.push(site_loc);
                new_origins.push(orig_origins.get(i).copied().flatten());
                continue;
            }

            // ---- Eligible: build the rename map and splice. ----
            // params -> call args; every other callee value -> a fresh id.
            let mut rename: HashMap<Value, Value> = HashMap::new();
            for ((pv, _), arg) in template.params.iter().zip(inst.args.iter()) {
                rename.insert(*pv, *arg);
            }
            // Pre-allocate fresh ids for every callee-defined result.
            for cinst in &template.body {
                for r in &cinst.results {
                    rename.entry(*r).or_insert_with(|| {
                        let v = Value(next_value);
                        next_value += 1;
                        freshly_allocated.push(v.0);
                        v
                    });
                }
            }

            // Every callee arg must resolve through the rename map (single-block
            // SSA dominance guarantees this); a missing one means an external /
            // undefined reference — bail out and keep the call (fail-safe).
            let mut unresolved = false;
            let remap =
                |v: &Value, rename: &HashMap<Value, Value>, unresolved: &mut bool| -> Value {
                    match rename.get(v) {
                        Some(mapped) => *mapped,
                        None => {
                            *unresolved = true;
                            *v
                        }
                    }
                };
            let mut spliced: Vec<Instruction> = Vec::with_capacity(template.body.len());
            for cinst in &template.body {
                let args = cinst
                    .args
                    .iter()
                    .map(|a| remap(a, &rename, &mut unresolved))
                    .collect::<Vec<_>>();
                let results = cinst
                    .results
                    .iter()
                    .map(|r| remap(r, &rename, &mut unresolved))
                    .collect::<Vec<_>>();
                spliced.push(Instruction {
                    opcode: cinst.opcode.clone(),
                    args,
                    results,
                });
            }
            if unresolved {
                new_insts.push(inst.clone());
                new_locs.push(site_loc);
                new_origins.push(orig_origins.get(i).copied().flatten());
                continue;
            }

            // Pin the argument types now that we are committing this inline.
            for (arg, (_, pty)) in inst.args.iter().zip(template.params.iter()) {
                if !caller.value_types.contains_key(arg) {
                    new_value_types.entry(*arg).or_insert_with(|| pty.clone());
                }
            }
            // Pin every fresh value's type from the callee's derived type map.
            for (cv, mapped) in &rename {
                if mapped.0 >= fresh_base
                    && let Some(ty) = template.value_types.get(cv)
                {
                    new_value_types.entry(*mapped).or_insert_with(|| ty.clone());
                }
            }

            // Commit the spliced body (straight-line, in the call's position).
            for s in spliced {
                adj(&mut expected, format!("{:?}", s.opcode), 1);
                new_insts.push(s);
                new_locs.push(site_loc);
                new_origins.push(None);
            }
            // Wire returns -> call results via explicit Copy, pinning types.
            for (ret_arg, (result, rty)) in template
                .return_args
                .iter()
                .zip(inst.results.iter().zip(template.return_types.iter()))
            {
                let src = rename.get(ret_arg).copied().unwrap_or(*ret_arg);
                new_value_types.entry(src).or_insert_with(|| rty.clone());
                new_value_types
                    .entry(*result)
                    .or_insert_with(|| rty.clone());
                let copy = Instruction {
                    opcode: Opcode::Copy,
                    args: vec![src],
                    results: vec![*result],
                };
                adj(&mut expected, format!("{:?}", copy.opcode), 1);
                new_insts.push(copy);
                new_locs.push(site_loc);
                new_origins.push(None);
            }

            // Account the removed Call in the expected multiset.
            adj(&mut expected, format!("{:?}", inst.opcode), -1);

            total_insts = total_insts + template.body.len() + inst.results.len() - 1;
            sites += 1;
            changed = true;
        }

        if changed {
            let bb = caller.blocks.get_mut(&block_id).expect("block present");
            bb.instructions = new_insts;
            bb.source_locs = new_locs;
            caller.trust_ir_origins.insert(block_id, new_origins);
        }
    }

    if sites == 0 {
        return Ok(0);
    }

    // Commit pinned value types.
    for (v, ty) in new_value_types {
        caller.value_types.entry(v).or_insert(ty);
    }

    // Fresh-value uniqueness self-check (vreg freshness).
    let mut seen = std::collections::HashSet::new();
    for v in &freshly_allocated {
        if *v < fresh_base || !seen.insert(*v) {
            return Err(InlineError {
                detail: format!(
                    "inliner allocated a non-fresh/duplicate value id {v} (base {fresh_base}) in `{}`",
                    caller.name
                ),
            });
        }
    }

    // Structural fail-closed self-check: opcode multiset conservation.
    verify_opcode_conservation(caller, &expected)?;

    Ok(sites)
}

/// Assert that the caller's post-inline opcode multiset equals the expected
/// multiset `caller ⊎ renamed-callee-bodies ⊎ wiring-copies − removed-calls`.
/// Any drop/dup fails the compile CLOSED.
fn verify_opcode_conservation(
    caller: &Function,
    expected: &HashMap<String, i64>,
) -> Result<(), InlineError> {
    let actual = opcode_multiset(caller);
    // Compare in both directions (a key present in one but not the other, or a
    // count mismatch, is a violation).
    let mut keys: std::collections::HashSet<&String> = actual.keys().collect();
    keys.extend(expected.keys());
    for key in keys {
        let a = actual.get(key).copied().unwrap_or(0);
        let e = expected.get(key).copied().unwrap_or(0);
        if a != e {
            return Err(InlineError {
                detail: format!(
                    "inline self-check failed in `{}`: opcode {key} count {a} != expected {e} \
                     (an instruction was dropped or duplicated by the substitution)",
                    caller.name
                ),
            });
        }
    }
    Ok(())
}

// ===========================================================================
// Multi-block (CFG-splicing) inlining — OPT-4b
// ===========================================================================
//
// Extends the single-block straight-line splice above to callees with control
// flow (branches, loops, multiple returns) and memory. The transform is a
// structure-preserving CLONE of the callee's blocks into the caller:
//
//   * every callee VALUE and BLOCK id is fresh-renamed into the caller's space;
//   * the caller block holding the `Call` is SPLIT at the call: the instructions
//     BEFORE the call plus a `Jump` to the entry clone become the `pre` block
//     (it keeps the original block id, params, and predecessors); the
//     instructions AFTER the call move into a fresh `cont` block;
//   * each callee `Return v_j` becomes `Copy result_j <- v_j ; Jump cont`, so the
//     call's result values are `cont`'s block PARAMS, filled by copies in every
//     returning predecessor — exactly the LIR's conventional-SSA block-argument
//     protocol (a `Copy` in each predecessor; `Jump`/`Brif` carry no args). A
//     multi-return callee therefore joins naturally at `cont`.
//
// The callee CFG (including loops/back-edges) is cloned verbatim under the block
// rename, so its shape is identical to the standalone callee the bridge already
// validated. Downstream ISel consumes `Function::layout_order()` (RPO from the
// entry), so any well-formed reachable CFG lays out correctly without trusting
// `block_order`. Soundness of the SUBSTITUTION rests on this pass: a fail-closed
// self-check (block-id-agnostic opcode-multiset conservation + CFG
// well-formedness + fresh-value uniqueness) rejects any drop/dup/dangling-edge
// CLOSED, and the always-on differential torture sweep is the empirical backstop.
//
// Eligibility (fail-safe — anything unrecognized is NOT inlined):
//   * 2..=MAX_MB_CALLEE_BLOCKS blocks, <= max_mb_callee_insts() total insts;
//   * LEAF w.r.t. the in-module call graph: no calls to DEFINED functions and no
//     indirect/variadic-to-defined/Invoke anywhere (=> non-recursive, acyclic;
//     external/libc calls are allowed and cloned verbatim),
//     acyclic call graph; chains still collapse across rounds, bottom-up);
//   * no EH (Invoke/LandingPad/Resume, or non-empty eh_info), no stack slots
//     (`StackAddr` / non-empty `stack_slots` — avoids slot-index renumbering), no
//     proof-carrier guards / asserts (keeps callee ProofContext obligation ids
//     from ever aliasing into the caller's context);
//   * params + returns all safe-scalar (I8/I16/I32/I64/B1/F32/F64 — I64 covers
//     pointers; excludes I128/V128/aggregates/sret-by-value);
//   * every block ends in exactly one terminator (Jump/Brif/Switch/Return/Trap)
//     and >=1 block ends in `Return` (no noreturn callees);
//   * the entry block is NOT re-entered (no predecessor / not a loop header), so
//     its params are pure formals, substituted directly to the call arguments.

/// Integer (or bool) byte width, or `None` for non-integer types.
fn int_byte_width(t: &Type) -> Option<u32> {
    match t {
        Type::B1 | Type::I8 => Some(1),
        Type::I16 => Some(2),
        Type::I32 => Some(4),
        Type::I64 => Some(8),
        _ => None,
    }
}

/// True when `wide` is a STRICTLY wider integer type than `narrow` (both scalar
/// integers). Used to detect an ABI-widened callee return value that must be
/// truncated to the caller's logical result type.
fn int_strictly_wider(wide: &Type, narrow: &Type) -> bool {
    matches!((int_byte_width(wide), int_byte_width(narrow)), (Some(w), Some(n)) if w > n)
}

/// A callee terminator opcode (the last, and only-last, instruction of a block).
fn is_mb_terminator(op: &Opcode) -> bool {
    matches!(
        op,
        Opcode::Jump { .. }
            | Opcode::Brif { .. }
            | Opcode::Switch { .. }
            | Opcode::Return
            | Opcode::Trap
    )
}

/// Opcodes that make a callee ineligible for multi-block inlining regardless of
/// the call graph (EH, indirect/variadic calls, stack slots, discharge-bearing
/// proof carriers). Everything else — arithmetic, bitwise, shifts, float,
/// compares, converts, consts, loads/stores/atomics, `Assert`, obligation-free
/// guards, direct calls (handled separately by [`mb_call_to_defined`]), and the
/// accepted terminators — is inlinable. Fail-safe by construction.
fn is_mb_forbidden(op: &Opcode) -> bool {
    match op {
        Opcode::CallIndirect
        | Opcode::Invoke { .. }
        | Opcode::LandingPad { .. }
        | Opcode::Resume
        | Opcode::StackAddr { .. } => true,
        // Proof-carrier guards clone SOUNDLY only when they carry NO discharge
        // obligation id. `obligation: None` => the Certified-Elimination Kernel
        // ALWAYS KEEPS the guard (fail-safe), so the cloned instruction is a
        // faithful runtime check that cannot consult — or alias — the caller's
        // ProofContext. A `Some(id)` guard could alias a caller-discharged id and
        // authorize a WRONG elimination (roadmap OPT-4 soundness note), so reject
        // it.
        Opcode::GuardDivZero { obligation }
        | Opcode::GuardNull { obligation }
        | Opcode::GuardShiftRange { obligation, .. }
        | Opcode::GuardOverflow { obligation, .. }
        | Opcode::GuardBoundsCheck { obligation, .. } => obligation.is_some(),
        _ => false,
    }
}

/// True when `op` is a DIRECT (fixed or variadic) call to a function DEFINED in
/// this module. Such a call keeps the callee non-leaf w.r.t. the in-module call
/// graph, so admitting it could inline a recursive/cyclic body — reject. A direct
/// call to an EXTERNAL symbol (libc: `printf`/`sqrt`/`memcpy`/…) is opaque and
/// cannot form an in-module inline cycle, so it is allowed and cloned verbatim
/// (the variadic ABI is carried on the opcode and re-lowered identically).
fn mb_call_to_defined(op: &Opcode, defined: &std::collections::HashSet<String>) -> bool {
    match op {
        Opcode::Call { name } | Opcode::CallVariadic { name, .. } => defined.contains(name),
        _ => false,
    }
}

/// Block-id- and call-name-agnostic opcode key for the multi-block self-check.
/// Block-target-bearing terminators and calls are keyed by their variant name
/// only, so the block/value RENAMING the splice performs preserves the key;
/// count conservation still catches any dropped or duplicated instruction. The
/// separate CFG-well-formedness check catches a mis-wired edge.
fn mb_opcode_key(op: &Opcode) -> String {
    match op {
        Opcode::Jump { .. } => "Jump".to_string(),
        Opcode::Brif { .. } => "Brif".to_string(),
        Opcode::Switch { .. } => "Switch".to_string(),
        Opcode::Invoke { .. } => "Invoke".to_string(),
        Opcode::Call { .. } => "Call".to_string(),
        Opcode::CallVariadic { .. } => "CallVariadic".to_string(),
        other => format!("{other:?}"),
    }
}

fn mb_opcode_multiset(f: &Function) -> HashMap<String, i64> {
    let mut m: HashMap<String, i64> = HashMap::new();
    for bb in f.blocks.values() {
        for inst in &bb.instructions {
            *m.entry(mb_opcode_key(&inst.opcode)).or_insert(0) += 1;
        }
    }
    m
}

/// Highest block id in `f`, or 0 if it has none.
fn max_block_id(f: &Function) -> u32 {
    f.blocks.keys().map(|b| b.0).max().unwrap_or(0)
}

/// A snapshot of a multi-block callee, taken before any caller is mutated.
#[derive(Clone)]
struct MultiBlockTemplate {
    /// Entry block id (its params are the function's formal parameters).
    entry: Block,
    /// Every callee block, keyed by its (callee-local) id.
    blocks: HashMap<Block, BasicBlock>,
    /// A deterministic clone order over the callee's blocks.
    block_order: Vec<Block>,
    /// Entry-block params == formal parameters, positional (wired to call args).
    params: Vec<(Value, Type)>,
    /// Signature return types, positional (pins the wiring-copy result types).
    return_types: Vec<Type>,
    /// Soundly-derived types for callee values (renamed at splice time), so ISel
    /// resolves the inlined body identically to the standalone callee.
    value_types: HashMap<Value, Type>,
    /// Total instruction count across all blocks (for the caller-growth budget).
    total_insts: usize,
}

/// Build a [`MultiBlockTemplate`] for `f` if it is eligible for CFG-splice
/// inlining, else `None` (ineligible — never inlined, fail-safe). `defined` is
/// the set of function names defined in this module (for the leaf / non-recursion
/// gate: a callee may call EXTERNAL symbols but no in-module function).
fn build_multiblock_template(
    f: &Function,
    defined: &std::collections::HashSet<String>,
) -> Option<MultiBlockTemplate> {
    let dbg = std::env::var_os("TCG_MB_DEBUG").is_some();
    macro_rules! reject {
        ($($a:tt)*) => {{
            if dbg { eprintln!("mb-reject `{}`: {}", f.name, format!($($a)*)); }
            return None;
        }};
    }
    let nblocks = f.blocks.len();
    if !(2..=MAX_MB_CALLEE_BLOCKS).contains(&nblocks) {
        reject!("block count {nblocks} out of [2,{MAX_MB_CALLEE_BLOCKS}]");
    }
    if !f.eh_info.is_empty() || !f.stack_slots.is_empty() {
        reject!("eh_info or stack_slots present");
    }

    let entry = f.entry_block;
    let entry_bb = f.blocks.get(&entry)?;
    // Entry params == the signature's formal parameters, all safe-scalar.
    if entry_bb.params.len() != f.signature.params.len()
        || !entry_bb
            .params
            .iter()
            .all(|(_, ty)| is_safe_scalar_type(ty))
        || !f.signature.returns.iter().all(is_safe_scalar_type)
    {
        reject!(
            "param/return shape: entry_params={} sig_params={} returns_safe={}",
            entry_bb.params.len(),
            f.signature.params.len(),
            f.signature.returns.iter().all(is_safe_scalar_type)
        );
    }

    // Structural scan: instruction budget, single-terminator-per-block, leaf +
    // no forbidden ops, well-formed intra-callee edges, >=1 Return, matching
    // return arity, and entry-not-re-entered.
    let mut total = 0usize;
    let mut has_return = false;
    let mut all_succs: std::collections::HashSet<Block> = std::collections::HashSet::new();
    for bb in f.blocks.values() {
        if bb.instructions.is_empty() {
            reject!("empty block");
        }
        total += bb.instructions.len();
        let last = bb.instructions.len() - 1;
        for (idx, inst) in bb.instructions.iter().enumerate() {
            if is_mb_forbidden(&inst.opcode) {
                reject!("forbidden opcode {:?}", inst.opcode);
            }
            if mb_call_to_defined(&inst.opcode, defined) {
                reject!("calls in-module function {:?}", inst.opcode);
            }
            let is_term = is_mb_terminator(&inst.opcode);
            if idx == last {
                if !is_term {
                    reject!("block does not end in a terminator ({:?})", inst.opcode);
                }
                if matches!(inst.opcode, Opcode::Return) {
                    has_return = true;
                    if inst.args.len() != f.signature.returns.len() || !inst.results.is_empty() {
                        reject!("return arity mismatch");
                    }
                }
            } else if is_term {
                reject!("mid-block terminator {:?}", inst.opcode);
            }
        }
        for s in bb.successors() {
            if !f.blocks.contains_key(&s) {
                reject!("dangling intra-callee edge -> {}", s.0);
            }
            all_succs.insert(s);
        }
    }
    let inst_budget = max_mb_callee_insts();
    if total > inst_budget {
        reject!("total insts {total} > {inst_budget}");
    }
    if !has_return {
        reject!("no Return block (noreturn)");
    }
    if all_succs.contains(&entry) {
        reject!("entry block is re-entered (loop-header entry)");
    }

    // Carry ONLY the callee's OWN authoritative type facts: the adapter-recorded
    // `value_types` (which the standalone callee's ISel already relies on — e.g.
    // #381 external-call result types) plus the declared block-param types. We do
    // NOT re-derive arithmetic result types here: a wrong local guess would PIN a
    // conflicting width and defeat ISel's own inference (which resolves the
    // inlined body identically to the standalone callee once the entry params are
    // wired to the call args). Fewer, only-authoritative pins is the safe choice.
    let mut value_types: HashMap<Value, Type> = f.value_types.clone();
    for bb in f.blocks.values() {
        for (pv, ty) in &bb.params {
            value_types.entry(*pv).or_insert_with(|| ty.clone());
        }
    }

    Some(MultiBlockTemplate {
        entry,
        blocks: f.blocks.clone(),
        block_order: ordered_blocks(f),
        params: entry_bb.params.clone(),
        return_types: f.signature.returns.clone(),
        value_types,
        total_insts: total,
    })
}

/// A deterministic block order for `f`: its recorded `block_order` if present
/// (entry forced first), else sorted block ids.
fn ordered_blocks(f: &Function) -> Vec<Block> {
    let mut order: Vec<Block> = Vec::with_capacity(f.blocks.len());
    let mut seen: std::collections::HashSet<Block> = std::collections::HashSet::new();
    if f.blocks.contains_key(&f.entry_block) {
        order.push(f.entry_block);
        seen.insert(f.entry_block);
    }
    for b in &f.block_order {
        if f.blocks.contains_key(b) && seen.insert(*b) {
            order.push(*b);
        }
    }
    let mut rest: Vec<Block> = f
        .blocks
        .keys()
        .copied()
        .filter(|b| !seen.contains(b))
        .collect();
    rest.sort_by_key(|b| b.0);
    order.extend(rest);
    order
}

/// Safe source-loc read for a parallel `source_locs` vec that may be shorter
/// than the instruction list.
fn loc_at(locs: &[Option<SourceLoc>], i: usize) -> Option<SourceLoc> {
    locs.get(i).copied().flatten()
}

/// Inline every eligible multi-block call in `caller` via CFG splice. Returns the
/// number of sites inlined, or [`InlineError`] if a fail-closed self-check trips.
fn inline_multiblock_into_function(
    caller: &mut Function,
    templates: &HashMap<String, MultiBlockTemplate>,
) -> Result<usize, InlineError> {
    if templates.is_empty() {
        return Ok(0);
    }
    let caller_name = caller.name.clone();

    // Cheap pre-scan for any eligible call.
    let has_candidate = caller.blocks.values().any(|bb| {
        bb.instructions.iter().any(|inst| match &inst.opcode {
            Opcode::Call { name } => templates.contains_key(name) && *name != caller_name,
            _ => false,
        })
    });
    if !has_candidate {
        return Ok(0);
    }

    let mut next_value = max_value_id(caller).map_or(0, |h| h + 1);
    let fresh_value_base = next_value;
    let mut next_block = max_block_id(caller) + 1;
    let mut freshly_allocated: Vec<u32> = Vec::new();

    // Expected block-id-agnostic opcode multiset, adjusted as we splice.
    let mut expected = mb_opcode_multiset(caller);

    let mut sites = 0usize;
    let mut total_insts: usize = caller.blocks.values().map(|b| b.instructions.len()).sum();
    let mut new_value_types: HashMap<Value, Type> = HashMap::new();

    // Worklist over caller blocks; splitting a block enqueues its continuation so
    // subsequent calls in the same original block are still visited.
    let mut worklist: Vec<Block> = caller.block_order.clone();
    if worklist.is_empty() {
        worklist = caller.blocks.keys().copied().collect();
    }
    let mut wi = 0usize;
    while wi < worklist.len() {
        let block_id = worklist[wi];
        wi += 1;

        // Find the first inlinable call in this block.
        let Some(bb) = caller.blocks.get(&block_id) else {
            continue;
        };
        // The block must END in a recognized terminator, so the continuation we
        // carve out after the call is itself well-formed. A block that does not
        // (malformed / fall-through input) is skipped, not spliced (fail-safe).
        let ends_in_terminator = bb.instructions.last().is_some_and(|last| {
            is_mb_terminator(&last.opcode)
                || matches!(last.opcode, Opcode::Invoke { .. } | Opcode::Resume)
        });
        let mut found: Option<(usize, String)> = None;
        if ends_in_terminator {
            for (i, inst) in bb.instructions.iter().enumerate() {
                let Opcode::Call { name } = &inst.opcode else {
                    continue;
                };
                if !templates.contains_key(name) || *name == caller_name {
                    continue;
                }
                let t = &templates[name];
                // Per-site: arity match, a terminator after the call, growth budget.
                if inst.args.len() == t.params.len()
                    && inst.results.len() == t.return_types.len()
                    && i + 1 < bb.instructions.len()
                    && total_insts + t.total_insts + inst.results.len() <= MAX_FUNCTION_INSTS
                {
                    found = Some((i, name.clone()));
                    break;
                }
            }
        }
        let Some((call_idx, name)) = found else {
            continue;
        };
        let template = &templates[&name];

        // Snapshot everything we need from the caller block, then release the
        // borrow before mutating.
        let (call_args, call_results, orig_insts, orig_locs) = {
            let bb = &caller.blocks[&block_id];
            (
                bb.instructions[call_idx].args.clone(),
                bb.instructions[call_idx].results.clone(),
                bb.instructions.clone(),
                bb.source_locs.clone(),
            )
        };
        let site_loc = loc_at(&orig_locs, call_idx);
        let orig_origins: Vec<Option<TrustIrInstId>> = caller
            .trust_ir_origins
            .get(&block_id)
            .cloned()
            .unwrap_or_default();

        // Argument type-conflict check (fail-safe).
        let mut arg_conflict = false;
        for (arg, (_, pty)) in call_args.iter().zip(template.params.iter()) {
            if let Some(existing) = caller
                .value_types
                .get(arg)
                .or_else(|| new_value_types.get(arg))
                && existing != pty
            {
                arg_conflict = true;
                break;
            }
        }
        if arg_conflict {
            continue;
        }

        // Value rename: entry params -> call args; every other callee value -> a
        // fresh id (pre-allocated in a deterministic order).
        let mut val_map: HashMap<Value, Value> = HashMap::new();
        for ((pv, _), arg) in template.params.iter().zip(call_args.iter()) {
            val_map.insert(*pv, *arg);
        }
        for cb in &template.block_order {
            let Some(bb) = template.blocks.get(cb) else {
                continue;
            };
            for (pv, _) in &bb.params {
                if !val_map.contains_key(pv) {
                    val_map.insert(*pv, Value(next_value));
                    freshly_allocated.push(next_value);
                    next_value += 1;
                }
            }
            for inst in &bb.instructions {
                for r in &inst.results {
                    if !val_map.contains_key(r) {
                        val_map.insert(*r, Value(next_value));
                        freshly_allocated.push(next_value);
                        next_value += 1;
                    }
                }
            }
        }

        // Block rename: every callee block -> a fresh caller block id.
        let mut block_map: HashMap<Block, Block> = HashMap::new();
        for cb in &template.block_order {
            block_map.entry(*cb).or_insert_with(|| {
                let nb = Block(next_block);
                next_block += 1;
                nb
            });
        }
        for cb in template.blocks.keys() {
            block_map.entry(*cb).or_insert_with(|| {
                let nb = Block(next_block);
                next_block += 1;
                nb
            });
        }
        let cont_id = Block(next_block);
        next_block += 1;

        let mut unresolved = false;
        let mut bad_edge = false;
        let mut ret_type_bail = false;

        // Clone every callee block under the value + block rename.
        let mut cloned_blocks: Vec<(Block, BasicBlock, Vec<Option<TrustIrInstId>>)> = Vec::new();
        for cb in &template.block_order {
            let Some(src_bb) = template.blocks.get(cb) else {
                continue;
            };
            let new_bid = block_map[cb];
            // Entry params were substituted to call args, so the entry clone has
            // no params; other blocks keep their (fresh-renamed) params.
            let params: Vec<(Value, Type)> = if *cb == template.entry {
                Vec::new()
            } else {
                src_bb
                    .params
                    .iter()
                    .map(|(pv, ty)| (remap_value(pv, &val_map, &mut unresolved), ty.clone()))
                    .collect()
            };

            let mut new_insts: Vec<Instruction> =
                Vec::with_capacity(src_bb.instructions.len() + call_results.len());
            for inst in &src_bb.instructions {
                if matches!(inst.opcode, Opcode::Return) {
                    // Return v_j..  ->  wire result_j <- v_j ;  Jump cont.
                    //
                    // The callee's return ARG is the value it puts in the return
                    // register, which the ABI may WIDEN past the logical return
                    // type (e.g. a `zeroext i8` callee returns an I32-extended
                    // value; a standalone caller receives it typed as the logical
                    // I8). Inlining wires the return value straight into the
                    // caller's I8 result, so when the callee's return value is a
                    // WIDER integer we must TRUNCATE it to the return type (the low
                    // bits ARE the logical value) rather than Copy — otherwise the
                    // result carries the register width and mismatches the caller's
                    // uses. Equal types Copy; an unhandleable mismatch bails.
                    for (ret_arg, (result, rty)) in inst
                        .args
                        .iter()
                        .zip(call_results.iter().zip(template.return_types.iter()))
                    {
                        let src = remap_value(ret_arg, &val_map, &mut unresolved);
                        let src_ty = template.value_types.get(ret_arg);
                        let op = match src_ty {
                            Some(vt) if vt == rty => {
                                new_value_types.entry(src).or_insert_with(|| rty.clone());
                                Opcode::Copy
                            }
                            Some(vt) if int_strictly_wider(vt, rty) => {
                                // Keep `src`'s own (wider) type; narrow into result.
                                Opcode::Trunc { to_ty: rty.clone() }
                            }
                            None => {
                                new_value_types.entry(src).or_insert_with(|| rty.clone());
                                Opcode::Copy
                            }
                            Some(_) => {
                                ret_type_bail = true;
                                Opcode::Copy
                            }
                        };
                        new_value_types
                            .entry(*result)
                            .or_insert_with(|| rty.clone());
                        let wire = Instruction {
                            opcode: op,
                            args: vec![src],
                            results: vec![*result],
                        };
                        *expected.entry(mb_opcode_key(&wire.opcode)).or_insert(0) += 1;
                        new_insts.push(wire);
                    }
                    let jmp = Instruction {
                        opcode: Opcode::Jump { dest: cont_id },
                        args: vec![],
                        results: vec![],
                    };
                    *expected.entry(mb_opcode_key(&jmp.opcode)).or_insert(0) += 1;
                    new_insts.push(jmp);
                    continue;
                }

                let opcode = match &inst.opcode {
                    Opcode::Jump { dest } => Opcode::Jump {
                        dest: remap_block(dest, &block_map, &mut bad_edge),
                    },
                    Opcode::Brif {
                        cond,
                        then_dest,
                        else_dest,
                    } => Opcode::Brif {
                        cond: remap_value(cond, &val_map, &mut unresolved),
                        then_dest: remap_block(then_dest, &block_map, &mut bad_edge),
                        else_dest: remap_block(else_dest, &block_map, &mut bad_edge),
                    },
                    Opcode::Switch { cases, default } => Opcode::Switch {
                        cases: cases
                            .iter()
                            .map(|(k, b)| (*k, remap_block(b, &block_map, &mut bad_edge)))
                            .collect(),
                        default: remap_block(default, &block_map, &mut bad_edge),
                    },
                    other => other.clone(),
                };
                let args = inst
                    .args
                    .iter()
                    .map(|a| remap_value(a, &val_map, &mut unresolved))
                    .collect::<Vec<_>>();
                let results = inst
                    .results
                    .iter()
                    .map(|r| remap_value(r, &val_map, &mut unresolved))
                    .collect::<Vec<_>>();
                let cloned = Instruction {
                    opcode,
                    args,
                    results,
                };
                *expected.entry(mb_opcode_key(&cloned.opcode)).or_insert(0) += 1;
                new_insts.push(cloned);
            }

            let origins = vec![None; new_insts.len()];
            let locs = vec![site_loc; new_insts.len()];
            cloned_blocks.push((
                new_bid,
                BasicBlock {
                    params,
                    instructions: new_insts,
                    source_locs: locs,
                },
                origins,
            ));
        }

        // A dangling edge or an undefined callee reference => bail this site
        // (fail-safe: keep the call, undo nothing since we have not mutated the
        // caller's blocks yet). The pre-allocated fresh ids simply go unused.
        if unresolved || bad_edge || ret_type_bail {
            continue;
        }

        // ---- Commit: split the caller block and install the clones. ----
        // `pre` keeps the original block id, params, and predecessors: the
        // instructions before the call, then a Jump to the entry clone.
        let entry_clone = block_map[&template.entry];
        let mut pre_insts: Vec<Instruction> = orig_insts[..call_idx].to_vec();
        let mut pre_locs: Vec<Option<SourceLoc>> =
            (0..call_idx).map(|i| loc_at(&orig_locs, i)).collect();
        let mut pre_origins: Vec<Option<TrustIrInstId>> = (0..call_idx)
            .map(|i| orig_origins.get(i).copied().flatten())
            .collect();
        let pre_jump = Instruction {
            opcode: Opcode::Jump { dest: entry_clone },
            args: vec![],
            results: vec![],
        };
        *expected.entry(mb_opcode_key(&pre_jump.opcode)).or_insert(0) += 1;
        pre_insts.push(pre_jump);
        pre_locs.push(site_loc);
        pre_origins.push(None);

        // The removed Call.
        *expected.entry("Call".to_string()).or_insert(0) -= 1;

        // `cont` gets the post-call instructions; the call results become its
        // block params, filled by the return copies in each returning clone.
        let cont_insts: Vec<Instruction> = orig_insts[call_idx + 1..].to_vec();
        let cont_locs: Vec<Option<SourceLoc>> = (call_idx + 1..orig_insts.len())
            .map(|i| loc_at(&orig_locs, i))
            .collect();
        let cont_origins: Vec<Option<TrustIrInstId>> = (call_idx + 1..orig_insts.len())
            .map(|i| orig_origins.get(i).copied().flatten())
            .collect();
        let cont_params: Vec<(Value, Type)> = call_results
            .iter()
            .zip(template.return_types.iter())
            .map(|(r, ty)| (*r, ty.clone()))
            .collect();

        // Pin types: call args -> formal types, call results -> return types,
        // renamed callee values -> derived types.
        for (arg, (_, pty)) in call_args.iter().zip(template.params.iter()) {
            if !caller.value_types.contains_key(arg) {
                new_value_types.entry(*arg).or_insert_with(|| pty.clone());
            }
        }
        for (result, rty) in call_results.iter().zip(template.return_types.iter()) {
            new_value_types
                .entry(*result)
                .or_insert_with(|| rty.clone());
        }
        for (cv, mapped) in &val_map {
            if mapped.0 >= fresh_value_base
                && let Some(ty) = template.value_types.get(cv)
            {
                new_value_types.entry(*mapped).or_insert_with(|| ty.clone());
            }
        }

        // Install pre (mutate the original block in place).
        {
            let bb = caller
                .blocks
                .get_mut(&block_id)
                .expect("caller block present");
            bb.instructions = pre_insts;
            bb.source_locs = pre_locs;
        }
        caller.trust_ir_origins.insert(block_id, pre_origins);

        // Install the clones.
        for (bid, bb, origins) in cloned_blocks {
            caller.blocks.insert(bid, bb);
            caller.trust_ir_origins.insert(bid, origins);
            caller.block_order.push(bid);
        }
        // Install cont.
        caller.blocks.insert(
            cont_id,
            BasicBlock {
                params: cont_params,
                instructions: cont_insts,
                source_locs: cont_locs,
            },
        );
        caller.trust_ir_origins.insert(cont_id, cont_origins);
        caller.block_order.push(cont_id);

        total_insts = total_insts + template.total_insts + call_results.len();
        sites += 1;

        // Continue scanning the continuation for further calls.
        worklist.push(cont_id);
    }

    if sites == 0 {
        return Ok(0);
    }

    // Commit pinned value types.
    for (v, ty) in new_value_types {
        caller.value_types.entry(v).or_insert(ty);
    }

    // Fresh-value uniqueness self-check.
    let mut seen = std::collections::HashSet::new();
    for v in &freshly_allocated {
        if *v < fresh_value_base || !seen.insert(*v) {
            return Err(InlineError {
                detail: format!(
                    "multi-block inliner allocated a non-fresh/duplicate value id {v} \
                     (base {fresh_value_base}) in `{}`",
                    caller.name
                ),
            });
        }
    }

    // CFG well-formedness self-check: entry present; every block ends in exactly
    // one terminator; every named successor exists.
    verify_cfg_wellformed(caller)?;

    // Opcode-multiset conservation self-check (block-id-agnostic).
    let actual = mb_opcode_multiset(caller);
    let mut keys: std::collections::HashSet<&String> = actual.keys().collect();
    keys.extend(expected.keys());
    for key in keys {
        let a = actual.get(key).copied().unwrap_or(0);
        let e = expected.get(key).copied().unwrap_or(0);
        if a != e {
            return Err(InlineError {
                detail: format!(
                    "multi-block inline self-check failed in `{}`: opcode {key} count {a} \
                     != expected {e} (an instruction was dropped or duplicated)",
                    caller.name
                ),
            });
        }
    }

    Ok(sites)
}

/// Map a callee value through the rename table, flagging an unresolved reference.
fn remap_value(v: &Value, rename: &HashMap<Value, Value>, unresolved: &mut bool) -> Value {
    match rename.get(v) {
        Some(mapped) => *mapped,
        None => {
            *unresolved = true;
            *v
        }
    }
}

/// Map a callee block through the block table, flagging a dangling edge.
fn remap_block(b: &Block, block_map: &HashMap<Block, Block>, bad: &mut bool) -> Block {
    match block_map.get(b) {
        Some(mapped) => *mapped,
        None => {
            *bad = true;
            *b
        }
    }
}

/// Fail-closed CFG well-formedness check after multi-block splicing. Only checks
/// properties that are UNIVERSALLY true of any valid LIR (so it can never
/// false-positive-abort a compile because of an untouched, already-valid block):
///   * the entry block is still present;
///   * no recognized terminator appears BEFORE a block's last instruction (a
///     mid-block terminator is always malformed — catches a bad split);
///   * every named successor exists (catches a bad block remap / dangling edge).
///     The continuation's trailing terminator is guaranteed by construction (we only
///     splice blocks that already end in a terminator), and the opcode-multiset
///     conservation check catches any dropped/duplicated instruction.
fn verify_cfg_wellformed(f: &Function) -> Result<(), InlineError> {
    if !f.blocks.contains_key(&f.entry_block) {
        return Err(InlineError {
            detail: format!("multi-block inline dropped the entry block of `{}`", f.name),
        });
    }
    for (bid, bb) in &f.blocks {
        if bb.instructions.is_empty() {
            continue;
        }
        let last = bb.instructions.len() - 1;
        for inst in &bb.instructions[..last] {
            let is_term = is_mb_terminator(&inst.opcode)
                || matches!(inst.opcode, Opcode::Invoke { .. } | Opcode::Resume);
            if is_term {
                return Err(InlineError {
                    detail: format!(
                        "multi-block inline left a mid-block terminator in block {} of `{}`",
                        bid.0, f.name
                    ),
                });
            }
        }
        for s in bb.successors() {
            if !f.blocks.contains_key(&s) {
                return Err(InlineError {
                    detail: format!(
                        "multi-block inline created a dangling edge {}->{} in `{}`",
                        bid.0, s.0, f.name
                    ),
                });
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::{BasicBlock, Function, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
    use trust_cg_lower::types::Type;

    fn empty_ctx() -> ProofContext {
        ProofContext::default()
    }

    /// `add(a, b) = a + b`  — a pure single-block scalar leaf.
    fn callee_add() -> Function {
        let mut f = Function::new(
            "add",
            Signature {
                params: vec![Type::I64, Type::I64],
                returns: vec![Type::I64],
            },
        );
        let bb = BasicBlock {
            params: vec![(Value(0), Type::I64), (Value(1), Type::I64)],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iadd,
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        f.entry_block = Block(0);
        f.blocks.insert(Block(0), bb);
        f.block_order = vec![Block(0)];
        f
    }

    /// `caller()` computes `t = k0 + k1` via a call to `add`, returns `t`.
    fn caller_calls_add() -> Function {
        let mut f = Function::new(
            "caller",
            Signature {
                params: vec![],
                returns: vec![Type::I64],
            },
        );
        let bb = BasicBlock {
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 10,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 20,
                    },
                    args: vec![],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Call {
                        name: "add".to_string(),
                    },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        f.entry_block = Block(0);
        f.blocks.insert(Block(0), bb);
        f.block_order = vec![Block(0)];
        f
    }

    #[test]
    fn inlines_pure_scalar_leaf_and_removes_the_call() {
        let mut funcs = vec![
            (caller_calls_add(), empty_ctx()),
            (callee_add(), empty_ctx()),
        ];
        let stats = run_inline(&mut funcs, false).expect("inline ok");
        assert_eq!(stats.sites, 1, "exactly one call site inlined");

        let caller = &funcs[0].0;
        let bb = caller.blocks.get(&Block(0)).unwrap();
        // No Call remains.
        assert!(
            !bb.instructions
                .iter()
                .any(|i| matches!(&i.opcode, Opcode::Call { .. })),
            "the call must be gone: {:?}",
            bb.instructions
        );
        // The callee's Iadd was spliced in.
        assert!(
            bb.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::Iadd)),
            "callee body must be spliced in"
        );
        // A wiring Copy defines the original call result (Value(2)).
        assert!(
            bb.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::Copy) && i.results == vec![Value(2)]),
            "return value must be wired to the call result via Copy"
        );
    }

    #[test]
    fn kill_switch_disables_inlining() {
        // Exercise the disable path behaviorally via the explicit flag (the env
        // read itself is `inlining_disabled()`). Avoids mutating the
        // process-global env, which would race with parallel tests.
        let mut funcs = vec![
            (caller_calls_add(), empty_ctx()),
            (callee_add(), empty_ctx()),
        ];
        let stats = run_inline(&mut funcs, true).expect("inline ok");
        assert_eq!(stats.sites, 0, "kill switch must disable inlining");
        assert!(
            funcs[0].0.blocks[&Block(0)]
                .instructions
                .iter()
                .any(|i| matches!(&i.opcode, Opcode::Call { .. })),
            "the call must survive when inlining is disabled"
        );
    }

    #[test]
    fn does_not_inline_recursive_or_multi_block_callee() {
        // A two-block callee is ineligible (not single-block).
        let mut callee = callee_add();
        callee.blocks.insert(Block(1), BasicBlock::default());
        callee.name = "add".to_string();
        assert!(build_callee_template(&callee).is_none());

        // A callee with a memory op is ineligible.
        let mut callee2 = callee_add();
        callee2.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode = Opcode::Load {
            ty: Type::I64,
            align: None,
        };
        assert!(build_callee_template(&callee2).is_none());
    }

    #[test]
    fn self_recursion_is_not_inlined() {
        // `caller` that (nonsensically for the test) calls itself: name guard
        // must prevent inlining even if a template by that name exists.
        let mut f = caller_calls_add();
        f.name = "add".to_string(); // same name as the callee template
        let template = build_callee_template(&callee_add()).unwrap();
        let mut templates = HashMap::new();
        templates.insert("add".to_string(), template);
        let inlined = inline_into_function(&mut f, &templates).unwrap();
        assert_eq!(inlined, 0, "a call to a same-named function is skipped");
    }

    #[test]
    fn self_check_rejects_a_dropped_instruction() {
        // Directly exercise the fail-closed multiset check: claim to expect an
        // instruction that is not present.
        let caller = caller_calls_add();
        let mut bogus_expected = opcode_multiset(&caller);
        // Pretend a phantom extra Iadd should exist (simulating a dropped splice).
        *bogus_expected
            .entry(format!("{:?}", Opcode::Iadd))
            .or_insert(0) += 1;
        let err = verify_opcode_conservation(&caller, &bogus_expected)
            .expect_err("must reject a count mismatch");
        assert!(err.detail.contains("dropped or duplicated"));
    }

    #[test]
    fn call_chain_collapses_across_rounds() {
        // g(x) = h(x) + 1 ; h(x) = x ^ x  (both single-block scalar leaves after
        // h is inlined into g). One round inlines h into g; a second round makes
        // g a leaf and inlines g into `top`.
        let h = {
            let mut f = Function::new(
                "h",
                Signature {
                    params: vec![Type::I64],
                    returns: vec![Type::I64],
                },
            );
            let bb = BasicBlock {
                params: vec![(Value(0), Type::I64)],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Bxor,
                        args: vec![Value(0), Value(0)],
                        results: vec![Value(1)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(1)],
                        results: vec![],
                    },
                ],
                ..Default::default()
            };
            f.entry_block = Block(0);
            f.blocks.insert(Block(0), bb);
            f.block_order = vec![Block(0)];
            f
        };
        let g = {
            let mut f = Function::new(
                "g",
                Signature {
                    params: vec![Type::I64],
                    returns: vec![Type::I64],
                },
            );
            let bb = BasicBlock {
                params: vec![(Value(0), Type::I64)],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Call {
                            name: "h".to_string(),
                        },
                        args: vec![Value(0)],
                        results: vec![Value(1)],
                    },
                    Instruction {
                        opcode: Opcode::Iconst {
                            ty: Type::I64,
                            imm: 1,
                        },
                        args: vec![],
                        results: vec![Value(2)],
                    },
                    Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![Value(1), Value(2)],
                        results: vec![Value(3)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(3)],
                        results: vec![],
                    },
                ],
                ..Default::default()
            };
            f.entry_block = Block(0);
            f.blocks.insert(Block(0), bb);
            f.block_order = vec![Block(0)];
            f
        };
        let top = {
            let mut f = Function::new(
                "top",
                Signature {
                    params: vec![],
                    returns: vec![Type::I64],
                },
            );
            let bb = BasicBlock {
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst {
                            ty: Type::I64,
                            imm: 7,
                        },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Call {
                            name: "g".to_string(),
                        },
                        args: vec![Value(0)],
                        results: vec![Value(1)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(1)],
                        results: vec![],
                    },
                ],
                ..Default::default()
            };
            f.entry_block = Block(0);
            f.blocks.insert(Block(0), bb);
            f.block_order = vec![Block(0)];
            f
        };

        let mut funcs = vec![(top, empty_ctx()), (g, empty_ctx()), (h, empty_ctx())];
        let stats = run_inline(&mut funcs, false).expect("inline ok");
        // h->g (round 1), then g->top (round 2): 2 sites total.
        assert_eq!(stats.sites, 2, "the whole chain collapses");
        let top_fn = &funcs[0].0;
        assert!(
            !top_fn.blocks[&Block(0)]
                .instructions
                .iter()
                .any(|i| matches!(&i.opcode, Opcode::Call { .. })),
            "top must have no calls left after chain inlining"
        );
    }

    // -------------------------------------------------------------------
    // Multi-block (CFG-splicing) inliner tests
    // -------------------------------------------------------------------

    use trust_cg_lower::instructions::IntCC;

    fn run_mb(funcs: &mut [(Function, ProofContext)]) -> Result<InlineStats, InlineError> {
        // whole-pass ON, multi-block tier ON.
        run_inline_cfg(funcs, false, false)
    }

    /// `max2(a,b)`: a 3-block diamond leaf with TWO returns (join required).
    ///   entry(0): v2 = icmp sgt v0,v1 ; brif v2 -> b1, b2
    ///   b1: return v0
    ///   b2: return v1
    fn callee_max2() -> Function {
        let mut f = Function::new(
            "max2",
            Signature {
                params: vec![Type::I64, Type::I64],
                returns: vec![Type::I64],
            },
        );
        let e = BasicBlock {
            params: vec![(Value(0), Type::I64), (Value(1), Type::I64)],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Icmp {
                        cond: IntCC::SignedGreaterThan,
                    },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Brif {
                        cond: Value(2),
                        then_dest: Block(1),
                        else_dest: Block(2),
                    },
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        let b1 = BasicBlock {
            instructions: vec![Instruction {
                opcode: Opcode::Return,
                args: vec![Value(0)],
                results: vec![],
            }],
            ..Default::default()
        };
        let b2 = BasicBlock {
            instructions: vec![Instruction {
                opcode: Opcode::Return,
                args: vec![Value(1)],
                results: vec![],
            }],
            ..Default::default()
        };
        f.entry_block = Block(0);
        f.blocks.insert(Block(0), e);
        f.blocks.insert(Block(1), b1);
        f.blocks.insert(Block(2), b2);
        f.block_order = vec![Block(0), Block(1), Block(2)];
        f
    }

    /// `caller()` computes `max2(5, 9)` and returns it, in ONE block.
    fn caller_calls_max2(name: &str) -> Function {
        let mut f = Function::new(
            name,
            Signature {
                params: vec![],
                returns: vec![Type::I64],
            },
        );
        let bb = BasicBlock {
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 5,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 9,
                    },
                    args: vec![],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Call {
                        name: "max2".to_string(),
                    },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        f.entry_block = Block(0);
        f.blocks.insert(Block(0), bb);
        f.block_order = vec![Block(0)];
        f
    }

    #[test]
    fn multiblock_diamond_inlines_and_joins_at_continuation() {
        let mut funcs = vec![
            (caller_calls_max2("caller"), empty_ctx()),
            (callee_max2(), empty_ctx()),
        ];
        let stats = run_mb(&mut funcs).expect("mb inline ok");
        assert_eq!(stats.sites, 1, "one multi-block site inlined");

        let caller = &funcs[0].0;
        // No Call remains.
        assert!(
            !caller
                .blocks
                .values()
                .flat_map(|b| b.instructions.iter())
                .any(|i| matches!(&i.opcode, Opcode::Call { .. })),
            "the call must be gone"
        );
        // The diamond was cloned: an Icmp and a Brif now live in the caller.
        let icmps = caller
            .blocks
            .values()
            .flat_map(|b| b.instructions.iter())
            .filter(|i| matches!(i.opcode, Opcode::Icmp { .. }))
            .count();
        let brifs = caller
            .blocks
            .values()
            .flat_map(|b| b.instructions.iter())
            .filter(|i| matches!(i.opcode, Opcode::Brif { .. }))
            .count();
        assert_eq!(icmps, 1, "callee compare cloned once");
        assert_eq!(brifs, 1, "callee branch cloned once");
        // A continuation block declares the call result (Value(2)) as a param,
        // filled by a Copy in each returning clone.
        let cont = caller
            .blocks
            .values()
            .find(|b| b.params.iter().any(|(v, _)| *v == Value(2)))
            .expect("continuation with the call-result param must exist");
        assert!(
            cont.instructions
                .iter()
                .any(|i| matches!(i.opcode, Opcode::Return) && i.args == vec![Value(2)]),
            "continuation must return the joined value"
        );
        let copies_to_result = caller
            .blocks
            .values()
            .flat_map(|b| b.instructions.iter())
            .filter(|i| matches!(i.opcode, Opcode::Copy) && i.results == vec![Value(2)])
            .count();
        assert_eq!(copies_to_result, 2, "each return wires the result via Copy");
        // Every block ends in exactly one terminator, edges resolve.
        verify_cfg_wellformed(caller).expect("well-formed CFG");
    }

    #[test]
    fn multiblock_self_recursion_is_not_inlined() {
        // A caller named "max2" calling "max2" must not inline (name guard).
        let mut funcs = [
            (caller_calls_max2("max2"), empty_ctx()),
            (callee_max2(), empty_ctx()),
        ];
        // The caller shares the callee's name; build a template for the callee
        // shape and confirm the self-named call is skipped.
        let template =
            build_multiblock_template(&callee_max2(), &std::collections::HashSet::new()).unwrap();
        let mut templates = HashMap::new();
        templates.insert("max2".to_string(), template);
        let inlined = inline_multiblock_into_function(&mut funcs[0].0, &templates).unwrap();
        assert_eq!(inlined, 0, "a call to a same-named function is skipped");
    }

    #[test]
    fn multiblock_calls_gate_on_defined_vs_external() {
        // A callee that calls a function DEFINED in this module is rejected
        // (could be recursive/cyclic); a callee that calls only EXTERNAL symbols
        // (libc) is admitted — the call clones verbatim.
        let mut callee = callee_max2();
        callee
            .blocks
            .get_mut(&Block(1))
            .unwrap()
            .instructions
            .insert(
                0,
                Instruction {
                    opcode: Opcode::Call {
                        name: "other".to_string(),
                    },
                    args: vec![],
                    results: vec![],
                },
            );
        // "other" defined in-module => reject.
        let mut defined = std::collections::HashSet::new();
        defined.insert("other".to_string());
        assert!(build_multiblock_template(&callee, &defined).is_none());
        // "other" external (not in the defined set) => admit.
        assert!(build_multiblock_template(&callee, &std::collections::HashSet::new()).is_some());
    }

    #[test]
    fn multiblock_rejects_stack_slots_and_eh() {
        use trust_cg_lower::function::StackSlotInfo;
        let mut with_slots = callee_max2();
        with_slots.stack_slots.push(StackSlotInfo::new(8, 8));
        assert!(
            build_multiblock_template(&with_slots, &std::collections::HashSet::new()).is_none()
        );

        let mut with_eh = callee_max2();
        with_eh.eh_info.personality = Some("__gxx_personality_v0".to_string());
        assert!(build_multiblock_template(&with_eh, &std::collections::HashSet::new()).is_none());
    }

    #[test]
    fn multiblock_rejects_noreturn_callee() {
        // Replace both returns with Traps: no Return block => ineligible.
        let mut callee = callee_max2();
        for b in [Block(1), Block(2)] {
            callee.blocks.get_mut(&b).unwrap().instructions = vec![Instruction {
                opcode: Opcode::Trap,
                args: vec![],
                results: vec![],
            }];
        }
        assert!(build_multiblock_template(&callee, &std::collections::HashSet::new()).is_none());
    }

    #[test]
    fn multiblock_truncates_abi_widened_narrow_return() {
        // A callee that returns I8 but whose return ARG is an I32 (ABI-widened,
        // like a `zeroext i8` callee). Inlining must TRUNCATE the return value to
        // the caller's logical I8 result, not Copy the register-width value —
        // else a downstream I8 use mismatches the I32 result. This is the exact
        // shape of the pr37573 fail-closed ISel regression.
        let mut callee = Function::new(
            "nret",
            Signature {
                params: vec![Type::I32],
                returns: vec![Type::I8],
            },
        );
        let e = BasicBlock {
            params: vec![(Value(0), Type::I32)],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Trunc { to_ty: Type::I8 },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Sextend {
                        from_ty: Type::I8,
                        to_ty: Type::I32,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Jump { dest: Block(1) },
                    args: vec![],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        let b1 = BasicBlock {
            instructions: vec![Instruction {
                opcode: Opcode::Return,
                args: vec![Value(2)],
                results: vec![],
            }],
            ..Default::default()
        };
        callee.entry_block = Block(0);
        callee.blocks.insert(Block(0), e);
        callee.blocks.insert(Block(1), b1);
        callee.block_order = vec![Block(0), Block(1)];
        callee.value_types.insert(Value(0), Type::I32);
        callee.value_types.insert(Value(1), Type::I8);
        callee.value_types.insert(Value(2), Type::I32); // return arg widened to I32

        let mut caller = Function::new(
            "main",
            Signature {
                params: vec![],
                returns: vec![Type::I8],
            },
        );
        let bb = BasicBlock {
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I32,
                        imm: 300,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Call {
                        name: "nret".to_string(),
                    },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(1)],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        caller.entry_block = Block(0);
        caller.blocks.insert(Block(0), bb);
        caller.block_order = vec![Block(0)];
        caller.value_types.insert(Value(1), Type::I8); // adapter records call result as I8

        let mut funcs = vec![(caller, empty_ctx()), (callee, empty_ctx())];
        let stats = run_mb(&mut funcs).expect("mb inline ok");
        assert_eq!(stats.sites, 1);
        let caller = &funcs[0].0;
        // The return wiring must be a Trunc-to-I8 that defines the call result.
        let has_trunc_wire = caller
            .blocks
            .values()
            .flat_map(|b| b.instructions.iter())
            .any(|i| {
                matches!(&i.opcode, Opcode::Trunc { to_ty } if *to_ty == Type::I8)
                    && i.results == vec![Value(1)]
            });
        assert!(
            has_trunc_wire,
            "ABI-widened narrow return must be truncated to the result type"
        );
        assert_eq!(caller.value_types.get(&Value(1)), Some(&Type::I8));
        verify_cfg_wellformed(caller).expect("well-formed CFG");
    }

    #[test]
    fn multiblock_single_block_callee_is_not_an_mb_template() {
        // A single-block callee is handled by the straight-line tier, never MB.
        assert!(
            build_multiblock_template(&callee_add(), &std::collections::HashSet::new()).is_none()
        );
    }

    #[test]
    fn multiblock_vreg_and_block_id_collision_stress() {
        // Caller and callee deliberately share value ids (0,1,2) AND block ids
        // (0,1,2). After inlining, fresh renaming must avoid every collision and
        // the fail-closed self-checks must pass.
        let mut funcs = vec![
            (caller_calls_max2("caller"), empty_ctx()),
            (callee_max2(), empty_ctx()),
        ];
        let stats = run_mb(&mut funcs).expect("mb inline ok");
        assert_eq!(stats.sites, 1);
        let caller = &funcs[0].0;
        // Collect every defined value id; a value id defined by two DIFFERENT
        // block-param declarations or instruction results (other than the LIR's
        // legitimate copy-into-block-param convention) would be a collision.
        // Here we assert the caller's original ids (0,1,2) are still present and
        // the clone introduced fresh ids >= 3 with no duplicate block ids.
        let mut block_ids: Vec<u32> = caller.blocks.keys().map(|b| b.0).collect();
        block_ids.sort_unstable();
        block_ids.dedup();
        assert_eq!(
            block_ids.len(),
            caller.blocks.len(),
            "no duplicate block ids after clone"
        );
        // Entry preserved.
        assert!(caller.blocks.contains_key(&caller.entry_block));
        verify_cfg_wellformed(caller).expect("well-formed CFG");
    }

    #[test]
    fn multiblock_loop_callee_inlines_preserving_backedge() {
        // sum_to(n): loops accumulating 0..n. A back-edge (loop) callee must
        // clone verbatim under the rename and pass the fail-closed self-checks.
        //   entry(0)[n=v0]: v1 = iconst 0(acc); v2 = iconst 0(i); jump b1
        //   b1[acc=v1,i=v2 via copies]: v3 = icmp slt i, n; brif v3 -> b2, b3
        //   b2: v4 = iadd acc, i; v5 = iadd i, 1; copy v1<-v4; copy v2<-v5; jump b1
        //   b3: return acc(v1)
        let mut f = Function::new(
            "sum_to",
            Signature {
                params: vec![Type::I64],
                returns: vec![Type::I64],
            },
        );
        let e = BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 0,
                    },
                    args: vec![],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 0,
                    },
                    args: vec![],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Jump { dest: Block(1) },
                    args: vec![],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        let b1 = BasicBlock {
            params: vec![(Value(1), Type::I64), (Value(2), Type::I64)],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Icmp {
                        cond: IntCC::SignedLessThan,
                    },
                    args: vec![Value(2), Value(0)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Brif {
                        cond: Value(3),
                        then_dest: Block(2),
                        else_dest: Block(3),
                    },
                    args: vec![Value(3)],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        let b2 = BasicBlock {
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iadd,
                    args: vec![Value(1), Value(2)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Iadd,
                    args: vec![Value(2), Value(0)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Copy,
                    args: vec![Value(4)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Copy,
                    args: vec![Value(5)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Jump { dest: Block(1) },
                    args: vec![],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        let b3 = BasicBlock {
            instructions: vec![Instruction {
                opcode: Opcode::Return,
                args: vec![Value(1)],
                results: vec![],
            }],
            ..Default::default()
        };
        f.entry_block = Block(0);
        f.blocks.insert(Block(0), e);
        f.blocks.insert(Block(1), b1);
        f.blocks.insert(Block(2), b2);
        f.blocks.insert(Block(3), b3);
        f.block_order = vec![Block(0), Block(1), Block(2), Block(3)];

        // Sanity: eligible as an MB template (entry not re-entered; b1 is the
        // loop header, reached from entry AND b2 — entry itself has no pred).
        assert!(build_multiblock_template(&f, &std::collections::HashSet::new()).is_some());

        let mut caller = Function::new(
            "main",
            Signature {
                params: vec![],
                returns: vec![Type::I64],
            },
        );
        let cb = BasicBlock {
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 10,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Call {
                        name: "sum_to".to_string(),
                    },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(1)],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        caller.entry_block = Block(0);
        caller.blocks.insert(Block(0), cb);
        caller.block_order = vec![Block(0)];

        let mut funcs = vec![(caller, empty_ctx()), (f, empty_ctx())];
        let stats = run_mb(&mut funcs).expect("mb inline ok");
        assert_eq!(stats.sites, 1, "loop callee inlined");
        let caller = &funcs[0].0;
        assert!(
            !caller
                .blocks
                .values()
                .flat_map(|b| b.instructions.iter())
                .any(|i| matches!(&i.opcode, Opcode::Call { .. })),
            "call gone"
        );
        // The back-edge survives: some cloned block jumps back to the cloned
        // loop header (a block that is a successor of two predecessors).
        verify_cfg_wellformed(caller).expect("well-formed CFG");
        let jump_targets: Vec<u32> = caller
            .blocks
            .values()
            .flat_map(|b| b.instructions.iter())
            .filter_map(|i| match &i.opcode {
                Opcode::Jump { dest } => Some(dest.0),
                _ => None,
            })
            .collect();
        // At least one Jump target is shared by >=2 jumps (the loop header),
        // confirming the back-edge was preserved.
        let mut counts: HashMap<u32, usize> = HashMap::new();
        for t in jump_targets {
            *counts.entry(t).or_insert(0) += 1;
        }
        assert!(
            counts.values().any(|&c| c >= 2),
            "the loop header should be a shared jump target (back-edge preserved)"
        );
    }
}
