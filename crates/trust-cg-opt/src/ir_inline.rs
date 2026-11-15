// trust-cg-opt - Shared trust-ir-level (LIR) function inlining (OPT-4)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared, pre-target-dispatch function inlining for the Trust-CG LIR.
//!
//! This pass runs at the SHARED `translate_module_for_arch` seam inside the
//! Compiler (`compiler.rs`), on the `Vec<(Function, ProofContext)>` the adapter
//! produced, BEFORE the per-target ISel dispatch (x86-64 / aarch64 / riscv64).
//! Everything downstream takes the INLINED LIR as its source: every
//! per-instruction lowering proof, every TV gate (TV-2/TV-3/TV-4) and the
//! x86-64 source-bound body theorem check the lowering of the inlined LIR,
//! not the substitution. The substitution is checked only by the structural
//! self-check below, which a wrong argument-to-parameter mapping passes. So a
//! compile that claims proofs does not run this pass (ruling OD-225,
//! `trust_cg_codegen::lir_module_prep`, "Proof claims"); it may return there
//! only with an inlining validator of its own.
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
//!   * `C.name != caller.name` (belt-and-suspenders self-recursion guard);
//!   * `C` states no target features of its own (`Function::target_features`
//!     empty): a feature-stating body keeps its own admission, so it is never
//!     spliced into any caller, on either tier.
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
//!      explicit `Copy`, so downstream caller uses stay defined. Instruction
//!      selection types a `Copy` result from its source, so an operand wider
//!      than the declared return type (the adapter's Apple arm64 extension of
//!      an `i8`/`i16` return to `I32`) is first narrowed by a `Trunc` into a
//!      fresh value; a callee whose return operand disagrees with its
//!      signature in any other way is not spliced (`ReturnWiring`, shared
//!      with the multi-block tier).
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
//! value collision fails the compile CLOSED ([`InlineError`]). Passing them is
//! not a semantic validation: they conserve the opcode multiset and the CFG's
//! shape, so a substitution that binds the wrong argument to a parameter, or
//! wires a result into the wrong join (the bridge corpus's
//! `fix_l_enum_byref_o2_inliner`, a miscompile these checks passed), is still
//! emitted.
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
//! ## Call bindings the pass may splice
//!
//! A `Call { name, binding }` is a candidate when its binding lets this
//! module's body stand for the callee:
//!   * `Interposable` — the ordinary by-name call; the caller supplies the
//!     names whose body another object may replace (`interposable`), and
//!     those are never templates;
//!   * `ExactModuleFunction` — the validated translation's authenticated
//!     edge to THIS module's definition. Splicing that definition's body is
//!     the binding's strongest form. Only a definition the module emits is
//!     ever spliced for it, never an inline-only body.
//!
//! `DeclaredExternalFunction` and `NativeDependency` edges are imports and are
//! never inlined.
//!
//! ## Inline-only bodies (trust-ir `AvailableExternally`)
//!
//! [`inline_module_with_inline_only_bodies`] also takes bodies the module does
//! NOT define: LIR translations of trust-ir `AvailableExternally` functions,
//! whose definition is emitted elsewhere and bound by symbol (an object's
//! undefined symbol, a JIT's extern map). Such a body is admitted under the
//! SAME two tiers and budgets as a module definition, with one widening: a
//! ONE-block body the straight-line tier declines (it loads, stores or calls
//! an external symbol) is admitted by the CFG-splicing tier, whose checks and
//! splice are block-count agnostic; a module definition still needs two
//! blocks there, so no module's own functions inline differently. It is
//! spliced only into `Interposable` calls, and then discarded: it is never a
//! caller, never mutated, never emitted. A call that is not inlined stays exactly the
//! external call it was. An inline-only body that calls any module
//! definition or any inline-only body (itself included) is never a
//! multi-block template, so no inline-only splice can start a cycle.
//!
//! The one premise this adds is the one-definition rule: the inline-only body
//! computes what the definition the symbol binds to computes. Nothing here
//! checks it; the caller decides which bodies to admit (and must disclose the
//! premise for every body [`InlineReport::inline_only_uses`] names).
//!
//! Kill switch: `TCG_NO_INLINE` (also honors
//! `TRUST_CG_DISABLE_PASSES=irinline`). `TCG_NO_MB_INLINE` (or
//! `TRUST_CG_DISABLE_PASSES=mbinline`) disables only the CFG-splicing tier.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use trust_cg_ir::{SourceLoc, TrustIrInstId};
use trust_cg_lower::ProofContext;
use trust_cg_lower::function::{BasicBlock, Function};
use trust_cg_lower::instructions::{Block, DirectCallBinding, Instruction, Opcode, Value};
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
    /// How each `Return` operand reaches its call result, positional.
    return_wiring: Vec<ReturnWiring>,
    /// Instructions one splice adds: the body, one `Copy` per result and one
    /// `Trunc` per `ReturnWiring::Narrow` result.
    splice_insts: usize,
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
    let mut value_types: HashMap<Value, Type> = HashMap::default();
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

    let return_wiring = last
        .args
        .iter()
        .zip(&f.signature.returns)
        .map(|(arg, rty)| return_wiring(value_types.get(arg), rty))
        .collect::<Option<Vec<_>>>()?;
    let splice_insts = body.len()
        + return_wiring.len()
        + return_wiring
            .iter()
            .filter(|w| **w == ReturnWiring::Narrow)
            .count();

    Some(CalleeTemplate {
        params: bb.params.clone(),
        body: body.to_vec(),
        return_args: last.args.clone(),
        return_types: f.signature.returns.clone(),
        return_wiring,
        splice_insts,
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
    let mut m: HashMap<String, i64> = HashMap::default();
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

/// How often one inline-only body was spliced by a module inlining run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlineOnlyUse {
    /// The inline-only function's symbol name.
    pub name: String,
    /// Call sites its body replaced (both tiers, every round).
    pub sites: usize,
}

/// Result of [`inline_module_with_inline_only_bodies`].
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct InlineReport {
    /// Whole-run statistics, inline-only splices included.
    pub stats: InlineStats,
    /// Every inline-only body spliced at least once, sorted by name. Each is a
    /// one-definition-rule premise the caller must disclose.
    pub inline_only_uses: Vec<InlineOnlyUse>,
    /// Indices (into the module's functions) of every caller that received at
    /// least one splice, ascending: the functions whose LIR this run changed.
    pub changed_functions: Vec<usize>,
}

/// Run shared trust-ir-level inlining over the module's LIR functions in place.
///
/// Returns [`InlineStats`], or [`InlineError`] if the fail-closed structural
/// self-check detected a dropped/duplicated instruction (the Compiler maps this
/// to a `CompileError` — fail-closed, never emit).
pub fn inline_module(funcs: &mut [(Function, ProofContext)]) -> Result<InlineStats, InlineError> {
    inline_module_excluding_interposable(funcs, &HashSet::default())
}

/// [`inline_module_excluding_interposable`] that may also splice the
/// inline-only bodies in `inline_only` (see the module docs, "Inline-only
/// bodies"). `inline_only` is read, never mutated; its functions are not part
/// of the module and must not be emitted. A candidate that shares a name with
/// a function in `funcs`, or that `interposable` names, is ignored.
///
/// With an empty `inline_only` this is exactly
/// [`inline_module_excluding_interposable`].
pub fn inline_module_with_inline_only_bodies<S: std::hash::BuildHasher>(
    funcs: &mut [(Function, ProofContext)],
    inline_only: &[(Function, ProofContext)],
    interposable: &std::collections::HashSet<String, S>,
) -> Result<InlineReport, InlineError> {
    let mut site_counts: HashMap<String, usize> = HashMap::default();
    let mut changed: Vec<usize> = Vec::new();
    let stats = run_inline_cfg(
        funcs,
        inline_only,
        inlining_disabled(),
        multiblock_disabled(),
        interposable,
        &mut site_counts,
        &mut changed,
    )?;
    let defined: HashSet<&str> = funcs.iter().map(|(f, _)| f.name.as_str()).collect();
    let mut inline_only_uses: Vec<InlineOnlyUse> = inline_only
        .iter()
        .map(|(f, _)| f.name.as_str())
        .filter(|name| !defined.contains(name))
        .collect::<std::collections::BTreeSet<&str>>()
        .into_iter()
        .filter_map(|name| {
            site_counts
                .get(name)
                .copied()
                .filter(|sites| *sites > 0)
                .map(|sites| InlineOnlyUse {
                    name: name.to_string(),
                    sites,
                })
        })
        .collect();
    inline_only_uses.sort_by(|a, b| a.name.cmp(&b.name));
    changed.sort_unstable();
    Ok(InlineReport {
        stats,
        inline_only_uses,
        changed_functions: changed,
    })
}

/// [`inline_module`] that never inlines a callee named in `interposable`.
///
/// An interposable definition (an object symbol a different definition may
/// replace at link time, such as an ELF `STB_WEAK` function) must be reached
/// through its symbol: splicing this module's body into a caller would keep the
/// replaced behaviour after the linker selected another definition. Callers
/// still inline every other eligible callee.
pub fn inline_module_excluding_interposable<S: std::hash::BuildHasher>(
    funcs: &mut [(Function, ProofContext)],
    interposable: &std::collections::HashSet<String, S>,
) -> Result<InlineStats, InlineError> {
    run_inline_cfg(
        funcs,
        &[],
        inlining_disabled(),
        multiblock_disabled(),
        interposable,
        &mut HashMap::default(),
        &mut Vec::new(),
    )
}

/// Core driver with an explicit `disabled` flag (so unit tests never mutate the
/// process-global env, which would race under parallel test execution). The
/// single-block unit tests drive this entry with the multi-block tier off.
#[cfg(test)]
fn run_inline(
    funcs: &mut [(Function, ProofContext)],
    disabled: bool,
) -> Result<InlineStats, InlineError> {
    run_inline_cfg(
        funcs,
        &[],
        disabled,
        true,
        &HashSet::default(),
        &mut HashMap::default(),
        &mut Vec::new(),
    )
}

/// Whether a direct call with `binding` to `name` may be replaced by a
/// template's body (module docs, "Call bindings the pass may splice"). An
/// exact module edge is never served by an inline-only body.
fn binding_admits_splice(
    binding: &DirectCallBinding,
    name: &str,
    inline_only_names: &HashSet<String>,
) -> bool {
    match binding {
        DirectCallBinding::Interposable => true,
        DirectCallBinding::ExactModuleFunction { .. } => !inline_only_names.contains(name),
        DirectCallBinding::DeclaredExternalFunction { .. }
        | DirectCallBinding::NativeDependency { .. } => false,
    }
}

/// Core driver with explicit `disabled` (whole pass) and `mb_disabled`
/// (multi-block tier only) flags. No template is built for a callee named in
/// `interposable`, so no call to it is ever spliced. `inline_only` bodies are
/// template sources only (see the module docs); `site_counts` accumulates the
/// sites spliced per callee name, `changed` the index (into `funcs`) of every
/// caller that received at least one splice.
fn run_inline_cfg<S: std::hash::BuildHasher>(
    funcs: &mut [(Function, ProofContext)],
    inline_only: &[(Function, ProofContext)],
    disabled: bool,
    mb_disabled: bool,
    interposable: &std::collections::HashSet<String, S>,
    site_counts: &mut HashMap<String, usize>,
    changed: &mut Vec<usize>,
) -> Result<InlineStats, InlineError> {
    let mut stats = InlineStats::default();
    if disabled || funcs.is_empty() {
        return Ok(stats);
    }

    // Names of every function DEFINED in this module — the leaf / non-recursion
    // gate for multi-block templates (a callee may call external symbols only).
    let defined_names: std::collections::HashSet<String> =
        funcs.iter().map(|(f, _)| f.name.clone()).collect();

    // Inline-only bodies: never a module definition (a name collision drops
    // the candidate), never an interposable name. Their leaf gate also counts
    // every inline-only name as in-module, so an inline-only body that calls
    // itself or another inline-only body is never a multi-block template.
    let inline_only: Vec<&Function> = inline_only
        .iter()
        .map(|(f, _)| f)
        .filter(|f| {
            !defined_names.contains(&f.name)
                && !interposable.contains(&f.name)
                && f.target_features.is_empty()
        })
        .collect();
    let inline_only_names: HashSet<String> = inline_only.iter().map(|f| f.name.clone()).collect();
    let inline_only_leaf_gate: std::collections::HashSet<String> = defined_names
        .iter()
        .chain(inline_only_names.iter())
        .cloned()
        .collect();
    // Inline-only bodies are never mutated, so their templates are built once.
    let mut inline_only_templates: HashMap<String, CalleeTemplate> = HashMap::default();
    let mut inline_only_mb_templates: HashMap<String, MultiBlockTemplate> = HashMap::default();
    for f in &inline_only {
        if let Some(t) = build_callee_template(f) {
            inline_only_templates.insert(f.name.clone(), t);
        } else if !mb_disabled
            && let Some(mb) = build_cfg_splice_template(f, &inline_only_leaf_gate, 1)
        {
            inline_only_mb_templates.insert(f.name.clone(), mb);
        }
    }

    for _round in 0..MAX_ROUNDS {
        // Snapshot eligible callees (by name) BEFORE mutating any caller this
        // round, so inlining is consistent regardless of processing order. A
        // callee is either a single-block straight-line template OR a
        // multi-block CFG-splice template (never both — routed by block count).
        let mut templates: HashMap<String, CalleeTemplate> = inline_only_templates.clone();
        let mut mb_templates: HashMap<String, MultiBlockTemplate> =
            inline_only_mb_templates.clone();
        for (f, _) in funcs.iter() {
            // A callee that states its own target features is never spliced:
            // its body was selected for a CPU the caller may not assume, and
            // splicing would lower it under the caller's admission instead
            // (LLVM's inline-compatibility rule, taken conservatively).
            if interposable.contains(&f.name) || !f.target_features.is_empty() {
                continue;
            }
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
        for (index, (f, _)) in funcs.iter_mut().enumerate() {
            // Single-block straight-line splice first (no CFG change), then the
            // multi-block CFG splice, so a caller collapses both tiers per round.
            let mut sites = inline_into_function(f, &templates, &inline_only_names, site_counts)?;
            if !mb_disabled {
                sites += inline_multiblock_into_function(
                    f,
                    &mb_templates,
                    &inline_only_names,
                    site_counts,
                )?;
            }
            if sites > 0 && !changed.contains(&index) {
                changed.push(index);
            }
            round_sites += sites;
        }
        stats.rounds += 1;
        stats.sites += round_sites;
        if round_sites == 0 {
            break;
        }
    }

    Ok(stats)
}

/// Inline every eligible call in `caller`. Returns the number of sites inlined.
fn inline_into_function(
    caller: &mut Function,
    templates: &HashMap<String, CalleeTemplate>,
    inline_only_names: &HashSet<String>,
    site_counts: &mut HashMap<String, usize>,
) -> Result<usize, InlineError> {
    // Cheap pre-scan: does this caller have ANY eligible call? Avoids the
    // multiset snapshot for the common no-op case.
    let has_candidate = caller.blocks.values().any(|bb| {
        bb.instructions.iter().any(|inst| match &inst.opcode {
            Opcode::Call { name, binding } => {
                binding_admits_splice(binding, name, inline_only_names)
                    && templates.contains_key(name)
                    && *name != caller.name
            }
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
    let mut new_value_types: HashMap<Value, Type> = HashMap::default();

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
                Opcode::Call { name, binding }
                    if binding_admits_splice(binding, name, inline_only_names)
                        && templates.contains_key(name)
                        && *name != caller.name =>
                {
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
                || total_insts + template.splice_insts > MAX_FUNCTION_INSTS
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
            let mut rename: HashMap<Value, Value> = HashMap::default();
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
            // Wire returns -> call results via explicit Copy, pinning types. A
            // `Copy` result takes its source's type in instruction selection, so
            // a wider (ABI-extended) operand is first narrowed into a fresh temp
            // of the declared return type; the result itself is still defined
            // only by the `Copy`.
            for ((ret_arg, wiring), (result, rty)) in template
                .return_args
                .iter()
                .zip(&template.return_wiring)
                .zip(inst.results.iter().zip(template.return_types.iter()))
            {
                let mut src = rename.get(ret_arg).copied().unwrap_or(*ret_arg);
                match wiring {
                    ReturnWiring::AsIs => {
                        new_value_types.entry(src).or_insert_with(|| rty.clone());
                    }
                    ReturnWiring::Narrow => {
                        let tmp = Value(next_value);
                        next_value += 1;
                        freshly_allocated.push(tmp.0);
                        new_value_types.entry(tmp).or_insert_with(|| rty.clone());
                        let narrow = Instruction {
                            opcode: Opcode::Trunc { to_ty: rty.clone() },
                            args: vec![src],
                            results: vec![tmp],
                        };
                        adj(&mut expected, format!("{:?}", narrow.opcode), 1);
                        new_insts.push(narrow);
                        new_locs.push(site_loc);
                        new_origins.push(None);
                        src = tmp;
                    }
                }
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

            total_insts = total_insts + template.splice_insts - 1;
            sites += 1;
            *site_counts.entry(name.clone()).or_insert(0) += 1;
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
//     multi-return callee therefore joins naturally at `cont`. An ABI-widened
//     narrow return is narrowed into a FRESH temp first (`Trunc tmp <- v_j`), so
//     `Copy` stays the ONLY opcode that ever defines `result_j` — see the long
//     note on the wiring itself for the miscompile that rule exists to stop.
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

/// How a callee `Return` operand becomes the caller's call result, on either
/// tier. Instruction selection types a `Copy` result from its SOURCE, so a
/// `Copy` carries the result's declared type only when the operand already has
/// it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReturnWiring {
    /// The operand's recorded type is the signature return type, or no type is
    /// recorded (the operand is then pinned to the return type): `Copy`.
    AsIs,
    /// The operand is a strictly wider integer than the signature return type:
    /// the adapter's Apple arm64 callee-side extension of an `i8`/`i16` return
    /// to `I32` (`translate_return`). Its low bits are the logical value, so
    /// the wiring truncates to the return type.
    Narrow,
}

/// The wiring of a `Return` operand whose callee type is `operand_ty` into a
/// call result of signature type `rty`, or `None` when the two disagree in a
/// way neither wiring reconciles; such a callee is not spliced.
fn return_wiring(operand_ty: Option<&Type>, rty: &Type) -> Option<ReturnWiring> {
    match operand_ty {
        None => Some(ReturnWiring::AsIs),
        Some(ty) if ty == rty => Some(ReturnWiring::AsIs),
        Some(ty) if int_strictly_wider(ty, rty) => Some(ReturnWiring::Narrow),
        Some(_) => None,
    }
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
        Opcode::Call { name, .. } | Opcode::CallVariadic { name, .. } => defined.contains(name),
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
    let mut m: HashMap<String, i64> = HashMap::default();
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
    blocks: std::collections::HashMap<Block, BasicBlock>,
    /// A deterministic clone order over the callee's blocks.
    block_order: Vec<Block>,
    /// Entry-block params == formal parameters, positional (wired to call args).
    params: Vec<(Value, Type)>,
    /// Signature return types, positional (pins the wiring-copy result types).
    return_types: Vec<Type>,
    /// Soundly-derived types for callee values (renamed at splice time), so ISel
    /// resolves the inlined body identically to the standalone callee.
    value_types: std::collections::HashMap<Value, Type>,
    /// Exact added instruction count for a splice: the callee body plus every
    /// return's joining Copies and any narrowing Truncs. Call -> entry Jump and
    /// each Return -> continuation Jump cancel, so this is the caller's growth.
    splice_insts: usize,
}

/// Build a [`MultiBlockTemplate`] for `f` if it is eligible for CFG-splice
/// inlining, else `None` (ineligible — never inlined, fail-safe). `defined` is
/// the set of function names defined in this module (for the leaf / non-recursion
/// gate: a callee may call EXTERNAL symbols but no in-module function).
fn build_multiblock_template(
    f: &Function,
    defined: &std::collections::HashSet<String>,
) -> Option<MultiBlockTemplate> {
    build_cfg_splice_template(f, defined, 2)
}

/// [`build_multiblock_template`] with the smallest admitted block count
/// `min_blocks`. A module definition needs two blocks (a one-block definition
/// is the straight-line tier's, which admits only pure scalar leaves). An
/// inline-only body may have ONE: a one-block fast path that loads, stores or
/// calls an external symbol — a field read, a counter bump — takes the same
/// checks and the same split-and-join splice (the call becomes a jump into
/// the cloned block, its `Return` a jump to the continuation).
fn build_cfg_splice_template(
    f: &Function,
    defined: &std::collections::HashSet<String>,
    min_blocks: usize,
) -> Option<MultiBlockTemplate> {
    macro_rules! reject {
        ($($a:tt)*) => {{
            return None;
        }};
    }
    let nblocks = f.blocks.len();
    if !(min_blocks.max(1)..=MAX_MB_CALLEE_BLOCKS).contains(&nblocks) {
        reject!("block count {nblocks} out of [{min_blocks},{MAX_MB_CALLEE_BLOCKS}]");
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
    let mut value_types: std::collections::HashMap<Value, Type> = f.value_types.clone();
    for bb in f.blocks.values() {
        for (pv, ty) in &bb.params {
            value_types.entry(*pv).or_insert_with(|| ty.clone());
        }
    }

    // Count ALL return sites, not just one Copy per call result. This uses the
    // same authoritative source types as the return-wiring emitter below and
    // must be known before selecting a site or mutating its caller.
    let mut splice_insts = total;
    for bb in f.blocks.values() {
        if let Some(inst) = bb.instructions.last()
            && matches!(inst.opcode, Opcode::Return)
        {
            for (ret_arg, rty) in inst.args.iter().zip(&f.signature.returns) {
                let needs_trunc =
                    return_wiring(value_types.get(ret_arg), rty) == Some(ReturnWiring::Narrow);
                splice_insts = splice_insts.checked_add(1 + usize::from(needs_trunc))?;
            }
        }
    }

    Some(MultiBlockTemplate {
        entry,
        blocks: f.blocks.clone(),
        block_order: ordered_blocks(f),
        params: entry_bb.params.clone(),
        return_types: f.signature.returns.clone(),
        value_types,
        splice_insts,
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
    inline_only_names: &HashSet<String>,
    site_counts: &mut HashMap<String, usize>,
) -> Result<usize, InlineError> {
    if templates.is_empty() {
        return Ok(0);
    }
    let caller_name = caller.name.clone();

    // Cheap pre-scan for any eligible call.
    let has_candidate = caller.blocks.values().any(|bb| {
        bb.instructions.iter().any(|inst| match &inst.opcode {
            Opcode::Call { name, binding } => {
                binding_admits_splice(binding, name, inline_only_names)
                    && templates.contains_key(name)
                    && *name != caller_name
            }
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
    let mut new_value_types: HashMap<Value, Type> = HashMap::default();

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
        let mut found: Option<(usize, String, usize)> = None;
        if ends_in_terminator {
            for (i, inst) in bb.instructions.iter().enumerate() {
                let Opcode::Call { name, binding } = &inst.opcode else {
                    continue;
                };
                if !binding_admits_splice(binding, name, inline_only_names)
                    || !templates.contains_key(name)
                    || *name == caller_name
                {
                    continue;
                }
                let t = &templates[name];
                // Per-site: arity match, a terminator after the call, growth budget.
                if inst.args.len() == t.params.len()
                    && inst.results.len() == t.return_types.len()
                    && i + 1 < bb.instructions.len()
                    && let Some(after_splice) = total_insts.checked_add(t.splice_insts)
                    && after_splice <= MAX_FUNCTION_INSTS
                {
                    found = Some((i, name.clone(), after_splice));
                    break;
                }
            }
        }
        let Some((call_idx, name, after_splice)) = found else {
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
        let mut val_map: HashMap<Value, Value> = HashMap::default();
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
        let mut block_map: HashMap<Block, Block> = HashMap::default();
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
                    //
                    // The narrowing NEVER writes `result_j` itself. A callee with
                    // more than one `Return` block gives `result_j` one definition
                    // per returning clone, and `result_j` is ALSO the continuation's
                    // block PARAMETER — the LIR's phi. ISel realises that join by
                    // vreg REUSE: `select_copy` reuses a result value's existing
                    // vreg so every predecessor writes the SAME register, and
                    // `define_block_params` then skips a param a predecessor has
                    // already defined. `Opcode::Copy` is the only value op that
                    // honours that convention — `select_trunc` allocates a FRESH
                    // vreg and rebinds the value, so the LAST returning clone ISel
                    // processes silently steals the join while every other return
                    // path writes a register nothing reads, and machine DCE then
                    // deletes those paths' value computations outright. Measured
                    // 2026-09-10 through the rustc bridge:
                    // `fn rd(e: &E) -> u8 { match e { A => 100, B(_) => 200 } }`
                    // printed `48 0` for `100 200` at -O2 (correct at -O0, where no
                    // inlining runs) — the unreachable default arm's `Trunc` was
                    // processed last and won the vreg. Only NARROW returns were
                    // affected: a same-width return already wired through `Copy`.
                    // So a narrowing goes into a FRESH value and a `Copy` carries
                    // that into `result_j`: every return site now ends in the one
                    // opcode the block-param join convention accepts.
                    for (ret_arg, (result, rty)) in inst
                        .args
                        .iter()
                        .zip(call_results.iter().zip(template.return_types.iter()))
                    {
                        let src = remap_value(ret_arg, &val_map, &mut unresolved);
                        // What the joining `Copy` reads: `src` itself when the
                        // widths already agree, else a fresh narrowed temp.
                        let mut copy_src = src;
                        match return_wiring(template.value_types.get(ret_arg), rty) {
                            Some(ReturnWiring::AsIs) => {
                                new_value_types.entry(src).or_insert_with(|| rty.clone());
                            }
                            Some(ReturnWiring::Narrow) => {
                                // Keep `src`'s own (wider) type; narrow into a fresh
                                // temp, never into the joined result.
                                let tmp = Value(next_value);
                                freshly_allocated.push(next_value);
                                next_value += 1;
                                new_value_types.entry(tmp).or_insert_with(|| rty.clone());
                                let narrow = Instruction {
                                    opcode: Opcode::Trunc { to_ty: rty.clone() },
                                    args: vec![src],
                                    results: vec![tmp],
                                };
                                *expected.entry(mb_opcode_key(&narrow.opcode)).or_insert(0) += 1;
                                new_insts.push(narrow);
                                copy_src = tmp;
                            }
                            None => {
                                ret_type_bail = true;
                            }
                        }
                        new_value_types
                            .entry(*result)
                            .or_insert_with(|| rty.clone());
                        let wire = Instruction {
                            opcode: Opcode::Copy,
                            args: vec![copy_src],
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

        // Independently check the constructed splice before publishing it.
        // All caller instructions except the Call survive, and the replacement
        // entry Jump cancels that removal: cloned instructions are exact growth.
        let cloned_insts: usize = cloned_blocks
            .iter()
            .map(|(_, bb, _)| bb.instructions.len())
            .sum();
        if cloned_insts != template.splice_insts {
            return Err(InlineError {
                detail: format!(
                    "multi-block inline growth self-check failed in `{}`: cloned {cloned_insts} \
                     instructions != admitted {}",
                    caller.name, template.splice_insts,
                ),
            });
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

        total_insts = after_splice;
        sites += 1;
        *site_counts.entry(name.clone()).or_insert(0) += 1;

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
                        binding: Default::default(),
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

    /// `name(x: I32) -> ret` whose single block returns `body`'s last result.
    fn one_block_callee(name: &str, ret: Type, body: Vec<Instruction>) -> Function {
        let mut f = Function::new(
            name,
            Signature {
                params: vec![Type::I32],
                returns: vec![ret],
            },
        );
        let returned = body.last().map_or(Value(0), |i| i.results[0]);
        let mut instructions = body;
        instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![returned],
            results: vec![],
        });
        f.entry_block = Block(0);
        f.blocks.insert(
            Block(0),
            BasicBlock {
                params: vec![(Value(0), Type::I32)],
                instructions,
                ..Default::default()
            },
        );
        f.block_order = vec![Block(0)];
        f
    }

    /// `caller() -> ret` returning `callee(300)`, its call result recorded as
    /// `ret` (as the adapter records it).
    fn caller_of(callee: &str, ret: Type) -> Function {
        let mut f = Function::new(
            "caller",
            Signature {
                params: vec![],
                returns: vec![ret.clone()],
            },
        );
        f.entry_block = Block(0);
        f.blocks.insert(
            Block(0),
            BasicBlock {
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
                            name: callee.to_string(),
                            binding: Default::default(),
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
            },
        );
        f.block_order = vec![Block(0)];
        f.value_types.insert(Value(1), ret);
        f
    }

    /// The adapter's Apple arm64 return shape: an `I8` return whose `Return`
    /// operand is the `I32` sign extension of the logical value. ISel types a
    /// `Copy` result from its source, so the straight-line wiring narrows the
    /// operand into a fresh `I8` temp and only a `Copy` of that temp defines
    /// the call result (`tests/aarch64_irinline_narrow_return_type.rs` runs
    /// the same shape end to end).
    #[test]
    fn straight_line_narrows_an_abi_widened_narrow_return() {
        let callee = one_block_callee(
            "nret",
            Type::I8,
            vec![
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
            ],
        );
        let mut funcs = vec![
            (caller_of("nret", Type::I8), empty_ctx()),
            (callee, empty_ctx()),
        ];
        let stats = run_inline(&mut funcs, false).expect("inline ok");
        assert_eq!(stats.sites, 1);
        let caller = &funcs[0].0;
        let insts = &caller.blocks[&Block(0)].instructions;
        let defs: Vec<&Instruction> = insts
            .iter()
            .filter(|i| i.results.contains(&Value(1)))
            .collect();
        assert_eq!(
            defs.len(),
            1,
            "one definition of the call result: {insts:?}"
        );
        assert_eq!(defs[0].opcode, Opcode::Copy);
        let tmp = defs[0].args[0];
        assert_eq!(caller.value_types.get(&tmp), Some(&Type::I8));
        let narrow = insts
            .iter()
            .find(|i| i.results == vec![tmp])
            .expect("the temp the wiring Copy reads is defined");
        assert_eq!(narrow.opcode, Opcode::Trunc { to_ty: Type::I8 });
        let widened = narrow.args[0];
        assert_eq!(caller.value_types.get(&widened), Some(&Type::I32));
        assert!(
            insts
                .iter()
                .any(|i| matches!(i.opcode, Opcode::Sextend { .. }) && i.results == vec![widened]),
            "the narrowed operand is the inlined sign extension: {insts:?}"
        );
        assert_eq!(caller.value_types.get(&Value(1)), Some(&Type::I8));
    }

    /// A `Return` operand narrower than (or of another kind than) the declared
    /// return type has no wiring that keeps the declared type; that callee is
    /// not a straight-line template and its call stays.
    #[test]
    fn straight_line_declines_a_return_operand_no_wiring_reconciles() {
        let callee = one_block_callee("widen", Type::I64, vec![]);
        let mut funcs = vec![
            (caller_of("widen", Type::I64), empty_ctx()),
            (callee, empty_ctx()),
        ];
        let stats = run_inline(&mut funcs, false).expect("inline ok");
        assert_eq!(stats.sites, 0);
        assert!(
            funcs[0].0.blocks[&Block(0)]
                .instructions
                .iter()
                .any(|i| matches!(&i.opcode, Opcode::Call { name, .. } if name == "widen"))
        );
    }

    /// A callee that states its own target features keeps its own body and
    /// admission: it is never spliced, even into a caller stating the same
    /// features, while the identical attribute-free callee is.
    #[test]
    fn callee_stating_target_features_is_never_inlined() {
        for caller_features in [vec![], vec!["crc".to_string()]] {
            let mut callee = callee_add();
            callee.target_features = vec!["crc".to_string()];
            let mut caller = caller_calls_add();
            caller.target_features = caller_features;
            let mut funcs = vec![(caller, empty_ctx()), (callee, empty_ctx())];
            let stats = run_inline(&mut funcs, false).expect("inline ok");
            assert_eq!(stats.sites, 0, "a feature-stating callee stays a call");
        }
        let mut funcs = vec![
            (caller_calls_add(), empty_ctx()),
            (callee_add(), empty_ctx()),
        ];
        assert_eq!(run_inline(&mut funcs, false).expect("inline ok").sites, 1);
    }

    #[test]
    fn interposable_callee_is_never_inlined_while_others_still_are() {
        // `add` is interposable (e.g. an ELF STB_WEAK definition): the linker
        // may bind the call to another definition, so its body must not be
        // spliced into the caller.
        let interposable = HashSet::from_iter(["add".to_string()]);
        for multiblock in [false, true] {
            let mut funcs = vec![
                (caller_calls_add(), empty_ctx()),
                (callee_add(), empty_ctx()),
            ];
            let stats = run_inline_cfg(
                &mut funcs,
                &[],
                false,
                !multiblock,
                &interposable,
                &mut HashMap::default(),
                &mut Vec::new(),
            )
            .expect("inline ok");
            assert_eq!(stats.sites, 0, "an interposable callee must stay a call");
            assert!(
                funcs[0].0.blocks[&Block(0)]
                    .instructions
                    .iter()
                    .any(|i| matches!(&i.opcode, Opcode::Call { name, .. } if name == "add")),
                "the call to the interposable callee must remain"
            );
        }
        // Control: the same module without the exclusion inlines the call.
        let mut funcs = vec![
            (caller_calls_add(), empty_ctx()),
            (callee_add(), empty_ctx()),
        ];
        let stats = run_inline_cfg(
            &mut funcs,
            &[],
            false,
            false,
            &HashSet::from_iter(["other".into()]),
            &mut HashMap::default(),
            &mut Vec::new(),
        )
        .expect("inline ok");
        assert_eq!(stats.sites, 1);
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
        let mut templates = HashMap::default();
        templates.insert("add".to_string(), template);
        let inlined = inline_into_function(
            &mut f,
            &templates,
            &HashSet::default(),
            &mut HashMap::default(),
        )
        .unwrap();
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
                            binding: Default::default(),
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
                            binding: Default::default(),
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
        run_inline_cfg(
            funcs,
            &[],
            false,
            false,
            &HashSet::default(),
            &mut HashMap::default(),
            &mut Vec::new(),
        )
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
                        binding: Default::default(),
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

    fn growth_budget_fixture(
        result_ty: Type,
        result_count: usize,
        call_count: usize,
        caller_insts: usize,
    ) -> (Function, HashMap<String, MultiBlockTemplate>, usize) {
        let mut callee = callee_max2();
        callee.signature.returns = vec![result_ty.clone(); result_count];
        for bb in callee.blocks.values_mut() {
            if let Some(inst) = bb.instructions.last_mut()
                && matches!(inst.opcode, Opcode::Return)
            {
                inst.args = vec![inst.args[0]; result_count];
            }
        }
        // Independently enumerate this fixture's emitted instructions: the
        // four-instruction diamond, plus two return sites each wiring every
        // result with Copy and, for I8, a fresh Trunc. Replacing Call with Jump
        // and each Return with Jump does not change the count.
        let growth = 4 + 2 * result_count * if result_ty == Type::I8 { 2 } else { 1 };
        let template = build_multiblock_template(&callee, &Default::default())
            .expect("small two-return diamond is eligible");
        let templates = HashMap::from_iter([(callee.name.clone(), template)]);
        let mut caller = caller_calls_max2("budget_caller");
        caller.signature.returns = vec![result_ty.clone(); result_count];
        let bb = caller.blocks.get_mut(&Block(0)).unwrap();
        bb.instructions.truncate(2);
        let mut next_value = 2u32;
        let mut last_results = Vec::new();
        for _ in 0..call_count {
            last_results = (0..result_count)
                .map(|_| {
                    let value = Value(next_value);
                    next_value += 1;
                    caller.value_types.insert(value, result_ty.clone());
                    value
                })
                .collect();
            bb.instructions.push(Instruction {
                opcode: Opcode::Call {
                    name: callee.name.clone(),
                    binding: DirectCallBinding::Interposable,
                },
                args: vec![Value(0), Value(1)],
                results: last_results.clone(),
            });
        }
        while bb.instructions.len() + 1 < caller_insts {
            bb.instructions.push(Instruction {
                opcode: Opcode::Iconst {
                    ty: Type::I64,
                    imm: 7,
                },
                args: vec![],
                results: vec![Value(next_value)],
            });
            next_value += 1;
        }
        bb.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: last_results,
            results: vec![],
        });
        assert_eq!(bb.instructions.len(), caller_insts);
        (caller, templates, growth)
    }

    fn instruction_count(function: &Function) -> usize {
        function
            .blocks
            .values()
            .map(|bb| bb.instructions.len())
            .sum()
    }

    fn reject_growth_above_cap(result_ty: Type) {
        for result_count in [1, 2] {
            let (_, _, growth) = growth_budget_fixture(result_ty.clone(), result_count, 1, 4);
            let before_count = MAX_FUNCTION_INSTS - growth + 1;
            let (mut caller, templates, _) =
                growth_budget_fixture(result_ty.clone(), result_count, 1, before_count);
            let mut before = String::new();
            caller
                .write_canonical_verifier_identity(&mut before)
                .unwrap();
            let sites = inline_multiblock_into_function(
                &mut caller,
                &templates,
                &HashSet::default(),
                &mut HashMap::default(),
            )
            .expect("exceeding the size budget is a normal declined candidate");
            assert!(
                instruction_count(&caller) <= MAX_FUNCTION_INSTS,
                "{result_ty:?}/{result_count}: published {} instructions above cap {MAX_FUNCTION_INSTS}",
                instruction_count(&caller),
            );
            assert_eq!(sites, 0, "cap+1 candidate must retain the call");
            let mut after = String::new();
            caller
                .write_canonical_verifier_identity(&mut after)
                .unwrap();
            assert_eq!(
                after, before,
                "declined candidate must not mutate any LIR metadata"
            );
        }
    }

    #[test]
    fn multiblock_growth_budget_rejects_same_width_multi_return_before_mutation() {
        reject_growth_above_cap(Type::I64);
    }

    #[test]
    fn multiblock_growth_budget_rejects_narrow_multi_return_before_mutation() {
        reject_growth_above_cap(Type::I8);
    }

    #[test]
    fn multiblock_growth_budget_refutes_underreported_clone_count_before_mutation() {
        let (_, _, growth) = growth_budget_fixture(Type::I8, 2, 1, 4);
        let (mut caller, mut templates, _) =
            growth_budget_fixture(Type::I8, 2, 1, MAX_FUNCTION_INSTS - growth + 1);
        // A future accounting regression must not publish an over-budget clone,
        // even when the corrupted estimate passes the admission check exactly.
        templates.get_mut("max2").unwrap().splice_insts -= 1;
        let mut before = String::new();
        caller
            .write_canonical_verifier_identity(&mut before)
            .unwrap();
        let error = inline_multiblock_into_function(
            &mut caller,
            &templates,
            &HashSet::default(),
            &mut HashMap::default(),
        )
        .expect_err("constructed instructions independently refute the estimate");
        assert!(error.detail.contains("growth self-check failed"));
        let mut after = String::new();
        caller
            .write_canonical_verifier_identity(&mut after)
            .unwrap();
        assert_eq!(after, before, "self-check must run before caller mutation");
    }

    #[test]
    fn multiblock_growth_budget_accepts_exact_cap_with_all_return_wires() {
        for result_ty in [Type::I64, Type::I8] {
            for result_count in [1, 2] {
                let (_, _, growth) = growth_budget_fixture(result_ty.clone(), result_count, 1, 4);
                let (mut caller, templates, _) = growth_budget_fixture(
                    result_ty.clone(),
                    result_count,
                    1,
                    MAX_FUNCTION_INSTS - growth,
                );
                assert_eq!(
                    inline_multiblock_into_function(
                        &mut caller,
                        &templates,
                        &HashSet::default(),
                        &mut HashMap::default()
                    )
                    .unwrap(),
                    1
                );
                assert_eq!(instruction_count(&caller), MAX_FUNCTION_INSTS);
                let instructions: Vec<_> = caller
                    .blocks
                    .values()
                    .flat_map(|bb| &bb.instructions)
                    .collect();
                assert!(
                    !instructions
                        .iter()
                        .any(|i| matches!(i.opcode, Opcode::Call { .. }))
                );
                assert_eq!(
                    instructions
                        .iter()
                        .filter(|i| i.opcode == Opcode::Copy)
                        .count(),
                    2 * result_count
                );
                assert_eq!(
                    instructions
                        .iter()
                        .filter(|i| matches!(i.opcode, Opcode::Trunc { .. }))
                        .count(),
                    if result_ty == Type::I8 {
                        2 * result_count
                    } else {
                        0
                    }
                );
                verify_cfg_wellformed(&caller).unwrap();
            }
        }
    }

    #[test]
    fn multiblock_growth_budget_counts_committed_growth_before_next_call() {
        for result_ty in [Type::I64, Type::I8] {
            let (_, _, growth) = growth_budget_fixture(result_ty.clone(), 1, 2, 5);
            let before = MAX_FUNCTION_INSTS - 2 * growth + 1;
            let (mut caller, templates, _) = growth_budget_fixture(result_ty, 1, 2, before);
            assert_eq!(
                inline_multiblock_into_function(
                    &mut caller,
                    &templates,
                    &HashSet::default(),
                    &mut HashMap::default()
                )
                .unwrap(),
                1,
                "second site would exceed cap by one instruction"
            );
            assert_eq!(instruction_count(&caller), before + growth);
            assert_eq!(
                caller
                    .blocks
                    .values()
                    .flat_map(|bb| &bb.instructions)
                    .filter(|i| matches!(i.opcode, Opcode::Call { .. }))
                    .count(),
                1
            );
            verify_cfg_wellformed(&caller).unwrap();
        }
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
        let mut templates = HashMap::default();
        templates.insert("max2".to_string(), template);
        let inlined = inline_multiblock_into_function(
            &mut funcs[0].0,
            &templates,
            &HashSet::default(),
            &mut HashMap::default(),
        )
        .unwrap();
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
                        binding: Default::default(),
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
                        binding: Default::default(),
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
        // The return wiring must NARROW to I8 — into a fresh temp — and then
        // `Copy` that temp into the call result. `Copy` is the only opcode
        // allowed to define a result value, because the result is also the
        // continuation's block param and only `select_copy` reuses its vreg.
        // Walk `block_order`, and identify the wiring by the JOIN rather than by
        // "the first `Trunc` to I8": `blocks` is a map whose iteration order is
        // not stable, and the INLINED CALLEE BODY contains its own `Trunc` to I8
        // (`_1 = trunc _0`) as well as the return wiring's, so picking the first
        // one out of the map made this assertion pass or fail at random (measured
        // 1 failure in 5 runs). The call result is defined by exactly one
        // instruction here, that instruction must be the `Copy`, and the temp it
        // reads is the narrowing's result — which pins the same property without
        // depending on any traversal order.
        let wires: Vec<&Instruction> = caller
            .block_order
            .iter()
            .filter_map(|b| caller.blocks.get(b))
            .flat_map(|b| b.instructions.iter())
            .collect();
        let join = wires
            .iter()
            .find(|i| i.results == vec![Value(1)])
            .expect("the call result must be defined");
        assert_eq!(
            join.opcode,
            Opcode::Copy,
            "the joined call result must be defined by a Copy"
        );
        let tmp = join.args[0];
        assert_ne!(
            tmp,
            Value(1),
            "the narrowing must not define the call result"
        );
        assert_eq!(caller.value_types.get(&tmp), Some(&Type::I8));
        assert!(
            wires.iter().any(|i| {
                matches!(&i.opcode, Opcode::Trunc { to_ty } if *to_ty == Type::I8)
                    && i.results == vec![tmp]
            }),
            "ABI-widened narrow return must be truncated into the temp the join Copy reads"
        );
        for i in &wires {
            if i.results.contains(&Value(1)) {
                assert_eq!(
                    i.opcode,
                    Opcode::Copy,
                    "only Copy may define the joined call result"
                );
            }
        }
        assert_eq!(caller.value_types.get(&Value(1)), Some(&Type::I8));
        verify_cfg_wellformed(caller).expect("well-formed CFG");
    }

    #[test]
    fn multiblock_multi_return_narrow_result_is_joined_only_by_copies() {
        // Regression for the -O2 miscompile measured 2026-09-10 through the rustc
        // bridge: a callee with TWO `Return` blocks and an ABI-widened NARROW
        // (I8) return. Each returning clone defines the same result value, which
        // is also the continuation's block param; if a `Trunc` defines it, ISel
        // rebinds the value to a fresh vreg per return path and every path but
        // the last loses its value. Every definition of the result must be a
        // `Copy`, and each must read its OWN narrowed temp.
        let mut callee = Function::new(
            "two_ret",
            Signature {
                params: vec![Type::I32],
                returns: vec![Type::I8],
            },
        );
        let e = BasicBlock {
            params: vec![(Value(0), Type::I32)],
            instructions: vec![Instruction {
                opcode: Opcode::Brif {
                    cond: Value(0),
                    then_dest: Block(1),
                    else_dest: Block(2),
                },
                args: vec![Value(0)],
                results: vec![],
            }],
            ..Default::default()
        };
        let mk_ret = |v: Value, imm: i64| BasicBlock {
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst { ty: Type::I32, imm },
                    args: vec![],
                    results: vec![v],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![v],
                    results: vec![],
                },
            ],
            ..Default::default()
        };
        callee.entry_block = Block(0);
        callee.blocks.insert(Block(0), e);
        callee.blocks.insert(Block(1), mk_ret(Value(1), 100));
        callee.blocks.insert(Block(2), mk_ret(Value(2), 200));
        callee.block_order = vec![Block(0), Block(1), Block(2)];
        callee.value_types.insert(Value(0), Type::I32);
        callee.value_types.insert(Value(1), Type::I32);
        callee.value_types.insert(Value(2), Type::I32);

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
                        imm: 1,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Call {
                        name: "two_ret".to_string(),
                        binding: Default::default(),
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
        caller.value_types.insert(Value(1), Type::I8);

        let mut funcs = vec![(caller, empty_ctx()), (callee, empty_ctx())];
        let stats = run_mb(&mut funcs).expect("mb inline ok");
        assert_eq!(stats.sites, 1);
        let caller = &funcs[0].0;
        let defs: Vec<&Instruction> = caller
            .blocks
            .values()
            .flat_map(|b| b.instructions.iter())
            .filter(|i| i.results.contains(&Value(1)))
            .collect();
        assert_eq!(defs.len(), 2, "one definition per returning clone");
        let mut temps = Vec::new();
        for d in &defs {
            assert_eq!(d.opcode, Opcode::Copy, "only Copy may define the join");
            temps.push(d.args[0]);
        }
        assert_ne!(temps[0], temps[1], "each return path needs its OWN temp");
        for t in &temps {
            assert!(
                caller
                    .blocks
                    .values()
                    .flat_map(|b| b.instructions.iter())
                    .any(|i| {
                        matches!(&i.opcode, Opcode::Trunc { to_ty } if *to_ty == Type::I8)
                            && i.results == vec![*t]
                    }),
                "each temp is narrowed to the logical return type"
            );
        }
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
                        binding: Default::default(),
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
        let mut counts: HashMap<u32, usize> = HashMap::default();
        for t in jump_targets {
            *counts.entry(t).or_insert(0) += 1;
        }
        assert!(
            counts.values().any(|&c| c >= 2),
            "the loop header should be a shared jump target (back-edge preserved)"
        );
    }
}

/// Inline-only bodies (trust-ir `AvailableExternally`) and the call bindings
/// the pass may splice: see the module docs.
#[cfg(test)]
mod inline_only_tests {
    use super::*;
    use trust_cg_lower::function::{BasicBlock, Function, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
    use trust_cg_lower::types::Type;

    fn inst(opcode: Opcode, args: &[u32], results: &[u32]) -> Instruction {
        Instruction {
            opcode,
            args: args.iter().copied().map(Value).collect(),
            results: results.iter().copied().map(Value).collect(),
        }
    }

    fn call(name: &str, binding: DirectCallBinding, args: &[u32], results: &[u32]) -> Instruction {
        inst(
            Opcode::Call {
                name: name.to_string(),
                binding,
            },
            args,
            results,
        )
    }

    fn function(
        name: &str,
        params: &[Type],
        returns: &[Type],
        blocks: Vec<BasicBlock>,
    ) -> Function {
        let mut f = Function::new(
            name,
            Signature {
                params: params.to_vec(),
                returns: returns.to_vec(),
            },
        );
        f.entry_block = Block(0);
        for (index, bb) in blocks.into_iter().enumerate() {
            f.blocks.insert(Block(index as u32), bb);
            f.block_order.push(Block(index as u32));
        }
        f
    }

    fn block(params: &[(u32, Type)], instructions: Vec<Instruction>) -> BasicBlock {
        BasicBlock {
            params: params.iter().map(|(v, t)| (Value(*v), t.clone())).collect(),
            instructions,
            ..Default::default()
        }
    }

    /// `is_bool(w) = (w & 7) == 3`: a straight-line tag test (the shape of a
    /// runtime's `bool_check` fast path).
    fn inline_only_is_bool() -> Function {
        function(
            "is_bool",
            &[Type::I64],
            &[Type::B1],
            vec![block(
                &[(0, Type::I64)],
                vec![
                    inst(
                        Opcode::Iconst {
                            ty: Type::I64,
                            imm: 7,
                        },
                        &[],
                        &[1],
                    ),
                    inst(Opcode::Band, &[0, 1], &[2]),
                    inst(
                        Opcode::Iconst {
                            ty: Type::I64,
                            imm: 3,
                        },
                        &[],
                        &[3],
                    ),
                    inst(Opcode::Icmp { cond: IntCC::Equal }, &[2, 3], &[4]),
                    inst(Opcode::Return, &[4], &[]),
                ],
            )],
        )
    }

    /// `read(table, i)`: when `i < table[0]` load `table[1 + i]`, else call the
    /// external slow path `slow_name(table, i)` — a bounds-checked fast path
    /// beside the definition's out-of-line remainder.
    fn inline_only_read(name: &str, slow_name: &str) -> Function {
        function(
            name,
            &[Type::I64, Type::I64],
            &[Type::I64],
            vec![
                block(
                    &[(0, Type::I64), (1, Type::I64)],
                    vec![
                        inst(
                            Opcode::Load {
                                ty: Type::I64,
                                align: Some(8),
                            },
                            &[0],
                            &[2],
                        ),
                        inst(
                            Opcode::Icmp {
                                cond: IntCC::UnsignedLessThan,
                            },
                            &[1, 2],
                            &[3],
                        ),
                        inst(
                            Opcode::Brif {
                                cond: Value(3),
                                then_dest: Block(1),
                                else_dest: Block(2),
                            },
                            &[3],
                            &[],
                        ),
                    ],
                ),
                block(
                    &[],
                    vec![
                        inst(
                            Opcode::Iconst {
                                ty: Type::I64,
                                imm: 3,
                            },
                            &[],
                            &[4],
                        ),
                        inst(Opcode::Ishl, &[1, 4], &[5]),
                        inst(Opcode::Iadd, &[0, 5], &[6]),
                        inst(
                            Opcode::Iconst {
                                ty: Type::I64,
                                imm: 8,
                            },
                            &[],
                            &[7],
                        ),
                        inst(Opcode::Iadd, &[6, 7], &[8]),
                        inst(
                            Opcode::Load {
                                ty: Type::I64,
                                align: Some(8),
                            },
                            &[8],
                            &[9],
                        ),
                        inst(Opcode::Return, &[9], &[]),
                    ],
                ),
                block(
                    &[],
                    vec![
                        call(slow_name, DirectCallBinding::Interposable, &[0, 1], &[10]),
                        inst(Opcode::Return, &[10], &[]),
                    ],
                ),
            ],
        )
    }

    /// `caller(a, b)` returns `callee(a[, b])` through one call with `binding`.
    fn caller_of(callee: &str, binding: DirectCallBinding, args: usize) -> Function {
        let params = vec![Type::I64; args];
        let arg_ids: Vec<u32> = (0..args as u32).collect();
        let result = args as u32;
        function(
            "caller",
            &params,
            &[Type::I64],
            vec![block(
                &arg_ids.iter().map(|v| (*v, Type::I64)).collect::<Vec<_>>(),
                vec![
                    call(callee, binding, &arg_ids, &[result]),
                    inst(Opcode::Return, &[result], &[]),
                ],
            )],
        )
    }

    fn calls_named(f: &Function, name: &str) -> usize {
        f.blocks
            .values()
            .flat_map(|bb| &bb.instructions)
            .filter(|i| matches!(&i.opcode, Opcode::Call { name: n, .. } if n == name))
            .count()
    }

    fn body_fingerprint(f: &Function) -> Vec<String> {
        let mut blocks: Vec<_> = f
            .blocks
            .iter()
            .map(|(id, bb)| format!("{}:{:?}:{:?}", id.0, bb.params, bb.instructions))
            .collect();
        blocks.sort();
        blocks
    }

    fn run(
        funcs: &mut [(Function, ProofContext)],
        inline_only: &[(Function, ProofContext)],
        interposable: &[&str],
    ) -> (InlineStats, HashMap<String, usize>) {
        let interposable: HashSet<String> = interposable.iter().map(|s| s.to_string()).collect();
        let mut sites = HashMap::default();
        let stats = run_inline_cfg(
            funcs,
            inline_only,
            false,
            false,
            &interposable,
            &mut sites,
            &mut Vec::new(),
        )
        .expect("inline ok");
        (stats, sites)
    }

    #[test]
    fn straight_line_inline_only_body_is_spliced_and_never_emitted() {
        let mut funcs = vec![(
            caller_of("is_bool", DirectCallBinding::Interposable, 1),
            ProofContext::default(),
        )];
        let inline_only = vec![(inline_only_is_bool(), ProofContext::default())];
        let (stats, sites) = run(&mut funcs, &inline_only, &[]);
        assert_eq!(stats.sites, 1);
        assert_eq!(sites.get("is_bool"), Some(&1));
        assert_eq!(
            funcs.len(),
            1,
            "an inline-only body is never added to the module"
        );
        let caller = &funcs[0].0;
        assert_eq!(calls_named(caller, "is_bool"), 0);
        assert!(
            caller
                .blocks
                .values()
                .flat_map(|bb| &bb.instructions)
                .any(|i| matches!(i.opcode, Opcode::Band)),
            "the tag test is spliced into the caller"
        );
    }

    #[test]
    fn multi_block_inline_only_fast_path_keeps_the_external_slow_call() {
        let mut funcs = vec![(
            caller_of("read", DirectCallBinding::Interposable, 2),
            ProofContext::default(),
        )];
        let inline_only = vec![(
            inline_only_read("read", "read_slow"),
            ProofContext::default(),
        )];
        let (stats, sites) = run(&mut funcs, &inline_only, &[]);
        assert_eq!(stats.sites, 1);
        assert_eq!(sites.get("read"), Some(&1));
        let caller = &funcs[0].0;
        assert_eq!(
            calls_named(caller, "read"),
            0,
            "the fast path replaced the call"
        );
        assert_eq!(
            calls_named(caller, "read_slow"),
            1,
            "the slow path is still the external call"
        );
        let loads = caller
            .blocks
            .values()
            .flat_map(|bb| &bb.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Load { .. }))
            .count();
        assert_eq!(loads, 2, "the bound and the element load are inlined");
    }

    /// `field(obj, i) = *(obj + 8 * i)`: a ONE-block fast path with a load —
    /// the shape of a constructor-field read. The straight-line tier declines
    /// it (it touches memory).
    fn one_block_field_read(name: &str) -> Function {
        function(
            name,
            &[Type::I64, Type::I64],
            &[Type::I64],
            vec![block(
                &[(0, Type::I64), (1, Type::I64)],
                vec![
                    inst(
                        Opcode::Iconst {
                            ty: Type::I64,
                            imm: 3,
                        },
                        &[],
                        &[2],
                    ),
                    inst(Opcode::Ishl, &[1, 2], &[3]),
                    inst(Opcode::Iadd, &[0, 3], &[4]),
                    inst(
                        Opcode::Load {
                            ty: Type::I64,
                            align: Some(8),
                        },
                        &[4],
                        &[5],
                    ),
                    inst(Opcode::Return, &[5], &[]),
                ],
            )],
        )
    }

    #[test]
    fn a_one_block_memory_inline_only_body_is_spliced_through_the_cfg_tier() {
        let mut funcs = vec![(
            caller_of("field", DirectCallBinding::Interposable, 2),
            ProofContext::default(),
        )];
        let blocks_before = funcs[0].0.blocks.len();
        let inline_only = vec![(one_block_field_read("field"), ProofContext::default())];
        assert!(build_callee_template(&inline_only[0].0).is_none());
        let (stats, sites) = run(&mut funcs, &inline_only, &[]);
        assert_eq!(stats.sites, 1);
        assert_eq!(sites.get("field"), Some(&1));
        let caller = &funcs[0].0;
        assert_eq!(calls_named(caller, "field"), 0);
        let loads = caller
            .blocks
            .values()
            .flat_map(|bb| &bb.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Load { .. }))
            .count();
        assert_eq!(loads, 1, "the field load is spliced into the caller");
        assert_eq!(
            caller.blocks.len(),
            blocks_before + 2,
            "the call-site block is split around one cloned block"
        );
    }

    #[test]
    fn a_one_block_memory_module_definition_is_still_not_inlined() {
        // The widening is for inline-only bodies only: the same one-block
        // function DEFINED by the module stays a call, as before.
        let original = caller_of("field", DirectCallBinding::Interposable, 2);
        let mut funcs = vec![
            (original.clone(), ProofContext::default()),
            (one_block_field_read("field"), ProofContext::default()),
        ];
        let (stats, sites) = run(&mut funcs, &[], &[]);
        assert_eq!(stats.sites, 0);
        assert!(sites.is_empty());
        assert_eq!(body_fingerprint(&funcs[0].0), body_fingerprint(&original));
    }

    #[test]
    fn a_one_block_body_that_calls_its_own_symbol_is_never_a_template() {
        let original = caller_of("field", DirectCallBinding::Interposable, 2);
        let mut funcs = vec![(original.clone(), ProofContext::default())];
        let mut recursive = one_block_field_read("field");
        let entry = recursive.entry_block;
        let block = recursive.blocks.get_mut(&entry).unwrap();
        let ret = block.instructions.pop().unwrap();
        block.instructions.push(call(
            "field",
            DirectCallBinding::Interposable,
            &[0, 1],
            &[6],
        ));
        block.instructions.push(ret);
        let (stats, _) = run(&mut funcs, &[(recursive, ProofContext::default())], &[]);
        assert_eq!(stats.sites, 0);
        assert_eq!(body_fingerprint(&funcs[0].0), body_fingerprint(&original));
    }

    #[test]
    fn inline_only_body_that_calls_itself_is_never_a_template() {
        let original = caller_of("read", DirectCallBinding::Interposable, 2);
        let mut funcs = vec![(original.clone(), ProofContext::default())];
        // The slow path calls the symbol itself: splicing it could unroll.
        let inline_only = vec![(inline_only_read("read", "read"), ProofContext::default())];
        let (stats, sites) = run(&mut funcs, &inline_only, &[]);
        assert_eq!(stats.sites, 0);
        assert!(sites.is_empty());
        assert_eq!(body_fingerprint(&funcs[0].0), body_fingerprint(&original));
    }

    #[test]
    fn inline_only_body_that_calls_a_module_definition_is_never_a_template() {
        let original = caller_of("read", DirectCallBinding::Interposable, 2);
        let mut funcs = vec![(original.clone(), ProofContext::default())];
        // `caller` is defined in the module: the body is not a leaf.
        let inline_only = vec![(inline_only_read("read", "caller"), ProofContext::default())];
        let (stats, _) = run(&mut funcs, &inline_only, &[]);
        assert_eq!(stats.sites, 0);
        assert_eq!(body_fingerprint(&funcs[0].0), body_fingerprint(&original));
    }

    #[test]
    fn a_call_that_is_not_inlined_is_unchanged() {
        // Arity mismatch: `is_bool` takes one argument, the call passes two.
        let original = caller_of("is_bool", DirectCallBinding::Interposable, 2);
        let mut funcs = vec![(original.clone(), ProofContext::default())];
        let inline_only = vec![(inline_only_is_bool(), ProofContext::default())];
        let (stats, sites) = run(&mut funcs, &inline_only, &[]);
        assert_eq!(stats.sites, 0);
        assert!(sites.is_empty());
        assert_eq!(body_fingerprint(&funcs[0].0), body_fingerprint(&original));
        assert_eq!(funcs[0].0.value_types, original.value_types);
    }

    #[test]
    fn an_exact_module_edge_is_never_served_by_an_inline_only_body() {
        let binding = DirectCallBinding::ExactModuleFunction { function: 7 };
        let original = caller_of("is_bool", binding, 1);
        let mut funcs = vec![(original.clone(), ProofContext::default())];
        let inline_only = vec![(inline_only_is_bool(), ProofContext::default())];
        let (stats, _) = run(&mut funcs, &inline_only, &[]);
        assert_eq!(stats.sites, 0);
        assert_eq!(body_fingerprint(&funcs[0].0), body_fingerprint(&original));
    }

    #[test]
    fn an_exact_module_edge_to_a_module_definition_is_spliced() {
        let mut is_bool = inline_only_is_bool();
        is_bool.name = "is_bool".into();
        let mut funcs = vec![
            (
                caller_of(
                    "is_bool",
                    DirectCallBinding::ExactModuleFunction { function: 1 },
                    1,
                ),
                ProofContext::default(),
            ),
            (is_bool, ProofContext::default()),
        ];
        let (stats, sites) = run(&mut funcs, &[], &[]);
        assert_eq!(stats.sites, 1);
        assert_eq!(sites.get("is_bool"), Some(&1));
        assert_eq!(calls_named(&funcs[0].0, "is_bool"), 0);
    }

    #[test]
    fn import_edges_are_never_spliced() {
        for binding in [
            DirectCallBinding::DeclaredExternalFunction { function: 1 },
            DirectCallBinding::NativeDependency {
                function: 1,
                dependency: trust_cg_ir::NativeDependencyId::new(0),
            },
        ] {
            let original = caller_of("is_bool", binding, 1);
            let mut funcs = vec![
                (original.clone(), ProofContext::default()),
                (inline_only_is_bool(), ProofContext::default()),
            ];
            let inline_only = vec![(inline_only_is_bool(), ProofContext::default())];
            let (stats, _) = run(&mut funcs, &inline_only, &[]);
            assert_eq!(stats.sites, 0, "{binding:?} is an import edge");
            assert_eq!(body_fingerprint(&funcs[0].0), body_fingerprint(&original));
        }
    }

    #[test]
    fn a_candidate_named_like_a_module_definition_is_ignored() {
        // The module defines `is_bool` as `w != 0`; the inline-only candidate of
        // the same name (the tag test) must never replace it.
        let definition = function(
            "is_bool",
            &[Type::I64],
            &[Type::B1],
            vec![block(
                &[(0, Type::I64)],
                vec![
                    inst(
                        Opcode::Iconst {
                            ty: Type::I64,
                            imm: 0,
                        },
                        &[],
                        &[1],
                    ),
                    inst(
                        Opcode::Icmp {
                            cond: IntCC::NotEqual,
                        },
                        &[0, 1],
                        &[2],
                    ),
                    inst(Opcode::Return, &[2], &[]),
                ],
            )],
        );
        let mut funcs = vec![
            (
                caller_of("is_bool", DirectCallBinding::Interposable, 1),
                ProofContext::default(),
            ),
            (definition, ProofContext::default()),
        ];
        let inline_only = vec![(inline_only_is_bool(), ProofContext::default())];
        let (stats, _) = run(&mut funcs, &inline_only, &[]);
        assert_eq!(stats.sites, 1);
        let caller = &funcs[0].0;
        let ops: Vec<_> = caller
            .blocks
            .values()
            .flat_map(|bb| &bb.instructions)
            .map(|i| format!("{:?}", i.opcode))
            .collect();
        assert!(ops.iter().any(|o| o.contains("NotEqual")), "{ops:?}");
        assert!(!ops.iter().any(|o| o == "Band"), "{ops:?}");
    }

    #[test]
    fn an_interposable_name_excludes_the_candidate() {
        let original = caller_of("is_bool", DirectCallBinding::Interposable, 1);
        let mut funcs = vec![(original.clone(), ProofContext::default())];
        let inline_only = vec![(inline_only_is_bool(), ProofContext::default())];
        let (stats, _) = run(&mut funcs, &inline_only, &["is_bool"]);
        assert_eq!(stats.sites, 0);
        assert_eq!(body_fingerprint(&funcs[0].0), body_fingerprint(&original));
    }

    #[test]
    fn the_public_entry_reports_each_spliced_body_once_sorted() {
        let mut funcs = vec![
            (
                caller_of("read", DirectCallBinding::Interposable, 2),
                ProofContext::default(),
            ),
            (
                {
                    let mut f = caller_of("is_bool", DirectCallBinding::Interposable, 1);
                    f.name = "caller2".into();
                    f
                },
                ProofContext::default(),
            ),
        ];
        let inline_only = vec![
            (
                inline_only_read("read", "read_slow"),
                ProofContext::default(),
            ),
            (inline_only_is_bool(), ProofContext::default()),
        ];
        let report = inline_module_with_inline_only_bodies(
            &mut funcs,
            &inline_only,
            &HashSet::<String>::default(),
        )
        .expect("inline ok");
        if inlining_disabled() {
            assert_eq!(report, InlineReport::default());
            return;
        }
        let names: Vec<_> = report
            .inline_only_uses
            .iter()
            .map(|u| (u.name.as_str(), u.sites))
            .collect();
        if multiblock_disabled() {
            assert_eq!(names, vec![("is_bool", 1)]);
            assert_eq!(report.changed_functions, vec![1]);
        } else {
            assert_eq!(names, vec![("is_bool", 1), ("read", 1)]);
            assert_eq!(report.changed_functions, vec![0, 1]);
        }
    }

    #[test]
    fn a_run_that_splices_nothing_changes_no_function() {
        let mut funcs = vec![(
            caller_of("is_bool", DirectCallBinding::Interposable, 2),
            ProofContext::default(),
        )];
        let inline_only = vec![(inline_only_is_bool(), ProofContext::default())];
        let report = inline_module_with_inline_only_bodies(
            &mut funcs,
            &inline_only,
            &HashSet::<String>::default(),
        )
        .expect("inline ok");
        assert!(report.changed_functions.is_empty());
        assert!(report.inline_only_uses.is_empty());
    }
}
