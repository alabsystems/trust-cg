// trust-cg-codegen/wasm/opt.rs - the validated local emission pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The wasm lane's local emission pass, and the per-function translation
//! validation that decides whether its output is used.
//!
//! The lowering binds one local per SSA value and per scratch temporary and
//! moves values between them with `local.get a; local.set b` copies. On the
//! EMITTED body of every function, after `frame_bounds::check` has run on it,
//! the control cleanup of `opt/control.rs` first deletes the branches and
//! `return`s falling through already does, dead code, and the constructs no
//! branch names, and turns one-branch `if` arms into `br_if`; its result is
//! checked against the body by `trust_cg_verify::wasm_local_tv::
//! validate_control` (a lockstep simulation) and, when accepted, is the PRE
//! body of everything below. [`optimize_with`] then applies the segment-local
//! rewrites of `opt/rewrite.rs`
//! in the lowering's own local index space — single-use stackify with
//! `local.tee`, dead-definition `drop`/vacuum, narrow-canonicalization
//! elimination, memarg offset folding, and the load/store expansion of small
//! `memory.copy`s — which also yield a FACT claimed for every local (an
//! unsigned bound, a sign-extension width). On their output it then
//! rewrites:
//!
//! 1. **constant rematerialization** — a declared local whose every write is
//!    `<const k>; local.set l` with one and the same constant `k` (no
//!    relocation in it) or a copy `local.get r; local.set l` from a local
//!    already rematerialized with `k`, and which is either never live at
//!    function entry or has `k == 0` (the value a declared local starts
//!    with), is removed: the writes are deleted with their operand, and every
//!    `local.get l` becomes `<const k>`. Applied when it does not grow the
//!    body; resolved to a fixpoint, so a chain of copies of a constant is
//!    removed whole.
//! 2. **copy-affinity colouring** — liveness of every local over the body's
//!    basic blocks, an interference graph (a local written while another of
//!    its type is live interferes with it, except the source of the copy
//!    that writes it; a declared local live at entry, which reads its zero,
//!    interferes with the parameters), copies coalesced by union-find in
//!    loop-depth order when their classes do not interfere, then greedy
//!    colouring of the classes onto parameter slots and new declared slots.
//!    Parameters are pre-coloured to their own index.
//! 3. **self-copy deletion** — a `local.get c; local.set c` left by the
//!    colouring is deleted, and `local.get c; local.tee c` becomes
//!    `local.get c`; a `local.set c` directly followed by `local.get c` is
//!    `local.tee c`.
//! 4. **reorder by use count** — declared slots are renumbered so the most
//!    referenced ones get the indices with a one-byte LEB128 encoding.
//! 5. **dead writes** — before the colouring (so a dead write costs no slot)
//!    and again after it (where a merged copy can leave one), a write no
//!    path reads is removed by [`drop_dead_writes`]: a `local.tee` is
//!    deleted, a `local.set` is deleted with the `local.get` or constant
//!    directly before it, or becomes `drop`.
//!
//! **Selection.** Single-use stackify carries a pressure condition
//! (`opt/rewrite.rs`, rule 1): a move may not raise the number of locals of
//! a type live at a local write above the most the input has at any write of
//! that type. Where it kept a definition in its local, the candidate without
//! the condition is built as well, and the pressure-limited one is used when
//! it has no more code bytes (fewer declared locals breaking a tie) or when it
//! declares at most [`BASELINE_CACHED_LOCALS`] locals, all `i32`/`i64`, where
//! the other declares more, at a cost of at most [`CACHED_LOCALS_BYTES`]. Both
//! are profitability rules: either candidate is validated the same way. A
//! candidate the validator refuses after dead writes were removed is rebuilt
//! once without that removal before the function keeps its baseline body; the
//! first refusal is counted in [`WasmLocalOptSummary::dead_write_retries`]
//! whatever the rebuild's outcome.
//!
//! Relocations move with the bytes they patch. The pass returns the rewritten
//! body together with the IMAGE of every original local (its new index, its
//! constant, or nothing) and its claimed fact — the claims [`validate_pending`]
//! checks with `trust_cg_verify::wasm_local_tv`, against the module's own
//! function and type signatures, once the whole module is lowered (the pass
//! itself runs then too, because the stack effect of a `call` depends on its
//! callee's final signature).
//!
//! **Fail closed, never refuse.** Until it is validated the module holds each
//! function's BASELINE body: the lane's output before this pass existed
//! (`locals::coalesce` for functions declaring at least
//! [`super::locals::BASELINE_COALESCE_MIN_LOCALS`] locals, the lowering's own
//! body otherwise). A body this pass cannot decode, a function past its
//! liveness or interference budget, a candidate over an engine limit, and a
//! candidate the validator does not accept all keep the baseline, and the
//! reason is counted in [`WasmLocalOptSummary`].
//!
//! **Only at O1 and above.** A module or object compiled at O0 (the rustc
//! bridge's debug profile, or its `no-wasm-local-opt` kill switch) never runs
//! the pass: every function is emitted with its baseline body, byte-identical
//! to the lane before this pass existed.

use std::collections::{BTreeMap, HashMap, HashSet};

use trust_cg_verify::wasm_cfg_proofs::{FuncSig, ValKind};
use trust_cg_verify::wasm_local_tv::{
    self as tv, LocalFacts, LocalImage, ResidualPolicy, TvBody, TvReloc, TvRequest, TvTypes,
};
use trust_cg_verify::wasm_nowrap_premise::{NoWrapPremise, NoWrapRefusal};

use super::encode::{FuncBody, FuncType, Reloc, RelocTarget, ValType, WasmModule, write_uleb128};
use super::locals::{self, Kind};

mod control;
#[cfg(test)]
mod premise_mutants_tests;
mod rewrite;

use rewrite::RewriteStats;

/// Words of block live-in bitsets one function may use.
const MAX_LIVE_WORDS: usize = 1 << 22;
/// Liveness, interference and coalescing steps one function may take.
const MAX_WORK: usize = 1 << 27;
/// Interference edges one function may record.
const MAX_EDGES: usize = 1 << 21;
/// The validator's work budget per function.
const TV_MAX_WORK: usize = 1 << 28;
/// The control-cleanup validator's work budget per function.
const CONTROL_TV_MAX_WORK: usize = 1 << 24;
/// A residual (syntactically unequal) equality rejects the candidate: the
/// emitted bytes never depend on whether, or how fast, an external solver
/// certifies one on the compiling host, and no solver time is spent.
const TV_RESIDUAL: ResidualPolicy = ResidualPolicy::Refuse;

/// A function body before encoding: declared locals, code, relocations.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Body {
    /// Declared (non-parameter) locals, in index order.
    pub declared: Vec<ValType>,
    /// The code (no trailing `end`).
    pub code: Vec<u8>,
    /// Relocations against `code`.
    pub relocs: Vec<Reloc>,
}

/// A rewritten body, the image of every original local and the fact claimed
/// for it (empty: none).
#[derive(Debug, Clone)]
pub(crate) struct Candidate {
    pub body: Body,
    pub image: Vec<LocalImage>,
    pub facts: Vec<LocalFacts>,
    /// Copies deleted (`local.get c; local.set c` and the `tee` form).
    pub copies_deleted: usize,
    /// Locals replaced by a constant.
    pub rematerialized: usize,
    /// What the segment rewrites (`opt/rewrite.rs`) did.
    pub rewrite: RewriteStats,
    /// Writes [`drop_dead_writes`] removed (also counted in `rewrite`).
    pub dead_writes: usize,
}

/// Why [`optimize_with`] produced no candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Decline {
    /// The pass's decoder does not read the body.
    Undecodable,
    /// Liveness or interference exceeded its budget.
    Budget,
    /// Nothing to rewrite.
    NoChange,
}

impl Decline {
    fn as_str(self) -> &'static str {
        match self {
            Decline::Undecodable => "undecodable",
            Decline::Budget => "liveness_budget",
            Decline::NoChange => "no_change",
        }
    }
}

/// One function's body, queued on the module until [`validate_pending`]
/// rewrites and validates it with the module's final signatures.
#[derive(Debug, Clone)]
pub(crate) struct PendingLocalOpt {
    /// The function's index.
    pub func: u32,
    /// The function's name (engine-limit diagnostics).
    pub name: String,
    /// Parameter types.
    pub params: Vec<ValType>,
    /// Result count.
    pub results: usize,
    /// The body the pass starts from (after `frame_bounds::check`).
    pub pre: Body,
    /// Locals that keep a slot of their own (the frame base).
    pub exclusive: Vec<u32>,
    /// The frame-base local and the bound its prologue's stack guard gives
    /// it (`2^32 - 1 - frame size`), for a function whose prologue has one.
    pub frame_base: Option<(u32, u64)>,
    /// The no-wrap premises `trust_cg_verify::wasm_nowrap_premise` admitted
    /// for this body's GEP additions.
    pub premises: Vec<NoWrapPremise>,
    /// The lane's claims the premise checker refused, by reason.
    pub refused: Vec<NoWrapRefusal>,
}

/// What the local emission pass did to one module.
///
/// `optimized` counts functions whose rewritten body the per-segment
/// translation validator (`trust_cg_verify::wasm_local_tv`) accepted against
/// the lane's own pre-colouring body (the control-cleaned body, when the
/// control validator accepted its cleanup). That is an emission-level
/// equivalence of two wasm bodies of one function; it is not a proof that
/// either body computes what the trust-ir function computes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WasmLocalOptSummary {
    /// Whether the pass ran: false at O0, where every function is emitted
    /// with its baseline body and every count below is zero.
    pub enabled: bool,
    /// Functions the pass saw.
    pub functions: usize,
    /// Functions emitted with their validated rewritten body.
    pub optimized: usize,
    /// Functions with nothing to rewrite (not a fallback).
    pub unchanged: usize,
    /// Functions emitted with their baseline body, by reason.
    pub fallbacks: BTreeMap<String, usize>,
    /// Candidates the validator refused after dead writes were removed, by
    /// that refusal's reason; each was rebuilt once without the removal, and
    /// the function is counted again under `optimized` or `fallbacks` by the
    /// rebuild's outcome.
    pub dead_write_retries: BTreeMap<String, usize>,
    /// Declared locals of the baseline bodies of the optimized functions.
    pub declared_locals_before: usize,
    /// Declared locals of the emitted bodies of the optimized functions.
    pub declared_locals_after: usize,
    /// Code bytes of the baseline bodies of the optimized functions.
    pub code_bytes_before: usize,
    /// Code bytes of the emitted bodies of the optimized functions.
    pub code_bytes_after: usize,
    /// Copies deleted in the optimized functions.
    pub copies_deleted: usize,
    /// Locals rematerialized as constants in the optimized functions.
    pub rematerialized: usize,
    /// Definitions moved to their single use in the optimized functions.
    pub stackified: usize,
    /// Of those, the ones that left a `local.tee`.
    pub tees: usize,
    /// Dead definitions deleted or turned into `drop`.
    pub dead_defs: usize,
    /// Narrow masks and sign extensions deleted.
    pub masks_removed: usize,
    /// Constant additions folded into memarg offsets (or of zero, deleted).
    pub offsets_folded: usize,
    /// Small `memory.copy`s expanded into loads and stores.
    pub copies_expanded: usize,
    /// Segments the validator compared.
    pub tv_segments: usize,
    /// Effects the validator compared.
    pub tv_effects: usize,
    /// Residual equalities the solver certified (0 while the emitting
    /// policy refuses residuals).
    pub tv_residuals_proven: usize,
    /// Claimed local facts the validator checked at segment ends.
    pub tv_facts_checked: usize,
    /// Loads and stores the validator compared with a folded offset.
    pub tv_offsets_folded: usize,
    /// Of those, the ones whose comparison used a trust-ir no-wrap premise
    /// of a GEP's address addition (`trust_cg_verify::wasm_nowrap_premise`).
    pub tv_premised_folds: usize,
    /// No-wrap premises the premise checker admitted, over every function
    /// the pass saw.
    pub nowrap_premises: usize,
    /// The lane's no-wrap claims the premise checker refused, by reason.
    pub nowrap_refusals: BTreeMap<String, usize>,
    /// `memory.copy`s the validator matched with a run of loads and stores.
    pub tv_copies_expanded: usize,
    /// Functions emitted with a body derived from their control-cleaned
    /// body (`opt/control.rs`), which the control validator accepted.
    pub control_cleaned: usize,
    /// Control cleanups the control validator refused, by reason; each such
    /// function continues from its uncleaned body.
    pub control_refusals: BTreeMap<String, usize>,
    /// What the accepted cleanups of the emitted functions removed or
    /// rewrote, by rule (`br`, `return`, `dead`, `block`, `else`, `br_if`).
    pub control_rewrites: BTreeMap<String, usize>,
    /// Pairs of program points the control validator visited for them.
    pub tv_control_states: usize,
}

impl WasmLocalOptSummary {
    /// Functions that fell back to their baseline body.
    pub fn fallback_count(&self) -> usize {
        self.fallbacks.values().sum()
    }

    /// Canonical JSON rendering.
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "means": "per-function, per-segment translation validation of the local emission \
                      pass (single-use stackify, tee and dead-definition removal, narrow-mask \
                      elimination, memarg offset folding, small-copy expansion, colouring, \
                      self-copy deletion, reorder, constant rematerialization) against the lane's \
                      own pre-colouring body, after a control cleanup (fall-through branches and \
                      returns, dead code, unnamed constructs, empty else arms, br_if) validated \
                      against the lowering's body by a lockstep simulation; an emission \
                      equivalence, not a proof that the module computes what the trust-ir \
                      functions compute. A fold counted in tv_premised_folds rests on a trust-ir \
                      premise (a defined GEP's address does not pass 2^32 - 1) that a checker \
                      re-derived from the function: those bodies agree on every execution in \
                      which the premised GEPs are defined",
            "enabled": self.enabled,
            "functions": self.functions,
            "optimized": self.optimized,
            "unchanged": self.unchanged,
            "fallback_count": self.fallback_count(),
            "fallbacks": self.fallbacks,
            "dead_write_retries": self.dead_write_retries,
            "declared_locals_before": self.declared_locals_before,
            "declared_locals_after": self.declared_locals_after,
            "code_bytes_before": self.code_bytes_before,
            "code_bytes_after": self.code_bytes_after,
            "copies_deleted": self.copies_deleted,
            "rematerialized": self.rematerialized,
            "stackified": self.stackified,
            "tees": self.tees,
            "dead_defs": self.dead_defs,
            "masks_removed": self.masks_removed,
            "offsets_folded": self.offsets_folded,
            "copies_expanded": self.copies_expanded,
            "tv_segments": self.tv_segments,
            "tv_effects": self.tv_effects,
            "tv_residuals_proven": self.tv_residuals_proven,
            "tv_facts_checked": self.tv_facts_checked,
            "tv_offsets_folded": self.tv_offsets_folded,
            "tv_premised_folds": self.tv_premised_folds,
            "nowrap_premises": self.nowrap_premises,
            "nowrap_refusals": self.nowrap_refusals,
            "tv_copies_expanded": self.tv_copies_expanded,
            "control_cleaned": self.control_cleaned,
            "control_refusals": self.control_refusals,
            "control_rewrites": self.control_rewrites,
            "tv_control_states": self.tv_control_states,
        })
    }
}

/// The validator's kind of a value type.
pub(crate) fn kind_of(v: ValType) -> ValKind {
    match v {
        ValType::I32 => ValKind::I32,
        ValType::I64 => ValKind::I64,
        ValType::F32 => ValKind::F32,
        ValType::F64 => ValKind::F64,
    }
}

fn sig_of(t: &FuncType) -> FuncSig {
    FuncSig {
        params: t.params.iter().copied().map(kind_of).collect(),
        results: t.results.iter().copied().map(kind_of).collect(),
    }
}

fn tv_relocs(relocs: &[Reloc]) -> Vec<TvReloc> {
    relocs
        .iter()
        .map(|r| {
            let target = match r.target {
                RelocTarget::Func(i) => (1u64 << 32) | u64::from(i),
                RelocTarget::Data(i) => (2u64 << 32) | u64::from(i),
                RelocTarget::Global(i) => (3u64 << 32) | u64::from(i),
                RelocTarget::Table => 4u64 << 32,
                RelocTarget::Type(i) => (5u64 << 32) | u64::from(i),
            };
            TvReloc {
                offset: r.offset,
                kind: r.kind as u8,
                target,
                addend: r.addend,
            }
        })
        .collect()
}

struct ModuleTypes<'a>(&'a WasmModule);

impl TvTypes for ModuleTypes<'_> {
    fn func(&self, index: u32) -> Option<FuncSig> {
        self.0.func_type_of(index).map(sig_of)
    }
    fn type_at(&self, index: u32) -> Option<FuncSig> {
        self.0.type_at(index).map(sig_of)
    }
    fn global(&self, index: u32) -> Option<ValKind> {
        self.0.global_type(index).map(kind_of)
    }
}

/// Validate one candidate against its pre body with the module's signatures,
/// under the no-wrap `premises` of the trust-ir function named `function`
/// (active only where bound to that name and to `pre`).
pub(crate) fn validate_candidate(
    module: &WasmModule,
    params: &[ValType],
    pre: &Body,
    cand: &Candidate,
    function: &str,
    premises: &[NoWrapPremise],
) -> Result<tv::TvReport, tv::TvFailure> {
    let params: Vec<ValKind> = params.iter().copied().map(kind_of).collect();
    let pre_locals: Vec<ValKind> = pre.declared.iter().copied().map(kind_of).collect();
    let post_locals: Vec<ValKind> = cand.body.declared.iter().copied().map(kind_of).collect();
    let pre_relocs = tv_relocs(&pre.relocs);
    let post_relocs = tv_relocs(&cand.body.relocs);
    let types = ModuleTypes(module);
    tv::validate_with_premises(
        &TvRequest {
            params: &params,
            pre: TvBody {
                locals: &pre_locals,
                code: &pre.code,
                relocs: &pre_relocs,
            },
            post: TvBody {
                locals: &post_locals,
                code: &cand.body.code,
                relocs: &post_relocs,
            },
            image: &cand.image,
            facts: &cand.facts,
            types: &types,
            residual: TV_RESIDUAL,
            max_work: TV_MAX_WORK,
        },
        function,
        premises,
    )
}

#[cfg(test)]
thread_local! {
    /// Test hook: while `Some`, every module [`validate_pending`] is given,
    /// queue included, as it was before the pass (the baseline bodies).
    pub(crate) static CAPTURED: std::cell::RefCell<Option<Vec<WasmModule>>> =
        const { std::cell::RefCell::new(None) };
}

/// Rewrite every queued body of `module`, validate each candidate, and swap
/// in the accepted ones (module docs). Run once the module's functions and
/// types are final.
pub(crate) fn validate_pending(module: &mut WasmModule) -> WasmLocalOptSummary {
    #[cfg(test)]
    CAPTURED.with(|c| {
        if let Some(v) = c.borrow_mut().as_mut() {
            v.push(module.clone());
        }
    });
    let mut summary = WasmLocalOptSummary::default();
    for p in module.take_local_opt() {
        summary.functions += 1;
        summary.nowrap_premises += p.premises.len();
        for why in &p.refused {
            *summary
                .nowrap_refusals
                .entry(why.as_str().to_string())
                .or_default() += 1;
        }
        let cleaned = clean_control(module, &p, &mut summary);
        let pre = cleaned.as_ref().map_or(&p.pre, |c| &c.body);
        let premises = cleaned.as_ref().map_or(&p.premises, |c| &c.premises);
        let nowrap: Vec<u32> = premises.iter().map(|q| q.result()).collect();
        let attempt = |module: &WasmModule, variant: Variant| {
            optimize_with(
                &p.params,
                pre,
                &p.exclusive,
                p.frame_base,
                &nowrap,
                &ModuleTypes(module),
                variant,
            )
        };
        let mut variant = Variant::FULL;
        let first = match attempt(module, variant) {
            // Where the pressure condition kept a definition in its local,
            // the candidate without it is built too (module docs, selection).
            Ok(c) if c.rewrite.pressure_kept > 0 => {
                let free = Variant {
                    pressure: false,
                    ..variant
                };
                match attempt(module, free) {
                    Ok(f) if !prefer_pressure_limited(&c.body, &f.body) => {
                        variant = free;
                        Ok(f)
                    }
                    _ => Ok(c),
                }
            }
            other => other,
        };
        let cand = match first {
            Ok(c) => c,
            Err(Decline::NoChange) => {
                // Only the control cleanup changed the body: it is emitted
                // as the control validator accepted it.
                match &cleaned {
                    Some(c) => match install_body(module, &p, &c.body, &mut summary) {
                        Ok(()) => c.credit(&mut summary),
                        Err(reason) => *summary.fallbacks.entry(reason).or_default() += 1,
                    },
                    None => summary.unchanged += 1,
                }
                continue;
            }
            Err(d) => {
                *summary.fallbacks.entry(d.as_str().to_string()).or_default() += 1;
                continue;
            }
        };
        let retry = cand.dead_writes > 0;
        let first = install(module, &p, pre, premises, cand, &mut summary);
        let installed = settle(first, retry, &mut summary, |summary| {
            let without = Variant {
                dead_writes: false,
                ..variant
            };
            match attempt(module, without) {
                Ok(c) => install(module, &p, pre, premises, c, summary),
                Err(d) => Err(d.as_str().to_string()),
            }
        });
        if installed && let Some(c) = &cleaned {
            c.credit(&mut summary);
        }
    }
    summary
}

/// A function's control-cleaned body (`opt/control.rs`), accepted by the
/// control validator against the lowering's body, with the no-wrap premises
/// it carried from that body to this one.
struct Cleaned {
    body: Body,
    stats: control::ControlStats,
    states: usize,
    premises: Vec<NoWrapPremise>,
}

impl Cleaned {
    /// Count the cleanup of a function emitted with a body derived from it.
    fn credit(&self, summary: &mut WasmLocalOptSummary) {
        summary.control_cleaned += 1;
        summary.tv_control_states += self.states;
        for (rule, k) in self.stats.by_rule() {
            if k > 0 {
                *summary
                    .control_rewrites
                    .entry(rule.to_string())
                    .or_default() += k;
            }
        }
    }
}

/// Clean `p.pre`'s control and validate the result against it with
/// `wasm_local_tv::validate_control_with_premises`, which carries `p`'s
/// premises to the cleaned body; `None` when nothing changed or the
/// validator refused (counted by reason).
fn clean_control(
    module: &WasmModule,
    p: &PendingLocalOpt,
    summary: &mut WasmLocalOptSummary,
) -> Option<Cleaned> {
    let types = ModuleTypes(module);
    let (body, stats) = control::cleanup(p.results, &p.pre, &types)?;
    let locals: Vec<ValKind> = p.pre.declared.iter().copied().map(kind_of).collect();
    let pre_relocs = tv_relocs(&p.pre.relocs);
    let post_relocs = tv_relocs(&body.relocs);
    let verdict = tv::validate_control_with_premises(
        &tv::ControlTvRequest {
            results: p.results,
            pre: TvBody {
                locals: &locals,
                code: &p.pre.code,
                relocs: &pre_relocs,
            },
            post: TvBody {
                locals: &locals,
                code: &body.code,
                relocs: &post_relocs,
            },
            types: &types,
            max_work: CONTROL_TV_MAX_WORK,
        },
        &p.premises,
    );
    match verdict {
        Ok((report, premises)) => Some(Cleaned {
            body,
            stats,
            states: report.states,
            premises,
        }),
        Err(f) => {
            *summary
                .control_refusals
                .entry(format!("tv_{}", f.kind.as_str()))
                .or_default() += 1;
            None
        }
    }
}

/// Emit `body` for `p`'s function as it is (its declared locals unchanged),
/// within the engine limits, and count it as optimized.
fn install_body(
    module: &mut WasmModule,
    p: &PendingLocalOpt,
    body: &Body,
    summary: &mut WasmLocalOptSummary,
) -> Result<(), String> {
    let runs = super::lower::run_length_encode(&body.declared);
    if super::locals::check_limits(&p.name, p.params.len(), p.results, &runs, body.code.len())
        .is_err()
    {
        return Err("engine_limits".to_string());
    }
    let Some(baseline) = module.body_of(p.func) else {
        return Err("missing_body".to_string());
    };
    let before_locals: usize = baseline.locals.iter().map(|(c, _)| *c as usize).sum();
    let before_code = baseline.code.len();
    let emitted = FuncBody {
        locals: runs,
        code: body.code.clone(),
        relocs: body.relocs.clone(),
    };
    if !module.replace_body(p.func, emitted) {
        return Err("missing_body".to_string());
    }
    summary.optimized += 1;
    summary.declared_locals_before += before_locals;
    summary.declared_locals_after += body.declared.len();
    summary.code_bytes_before += before_code;
    summary.code_bytes_after += body.code.len();
    Ok(())
}

/// Record a function's validation outcome. A `first` refusal of a candidate
/// whose dead writes were removed (`retry`) is counted by its reason in
/// [`WasmLocalOptSummary::dead_write_retries`] and the candidate is rebuilt
/// once without that removal by `rebuild`; a refusal that stands is counted
/// in [`WasmLocalOptSummary::fallbacks`] and the function keeps its baseline
/// body. Returns whether a candidate was installed.
fn settle(
    first: Result<(), String>,
    retry: bool,
    summary: &mut WasmLocalOptSummary,
    rebuild: impl FnOnce(&mut WasmLocalOptSummary) -> Result<(), String>,
) -> bool {
    let verdict = match first {
        Err(reason) if retry => {
            *summary.dead_write_retries.entry(reason).or_default() += 1;
            rebuild(summary)
        }
        other => other,
    };
    match verdict {
        Ok(()) => true,
        Err(reason) => {
            *summary.fallbacks.entry(reason).or_default() += 1;
            false
        }
    }
}

/// Declared locals V8's Liftoff (14.6, arm64, as measured) keeps as constants
/// in its cache on entry when every declared local is `i32` or `i64`; a
/// function declaring more, or declaring any other type, spills them all and
/// zero-fills their frame slots on every call (a store loop past this count).
const BASELINE_CACHED_LOCALS: usize = 12;

/// Code bytes a candidate may spend over another to stay within
/// [`BASELINE_CACHED_LOCALS`] where the other exceeds it: one kept
/// definition, a `local.set` and its `local.get`.
const CACHED_LOCALS_BYTES: usize = 4;

/// Whether the pressure-limited body `limited` is used rather than `free`,
/// the body without the pressure condition (module docs, selection): when
/// it has no more code bytes (fewer declared locals breaking a tie), or when
/// it declares at most [`BASELINE_CACHED_LOCALS`], all `i32`/`i64` (the only
/// case in which Liftoff caches them), where `free` declares more, at a cost
/// of at most [`CACHED_LOCALS_BYTES`].
fn prefer_pressure_limited(limited: &Body, free: &Body) -> bool {
    let (lc, ld) = (limited.code.len(), limited.declared.len());
    let (fc, fd) = (free.code.len(), free.declared.len());
    let cacheable = ld <= BASELINE_CACHED_LOCALS
        && limited
            .declared
            .iter()
            .all(|t| matches!(t, ValType::I32 | ValType::I64));
    (lc, ld) <= (fc, fd)
        || (fd > BASELINE_CACHED_LOCALS && cacheable && lc <= fc + CACHED_LOCALS_BYTES)
}

/// Emit `cand` for `p`'s function when it is within the engine limits and the
/// validator accepts it against `pre` (`p.pre`, or its validated control
/// cleanup) under `premises` (`p.premises`, or those the control validator
/// carried to the cleanup); otherwise return why the function keeps its
/// baseline body.
fn install(
    module: &mut WasmModule,
    p: &PendingLocalOpt,
    pre: &Body,
    premises: &[NoWrapPremise],
    cand: Candidate,
    summary: &mut WasmLocalOptSummary,
) -> Result<(), String> {
    let runs = super::lower::run_length_encode(&cand.body.declared);
    if super::locals::check_limits(
        &p.name,
        p.params.len(),
        p.results,
        &runs,
        cand.body.code.len(),
    )
    .is_err()
    {
        return Err("engine_limits".to_string());
    }
    let verdict = validate_candidate(module, &p.params, pre, &cand, &p.name, premises);
    match verdict {
        Ok(report) => {
            let Some(baseline) = module.body_of(p.func) else {
                return Err("missing_body".to_string());
            };
            let before_locals: usize = baseline.locals.iter().map(|(c, _)| *c as usize).sum();
            let before_code = baseline.code.len();
            let body = FuncBody {
                locals: runs,
                code: cand.body.code.clone(),
                relocs: cand.body.relocs.clone(),
            };
            if !module.replace_body(p.func, body) {
                return Err("missing_body".to_string());
            }
            summary.optimized += 1;
            summary.declared_locals_before += before_locals;
            summary.declared_locals_after += cand.body.declared.len();
            summary.code_bytes_before += before_code;
            summary.code_bytes_after += cand.body.code.len();
            summary.copies_deleted += cand.copies_deleted;
            summary.rematerialized += cand.rematerialized;
            let r = cand.rewrite;
            summary.stackified += r.stackified;
            summary.tees += r.tees;
            summary.dead_defs += r.dead_defs;
            summary.masks_removed += r.masks_removed;
            summary.offsets_folded += r.offsets_folded;
            summary.copies_expanded += r.copies_expanded;
            summary.tv_segments += report.segments;
            summary.tv_effects += report.effects;
            summary.tv_residuals_proven += report.residuals_proven;
            summary.tv_facts_checked += report.facts_checked;
            summary.tv_offsets_folded += report.offsets_folded;
            summary.tv_premised_folds += report.premised_folds;
            summary.tv_copies_expanded += report.copies_expanded;
            Ok(())
        }
        Err(f) => Err(format!("tv_{}", f.kind.as_str())),
    }
}

/// A set of small integers with O(1) insert, remove and iteration.
struct SparseSet {
    members: Vec<u32>,
    pos: Vec<u32>,
}

impl SparseSet {
    fn new(n: usize) -> Self {
        SparseSet {
            members: Vec::new(),
            pos: vec![u32::MAX; n],
        }
    }
    fn insert(&mut self, x: u32) {
        if self.pos[x as usize] == u32::MAX {
            self.pos[x as usize] = self.members.len() as u32;
            self.members.push(x);
        }
    }
    fn remove(&mut self, x: u32) {
        let i = self.pos[x as usize];
        if i == u32::MAX {
            return;
        }
        let last = self.members.pop().unwrap_or(x);
        if last != x {
            self.members[i as usize] = last;
            self.pos[last as usize] = i;
        }
        self.pos[x as usize] = u32::MAX;
    }
    fn contains(&self, x: u32) -> bool {
        self.pos[x as usize] != u32::MAX
    }
    fn clear(&mut self) {
        for &m in &self.members {
            self.pos[m as usize] = u32::MAX;
        }
        self.members.clear();
    }
}

fn uf_find(parent: &mut [u32], x: u32) -> u32 {
    let mut r = x;
    while parent[r as usize] != r {
        r = parent[r as usize];
    }
    let mut c = x;
    while parent[c as usize] != r {
        let next = parent[c as usize];
        parent[c as usize] = r;
        c = next;
    }
    r
}

fn pair(a: u32, b: u32) -> u64 {
    let (lo, hi) = if a < b { (a, b) } else { (b, a) };
    (u64::from(lo) << 32) | u64::from(hi)
}

/// Is the constant instruction `bytes` the zero of its type?
fn const_is_zero(bytes: &[u8]) -> bool {
    match bytes.first() {
        // LEB128 payload bits all clear: zero, whether read signed or not.
        Some(0x41 | 0x42) => bytes[1..].iter().all(|b| b & 0x7f == 0),
        Some(0x43 | 0x44) => bytes[1..].iter().all(|&b| b == 0),
        _ => false,
    }
}

fn uleb_len(v: u64) -> usize {
    let mut n = 1;
    let mut v = v >> 7;
    while v != 0 {
        n += 1;
        v >>= 7;
    }
    n
}

/// Block-level liveness of a decoded body's locals: only a local with an
/// upward-exposed read in some block is ever live across a block boundary.
pub(crate) struct Liveness {
    /// Local -> its liveness bit (`u32::MAX` for none).
    gbit: Vec<u32>,
    /// Liveness bit -> local.
    glocal: Vec<u32>,
    words: usize,
    /// Live-in bitset of every block, `words` words each.
    live_in: Vec<u64>,
}

impl Liveness {
    /// Whether local `l` is live into block `b`.
    pub(crate) fn live_in(&self, b: usize, l: u32) -> bool {
        match self.gbit.get(l as usize) {
            Some(&g) if g != u32::MAX => {
                let g = g as usize;
                self.live_in[b * self.words + g / 64] >> (g % 64) & 1 == 1
            }
            _ => false,
        }
    }

    /// Whether local `l` is live out of block `b`.
    pub(crate) fn live_out(&self, cfg: &locals::Cfg, b: usize, l: u32) -> bool {
        cfg.succs[b].iter().any(|&s| self.live_in(s, l))
    }

    /// The locals live out of block `b`.
    pub(crate) fn live_out_set(&self, cfg: &locals::Cfg, b: usize) -> Vec<u32> {
        let mut out = vec![0u64; self.words];
        for &s in &cfg.succs[b] {
            let row = &self.live_in[s * self.words..(s + 1) * self.words];
            for (o, x) in out.iter_mut().zip(row) {
                *o |= *x;
            }
        }
        let mut set = Vec::new();
        for (wi, &word) in out.iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                set.push(self.glocal[wi * 64 + bits.trailing_zeros() as usize]);
                bits &= bits - 1;
            }
        }
        set
    }
}

/// [`Liveness`] of `ins` over `cfg` for `n` locals, charging `work`.
pub(crate) fn block_liveness(
    ins: &[locals::Ins],
    cfg: &locals::Cfg,
    n: usize,
    work: &mut usize,
) -> Result<Liveness, Decline> {
    let nb = cfg.first.len();
    let mut spend = |w: usize| -> Result<(), Decline> {
        *work = work.saturating_add(w);
        if *work > MAX_WORK {
            Err(Decline::Budget)
        } else {
            Ok(())
        }
    };
    let local_of = |k: Kind| -> Option<(u32, bool)> {
        match k {
            Kind::Get(i) => Some((i, false)),
            Kind::Set(i) | Kind::Tee(i) => Some((i, true)),
            _ => None,
        }
    };
    // Upward-exposed reads and writes per block; locals read before being
    // written in some block are the only ones live across a block boundary.
    let mut gbit = vec![u32::MAX; n];
    let mut glocal: Vec<u32> = Vec::new();
    let mut uses: Vec<Vec<u32>> = vec![Vec::new(); nb];
    let mut defs: Vec<Vec<u32>> = vec![Vec::new(); nb];
    {
        let mut seen = vec![usize::MAX; n];
        let mut wrote = vec![usize::MAX; n];
        for (i, x) in ins.iter().enumerate() {
            let Some((l, write)) = local_of(x.kind) else {
                continue;
            };
            let b = cfg.block_of[i];
            let li = l as usize;
            if write {
                if wrote[li] != b {
                    wrote[li] = b;
                    defs[b].push(l);
                }
                seen[li] = b;
            } else if seen[li] != b {
                seen[li] = b;
                if gbit[li] == u32::MAX {
                    gbit[li] = glocal.len() as u32;
                    glocal.push(l);
                }
                uses[b].push(l);
            }
        }
    }
    let words = glocal.len().div_ceil(64);
    if nb.saturating_mul(words) > MAX_LIVE_WORDS {
        return Err(Decline::Budget);
    }
    let mut live_in = vec![0u64; nb * words];
    if words > 0 {
        let mut queued = vec![true; nb];
        let mut stack: Vec<usize> = (0..nb).collect();
        let mut out = vec![0u64; words];
        while let Some(b) = stack.pop() {
            queued[b] = false;
            out.iter_mut().for_each(|w| *w = 0);
            for &s in &cfg.succs[b] {
                for (o, x) in out.iter_mut().zip(&live_in[s * words..(s + 1) * words]) {
                    *o |= *x;
                }
            }
            for &l in &defs[b] {
                let g = gbit[l as usize];
                if g != u32::MAX {
                    out[g as usize / 64] &= !(1u64 << (g % 64));
                }
            }
            for &l in &uses[b] {
                let g = gbit[l as usize] as usize;
                out[g / 64] |= 1u64 << (g % 64);
            }
            spend(words * (cfg.succs[b].len() + 2))?;
            if out[..] != live_in[b * words..(b + 1) * words] {
                live_in[b * words..(b + 1) * words].copy_from_slice(&out);
                for &q in &cfg.preds[b] {
                    if !queued[q] {
                        queued[q] = true;
                        stack.push(q);
                    }
                }
            }
        }
    }
    Ok(Liveness {
        gbit,
        glocal,
        words,
        live_in,
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Act {
    Keep,
    Delete,
}

/// [`optimize_with`] with every part of the pass on.
#[cfg(test)]
pub(crate) fn optimize(
    params: &[ValType],
    pre: &Body,
    exclusive: &[u32],
    frame_base: Option<(u32, u64)>,
    types: &dyn TvTypes,
) -> Result<Candidate, Decline> {
    optimize_with(
        params,
        pre,
        exclusive,
        frame_base,
        &[],
        types,
        Variant::FULL,
    )
}

/// Which optional parts of the pass a candidate uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Variant {
    /// Rule 1's pressure condition.
    pressure: bool,
    /// The dead-write removal.
    dead_writes: bool,
}

impl Variant {
    const FULL: Variant = Variant {
        pressure: true,
        dead_writes: true,
    };
}

/// Rewrite one function body (module docs) with the parts `variant` turns
/// on. `params` are the function's parameter types; `pre` the lowering's
/// body after `frame_bounds::check`; `frame_base` the frame-base local and the
/// bound its prologue's stack guard gives it, when it has one; `nowrap` the
/// locals whose single write carries an admitted no-wrap premise (rule 4 may
/// fold their addition whatever bounds its operand; the validator decides);
/// `types` the module's signatures. Each local in `exclusive` keeps a slot no
/// other local shares, so the single-write premise `frame_bounds::check`
/// takes of the frame-base local still holds on the emitted body.
fn optimize_with(
    params: &[ValType],
    pre: &Body,
    exclusive: &[u32],
    frame_base: Option<(u32, u64)>,
    nowrap: &[u32],
    types: &dyn TvTypes,
    variant: Variant,
) -> Result<Candidate, Decline> {
    let Variant {
        pressure,
        dead_writes,
    } = variant;
    let n_pre = params.len() + pre.declared.len();
    // A second round reaches the definitions the first one left next to
    // their use (a move can make a set and its read adjacent). Its input
    // keeps the lowering's local index space (plus scratch locals), and
    // every value a pre local holds at a boundary is unchanged, so its
    // claims are claims about the pre locals too.
    let rewritten = match rewrite::rewrite(params, pre, frame_base, nowrap, types, pressure) {
        Some(first) if first.body.code != pre.code => {
            match rewrite::rewrite(params, &first.body, frame_base, nowrap, types, pressure) {
                Some(mut second) => {
                    second.stats = second.stats.plus(first.stats);
                    Some(second)
                }
                None => Some(first),
            }
        }
        other => other,
    };
    let (src, mut facts, mut stats) = match &rewritten {
        Some(r) => (&r.body, r.facts.clone(), r.stats),
        None => (pre, Vec::new(), RewriteStats::default()),
    };
    facts.truncate(n_pre);
    // Dead writes are removed before the colouring, so they cost no slot,
    // and again after it, where a merged copy can leave one.
    let mut removed = 0usize;
    let cleaned = if dead_writes {
        drop_dead_writes(params, src)
    } else {
        None
    };
    let src = match &cleaned {
        Some((body, k)) => {
            removed += k;
            body
        }
        None => src,
    };
    let mut cand = colour(params, src, exclusive)?;
    if dead_writes && let Some((body, k)) = drop_dead_writes(params, &cand.body) {
        cand.body = body;
        removed += k;
    }
    stats.dead_defs += removed;
    cand.dead_writes = removed;
    cand.image.truncate(n_pre);
    cand.facts = facts;
    cand.rewrite = stats;
    if cand.body.code == pre.code && cand.body.declared == pre.declared {
        return Err(Decline::NoChange);
    }
    Ok(cand)
}

/// Rounds of [`drop_dead_writes`] per application: a deleted read can make an
/// earlier write dead.
const DEAD_WRITE_ROUNDS: usize = 3;

/// Delete the writes of `body` whose value no path reads: a dead `local.tee
/// l` is deleted (its value stays on the stack), a dead `local.set l` is
/// deleted together with the `local.get`/constant that directly precedes it
/// in its basic block, or becomes `drop` otherwise. Liveness is that of
/// `body` itself, over its basic blocks, recomputed each round. Returns the
/// body and the writes removed; `None` when it cannot be read (the caller
/// keeps `body`).
fn drop_dead_writes(params: &[ValType], body: &Body) -> Option<(Body, usize)> {
    let n = params.len() + body.declared.len();
    let mut cur = body.clone();
    let mut removed = 0usize;
    for _ in 0..DEAD_WRITE_ROUNDS {
        let (ins, tables) = locals::decode(&cur.code)?;
        if ins.is_empty() {
            break;
        }
        let m = ins.len();
        for x in &ins {
            if let Kind::Get(l) | Kind::Set(l) | Kind::Tee(l) = x.kind
                && l as usize >= n
            {
                return None;
            }
        }
        let mut relocated = vec![false; m];
        for r in &cur.relocs {
            let at = r.offset as usize;
            let k = ins.partition_point(|x| x.start <= at).checked_sub(1)?;
            if at >= ins[k].end {
                return None;
            }
            relocated[k] = true;
        }
        let cfg = locals::cfg(&ins, &tables)?;
        let mut work = 0usize;
        let live = block_liveness(&ins, &cfg, n, &mut work).ok()?;
        // Per instruction: kept, deleted, or (a set) replaced by `drop`.
        let mut act = vec![Act::Keep; m];
        let mut to_drop = vec![false; m];
        let mut set = SparseSet::new(n);
        let mut changed = 0usize;
        for b in 0..cfg.first.len() {
            set.clear();
            for l in live.live_out_set(&cfg, b) {
                set.insert(l);
            }
            for i in (cfg.first[b]..=cfg.last[b]).rev() {
                if act[i] != Act::Keep {
                    continue;
                }
                match ins[i].kind {
                    Kind::Get(l) => set.insert(l),
                    Kind::Set(l) if !set.contains(l) => {
                        let producer = (i > cfg.first[b]).then(|| i - 1).filter(|&j| {
                            !relocated[j]
                                && match ins[j].kind {
                                    Kind::Get(_) => true,
                                    Kind::Plain => matches!(cur.code[ins[j].start], 0x41..=0x44),
                                    _ => false,
                                }
                        });
                        act[i] = Act::Delete;
                        match producer {
                            Some(j) => act[j] = Act::Delete,
                            None => {
                                act[i] = Act::Keep;
                                to_drop[i] = true;
                            }
                        }
                        changed += 1;
                    }
                    Kind::Tee(l) if !set.contains(l) => {
                        act[i] = Act::Delete;
                        changed += 1;
                    }
                    Kind::Set(l) | Kind::Tee(l) => set.remove(l),
                    _ => {}
                }
            }
            // A block whose only straight-line instructions were dead tees
            // passes a value through unchanged; it keeps its last tee, so it
            // still takes and leaves that value.
            let straight =
                |k: Kind| matches!(k, Kind::Plain | Kind::Get(_) | Kind::Set(_) | Kind::Tee(_));
            let range = cfg.first[b]..=cfg.last[b];
            if range.clone().any(|i| act[i] == Act::Delete)
                && range
                    .clone()
                    .all(|i| !straight(ins[i].kind) || act[i] == Act::Delete)
                && let Some(i) = range.rev().find(|&i| matches!(ins[i].kind, Kind::Tee(_)))
            {
                act[i] = Act::Keep;
                changed -= 1;
            }
        }
        if changed == 0 {
            break;
        }
        removed += changed;
        let mut code = Vec::with_capacity(cur.code.len());
        let mut new_start = vec![usize::MAX; m];
        for (i, x) in ins.iter().enumerate() {
            if act[i] != Act::Keep {
                continue;
            }
            new_start[i] = code.len();
            if to_drop[i] {
                code.push(0x1a);
            } else {
                code.extend_from_slice(&cur.code[x.start..x.end]);
            }
        }
        let mut relocs = Vec::with_capacity(cur.relocs.len());
        for r in &cur.relocs {
            let at = r.offset as usize;
            let k = ins.partition_point(|x| x.start <= at).checked_sub(1)?;
            if new_start[k] == usize::MAX {
                return None;
            }
            let offset = u32::try_from(at - ins[k].start + new_start[k]).ok()?;
            relocs.push(Reloc { offset, ..*r });
        }
        cur = Body {
            declared: cur.declared,
            code,
            relocs,
        };
    }
    Some((cur, removed))
}

/// Steps 1-4 of the module docs (rematerialization, colouring, self-copy
/// deletion, reorder) on `pre`, the rewritten body, plus `local.set c;
/// local.get c` merged into `local.tee c` where the colouring left one.
fn colour(params: &[ValType], pre: &Body, exclusive: &[u32]) -> Result<Candidate, Decline> {
    let (ins, tables) = locals::decode(&pre.code).ok_or(Decline::Undecodable)?;
    let m = ins.len();
    let p = params.len();
    let n = p + pre.declared.len();
    if m == 0 || n == 0 {
        return Ok(Candidate {
            body: pre.clone(),
            image: (0..n as u32).map(LocalImage::Local).collect(),
            facts: Vec::new(),
            copies_deleted: 0,
            rematerialized: 0,
            rewrite: RewriteStats::default(),
            dead_writes: 0,
        });
    }
    let ty = |l: usize| -> ValType {
        if l < p {
            params[l]
        } else {
            pre.declared[l - p]
        }
    };
    let local_of = |k: Kind| -> Option<(u32, bool)> {
        match k {
            Kind::Get(i) => Some((i, false)),
            Kind::Set(i) | Kind::Tee(i) => Some((i, true)),
            _ => None,
        }
    };
    for x in &ins {
        if let Some((l, _)) = local_of(x.kind)
            && l as usize >= n
        {
            return Err(Decline::Undecodable);
        }
    }
    // Instructions that carry a relocation are copied verbatim, never
    // rewritten; a relocation outside every instruction is malformed.
    let mut relocated = vec![false; m];
    for r in &pre.relocs {
        let at = r.offset as usize;
        let k = ins
            .partition_point(|x| x.start <= at)
            .checked_sub(1)
            .ok_or(Decline::Undecodable)?;
        if at >= ins[k].end || local_of(ins[k].kind).is_some() {
            return Err(Decline::Undecodable);
        }
        relocated[k] = true;
    }
    let cfg = locals::cfg(&ins, &tables).ok_or(Decline::Undecodable)?;
    let nb = cfg.first.len();
    let mut work = 0usize;
    let live = block_liveness(&ins, &cfg, n, &mut work)?;
    let (gbit, glocal, words, live_in) = (&live.gbit, &live.glocal, live.words, &live.live_in);
    let mut spend = |w: usize| -> Result<(), Decline> {
        work = work.saturating_add(w);
        if work > MAX_WORK {
            Err(Decline::Budget)
        } else {
            Ok(())
        }
    };
    let live_at_entry = |l: usize| -> bool {
        let g = gbit[l];
        g != u32::MAX && live_in[g as usize / 64] >> (g % 64) & 1 == 1
    };

    // 1. Constant rematerialization. A write of `l` is `<const>; local.set l`
    // or the copy `local.get r; local.set l`; a local with a `tee` or any
    // other write is never rematerialized.
    #[derive(Clone, Copy)]
    enum Src {
        Const(usize, usize),
        Copy(u32),
    }
    let mut gets = vec![0usize; n];
    let mut srcs: Vec<Vec<Src>> = vec![Vec::new(); n];
    let mut remat_ok = vec![true; n];
    // `copied_into[r]`: the locals with a write copied from `r`.
    let mut copied_into: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (i, x) in ins.iter().enumerate() {
        match x.kind {
            Kind::Get(l) => gets[l as usize] += 1,
            Kind::Tee(l) => remat_ok[l as usize] = false,
            Kind::Set(l) => {
                let li = l as usize;
                let src = (i > 0).then(|| &ins[i - 1]).and_then(|c| match c.kind {
                    Kind::Plain
                        if matches!(pre.code[c.start], 0x41..=0x44) && !relocated[i - 1] =>
                    {
                        Some(Src::Const(c.start, c.end))
                    }
                    Kind::Get(r) if r != l => Some(Src::Copy(r)),
                    _ => None,
                });
                match src {
                    Some(src) => {
                        if let Src::Copy(r) = src {
                            copied_into[r as usize].push(l);
                        }
                        srcs[li].push(src);
                    }
                    None => remat_ok[li] = false,
                }
            }
            _ => {}
        }
    }
    // A local is rematerialized with the constant `k` when every write is
    // `k` itself or a copy of a local already rematerialized with `k` (so it
    // always holds `k` once written), it is not live at entry unless `k` is
    // the zero it starts with, and replacing it does not grow the body. Each
    // newly rematerialized local re-examines the locals copied from it, so
    // copy chains of a constant resolve in any order.
    let mut remat: Vec<Option<Vec<u8>>> = vec![None; n];
    let mut queue: Vec<u32> = (p as u32..n as u32).rev().collect();
    let mut queued = vec![true; n];
    while let Some(l) = queue.pop() {
        let li = l as usize;
        queued[li] = false;
        if li < p || remat[li].is_some() || !remat_ok[li] || srcs[li].is_empty() {
            continue;
        }
        spend(srcs[li].len() + 1)?;
        let mut k: Option<&[u8]> = None;
        let mut constant = true;
        for src in &srcs[li] {
            let bytes = match *src {
                Src::Const(s, e) => &pre.code[s..e],
                Src::Copy(r) => match remat[r as usize].as_deref() {
                    Some(b) => b,
                    None => {
                        constant = false;
                        break;
                    }
                },
            };
            match k {
                None => k = Some(bytes),
                Some(k0) if k0 != bytes => {
                    constant = false;
                    break;
                }
                Some(_) => {}
            }
        }
        let Some(bytes) = k.filter(|_| constant) else {
            continue;
        };
        if !const_is_zero(bytes) && live_at_entry(li) {
            continue;
        }
        let width = bytes.len();
        let get = 1 + uleb_len(u64::from(l));
        let before = srcs[li].len() * (width + get) + gets[li] * get;
        let after = gets[li] * width;
        if after > before {
            continue;
        }
        remat[li] = Some(bytes.to_vec());
        for &u in &copied_into[li] {
            if !queued[u as usize] {
                queued[u as usize] = true;
                queue.push(u);
            }
        }
    }

    // 2. Interference among the remaining locals.
    let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut edges: HashSet<u64> = HashSet::new();
    let mut live = SparseSet::new(n);
    let mut out = vec![0u64; words];
    for b in 0..nb {
        live.clear();
        out.iter_mut().for_each(|w| *w = 0);
        for &s in &cfg.succs[b] {
            for (o, x) in out.iter_mut().zip(&live_in[s * words..(s + 1) * words]) {
                *o |= *x;
            }
        }
        spend(words * (cfg.succs[b].len() + 1))?;
        for (wi, &word) in out.iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                let l = glocal[wi * 64 + bits.trailing_zeros() as usize];
                bits &= bits - 1;
                if remat[l as usize].is_none() {
                    live.insert(l);
                }
            }
        }
        for i in (cfg.first[b]..=cfg.last[b]).rev() {
            match ins[i].kind {
                Kind::Set(x) | Kind::Tee(x) if remat[x as usize].is_none() => {
                    let src = match (i > cfg.first[b]).then(|| ins[i - 1].kind) {
                        Some(Kind::Get(a)) if a != x && remat[a as usize].is_none() => Some(a),
                        _ => None,
                    };
                    spend(live.members.len() + 1)?;
                    for &y in &live.members {
                        if y != x
                            && Some(y) != src
                            && ty(y as usize) == ty(x as usize)
                            && edges.insert(pair(x, y))
                        {
                            adj[x as usize].push(y);
                            adj[y as usize].push(x);
                        }
                    }
                    if edges.len() > MAX_EDGES {
                        return Err(Decline::Budget);
                    }
                    live.remove(x);
                }
                Kind::Get(x) if remat[x as usize].is_none() => live.insert(x),
                _ => {}
            }
        }
        if b == 0 {
            // Entry: every parameter holds its argument and every declared
            // local its zero, so a declared local live here interferes with
            // each parameter of its type.
            let entry: Vec<u32> = live.members.clone();
            for &l in &entry {
                if (l as usize) < p {
                    continue;
                }
                for q in 0..p as u32 {
                    if ty(q as usize) == ty(l as usize) && edges.insert(pair(q, l)) {
                        adj[q as usize].push(l);
                        adj[l as usize].push(q);
                    }
                }
            }
        }
    }

    // 3. Coalesce copies, innermost loops first.
    let mut depth = vec![0u32; m];
    {
        let mut opened: Vec<bool> = Vec::new();
        let mut d = 0u32;
        for (i, x) in ins.iter().enumerate() {
            match x.kind {
                Kind::Block | Kind::If => opened.push(false),
                Kind::Loop => {
                    opened.push(true);
                    d += 1;
                }
                Kind::End if opened.pop() == Some(true) => d = d.saturating_sub(1),
                _ => {}
            }
            depth[i] = d;
        }
    }
    let mut copies: Vec<(u32, usize, u32, u32)> = Vec::new();
    for i in 1..m {
        let (Kind::Set(b) | Kind::Tee(b)) = ins[i].kind else {
            continue;
        };
        let Kind::Get(a) = ins[i - 1].kind else {
            continue;
        };
        if a != b
            && remat[a as usize].is_none()
            && remat[b as usize].is_none()
            && ty(a as usize) == ty(b as usize)
        {
            copies.push((depth[i], i, a, b));
        }
    }
    copies.sort_by(|x, y| y.0.cmp(&x.0).then(x.1.cmp(&y.1)));
    let mut parent: Vec<u32> = (0..n as u32).collect();
    let mut param_of: Vec<Option<u32>> = (0..n).map(|l| (l < p).then_some(l as u32)).collect();
    for &(_, _, a, b) in &copies {
        if exclusive.contains(&a) || exclusive.contains(&b) {
            continue;
        }
        let ra = uf_find(&mut parent, a);
        let rb = uf_find(&mut parent, b);
        if ra == rb
            || (param_of[ra as usize].is_some() && param_of[rb as usize].is_some())
            || edges.contains(&pair(ra, rb))
        {
            continue;
        }
        // The class with the longer adjacency survives.
        let (keep, gone) = if adj[ra as usize].len() >= adj[rb as usize].len() {
            (ra, rb)
        } else {
            (rb, ra)
        };
        parent[gone as usize] = keep;
        if param_of[keep as usize].is_none() {
            param_of[keep as usize] = param_of[gone as usize];
        }
        let moved = std::mem::take(&mut adj[gone as usize]);
        spend(moved.len() + 1)?;
        for y in moved {
            let ry = uf_find(&mut parent, y);
            if edges.insert(pair(ry, keep)) {
                adj[keep as usize].push(ry);
                adj[ry as usize].push(keep);
            }
        }
        if edges.len() > MAX_EDGES {
            return Err(Decline::Budget);
        }
    }

    // 4. Colour the classes: parameters keep their slot, every other class
    // takes the first slot of its type no neighbour holds.
    let mut first_ref = vec![usize::MAX; n];
    let mut referenced = vec![false; n];
    for (i, x) in ins.iter().enumerate() {
        if let Some((l, _)) = local_of(x.kind) {
            let li = l as usize;
            if remat[li].is_none() {
                referenced[li] = true;
                let r = uf_find(&mut parent, l) as usize;
                first_ref[r] = first_ref[r].min(i);
            }
        }
    }
    const NO_SLOT: u32 = u32::MAX;
    let mut slot = vec![NO_SLOT; n];
    // Slot ids: `0..p` are the parameters; `p + k` is declared slot `k`.
    let mut slot_ty: Vec<ValType> = (0..p).map(ty).collect();
    for q in 0..p {
        let r = uf_find(&mut parent, q as u32) as usize;
        slot[r] = q as u32;
    }
    // An exclusive local is its own class (it took part in no union); its
    // slot is never offered to another class.
    for &e in exclusive {
        let e = e as usize;
        if e >= p && e < n && remat[e].is_none() && first_ref[e] != usize::MAX {
            slot[e] = slot_ty.len() as u32;
            slot_ty.push(ty(e));
        }
    }
    let mut order: Vec<u32> = (0..n as u32)
        .filter(|&l| {
            let li = l as usize;
            parent[li] == l && slot[li] == NO_SLOT && first_ref[li] != usize::MAX
        })
        .collect();
    order.sort_by_key(|&r| (first_ref[r as usize], r));
    let mut by_type: BTreeMap<u8, Vec<u32>> = BTreeMap::new();
    for q in 0..p {
        by_type.entry(ty(q).code()).or_default().push(q as u32);
    }
    let mut mark: Vec<u32> = Vec::new();
    for (stamp, &r) in order.iter().enumerate() {
        let stamp = stamp as u32 + 1;
        let neighbours = adj[r as usize].clone();
        spend(neighbours.len() + 1)?;
        for y in neighbours {
            let ry = uf_find(&mut parent, y) as usize;
            let s = slot[ry];
            if s != NO_SLOT {
                if mark.len() <= s as usize {
                    mark.resize(s as usize + 1, 0);
                }
                mark[s as usize] = stamp;
            }
        }
        let t = ty(r as usize);
        let list = by_type.entry(t.code()).or_default();
        let free = list
            .iter()
            .copied()
            .find(|&s| mark.get(s as usize).copied() != Some(stamp));
        let s = match free {
            Some(s) => s,
            None => {
                let s = slot_ty.len() as u32;
                slot_ty.push(t);
                list.push(s);
                s
            }
        };
        slot[r as usize] = s;
    }
    let slot_of = |parent: &mut [u32], l: u32| -> u32 { slot[uf_find(parent, l) as usize] };

    // 5. Deletions: rematerialized writes with their constant, and copies
    // the colouring turned into self-copies.
    let mut act = vec![Act::Keep; m];
    let mut copies_deleted = 0usize;
    for i in 0..m {
        match ins[i].kind {
            Kind::Set(x) if remat[x as usize].is_some() => {
                act[i] = Act::Delete;
                act[i - 1] = Act::Delete;
            }
            Kind::Set(b) | Kind::Tee(b) if i > 0 && remat[b as usize].is_none() => {
                let Kind::Get(a) = ins[i - 1].kind else {
                    continue;
                };
                if remat[a as usize].is_some()
                    || act[i - 1] != Act::Keep
                    || slot_of(&mut parent, a) != slot_of(&mut parent, b)
                {
                    continue;
                }
                act[i] = Act::Delete;
                if matches!(ins[i].kind, Kind::Set(_)) {
                    act[i - 1] = Act::Delete;
                }
                copies_deleted += 1;
            }
            _ => {}
        }
    }

    // 6. Reorder declared slots by use count: the most used take the indices
    // below 128, grouped by type; the rest follow grouped by type.
    let nslots = slot_ty.len();
    let mut tees: Vec<(usize, Vec<u8>)> = Vec::new();
    let mut uses_of = vec![0usize; nslots];
    for (i, x) in ins.iter().enumerate() {
        if act[i] != Act::Keep {
            continue;
        }
        if let Some((l, _)) = local_of(x.kind)
            && remat[l as usize].is_none()
        {
            uses_of[slot_of(&mut parent, l) as usize] += 1;
        }
    }
    let mut declared_slots: Vec<usize> = (p..nslots).collect();
    declared_slots.sort_by(|&a, &b| uses_of[b].cmp(&uses_of[a]).then(a.cmp(&b)));
    let hot = 128usize.saturating_sub(p).min(declared_slots.len());
    let type_rank = |t: ValType| match t {
        ValType::I32 => 0,
        ValType::I64 => 1,
        ValType::F32 => 2,
        ValType::F64 => 3,
    };
    let (hot_slots, cold_slots) = declared_slots.split_at(hot);
    let mut hot_slots = hot_slots.to_vec();
    let mut cold_slots = cold_slots.to_vec();
    hot_slots.sort_by_key(|&s| type_rank(slot_ty[s]));
    cold_slots.sort_by_key(|&s| type_rank(slot_ty[s]));
    let mut final_index = vec![0u32; nslots];
    for (q, f) in final_index.iter_mut().enumerate().take(p) {
        *f = q as u32;
    }
    let mut new_declared = Vec::with_capacity(nslots - p);
    for (k, &s) in hot_slots.iter().chain(cold_slots.iter()).enumerate() {
        final_index[s] = (p + k) as u32;
        new_declared.push(slot_ty[s]);
    }

    // 7. Re-encode, moving relocations with their instruction. A kept
    // `local.set c` whose next kept instruction is `local.get c` (the same
    // slot) is `local.tee c`.
    let mut code = Vec::with_capacity(pre.code.len());
    let mut new_start = vec![usize::MAX; m];
    let mut merged = vec![false; m];
    for i in 0..m {
        if act[i] != Act::Keep || merged[i] {
            continue;
        }
        let Kind::Set(a) = ins[i].kind else { continue };
        if remat[a as usize].is_some() {
            continue;
        }
        let Some(j) = (i + 1..m).find(|&j| act[j] == Act::Keep) else {
            continue;
        };
        if let Kind::Get(b) = ins[j].kind
            && remat[b as usize].is_none()
            && slot_of(&mut parent, a) == slot_of(&mut parent, b)
        {
            merged[j] = true;
            act[j] = Act::Delete;
            let s = slot_of(&mut parent, a) as usize;
            let mut tee = vec![0x22];
            write_uleb128(&mut tee, u64::from(final_index[s]));
            tees.push((i, tee));
        }
    }
    let tees: HashMap<usize, Vec<u8>> = tees.into_iter().collect();
    for (i, x) in ins.iter().enumerate() {
        if act[i] != Act::Keep {
            continue;
        }
        new_start[i] = code.len();
        if let Some(t) = tees.get(&i) {
            code.extend_from_slice(t);
            continue;
        }
        match x.kind {
            Kind::Get(l) if remat[l as usize].is_some() => {
                code.extend_from_slice(remat[l as usize].as_deref().unwrap_or_default());
            }
            Kind::Get(l) | Kind::Set(l) | Kind::Tee(l) => {
                code.push(pre.code[x.start]);
                let s = slot_of(&mut parent, l) as usize;
                write_uleb128(&mut code, u64::from(final_index[s]));
            }
            _ => code.extend_from_slice(&pre.code[x.start..x.end]),
        }
    }
    let mut relocs = Vec::with_capacity(pre.relocs.len());
    for r in &pre.relocs {
        let at = r.offset as usize;
        let k = ins
            .partition_point(|x| x.start <= at)
            .checked_sub(1)
            .ok_or(Decline::Undecodable)?;
        if act[k] != Act::Keep || new_start[k] == usize::MAX {
            return Err(Decline::Undecodable);
        }
        let offset =
            u32::try_from(at - ins[k].start + new_start[k]).map_err(|_| Decline::Undecodable)?;
        relocs.push(Reloc { offset, ..*r });
    }

    let mut image = Vec::with_capacity(n);
    let mut rematerialized = 0usize;
    for l in 0..n {
        image.push(if let Some(bytes) = &remat[l] {
            rematerialized += 1;
            LocalImage::Const(bytes.clone())
        } else if l < p || referenced[l] {
            LocalImage::Local(final_index[slot_of(&mut parent, l as u32) as usize])
        } else {
            LocalImage::Unused
        });
    }
    Ok(Candidate {
        body: Body {
            declared: new_declared,
            code,
            relocs,
        },
        image,
        facts: Vec::new(),
        copies_deleted,
        rematerialized,
        rewrite: RewriteStats::default(),
        dead_writes: 0,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const GET: u8 = 0x20;
    const SET: u8 = 0x21;
    const I32_CONST: u8 = 0x41;
    const I32_ADD: u8 = 0x6a;
    const I32_STORE: u8 = 0x36;
    const DROP: u8 = 0x1a;
    const BLOCK: u8 = 0x02;
    const LOOP: u8 = 0x03;
    const END: u8 = 0x0b;
    const BR_IF: u8 = 0x0d;
    const VOID: u8 = 0x40;
    const I32: ValType = ValType::I32;
    const I64: ValType = ValType::I64;

    fn body(declared: &[ValType], code: &[u8]) -> Body {
        Body {
            declared: declared.to_vec(),
            code: code.to_vec(),
            relocs: Vec::new(),
        }
    }

    /// No function or type has a signature.
    fn opt(params: &[ValType], pre: &Body) -> Result<Candidate, Decline> {
        optimize(params, pre, &[], None, &ModuleTypes(&WasmModule::new()))
    }

    /// Colour `pre` (steps 1-4 alone) and require the validator to accept it.
    fn coloured(params: &[ValType], pre: &Body) -> Candidate {
        let cand = colour(params, pre, &[]).expect("a candidate");
        let module = WasmModule::new();
        if let Err(f) = validate_candidate(&module, params, pre, &cand, "", &[]) {
            panic!("the validator refused the colouring: {f}");
        }
        cand
    }

    /// Optimize `pre` and require the validator to accept the result.
    fn accepted(params: &[ValType], pre: &Body) -> Candidate {
        let cand = opt(params, pre).expect("a candidate");
        let module = WasmModule::new();
        if let Err(f) = validate_candidate(&module, params, pre, &cand, "", &[]) {
            panic!("the validator refused the pass's own output: {f}");
        }
        cand
    }

    #[test]
    fn a_copy_chain_coalesces_into_its_parameter_and_the_copies_disappear() {
        let pre = body(
            &[I64, I64, I64],
            &[GET, 0, SET, 1, GET, 1, SET, 2, GET, 2, SET, 3, GET, 3, DROP],
        );
        let c = coloured(&[I64], &pre);
        assert!(c.body.declared.is_empty());
        assert_eq!(c.body.code, vec![GET, 0, DROP]);
        assert_eq!(c.copies_deleted, 3);
        assert!(c.image.iter().all(|i| *i == LocalImage::Local(0)));
    }

    #[test]
    fn a_single_def_constant_local_is_rematerialized() {
        let pre = body(
            &[I32],
            &[
                I32_CONST, 7, SET, 1, BLOCK, VOID, END, GET, 1, GET, 0, I32_ADD, DROP,
            ],
        );
        let c = coloured(&[I32], &pre);
        assert!(c.body.declared.is_empty());
        assert_eq!(
            c.body.code,
            vec![BLOCK, VOID, END, I32_CONST, 7, GET, 0, I32_ADD, DROP]
        );
        assert_eq!(c.rematerialized, 1);
        assert_eq!(c.image[1], LocalImage::Const(vec![I32_CONST, 7]));
    }

    #[test]
    fn a_copy_chain_of_a_constant_is_rematerialized_whole() {
        // `a = 9; block {} b = a; c = b; return c + n`, the copies listed
        // before the constant they carry, so one sweep would not see it.
        let pre = body(
            &[I32, I32, I32],
            &[
                I32_CONST, 9, SET, 1, BLOCK, VOID, END, GET, 1, SET, 2, GET, 2, SET, 3, GET, 3,
                GET, 0, I32_ADD, DROP,
            ],
        );
        let c = coloured(&[I32], &pre);
        assert!(c.body.declared.is_empty(), "{:?}", c.body);
        assert_eq!(
            c.body.code,
            vec![BLOCK, VOID, END, I32_CONST, 9, GET, 0, I32_ADD, DROP]
        );
        assert_eq!(c.rematerialized, 3);
        for image in &c.image[1..=3] {
            assert_eq!(*image, LocalImage::Const(vec![I32_CONST, 9]));
        }
        // A copy whose other write is a different constant keeps its local.
        let mixed = body(
            &[I32, I32],
            &[
                I32_CONST, 9, SET, 1, GET, 1, SET, 2, BLOCK, VOID, END, I32_CONST, 8, SET, 2, GET,
                2, DROP,
            ],
        );
        let c = coloured(&[I32], &mixed);
        assert_eq!(c.image[1], LocalImage::Const(vec![I32_CONST, 9]));
        assert!(matches!(c.image[2], LocalImage::Local(_)));
        // A copy from a parameter is never a constant.
        let from_param = body(&[I32], &[GET, 0, SET, 1, BLOCK, VOID, END, GET, 1, DROP]);
        let c = coloured(&[I32], &from_param);
        assert_eq!(c.rematerialized, 0);
    }

    /// `loop { drop a; a = k; br_if n }`: the first iteration reads `a`'s
    /// initial zero.
    fn read_before_write(k: u8) -> Body {
        body(
            &[I32],
            &[
                LOOP, VOID, GET, 1, DROP, I32_CONST, k, SET, 1, GET, 0, BR_IF, 0, END,
            ],
        )
    }

    #[test]
    fn a_constant_read_before_its_write_is_rematerialized_only_when_zero() {
        let c = coloured(&[I32], &read_before_write(0));
        assert_eq!(c.rematerialized, 1);
        // `a` is live at entry holding zero, so a non-zero constant is not
        // what every read sees: the local stays.
        let c = colour(&[I32], &read_before_write(5), &[]);
        assert!(
            c.as_ref().map_or(true, |c| c.rematerialized == 0),
            "a non-zero constant read before its write was rematerialized"
        );
    }

    #[test]
    fn the_most_used_locals_get_one_byte_indices() {
        // 200 simultaneously live locals; local 200 is read eleven times.
        let mut code = Vec::new();
        let mut declared = Vec::new();
        for l in 1..=200u32 {
            code.extend([GET, 0, I32_CONST, 1, I32_ADD, SET]);
            write_uleb128(&mut code, u64::from(l));
            declared.push(I32);
        }
        for l in 1..=200u32 {
            code.push(GET);
            write_uleb128(&mut code, u64::from(l));
            code.push(DROP);
        }
        for _ in 0..10 {
            code.extend([GET, 0xc8, 0x01, DROP]);
        }
        // The parameter stays live to the end, so no local takes its slot.
        code.extend([GET, 0, DROP]);
        let pre = body(&declared, &code);
        let c = coloured(&[I32], &pre);
        assert_eq!(c.body.declared.len(), 200);
        assert_eq!(c.image[200], LocalImage::Local(1));
        assert!(c.body.code.len() < pre.code.len());
    }

    /// A module whose function 0 has `baseline` and a pending `candidate`.
    fn validate_one(pre: &Body, candidate: Candidate) -> (WasmModuleSummary, Vec<u8>) {
        let mut module = WasmModule::new();
        let ty = module.add_type(FuncType {
            params: vec![I32],
            results: vec![I32],
        });
        let baseline = FuncBody {
            locals: super::super::lower::run_length_encode(&pre.declared),
            code: pre.code.clone(),
            relocs: Vec::new(),
        };
        let idx = module.add_function(ty, baseline);
        let pending = PendingLocalOpt {
            func: idx,
            name: "f".to_string(),
            params: vec![I32],
            results: 1,
            pre: pre.clone(),
            exclusive: Vec::new(),
            frame_base: None,
            premises: Vec::new(),
            refused: Vec::new(),
        };
        let mut summary = WasmLocalOptSummary::default();
        if let Err(reason) = install(
            &mut module,
            &pending,
            &pending.pre,
            &[],
            candidate,
            &mut summary,
        ) {
            *summary.fallbacks.entry(reason).or_default() += 1;
        }
        let code = module.body_of(idx).expect("body").code.clone();
        (summary, code)
    }

    type WasmModuleSummary = WasmLocalOptSummary;

    /// `a = n; b = n + 1; store [n] = a; store [n + 4] = b; block {} return
    /// a + b` — `a` and `b` are both live across the block.
    fn two_live() -> Body {
        body(
            &[I32, I32],
            &[
                GET, 0, SET, 1, GET, 0, I32_CONST, 1, I32_ADD, SET, 2, GET, 0, GET, 1, I32_STORE,
                2, 0, GET, 0, GET, 2, I32_STORE, 2, 4, BLOCK, VOID, END, GET, 1, GET, 2, I32_ADD,
            ],
        )
    }

    fn candidate(declared: &[ValType], code: &[u8], image: Vec<LocalImage>) -> Candidate {
        Candidate {
            body: body(declared, code),
            image,
            facts: Vec::new(),
            copies_deleted: 0,
            rematerialized: 0,
            rewrite: RewriteStats::default(),
            dead_writes: 0,
        }
    }

    #[test]
    fn a_valid_candidate_replaces_the_baseline() {
        let pre = two_live();
        let c = accepted(&[I32], &pre);
        let (summary, code) = validate_one(&pre, c.clone());
        assert_eq!(summary.optimized, 1, "{summary:?}");
        assert_eq!(summary.fallback_count(), 0);
        assert_eq!(code, c.body.code);
    }

    /// Each deliberately wrong rewrite is refused by the validator, and the
    /// function keeps its baseline body with the reason counted.
    #[test]
    fn wrong_rewrites_fall_back_to_the_baseline() {
        let pre = two_live();
        let ident = || {
            vec![
                LocalImage::Local(0),
                LocalImage::Local(1),
                LocalImage::Local(2),
            ]
        };
        let mut swapped_image = ident();
        swapped_image.swap(1, 2);
        // `a` and `b` merged into one local although both are live: the
        // stores still see the right values, the block boundary does not.
        let merged = [
            GET, 0, SET, 1, GET, 0, GET, 1, I32_STORE, 2, 0, GET, 0, I32_CONST, 1, I32_ADD, SET, 1,
            GET, 0, GET, 1, I32_STORE, 2, 4, BLOCK, VOID, END, GET, 1, GET, 1, I32_ADD,
        ];
        // The two stores in the other order.
        let reordered = [
            GET, 0, SET, 1, GET, 0, I32_CONST, 1, I32_ADD, SET, 2, GET, 0, GET, 2, I32_STORE, 2, 4,
            GET, 0, GET, 1, I32_STORE, 2, 0, BLOCK, VOID, END, GET, 1, GET, 2, I32_ADD,
        ];
        // `a` (a copy of the parameter) claimed to be the constant 0.
        let remat = [
            GET, 0, I32_CONST, 1, I32_ADD, SET, 2, GET, 0, I32_CONST, 0, I32_STORE, 2, 0, GET, 0,
            GET, 2, I32_STORE, 2, 4, BLOCK, VOID, END, I32_CONST, 0, GET, 2, I32_ADD,
        ];
        let cases: Vec<(&str, Candidate, &str)> = vec![
            (
                "swap two locals",
                candidate(&[I32, I32], &pre.code, swapped_image),
                "tv_live_out_mismatch",
            ),
            (
                "drop a live-out",
                candidate(
                    &[I32],
                    &merged,
                    vec![
                        LocalImage::Local(0),
                        LocalImage::Local(1),
                        LocalImage::Local(1),
                    ],
                ),
                "tv_live_out_mismatch",
            ),
            (
                "reorder an effect",
                candidate(&[I32, I32], &reordered, ident()),
                "tv_effect_mismatch",
            ),
            (
                "remat a non-constant",
                candidate(
                    &[I32, I32],
                    &remat,
                    vec![
                        LocalImage::Local(0),
                        LocalImage::Const(vec![I32_CONST, 0]),
                        LocalImage::Local(2),
                    ],
                ),
                "tv_effect_mismatch",
            ),
        ];
        for (what, cand, reason) in cases {
            let (summary, code) = validate_one(&pre, cand);
            assert_eq!(summary.optimized, 0, "{what}: accepted");
            assert_eq!(summary.fallback_count(), 1, "{what}: {summary:?}");
            // The emitting policy refuses every residual, so the difference
            // is reported by its own class, without a solver.
            let (got, _) = summary.fallbacks.iter().next().expect("one reason");
            assert_eq!(got, reason, "{what}: fell back for `{got}`");
            assert_eq!(code, pre.code, "{what}: the baseline body was not kept");
        }
    }

    #[test]
    fn an_unreadable_body_is_declined() {
        // An atomic (0xfe) instruction is outside the pass's decoder.
        let pre = body(&[I32], &[GET, 0, 0xfe, 0x10, 2, 0, SET, 1]);
        assert_eq!(opt(&[I32], &pre).err(), Some(Decline::Undecodable));
    }

    // ---- The segment rewrites (`opt/rewrite.rs`) ----

    const TEE: u8 = 0x22;
    const I32_MUL: u8 = 0x6c;
    const I32_AND: u8 = 0x71;
    const I32_DIV_S: u8 = 0x6d;
    const I32_LOAD: u8 = 0x28;
    const I32_LOAD8_S: u8 = 0x2c;
    const I32_LOAD8_U: u8 = 0x2d;
    const I32_LOAD16_U: u8 = 0x2f;
    const EXTEND8_S: u8 = 0xc0;
    const MEMORY_COPY: [u8; 4] = [0xfc, 0x0a, 0x00, 0x00];

    /// The opcodes of `code`, as the validator's decoder reads them.
    fn opcodes(code: &[u8]) -> Vec<u8> {
        trust_cg_verify::wasm_cfg_proofs::decode_body(code, 0)
            .expect("decodes")
            .iter()
            .map(|x| x.opcode)
            .collect()
    }

    #[test]
    fn a_single_use_chain_is_stackified_into_one_expression() {
        // t1 = n + 1; t2 = t1 * 4; return t2
        let pre = body(
            &[I32, I32],
            &[
                GET, 0, I32_CONST, 1, I32_ADD, SET, 1, GET, 1, I32_CONST, 4, I32_MUL, SET, 2, GET,
                2,
            ],
        );
        let c = accepted(&[I32], &pre);
        assert_eq!(
            c.body.code,
            vec![GET, 0, I32_CONST, 1, I32_ADD, I32_CONST, 4, I32_MUL]
        );
        assert!(c.body.declared.is_empty());
        assert_eq!(c.rewrite.stackified, 2);
        assert_eq!(c.image[1], LocalImage::Unused);
    }

    #[test]
    fn a_value_read_twice_becomes_a_tee_at_its_first_read() {
        // t = n * n; store [n] = 7; return t + t — `n * n` moves past the
        // store (it is pure) to its first read, which keeps it in a tee.
        let pre = body(
            &[I32],
            &[
                GET, 0, GET, 0, I32_MUL, SET, 1, GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 1,
                GET, 1, I32_ADD,
            ],
        );
        let c = accepted(&[I32], &pre);
        let ops = opcodes(&c.body.code);
        assert_eq!(
            ops,
            vec![
                GET, I32_CONST, I32_STORE, GET, GET, I32_MUL, TEE, GET, I32_ADD
            ]
        );
        assert_eq!(c.rewrite.tees, 1);
    }

    #[test]
    fn an_effect_never_moves_past_another_effect() {
        // t = load [n]; store [n] = 7; return t — the load stays before the
        // store. t = n / n (traps on 0); store; return t — the division stays
        // before the store.
        for def in [
            vec![GET, 0, I32_LOAD, 2, 0],
            vec![GET, 0, GET, 0, I32_DIV_S],
        ] {
            let mut code = def.clone();
            code.extend([SET, 1, GET, 0, I32_CONST, 7, I32_STORE, 2, 0, GET, 1]);
            let pre = body(&[I32], &code);
            // Nothing else to rewrite: the pass declines, leaving the body.
            assert_eq!(opt(&[I32], &pre).err(), Some(Decline::NoChange));
        }
    }

    #[test]
    fn dead_definitions_are_vacuumed_or_dropped() {
        // t = n * 3 (dead, pure): deleted. u = load [n] (dead, may trap):
        // dropped, the load kept.
        let pre = body(
            &[I32, I32],
            &[
                GET, 0, I32_CONST, 3, I32_MUL, SET, 1, GET, 0, I32_LOAD, 2, 0, SET, 2, GET, 0,
            ],
        );
        let c = accepted(&[I32], &pre);
        assert_eq!(c.body.code, vec![GET, 0, I32_LOAD, 2, 0, DROP, GET, 0]);
        assert_eq!(c.rewrite.dead_defs, 2);
    }

    #[test]
    fn a_mask_or_extension_after_an_already_canonical_producer_is_removed() {
        let cases: Vec<(Vec<u8>, Vec<u8>, usize)> = vec![
            // load8_u & 0xff: removed.
            (
                vec![GET, 0, I32_LOAD8_U, 0, 0, I32_CONST, 0xff, 0x01, I32_AND],
                vec![GET, 0, I32_LOAD8_U, 0, 0],
                1,
            ),
            // load16_u & 0xff: kept (a non-canonical producer).
            (
                vec![GET, 0, I32_LOAD16_U, 1, 0, I32_CONST, 0xff, 0x01, I32_AND],
                vec![GET, 0, I32_LOAD16_U, 1, 0, I32_CONST, 0xff, 0x01, I32_AND],
                0,
            ),
            // extend8_s(load8_s): removed; extend8_s(load): kept.
            (
                vec![GET, 0, I32_LOAD8_S, 0, 0, EXTEND8_S],
                vec![GET, 0, I32_LOAD8_S, 0, 0],
                1,
            ),
            (
                vec![GET, 0, I32_LOAD, 2, 0, EXTEND8_S],
                vec![GET, 0, I32_LOAD, 2, 0, EXTEND8_S],
                0,
            ),
            // (n == 3) & 1: removed.
            (
                vec![GET, 0, I32_CONST, 3, 0x46, I32_CONST, 1, I32_AND],
                vec![GET, 0, I32_CONST, 3, 0x46],
                1,
            ),
        ];
        for (code, want, removed) in cases {
            let pre = body(&[], &code);
            match opt(&[I32], &pre) {
                Ok(c) => {
                    validate_candidate(&WasmModule::new(), &[I32], &pre, &c, "", &[])
                        .unwrap_or_else(|f| panic!("{code:02x?}: refused: {f}"));
                    assert_eq!(c.body.code, want, "{code:02x?}");
                    assert_eq!(c.rewrite.masks_removed, removed, "{code:02x?}");
                }
                Err(Decline::NoChange) => {
                    assert_eq!(want, code);
                    assert_eq!(removed, 0);
                }
                Err(d) => panic!("{code:02x?}: declined {d:?}"),
            }
        }
    }

    #[test]
    fn an_address_folds_into_the_offset_only_when_it_cannot_wrap() {
        // n + 0: always. (n & 0xff) + 8: bounded, folds. n + 8 with n a
        // parameter: may wrap, stays.
        let cases: Vec<(Vec<u8>, Vec<u8>)> = vec![
            (
                vec![GET, 0, I32_CONST, 0, I32_ADD, I32_LOAD, 2, 4],
                vec![GET, 0, I32_LOAD, 2, 4],
            ),
            (
                vec![
                    GET, 0, I32_CONST, 0xff, 0x01, I32_AND, I32_CONST, 8, I32_ADD, I32_LOAD, 2, 4,
                ],
                vec![GET, 0, I32_CONST, 0xff, 0x01, I32_AND, I32_LOAD, 2, 12],
            ),
            (
                vec![GET, 0, I32_CONST, 8, I32_ADD, I32_LOAD, 2, 4],
                vec![GET, 0, I32_CONST, 8, I32_ADD, I32_LOAD, 2, 4],
            ),
        ];
        for (code, want) in cases {
            let pre = body(&[], &code);
            match opt(&[I32], &pre) {
                Ok(c) => {
                    validate_candidate(&WasmModule::new(), &[I32], &pre, &c, "", &[])
                        .unwrap_or_else(|f| panic!("{code:02x?}: refused: {f}"));
                    assert_eq!(c.body.code, want, "{code:02x?}");
                }
                Err(Decline::NoChange) => assert_eq!(want, code),
                Err(d) => panic!("{code:02x?}: declined {d:?}"),
            }
        }
    }

    /// `f(%0: ptr) -> u32 { %1 = const usize 8; %2 = gep u8, ptr %0, %1;
    /// %3 = load u32, ptr %2 [offset=k]; ret %3 }` lowered as the lane does
    /// (`%n` in local `n`), and the premise the checker re-derives for it.
    fn gep_body(load_offset: &[u8]) -> (Body, Vec<NoWrapPremise>) {
        use trust_cg_verify::wasm_nowrap_premise::{NoWrapClaim, check_nowrap_premises};
        let module = trust_ir::parser::parse_module(
            "module \"nowrap\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
             functy.0 = (ptr) -> (u32)\n\nfn @f(functy.0) {\nbb0(%0: ptr):\n    \
             %1 = const usize 8\n    %2 = gep u8, ptr %0, %1\n    %3 = load u32, ptr %2\n    \
             ret %3\n}\n",
        )
        .expect("parses");
        let mut code = vec![
            I32_CONST, 8, SET, 1, GET, 0, GET, 1, I32_ADD, SET, 2, GET, 2, I32_LOAD, 2,
        ];
        code.extend_from_slice(load_offset);
        code.extend([SET, 3, GET, 3]);
        let pre = body(&[I32, I32, I32], &code);
        let slots: Vec<(trust_ir::ValueId, u32)> =
            (0..4).map(|n| (trust_ir::ValueId::new(n), n)).collect();
        let check = check_nowrap_premises(
            &module,
            &module.functions[0],
            &slots,
            &[ValKind::I32],
            &TvBody {
                locals: &[ValKind::I32; 3],
                code: &pre.code,
                relocs: &[],
            },
            &[NoWrapClaim {
                value: trust_ir::ValueId::new(2),
                add_offset: 8,
            }],
        );
        assert!(check.refused.is_empty(), "{check:?}");
        (pre, check.premises)
    }

    /// A GEP's addition carries its no-wrap premise into rule 4: the pass
    /// folds `x + 8` for a parameter `x` only with the premise, the validator
    /// accepts the fold only with it, and a fold whose offset would leave the
    /// `u32` range is not made.
    #[test]
    fn a_premised_gep_addition_folds_into_the_offset() {
        let types = ModuleTypes(&WasmModule::new());
        let (pre, premises) = gep_body(&[0]);
        let nowrap: Vec<u32> = premises.iter().map(|p| p.result()).collect();
        assert_eq!(nowrap, vec![2]);
        let plain = optimize_with(&[I32], &pre, &[], None, &[], &types, Variant::FULL)
            .expect("a candidate");
        assert_eq!(plain.rewrite.offsets_folded, 0);
        validate_candidate(&WasmModule::new(), &[I32], &pre, &plain, "f", &premises)
            .expect("validated");
        let c = optimize_with(&[I32], &pre, &[], None, &nowrap, &types, Variant::FULL)
            .expect("a candidate");
        assert_eq!(c.rewrite.offsets_folded, 1);
        assert_eq!(
            c.body.code,
            vec![GET, 0, I32_LOAD, 2, 8],
            "{:02x?}",
            c.body.code
        );
        let report = validate_candidate(&WasmModule::new(), &[I32], &pre, &c, "f", &premises)
            .expect("validated");
        assert_eq!((report.offsets_folded, report.premised_folds), (1, 1));
        let f =
            validate_candidate(&WasmModule::new(), &[I32], &pre, &c, "", &[]).expect_err("refused");
        assert_eq!(f.kind, tv::TvFailureKind::EffectMismatch, "{f}");
        // offset=0xFFFF_FFF8: adding 8 leaves the memarg's range.
        let (pre, premises) = gep_body(&[0xf8, 0xff, 0xff, 0xff, 0x0f]);
        let c = optimize_with(&[I32], &pre, &[], None, &[2], &types, Variant::FULL)
            .expect("a candidate");
        assert_eq!(c.rewrite.offsets_folded, 0, "{:02x?}", c.body.code);
        validate_candidate(&WasmModule::new(), &[I32], &pre, &c, "f", &premises)
            .expect("validated");
    }

    /// A framed body as the lowering emits it in a closed module: the
    /// prologue carves 32 bytes, guards the new stack pointer, then
    /// `a = base + 16; store [a + 8] = n; store [base + 4] = n`.
    fn guarded_frame() -> Body {
        // Locals: 1 saved sp, 2 base, 3 a.
        body(
            &[I32, I32, I32],
            &[
                0x23, 0, SET, 1, GET, 1, I32_CONST, 32, I32_SUB_, TEE, 2, 0x24, 0, GET, 2,
                I32_CONST, 0x80, 0x08, 0x49, GET, 2, GET, 1, 0x4b, 0x72, 0x04, VOID, 0x00, END,
                GET, 2, I32_CONST, 16, I32_ADD, SET, 3, BLOCK, VOID, END, GET, 3, I32_CONST, 8,
                I32_ADD, GET, 0, I32_STORE, 2, 0, GET, 2, I32_CONST, 4, I32_ADD, GET, 0, I32_STORE,
                2, 0, GET, 1, 0x24, 0,
            ],
        )
    }
    const I32_SUB_: u8 = 0x6b;

    #[test]
    fn a_guarded_frame_base_lets_frame_offsets_fold() {
        let pre = guarded_frame();
        let mut module = WasmModule::new();
        module
            .add_global(I32, true, super::super::encode::GlobalInit::I32(65536))
            .expect("the stack pointer global");
        let types = ModuleTypes(&module);
        // Without the guard's bound nothing folds through the frame base.
        let plain = optimize(&[I32], &pre, &[2], None, &types).expect("a candidate");
        validate_candidate(&module, &[I32], &pre, &plain, "", &[]).expect("validated");
        assert_eq!(plain.rewrite.offsets_folded, 0);
        let bound = u64::from(u32::MAX) - 32;
        let c = optimize(&[I32], &pre, &[2], Some((2, bound)), &types).expect("a candidate");
        let report = validate_candidate(&module, &[I32], &pre, &c, "", &[]).expect("validated");
        assert_eq!(c.rewrite.offsets_folded, 2, "{:02x?}", c.body.code);
        assert_eq!(report.offsets_folded, 2);
        assert!(report.facts_checked > 0);
        // A bound the guard does not give (a frame of 64 claimed for a carve
        // of 32) is refused by the validator.
        let wrong = optimize(
            &[I32],
            &pre,
            &[2],
            Some((2, u64::from(u32::MAX) - 64)),
            &types,
        )
        .expect("a candidate");
        let f = validate_candidate(&module, &[I32], &pre, &wrong, "", &[]).expect_err("refused");
        assert_eq!(f.kind, tv::TvFailureKind::FactUnproven, "{f}");
    }

    #[test]
    fn a_small_copy_becomes_loads_then_stores() {
        for n in [1u8, 3, 8, 12, 13, 24, 31, 32] {
            let mut code = vec![GET, 0, GET, 1, I32_CONST, n];
            code.extend(MEMORY_COPY);
            let pre = body(&[], &code);
            let c = accepted(&[I32, I32], &pre);
            let ops = opcodes(&c.body.code);
            assert!(!ops.contains(&0xfc), "n = {n}: {ops:02x?}");
            assert_eq!(c.rewrite.copies_expanded, 1);
            let last_load = ops.iter().rposition(|o| (0x28..=0x35).contains(o));
            let first_store = ops.iter().position(|o| (0x36..=0x3e).contains(o));
            assert!(last_load < first_store, "n = {n}: {ops:02x?}");
        }
        // 33 bytes stay a memory.copy.
        let mut code = vec![GET, 0, GET, 1, I32_CONST, 33];
        code.extend(MEMORY_COPY);
        assert_eq!(
            opt(&[I32, I32], &body(&[], &code)).err(),
            Some(Decline::NoChange)
        );
    }

    // ---- Pressure, dead writes and selection ----

    fn variant(pressure: bool, dead_writes: bool) -> Variant {
        Variant {
            pressure,
            dead_writes,
        }
    }

    /// `t = p0 + p1; u = p2 * 3; return (u - t) + u`: `p0` and `p1` are last
    /// read by `t`'s definition, and `u` is written between that definition
    /// and `t`'s read. Every write of the input has two locals live after it,
    /// so moving `t` past `u`'s write (which would keep `p0` and `p1` live
    /// there instead of `t`) exceeds the peak.
    fn pressure_body() -> Body {
        body(
            &[I32, I32],
            &[
                GET, 0, GET, 1, I32_ADD, SET, 3, GET, 2, I32_CONST, 3, I32_MUL, SET, 4, GET, 4,
                GET, 3, I32_SUB_, GET, 4, I32_ADD,
            ],
        )
    }

    fn accepted_variant(params: &[ValType], pre: &Body, v: Variant) -> Candidate {
        let module = WasmModule::new();
        let cand = optimize_with(params, pre, &[], None, &[], &ModuleTypes(&module), v)
            .expect("a candidate");
        if let Err(f) = validate_candidate(&module, params, pre, &cand, "", &[]) {
            panic!("the validator refused {v:?}: {f}");
        }
        cand
    }

    #[test]
    fn stackify_keeps_a_definition_whose_move_would_exceed_the_peak_pressure() {
        let pre = pressure_body();
        let params = [I32, I32, I32];
        let limited = accepted_variant(&params, &pre, variant(true, true));
        // Refused in both rounds.
        assert_eq!(
            limited.rewrite.pressure_kept, 2,
            "{:02x?}",
            limited.body.code
        );
        // `t` keeps its own write; `u` still moves to its first read.
        let ops = opcodes(&limited.body.code);
        assert_eq!(
            ops,
            vec![
                GET, GET, I32_ADD, SET, GET, I32_CONST, I32_MUL, TEE, GET, I32_SUB_, GET, I32_ADD
            ]
        );
        let free = accepted_variant(&params, &pre, variant(false, true));
        assert_eq!(free.rewrite.pressure_kept, 0);
        assert_eq!(
            opcodes(&free.body.code),
            vec![
                GET, I32_CONST, I32_MUL, TEE, GET, GET, I32_ADD, I32_SUB_, GET, I32_ADD
            ]
        );
        // Both fit the parameter slots; the unlimited one is smaller and is
        // the one selected.
        assert!(free.body.code.len() < limited.body.code.len());
        assert!(!prefer_pressure_limited(&limited.body, &free.body));
    }

    #[test]
    fn a_move_under_the_peak_is_not_refused() {
        // t = p0 + p1; store [p2] = 5; return t: no local write between
        // `t`'s definition and its read.
        let pre = body(
            &[I32],
            &[
                GET, 0, GET, 1, I32_ADD, SET, 3, GET, 2, I32_CONST, 5, I32_STORE, 2, 0, GET, 3,
            ],
        );
        let c = accepted_variant(&[I32, I32, I32], &pre, variant(true, true));
        assert_eq!(c.rewrite.pressure_kept, 0);
        assert_eq!(c.rewrite.stackified, 1);
        assert!(c.body.declared.is_empty());
    }

    #[test]
    fn the_selection_weighs_code_bytes_then_declared_locals() {
        let b = |code: usize, declared: usize| Body {
            declared: vec![I32; declared],
            code: vec![0x01; code],
            relocs: Vec::new(),
        };
        // No more code bytes: the pressure-limited body.
        assert!(prefer_pressure_limited(&b(10, 5), &b(10, 6)));
        assert!(prefer_pressure_limited(&b(9, 6), &b(10, 5)));
        assert!(!prefer_pressure_limited(&b(10, 6), &b(10, 5)));
        assert!(!prefer_pressure_limited(&b(11, 5), &b(10, 6)));
        // Within the cached-local limit where the other is past it, for at
        // most one kept definition's bytes.
        let lim = BASELINE_CACHED_LOCALS;
        assert!(prefer_pressure_limited(
            &b(10 + CACHED_LOCALS_BYTES, lim),
            &b(10, lim + 1)
        ));
        assert!(!prefer_pressure_limited(
            &b(11 + CACHED_LOCALS_BYTES, lim),
            &b(10, lim + 1)
        ));
        assert!(!prefer_pressure_limited(&b(12, lim + 1), &b(10, lim + 3)));
        assert!(!prefer_pressure_limited(&b(12, lim - 3), &b(10, lim)));
        // Liftoff caches declared locals only when all are i32/i64: a
        // pressure-limited body with a float local gains nothing from
        // staying within the limit, so the extra bytes are not paid.
        for float in [ValType::F32, ValType::F64] {
            let mut with_float = b(10 + CACHED_LOCALS_BYTES, lim);
            with_float.declared[0] = float;
            assert!(!prefer_pressure_limited(&with_float, &b(10, lim + 1)));
        }
        let mut wide = b(10 + CACHED_LOCALS_BYTES, lim);
        wide.declared[0] = I64;
        assert!(prefer_pressure_limited(&wide, &b(10, lim + 1)));
    }

    #[test]
    fn a_dead_write_retry_is_counted_by_its_first_refusal() {
        // Refused, then accepted on the rebuild: a retry and no fallback.
        let mut s = WasmLocalOptSummary::default();
        settle(Err("tv_stack_mismatch".into()), true, &mut s, |_| Ok(()));
        assert_eq!(s.dead_write_retries.get("tv_stack_mismatch"), Some(&1));
        assert_eq!(s.fallback_count(), 0);
        // Refused twice: the retry by the first reason, the fallback by the
        // second.
        settle(Err("tv_stack_mismatch".into()), true, &mut s, |_| {
            Err("tv_live_out_mismatch".into())
        });
        assert_eq!(s.dead_write_retries.get("tv_stack_mismatch"), Some(&2));
        assert_eq!(s.fallbacks.get("tv_live_out_mismatch"), Some(&1));
        // No dead writes removed: no rebuild, the refusal stands.
        settle(Err("tv_effect_mismatch".into()), false, &mut s, |_| {
            panic!("rebuilt a candidate without dead writes")
        });
        assert_eq!(s.fallbacks.get("tv_effect_mismatch"), Some(&1));
        // Accepted at once: nothing is counted.
        settle(Ok(()), true, &mut s, |_| panic!("rebuilt an accepted one"));
        assert_eq!(s.dead_write_retries.values().sum::<usize>(), 2);
        assert_eq!(s.fallback_count(), 2);
        assert_eq!(s.to_json()["dead_write_retries"]["tv_stack_mismatch"], 2);
    }

    /// The identity image over `n` locals.
    fn identity(n: u32) -> Vec<LocalImage> {
        (0..n).map(LocalImage::Local).collect()
    }

    #[test]
    fn dead_writes_are_deleted_or_dropped() {
        // tee 1 (never read); `local.get 0; local.set 2` (never read);
        // `p0 + 1` set into 3 (never read, not a single push).
        let b = body(
            &[I32, I32, I32],
            &[
                GET, 0, TEE, 1, DROP, GET, 0, SET, 2, GET, 0, I32_CONST, 1, I32_ADD, SET, 3, GET, 0,
            ],
        );
        let (out, removed) = drop_dead_writes(&[I32], &b).expect("readable");
        assert_eq!(removed, 3);
        assert_eq!(
            out.code,
            vec![GET, 0, DROP, GET, 0, I32_CONST, 1, I32_ADD, DROP, GET, 0]
        );
        let module = WasmModule::new();
        let cand = Candidate {
            body: out,
            image: identity(4),
            facts: Vec::new(),
            copies_deleted: 0,
            rematerialized: 0,
            rewrite: RewriteStats::default(),
            dead_writes: removed,
        };
        validate_candidate(&module, &[I32], &b, &cand, "", &[]).expect("accepted");
    }

    #[test]
    fn a_write_read_on_some_path_is_kept() {
        // block { p0; tee 1; br_if 0 } local.get 1: the tee is read after
        // the block.
        let b = body(
            &[I32],
            &[BLOCK, VOID, GET, 0, TEE, 1, BR_IF, 0, END, GET, 1],
        );
        let (out, removed) = drop_dead_writes(&[I32], &b).expect("readable");
        assert_eq!(removed, 0);
        assert_eq!(out.code, b.code);
    }

    #[test]
    fn a_block_that_only_passes_a_value_through_keeps_its_tee() {
        // block (i32) { block (i32) { p0 } tee 1 }: the segment between the
        // two `end`s is the dead tee alone; deleting it would leave a segment
        // that takes and leaves nothing where the input's takes and leaves
        // the block's value, which the validator refuses.
        let b = body(
            &[I32],
            &[BLOCK, 0x7f, BLOCK, 0x7f, GET, 0, END, TEE, 1, END],
        );
        let (out, removed) = drop_dead_writes(&[I32], &b).expect("readable");
        assert_eq!(removed, 0);
        assert_eq!(out.code, b.code);
        let module = WasmModule::new();
        let without = candidate(
            &[I32],
            &[BLOCK, 0x7f, BLOCK, 0x7f, GET, 0, END, END],
            identity(2),
        );
        let f = validate_candidate(&module, &[I32], &b, &without, "", &[]).expect_err("refused");
        assert_eq!(f.kind, tv::TvFailureKind::StackMismatch, "{f}");
    }
}
