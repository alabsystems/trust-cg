// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! P1.3 — SSA / loop-completeness checker over `trust_ir::Function`.
//!
//! This is a *structural* well-formedness gate that runs on the trust-ir
//! `Function` produced by a frontend (notably the rustc bridge) **before** it is
//! lowered to machine IR. It is independent of *how* the IR was built, so it
//! catches bugs in the producer's own dataflow reasoning. It generalizes the
//! bridge's MIR-side `loop_carried_aggregate_error` fail-closed guard (#71) into
//! a producer-agnostic check at the trust-ir boundary.
//!
//! Two invariants are enforced:
//!
//! 1. **SSA well-formedness.** Every value *use* is dominated by its definition
//!    (or is a parameter of the using block). Every branch's argument
//!    arity/types match the target block's parameters for ALL predecessors,
//!    including back-edges. A value defined inside the function is either an
//!    instruction result, a block parameter, or an entry-block parameter
//!    (function argument).
//!
//! 2. **Loop-completeness (the #71 invariant).** For every natural loop with
//!    header `H` and a back-edge `latch -> H` (computed from dominators) the
//!    loop-carried dataflow must actually route each variable's next-iteration
//!    value back to the right header parameter. Three sound, complementary
//!    sub-checks enforce this:
//!
//!    1. **Strong completeness.** A value defined inside the loop and *live
//!       across the back-edge* must be threaded as a back-edge argument; if it is
//!       dropped at the latch the header observes a stale value. (This also
//!       catches a dropped update consumed by an in-loop store — a stored-through
//!       value is a use, hence live.)
//!    2. **Positional reaching-definition (anti-swap).** The back-edge arguments
//!       are matched POSITIONALLY against `H`'s parameters. Slot `k`'s argument
//!       must be the reaching definition of slot `k`'s variable (the param itself
//!       when invariant, or an in-loop value derived from it). An argument that
//!       provably belongs to a *different* slot (a swapped `br H(%6,%5)`) is
//!       rejected — a set-membership check would have wrongly accepted it.
//!    3. **Dropped same-type update.** A value carried *unchanged* across the
//!       back-edge (a re-threaded header param, or an entry value with no phi at
//!       all) whose in-loop, *same-typed* update is computed and then DROPPED
//!       (dead) is rejected. This is the historical #71 shape (`let mut q=..;
//!       while .. { q.a += 1 }`): the scalarized aggregate field's in-loop store
//!       lowered to a fresh SSA value that was *dropped* on the back-edge, so the
//!       header kept the entry value (which dominates `H`, so plain SSA dominance
//!       is happy) and the update was silently lost. The same-type requirement
//!       keeps a genuinely-dead temp of a *different* type (`let _ = INVARIANT >
//!       0;`) from being mistaken for the missing update.
//!
//! The checker reuses the exact CFG-walk conventions already used by
//! `crate::fsym_trust_ir` (`block_successors`, predecessor maps, natural-loop
//! body computation) so its CFG model is identical to the rest of the crate.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use trust_ir::{Block, BlockId, Function, Inst, Ty, ValueId};

/// A directed CFG edge `source -> target`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize)]
pub struct CfgEdge {
    pub source: BlockId,
    pub target: BlockId,
}

/// A single SSA / loop-completeness violation.
///
/// `Serialize` is derived purely for the AI-usability diagnostics layer
/// (`crate::diag`): it lets a fail-closed event emit its typed fields as JSON.
/// The derive is additive — it changes no field and no gate decision.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub enum SsaViolation {
    /// A value is used but never defined anywhere in the function.
    UndefinedValue {
        value: ValueId,
        block: BlockId,
        detail: String,
    },
    /// A value's use is not dominated by its definition (and the using block
    /// does not declare it as a parameter).
    UseNotDominatedByDef {
        value: ValueId,
        use_block: BlockId,
        def_block: BlockId,
        detail: String,
    },
    /// A branch passes the wrong number of arguments to a target block.
    EdgeArgArityMismatch {
        edge: CfgEdge,
        passed: usize,
        expected: usize,
    },
    /// A branch passes an argument whose type does not match the target block's
    /// corresponding parameter type.
    EdgeArgTypeMismatch {
        edge: CfgEdge,
        param_index: usize,
        arg: ValueId,
        expected: Ty,
        found: Ty,
    },
    /// A branch targets a block that does not exist.
    EdgeTargetMissing { edge: CfgEdge },
    /// The #71 invariant: a value defined inside a loop is live across the
    /// back-edge but is NOT threaded as a loop-header parameter (the latch drops
    /// it instead of passing it as a back-edge argument). Failing closed here
    /// rather than miscompiling.
    LoopCarriedValueNotThreaded {
        value: ValueId,
        def_block: BlockId,
        header: BlockId,
        latch: BlockId,
    },
    /// The #71 invariant, POSITIONAL form: the back-edge argument at a header
    /// param's slot provably belongs to a *different* slot (it equals that other
    /// param or is derived from it inside the loop). A swapped thread such as
    /// `br H(%6,%5)` passes a set-membership check — both args are "present" — but
    /// routes each loop-carried variable's next value to the wrong slot, so a
    /// later iteration reads the wrong value. Failing closed rather than
    /// miscompiling.
    LoopCarriedSlotMisthreaded {
        header: BlockId,
        latch: BlockId,
        slot: usize,
        param: ValueId,
        arg: ValueId,
    },
    /// A block has no terminator, or a terminator appears before the end of a
    /// block. (A pre-condition for the dominance/loop analysis to be meaningful.)
    MalformedBlock { block: BlockId, detail: String },
}

impl SsaViolation {
    /// Single-line diagnostic suitable for a fail-closed `Err(String)`.
    pub fn message(&self) -> String {
        match self {
            SsaViolation::UndefinedValue {
                value,
                block,
                detail,
            } => format!(
                "value {value:?} used in bb{} is never defined ({detail})",
                block.index()
            ),
            SsaViolation::UseNotDominatedByDef {
                value,
                use_block,
                def_block,
                detail,
            } => format!(
                "value {value:?} used in bb{} is not dominated by its def in bb{} ({detail})",
                use_block.index(),
                def_block.index()
            ),
            SsaViolation::EdgeArgArityMismatch {
                edge,
                passed,
                expected,
            } => format!(
                "edge bb{}->bb{} passes {passed} arg(s) to a block with {expected} param(s)",
                edge.source.index(),
                edge.target.index()
            ),
            SsaViolation::EdgeArgTypeMismatch {
                edge,
                param_index,
                arg,
                expected,
                found,
            } => format!(
                "edge bb{}->bb{} arg {param_index} ({arg:?}) has type {found:?} but param expects {expected:?}",
                edge.source.index(),
                edge.target.index()
            ),
            SsaViolation::EdgeTargetMissing { edge } => format!(
                "edge bb{}->bb{} targets a missing block",
                edge.source.index(),
                edge.target.index()
            ),
            SsaViolation::LoopCarriedValueNotThreaded {
                value,
                def_block,
                header,
                latch,
            } => format!(
                "loop-carried value {value:?} defined in bb{} is live across back-edge bb{}->bb{} \
                 but has no loop-header parameter (failing closed rather than miscompiling, #71)",
                def_block.index(),
                latch.index(),
                header.index()
            ),
            SsaViolation::LoopCarriedSlotMisthreaded {
                header,
                latch,
                slot,
                param,
                arg,
            } => format!(
                "loop header bb{} param {param:?} (slot {slot}) is threaded the wrong value: \
                 back-edge bb{}->bb{} passes {arg:?}, which belongs to a different slot \
                 (failing closed rather than miscompiling, #71)",
                header.index(),
                latch.index(),
                header.index()
            ),
            SsaViolation::MalformedBlock { block, detail } => {
                format!("bb{}: {detail}", block.index())
            }
        }
    }
}

/// Result of running the checker. `Ok(())` when the function is well-formed and
/// loop-complete; `Err(violations)` (non-empty) otherwise.
pub type SsaCheckResult = Result<(), Vec<SsaViolation>>;

/// Run the SSA + loop-completeness checker on a trust-ir function.
///
/// On success the function is structurally sound to lower. On failure the
/// returned violations are deterministically ordered (so the first is a stable
/// fail-closed message).
pub fn check_function(function: &Function) -> SsaCheckResult {
    let mut violations = Vec::new();

    // 0. Structural sanity: every block ends in exactly one terminator. This is
    //    required for `block_successors` and the dominator computation to model
    //    control flow faithfully.
    if !check_block_structure(function, &mut violations) {
        // If blocks are malformed the CFG analyses below would be meaningless;
        // return early with the structural errors.
        return finish(violations);
    }

    // 1. Definitions: where each value is defined.
    let defs = collect_defs(function);

    // 2. CFG + dominators.
    let cfg = Cfg::new(function);
    let dominators = Dominators::compute(&cfg);

    // 3. SSA well-formedness (uses dominated by defs; edge arity/type).
    check_ssa(function, &defs, &dominators, &mut violations);

    // 4. Loop-completeness (#71): in-loop redefinitions live across a back-edge
    //    must be threaded through a header parameter.
    check_loop_completeness(function, &defs, &cfg, &dominators, &mut violations);

    finish(violations)
}

/// Convenience wrapper that collapses all violations into a single fail-closed
/// `Err(String)`, matching the bridge's `Result<_, String>` lowering contract.
///
/// The returned message is the first (deterministically ordered) violation,
/// which is sufficient for a fail-closed abort while remaining stable for tests.
pub fn check_function_fail_closed(function: &Function) -> Result<(), String> {
    check_function(function).map_err(|violations| {
        violations
            .first()
            .map(SsaViolation::message)
            .unwrap_or_else(|| "ssa/loop-completeness check failed".to_owned())
    })
}

fn finish(mut violations: Vec<SsaViolation>) -> SsaCheckResult {
    if violations.is_empty() {
        Ok(())
    } else {
        violations.sort_by_key(violation_sort_key);
        Err(violations)
    }
}

fn violation_sort_key(v: &SsaViolation) -> (u8, u32, u32) {
    match v {
        SsaViolation::MalformedBlock { block, .. } => (0, block.index(), 0),
        SsaViolation::EdgeTargetMissing { edge } => (1, edge.source.index(), edge.target.index()),
        SsaViolation::EdgeArgArityMismatch { edge, .. } => {
            (2, edge.source.index(), edge.target.index())
        }
        SsaViolation::EdgeArgTypeMismatch { edge, .. } => {
            (3, edge.source.index(), edge.target.index())
        }
        SsaViolation::UndefinedValue { value, block, .. } => (4, block.index(), value.index()),
        SsaViolation::UseNotDominatedByDef {
            value, use_block, ..
        } => (5, use_block.index(), value.index()),
        SsaViolation::LoopCarriedValueNotThreaded { header, value, .. } => {
            (6, header.index(), value.index())
        }
        SsaViolation::LoopCarriedSlotMisthreaded { header, param, .. } => {
            (7, header.index(), param.index())
        }
    }
}

// ---------------------------------------------------------------------------
// Block structure
// ---------------------------------------------------------------------------

fn check_block_structure(function: &Function, out: &mut Vec<SsaViolation>) -> bool {
    let mut ok = true;
    for block in &function.blocks {
        match block.body.last() {
            None => {
                ok = false;
                out.push(SsaViolation::MalformedBlock {
                    block: block.id,
                    detail: "block has no terminator".to_owned(),
                });
            }
            Some(last) if !last.is_terminator() => {
                ok = false;
                out.push(SsaViolation::MalformedBlock {
                    block: block.id,
                    detail: "block does not end in a terminator".to_owned(),
                });
            }
            Some(_) => {}
        }
        // A terminator may only appear as the final instruction.
        for node in block.body.iter().take(block.body.len().saturating_sub(1)) {
            if node.is_terminator() {
                ok = false;
                out.push(SsaViolation::MalformedBlock {
                    block: block.id,
                    detail: "terminator before end of block".to_owned(),
                });
                break;
            }
        }
    }
    ok
}

// ---------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------

/// Where a value is defined and, for instruction results, its position so that
/// same-block dominance can be decided.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DefSite {
    block: BlockId,
    /// `None` for a block parameter (defined at block entry, position -1);
    /// `Some(i)` for the result of the i-th instruction in `block.body`.
    inst_index: Option<usize>,
}

fn collect_defs(function: &Function) -> HashMap<ValueId, DefSite> {
    let mut defs = HashMap::new();
    for block in &function.blocks {
        for (value, _ty) in &block.params {
            defs.insert(
                *value,
                DefSite {
                    block: block.id,
                    inst_index: None,
                },
            );
        }
        for (inst_index, node) in block.body.iter().enumerate() {
            for result in &node.results {
                defs.insert(
                    *result,
                    DefSite {
                        block: block.id,
                        inst_index: Some(inst_index),
                    },
                );
            }
        }
    }
    defs
}

// ---------------------------------------------------------------------------
// CFG
// ---------------------------------------------------------------------------

/// Control-flow graph derived from terminator successors. Indexed by `BlockId`.
struct Cfg {
    entry: BlockId,
    /// All block ids in declaration order.
    blocks: Vec<BlockId>,
    successors: HashMap<BlockId, Vec<BlockId>>,
    predecessors: HashMap<BlockId, Vec<BlockId>>,
}

impl Cfg {
    fn new(function: &Function) -> Self {
        let blocks: Vec<BlockId> = function.blocks.iter().map(|b| b.id).collect();
        let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
        let mut predecessors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
        for id in &blocks {
            successors.entry(*id).or_default();
            predecessors.entry(*id).or_default();
        }
        for block in &function.blocks {
            for succ in block_successors(block) {
                successors.entry(block.id).or_default().push(succ);
                predecessors.entry(succ).or_default().push(block.id);
            }
        }
        Cfg {
            entry: function.entry,
            blocks,
            successors,
            predecessors,
        }
    }

    fn succ(&self, b: BlockId) -> &[BlockId] {
        self.successors.get(&b).map(Vec::as_slice).unwrap_or(&[])
    }

    fn pred(&self, b: BlockId) -> &[BlockId] {
        self.predecessors.get(&b).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Reverse-postorder over blocks reachable from entry.
    fn reverse_postorder(&self) -> Vec<BlockId> {
        let mut visited = HashSet::new();
        let mut post = Vec::new();
        // Iterative postorder DFS.
        let mut stack: Vec<(BlockId, usize)> = vec![(self.entry, 0)];
        visited.insert(self.entry);
        while let Some((node, idx)) = stack.pop() {
            let succs = self.succ(node);
            if idx < succs.len() {
                stack.push((node, idx + 1));
                let next = succs[idx];
                if visited.insert(next) {
                    stack.push((next, 0));
                }
            } else {
                post.push(node);
            }
        }
        post.reverse();
        post
    }
}

/// CFG successors of a block (the trust-ir convention, mirroring
/// `crate::fsym_trust_ir::block_successors`).
pub fn block_successors(block: &Block) -> Vec<BlockId> {
    let Some(last) = block.body.last() else {
        return Vec::new();
    };
    match &last.inst {
        Inst::Br { target, .. } => vec![*target],
        Inst::CondBr {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        Inst::Switch { default, cases, .. } => {
            let mut succs = Vec::with_capacity(cases.len() + 1);
            succs.push(*default);
            succs.extend(cases.iter().map(|case| case.target));
            succs
        }
        // Return / Unreachable / any non-terminator (shouldn't occur after the
        // structure check) have no successors.
        _ => Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// Dominators (Cooper–Harvey–Kennedy iterative algorithm)
// ---------------------------------------------------------------------------

struct Dominators {
    /// Immediate dominator of each reachable block (entry maps to itself).
    idom: HashMap<BlockId, BlockId>,
}

impl Dominators {
    fn compute(cfg: &Cfg) -> Self {
        let rpo = cfg.reverse_postorder();
        let rpo_number: HashMap<BlockId, usize> =
            rpo.iter().enumerate().map(|(i, b)| (*b, i)).collect();

        let mut idom: HashMap<BlockId, BlockId> = HashMap::new();
        idom.insert(cfg.entry, cfg.entry);

        let mut changed = true;
        while changed {
            changed = false;
            // Process in RPO, skipping the entry (index 0).
            for &b in rpo.iter().skip(1) {
                // Pick the first already-processed predecessor as the running idom.
                let mut new_idom: Option<BlockId> = None;
                for &p in cfg.pred(b) {
                    if idom.contains_key(&p) {
                        new_idom = Some(match new_idom {
                            None => p,
                            Some(cur) => intersect(&idom, &rpo_number, cur, p),
                        });
                    }
                }
                if let Some(new_idom) = new_idom
                    && idom.get(&b) != Some(&new_idom)
                {
                    idom.insert(b, new_idom);
                    changed = true;
                }
            }
        }

        Dominators { idom }
    }

    fn is_reachable(&self, b: BlockId) -> bool {
        self.idom.contains_key(&b)
    }

    /// Does `a` dominate `b`? (Reflexive: a dominates a.) Unreachable `b`
    /// is dominated by nothing except itself.
    fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        if a == b {
            return true;
        }
        if !self.is_reachable(b) {
            return false;
        }
        // Walk up b's idom chain; `a` dominates `b` iff it appears strictly
        // above `b`. The chain terminates at the entry (idom[entry] == entry).
        let mut cur = b;
        loop {
            let next = self.idom[&cur];
            if next == cur {
                // Reached the entry self-loop without finding `a`.
                return false;
            }
            if next == a {
                return true;
            }
            cur = next;
        }
    }
}

/// Walk up the dominator tree from the higher-RPO node until the two pointers
/// meet (the standard CHK `intersect`).
fn intersect(
    idom: &HashMap<BlockId, BlockId>,
    rpo_number: &HashMap<BlockId, usize>,
    mut a: BlockId,
    mut b: BlockId,
) -> BlockId {
    while a != b {
        // Higher RPO number == later in RPO == deeper; advance it upward.
        while rpo_number[&a] > rpo_number[&b] {
            a = idom[&a];
        }
        while rpo_number[&b] > rpo_number[&a] {
            b = idom[&b];
        }
    }
    a
}

// ---------------------------------------------------------------------------
// SSA well-formedness
// ---------------------------------------------------------------------------

fn check_ssa(
    function: &Function,
    defs: &HashMap<ValueId, DefSite>,
    dominators: &Dominators,
    out: &mut Vec<SsaViolation>,
) {
    // Per-block param membership for the "use is a param of this block" check.
    let block_params: HashMap<BlockId, Vec<ValueId>> = function
        .blocks
        .iter()
        .map(|b| (b.id, b.params.iter().map(|(v, _)| *v).collect()))
        .collect();
    let ty_of: HashMap<ValueId, Ty> = function
        .blocks
        .iter()
        .flat_map(|b| b.params.iter().map(|(v, t)| (*v, t.clone())))
        .collect();

    for block in &function.blocks {
        // Unreachable blocks are not lowered and their internal uses are vacuous;
        // skip dominance checks for them but still validate edge arity below.
        let reachable = dominators.is_reachable(block.id);

        for (inst_index, node) in block.body.iter().enumerate() {
            for used in non_terminator_value_uses(&node.inst) {
                check_one_use(
                    used,
                    block.id,
                    Some(inst_index),
                    reachable,
                    defs,
                    &block_params,
                    dominators,
                    "instruction operand",
                    out,
                );
            }
        }

        // Terminator edge arguments are uses at the *end* of this (source) block.
        for (target, args) in terminator_edges(block) {
            // Target existence + arity + type.
            let Some(target_block) = function_block(function, target) else {
                out.push(SsaViolation::EdgeTargetMissing {
                    edge: CfgEdge {
                        source: block.id,
                        target,
                    },
                });
                continue;
            };
            if target_block.params.len() != args.len() {
                out.push(SsaViolation::EdgeArgArityMismatch {
                    edge: CfgEdge {
                        source: block.id,
                        target,
                    },
                    passed: args.len(),
                    expected: target_block.params.len(),
                });
            } else {
                for (i, (arg, (_pv, param_ty))) in
                    args.iter().zip(target_block.params.iter()).enumerate()
                {
                    if let Some(arg_ty) = ty_of.get(arg)
                        && arg_ty != param_ty
                    {
                        out.push(SsaViolation::EdgeArgTypeMismatch {
                            edge: CfgEdge {
                                source: block.id,
                                target,
                            },
                            param_index: i,
                            arg: *arg,
                            expected: param_ty.clone(),
                            found: arg_ty.clone(),
                        });
                    }
                    // Note: instruction-result types are not tracked here (the
                    // trust-ir `Inst` carries result types positionally); only
                    // block-param-typed args get a type check. Arity + dominance
                    // are the load-bearing structural guarantees.
                }
            }

            // Dominance of each edge argument (a use at this block's terminator).
            for arg in &args {
                check_one_use(
                    *arg,
                    block.id,
                    None, // at terminator: position is end-of-block
                    reachable,
                    defs,
                    &block_params,
                    dominators,
                    "branch argument",
                    out,
                );
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn check_one_use(
    used: ValueId,
    use_block: BlockId,
    use_inst_index: Option<usize>,
    reachable: bool,
    defs: &HashMap<ValueId, DefSite>,
    block_params: &HashMap<BlockId, Vec<ValueId>>,
    dominators: &Dominators,
    context: &str,
    out: &mut Vec<SsaViolation>,
) {
    // A use of a value that is a parameter of the using block is always legal.
    if block_params
        .get(&use_block)
        .is_some_and(|ps| ps.contains(&used))
    {
        return;
    }
    let Some(def) = defs.get(&used) else {
        out.push(SsaViolation::UndefinedValue {
            value: used,
            block: use_block,
            detail: context.to_owned(),
        });
        return;
    };

    // Only meaningful for reachable use blocks; an unreachable block's defs
    // never execute.
    if !reachable {
        return;
    }

    let dominates = if def.block == use_block {
        match (def.inst_index, use_inst_index) {
            // param defines at entry: dominates every position in the block.
            (None, _) => true,
            // def at index d, use at index u: requires d < u (strict order).
            (Some(d), Some(u)) => d < u,
            // def at index d, use at terminator (end): always after.
            (Some(_), None) => true,
        }
    } else {
        dominators.dominates(def.block, use_block)
    };

    if !dominates {
        out.push(SsaViolation::UseNotDominatedByDef {
            value: used,
            use_block,
            def_block: def.block,
            detail: context.to_owned(),
        });
    }
}

// ---------------------------------------------------------------------------
// Loop-completeness (#71)
// ---------------------------------------------------------------------------

fn check_loop_completeness(
    function: &Function,
    defs: &HashMap<ValueId, DefSite>,
    cfg: &Cfg,
    dominators: &Dominators,
    out: &mut Vec<SsaViolation>,
) {
    // Liveness: live_out[b] = values that may be read on some path leaving b
    // before being redefined. Block params are kills at block entry; edge args
    // are uses at the source block.
    let liveness = Liveness::compute(function, cfg);

    // Values used anywhere (as a plain operand or an edge argument).
    // `collect_all_uses` includes terminator edge args, so a value being absent
    // here means it is neither read nor threaded — i.e. genuinely dead.
    let all_uses = collect_all_uses(function);

    // Best-effort static type of every value we can determine one for. The
    // dropped-update sub-check (3) requires the dead update to be the SAME TYPE
    // as the value it would replace; the positional checks need no types.
    let value_ty = collect_value_types(function);

    // Back-edges: edge (latch -> header) where header dominates latch.
    for back in back_edges(cfg, dominators) {
        let header = back.target;
        let latch = back.source;
        let loop_blocks = natural_loop_blocks(cfg, header, latch);

        // Values supplied by the latch to the header along the back-edge,
        // POSITIONALLY (slot k -> arg k). Set-membership is the unsound shortcut
        // that finding #2 exploits (a swapped `br H(%6,%5)` has both args
        // "present"), so we keep the full positional list and only derive a set
        // form for the carried-unchanged test in sub-check (3).
        let back_args = edge_args(function, latch, header);
        let threaded: BTreeSet<ValueId> = back_args.iter().copied().collect();

        let header_params: Vec<ValueId> = function_block(function, header)
            .map(|b| b.params.iter().map(|(v, _)| *v).collect())
            .unwrap_or_default();

        let live_across: BTreeSet<ValueId> = liveness.live_out(latch).copied().collect();

        // Edge-precise "live on the back-edge latch -> header": the values read on
        // some path FROM the header before redefinition. `live_out(latch)` unions
        // the live-in of EVERY successor of the latch, so for a multi-successor
        // latch (e.g. a `Switch` whose other arm continues an inner loop) it
        // over-approximates: a value live only on the latch's NON-back-edge
        // successor would spuriously appear "live across the back-edge". Keying
        // sub-check (1) off `live_in(header)` removes that imprecision — the header
        // (the back-edge's sole target) is exactly where a stale value would be
        // observed. (Properly threaded values are killed by the header's params, so
        // they are absent here; `live_across` above is still used by sub-check (3).)
        let live_into_header: BTreeSet<ValueId> = liveness.live_in(header).copied().collect();

        // (1) STRONG completeness: a value DEFINED INSIDE the loop that is LIVE
        //     ACROSS THE BACK-EDGE (needed by a later iteration / the header)
        //     must be threaded as a back-edge argument. If it is live across the
        //     back-edge but dropped at the latch, SSA-with-block-params cannot
        //     route it — the header would observe a stale value. This catches the
        //     strong form where the dropped redefinition is consumed, INCLUDING
        //     finding #3 (an update stored through an in-loop pointer is a use,
        //     hence live, hence caught here).
        for value in &live_into_header {
            let Some(def) = defs.get(value) else {
                continue;
            };
            let defined_in_loop = loop_blocks.contains(&def.block) && def.block != header;
            if !defined_in_loop || threaded.contains(value) {
                continue;
            }
            out.push(SsaViolation::LoopCarriedValueNotThreaded {
                value: *value,
                def_block: def.block,
                header,
                latch,
            });
        }

        // Per header param, its in-loop derivation set (values transitively
        // computed from that param inside the loop). A back-edge arg "belongs to"
        // slot j iff it equals param j or lies in param j's derivations — i.e. it
        // is the reaching definition of slot j's loop variable.
        let param_derivations: Vec<(ValueId, BTreeSet<ValueId>)> = header_params
            .iter()
            .map(|&p| (p, in_loop_derivations(function, &loop_blocks, p)))
            .collect();
        let belongs_to = |arg: ValueId, idx: usize| -> bool {
            let (p, derivs) = &param_derivations[idx];
            arg == *p || derivs.contains(&arg)
        };

        // (2) POSITIONAL anti-SWAP check (fixes the set-membership logic bug,
        //     finding #2). For slot k, the back-edge arg a_k is the next-iteration
        //     value of slot k's variable. If a_k provably belongs to a DIFFERENT
        //     slot j (it equals p_j or is derived from p_j) and does NOT belong to
        //     slot k, then slot k receives the wrong variable's value — the
        //     unsound `br H(%6,%5)` swap. This is positional and
        //     reaching-definition based, and sound: it fires only on a provable
        //     cross-slot misroute. Carrying a param unchanged (genuine invariant
        //     phi) or threading a freshly-computed value belongs to no other slot
        //     and is never flagged here (those shapes are handled, where unsound,
        //     by sub-check (3)).
        for (slot, &param) in header_params.iter().enumerate() {
            let Some(arg) = back_args.get(slot).copied() else {
                // Arity is enforced by invariant 1; nothing to position-check.
                continue;
            };
            if belongs_to(arg, slot) {
                continue; // a_k is p_k or its in-loop redefinition: correct slot.
            }
            let swapped_from_other =
                (0..param_derivations.len()).any(|j| j != slot && belongs_to(arg, j));
            if swapped_from_other {
                out.push(SsaViolation::LoopCarriedSlotMisthreaded {
                    header,
                    latch,
                    slot,
                    param,
                    arg,
                });
            }
        }

        // (3) DROPPED SAME-TYPE UPDATE of a value carried UNCHANGED across the
        //     back-edge. Two carried-unchanged forms are covered:
        //       - a loop-INVARIANT entry value `e` (defined outside the loop,
        //         dominating the header) read each iteration with NO header param
        //         at all (the historical #71 scalarized-aggregate-field shape:
        //         there is no phi for `q.a`); and
        //       - a header param `p_k` re-threaded UNCHANGED (a_k == p_k), the
        //         stale re-thread of finding #1.
        //     In both forms the loop computes an in-loop update `d` of `e` and
        //     DROPS it: `d` is dead (never used, never threaded). The update of a
        //     loop-carried value is its next-iteration value, hence SAME-TYPED as
        //     `e`; requiring `ty(d) == ty(e)` means a dead temp of a *different*
        //     type (e.g. `let _ = INVARIANT > 0;`, a bool) is NOT mistaken for a
        //     dropped i32 update — removing the false positive (#4) of the old
        //     type-blind fingerprint. Ordinary used computations (`arr[c + i]`)
        //     are not dead and so never match.
        let carried_unchanged = |used: ValueId| -> bool {
            // Header param carried unchanged: its slot's back-edge arg is itself.
            if let Some(slot) = header_params.iter().position(|p| *p == used) {
                return back_args.get(slot).copied() == Some(used);
            }
            // Loop-invariant entry value: defined outside the loop, live across
            // the back-edge, and not (re-)threaded on any slot.
            let def_outside = defs
                .get(&used)
                .is_some_and(|d| !loop_blocks.contains(&d.block));
            def_outside && live_across.contains(&used) && !threaded.contains(&used)
        };
        for block_id in &loop_blocks {
            let Some(block) = function_block(function, *block_id) else {
                continue;
            };
            for node in &block.body {
                if node.results.is_empty() {
                    continue;
                }
                // Dead: no result of this node is ever used or threaded.
                let produces_only_dead = node.results.iter().all(|r| !all_uses.contains(r));
                if !produces_only_dead {
                    continue;
                }
                let dead = node.results[0];
                let Some(dead_ty) = value_ty.get(&dead) else {
                    // Cannot type the result: do not fire (avoid false positives).
                    continue;
                };
                for used in non_terminator_value_uses(&node.inst) {
                    let same_type = value_ty.get(&used) == Some(dead_ty);
                    if same_type && carried_unchanged(used) {
                        out.push(SsaViolation::LoopCarriedValueNotThreaded {
                            value: dead,
                            def_block: *block_id,
                            header,
                            latch,
                        });
                        break;
                    }
                }
            }
        }
    }
}

/// All values that appear as a use (plain operand or edge argument) anywhere in
/// the function.
fn collect_all_uses(function: &Function) -> HashSet<ValueId> {
    let mut uses = HashSet::new();
    for block in &function.blocks {
        for node in &block.body {
            for u in non_terminator_value_uses(&node.inst) {
                uses.insert(u);
            }
        }
        for (_t, args) in terminator_edges(block) {
            for a in args {
                uses.insert(a);
            }
        }
    }
    uses
}

/// In-loop values transitively derived from `seed` through in-loop operands.
///
/// Starting from `seed`, repeatedly add any non-terminator instruction result
/// defined inside the loop whose operands include a value already reachable from
/// `seed`. The returned set excludes `seed` itself, so it is exactly the in-loop
/// redefinitions of the variable that `seed` names (its reaching definitions at
/// the latch are a subset of this). Block params are not instruction results, so
/// a header param is reached only through the instructions that consume it.
fn in_loop_derivations(
    function: &Function,
    loop_blocks: &HashSet<BlockId>,
    seed: ValueId,
) -> BTreeSet<ValueId> {
    let mut reachable: HashSet<ValueId> = HashSet::from([seed]);
    let mut derived: BTreeSet<ValueId> = BTreeSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for block_id in loop_blocks {
            let Some(block) = function_block(function, *block_id) else {
                continue;
            };
            for node in &block.body {
                if node.is_terminator() || node.results.is_empty() {
                    continue;
                }
                let consumes_reachable = non_terminator_value_uses(&node.inst)
                    .iter()
                    .any(|u| reachable.contains(u));
                if !consumes_reachable {
                    continue;
                }
                for r in &node.results {
                    if reachable.insert(*r) {
                        derived.insert(*r);
                        changed = true;
                    }
                }
            }
        }
    }
    derived
}

/// Best-effort static type of each value, for the same-type dropped-update check.
///
/// Covers block parameters (which carry an explicit type) and the common
/// single-result, type-bearing instructions. Values whose type cannot be
/// determined here are simply absent from the map; the dropped-update sub-check
/// then declines to fire on them, which is the false-positive-safe choice.
fn collect_value_types(function: &Function) -> HashMap<ValueId, Ty> {
    let mut tys: HashMap<ValueId, Ty> = HashMap::new();
    for block in &function.blocks {
        for (v, t) in &block.params {
            tys.insert(*v, t.clone());
        }
        for node in &block.body {
            let Some(result_ty) = single_result_ty(&node.inst) else {
                continue;
            };
            if let Some(r) = node.results.first() {
                tys.insert(*r, result_ty);
            }
        }
    }
    tys
}

/// The result type of a single-result, type-bearing instruction, or `None` for
/// instructions whose result type is not directly recoverable from the variant
/// (or which produce no value / multiple values).
fn single_result_ty(inst: &Inst) -> Option<Ty> {
    match inst {
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. } => Some(ty.clone()),
        Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
        // ICmp/FCmp carry the OPERAND type in `ty`; their RESULT is a boolean.
        // Returning `Bool` keeps a comparison from being mistaken for a
        // same-typed arithmetic update of its (wider) operand.
        Inst::ICmp { .. } | Inst::FCmp { .. } => Some(Ty::Bool),
        _ => None,
    }
}

/// Natural-loop body for back-edge `latch -> header`: header plus every block
/// that can reach `latch` without going through `header`. Mirrors
/// `crate::fsym_trust_ir::natural_loop_blocks`.
fn natural_loop_blocks(cfg: &Cfg, header: BlockId, latch: BlockId) -> HashSet<BlockId> {
    let mut loop_blocks = HashSet::from([header]);
    let mut stack = vec![latch];
    while let Some(b) = stack.pop() {
        if !loop_blocks.insert(b) {
            continue;
        }
        for &p in cfg.pred(b) {
            stack.push(p);
        }
    }
    loop_blocks
}

/// Back-edges of the CFG: edges `u -> v` where `v` dominates `u`.
fn back_edges(cfg: &Cfg, dominators: &Dominators) -> Vec<CfgEdge> {
    let mut edges = Vec::new();
    for &b in &cfg.blocks {
        if !dominators.is_reachable(b) {
            continue;
        }
        for &s in cfg.succ(b) {
            if dominators.dominates(s, b) {
                edges.push(CfgEdge {
                    source: b,
                    target: s,
                });
            }
        }
    }
    edges.sort_by_key(|e| (e.source.index(), e.target.index()));
    edges
}

// ---------------------------------------------------------------------------
// Liveness (backward dataflow)
// ---------------------------------------------------------------------------

struct Liveness {
    live_out: HashMap<BlockId, BTreeSet<ValueId>>,
    live_in: HashMap<BlockId, BTreeSet<ValueId>>,
}

impl Liveness {
    fn live_out(&self, b: BlockId) -> impl Iterator<Item = &ValueId> {
        self.live_out
            .get(&b)
            .map(|s| s.iter())
            .unwrap_or_else(|| EMPTY_SET.iter())
    }

    /// Values live at the ENTRY of block `b` — i.e. read on some path *from* `b`
    /// before being redefined (the header's own params are kills, so a properly
    /// threaded loop-carried value is absent). This is edge-precise for the
    /// loop-completeness check: a value is "live on the back-edge latch -> header"
    /// (needed by a later iteration) iff it is live-in at the header, regardless of
    /// which other successor of a multi-target latch also keeps it live.
    fn live_in(&self, b: BlockId) -> impl Iterator<Item = &ValueId> {
        self.live_in
            .get(&b)
            .map(|s| s.iter())
            .unwrap_or_else(|| EMPTY_SET.iter())
    }

    fn compute(function: &Function, cfg: &Cfg) -> Self {
        // Precompute per-block "uses" (values read before any redefinition in
        // that block) and "defs" (block params + instruction results) for the
        // standard live_in = use ∪ (live_out − def); live_out = ∪ succ live_in.
        //
        // Edge arguments are modeled as uses at the SOURCE block (block-param
        // SSA semantics): a value passed on an edge is read by the source.
        let mut upward_use: HashMap<BlockId, BTreeSet<ValueId>> = HashMap::new();
        let mut def: HashMap<BlockId, BTreeSet<ValueId>> = HashMap::new();

        for block in &function.blocks {
            let mut killed: HashSet<ValueId> = HashSet::new();
            let mut uses: BTreeSet<ValueId> = BTreeSet::new();
            let mut defs: BTreeSet<ValueId> = BTreeSet::new();

            // Block params are defined at entry (kill before any body use).
            for (v, _) in &block.params {
                killed.insert(*v);
                defs.insert(*v);
            }
            for node in &block.body {
                for used in non_terminator_value_uses(&node.inst) {
                    if !killed.contains(&used) {
                        uses.insert(used);
                    }
                }
                for r in &node.results {
                    killed.insert(*r);
                    defs.insert(*r);
                }
            }
            // Terminator edge args = uses at end of source block.
            for (_target, args) in terminator_edges(block) {
                for a in args {
                    if !killed.contains(&a) {
                        uses.insert(a);
                    }
                }
            }
            upward_use.insert(block.id, uses);
            def.insert(block.id, defs);
        }

        let mut live_in: HashMap<BlockId, BTreeSet<ValueId>> =
            cfg.blocks.iter().map(|b| (*b, BTreeSet::new())).collect();
        let mut live_out: HashMap<BlockId, BTreeSet<ValueId>> =
            cfg.blocks.iter().map(|b| (*b, BTreeSet::new())).collect();

        // Iterate to a fixpoint. Worklist seeded with all blocks; process in
        // reverse declaration order for faster convergence on simple CFGs.
        let mut worklist: VecDeque<BlockId> = cfg.blocks.iter().rev().copied().collect();
        let mut in_worklist: HashSet<BlockId> = cfg.blocks.iter().copied().collect();

        while let Some(b) = worklist.pop_front() {
            in_worklist.remove(&b);

            // live_out[b] = ∪ over succ s of live_in[s]
            let mut new_out: BTreeSet<ValueId> = BTreeSet::new();
            for &s in cfg.succ(b) {
                if let Some(set) = live_in.get(&s) {
                    new_out.extend(set.iter().copied());
                }
            }

            // live_in[b] = use[b] ∪ (live_out[b] − def[b])
            let empty = BTreeSet::new();
            let use_b = upward_use.get(&b).unwrap_or(&empty);
            let def_b = def.get(&b).unwrap_or(&empty);
            let mut new_in: BTreeSet<ValueId> = use_b.clone();
            for v in new_out.iter() {
                if !def_b.contains(v) {
                    new_in.insert(*v);
                }
            }

            let out_changed = live_out.get(&b) != Some(&new_out);
            let in_changed = live_in.get(&b) != Some(&new_in);
            live_out.insert(b, new_out);
            live_in.insert(b, new_in);

            if in_changed {
                // Predecessors depend on our live_in; re-queue them.
                for &p in cfg.pred(b) {
                    if in_worklist.insert(p) {
                        worklist.push_back(p);
                    }
                }
            }
            let _ = out_changed;
        }

        Liveness { live_out, live_in }
    }
}

use std::sync::LazyLock;
static EMPTY_SET: LazyLock<BTreeSet<ValueId>> = LazyLock::new(BTreeSet::new);

// ---------------------------------------------------------------------------
// Use / edge extraction
// ---------------------------------------------------------------------------

/// SSA value operands of a NON-terminator instruction. Terminator edge args are
/// handled separately by `terminator_edges` because they are edge-scoped uses.
///
/// This is exhaustive over `trust_ir::Inst` (rev 87e1af1). New variants must be
/// added here; the wildcard arms only cover variants with no `ValueId` operand.
pub fn non_terminator_value_uses(inst: &Inst) -> Vec<ValueId> {
    match inst {
        Inst::BinOp { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. } => vec![*lhs, *rhs],

        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } | Inst::Copy { operand, .. } => {
            vec![*operand]
        }

        Inst::Load { ptr, .. } => vec![*ptr],
        Inst::Store { ptr, value, .. } => vec![*ptr, *value],
        Inst::Alloca { count, .. } | Inst::HeapAlloc { count, .. } => {
            count.iter().copied().collect()
        }
        Inst::GEP { base, indices, .. } => {
            let mut v = vec![*base];
            v.extend(indices.iter().copied());
            v
        }
        Inst::PtrData { ptr, .. } | Inst::PtrMetadata { ptr, .. } => vec![*ptr],
        Inst::PtrFromParts { data, metadata, .. } => vec![*data, *metadata],

        Inst::AtomicLoad { ptr, .. } => vec![*ptr],
        Inst::AtomicStore { ptr, value, .. } | Inst::AtomicRMW { ptr, value, .. } => {
            vec![*ptr, *value]
        }
        Inst::CmpXchg {
            ptr,
            expected,
            desired,
            ..
        } => vec![*ptr, *expected, *desired],
        Inst::Fence { .. } => vec![],

        // Call is a non-terminator in trust-ir (only Br/CondBr/Switch/Return/
        // Unreachable terminate). CallIndirect's callee is also a value use.
        Inst::Call { args, .. } => args.clone(),
        Inst::CallIndirect { callee, args, .. } => {
            let mut v = vec![*callee];
            v.extend(args.iter().copied());
            v
        }

        Inst::ExtractField { aggregate, .. } => vec![*aggregate],
        Inst::InsertField {
            aggregate, value, ..
        } => vec![*aggregate, *value],
        Inst::ExtractElement { array, index, .. } => vec![*array, *index],
        Inst::InsertElement {
            array,
            index,
            value,
            ..
        } => vec![*array, *index, *value],

        Inst::Assume { cond } | Inst::Assert { cond } => vec![*cond],
        Inst::Select {
            cond,
            then_val,
            else_val,
            ..
        } => vec![*cond, *then_val, *else_val],

        Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => vec![*ptr],
        Inst::EndBorrow { borrow_ptr } => vec![*borrow_ptr],
        Inst::Retain { ptr } | Inst::Release { ptr } | Inst::IsUnique { ptr } => vec![*ptr],
        Inst::Dealloc { ptr } => vec![*ptr],

        Inst::BindSlot { frame, value, .. } => vec![*frame, *value],
        Inst::LoadSlot { frame, .. } | Inst::CloseFrame { frame } => vec![*frame],
        Inst::OpenFrame { .. } => vec![],

        // `k` is a u64 immediate, `ty` a type, and the general form's `fwd` a
        // FuncId (a function reference, not a value): the sequence is the sole
        // value use for all three sequence-map forms.
        Inst::SeqMapAddK { seq, .. } | Inst::SeqMapNot { seq, .. } | Inst::SeqMap { seq, .. } => {
            vec![*seq]
        }

        Inst::DialectOp(d) => d.operands.clone(),

        // No-value-operand instructions and the terminators (whose edge args are
        // handled by `terminator_edges`; their non-edge operands — `cond`/`value`
        // — ARE plain uses and are surfaced below).
        Inst::Const { .. } | Inst::NullPtr | Inst::GlobalAddr { .. } | Inst::Undef { .. } => vec![],

        // Terminators: surface the scrutinee operands as plain uses (the edge
        // args are returned by `terminator_edges`). `Br`/`Return`/`Unreachable`
        // have no scrutinee.
        Inst::CondBr { cond, .. } => vec![*cond],
        Inst::Switch { value, .. } => vec![*value],
        Inst::Return { values } => values.clone(),
        // `CoroSuspend` is a terminator with no successor edges (it lowers to a
        // store + return); its `frame` and yielded `value` are plain uses.
        Inst::CoroSuspend { frame, value, .. } => vec![*frame, *value],
        // `Invoke` is a terminator; its call `args` are plain uses, while its
        // `normal_args` are EDGE args returned by `terminator_edges`. `Resume`
        // is a terminator whose `exn` is a plain use. A `LandingPad` is a
        // non-terminator block entry that PRODUCES values and has no operands.
        Inst::Invoke { args, .. } => args.clone(),
        Inst::Resume { exn } => vec![*exn],
        Inst::LandingPad { .. } => vec![],
        Inst::Br { .. } | Inst::Unreachable => vec![],
    }
}

/// The (target, args) edges of a block's terminator. Empty for non-branching
/// terminators (`Return`, `Unreachable`) and for non-terminator last
/// instructions (which the structure check already rejects).
pub fn terminator_edges(block: &Block) -> Vec<(BlockId, Vec<ValueId>)> {
    let Some(last) = block.body.last() else {
        return Vec::new();
    };
    match &last.inst {
        Inst::Br { target, args } => vec![(*target, args.clone())],
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => vec![
            (*then_target, then_args.clone()),
            (*else_target, else_args.clone()),
        ],
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            let mut edges = vec![(*default, default_args.clone())];
            edges.extend(cases.iter().map(|c| (c.target, c.args.clone())));
            edges
        }
        // An invoke branches to its normal continuation (carrying `normal_args`)
        // or its landing pad (no edge args — the pad reads the exception from
        // ABI registers, not block params).
        Inst::Invoke {
            normal_dest,
            normal_args,
            unwind_dest,
            ..
        } => vec![
            (*normal_dest, normal_args.clone()),
            (*unwind_dest, Vec::new()),
        ],
        _ => Vec::new(),
    }
}

/// The argument list the source block passes to `target` on its terminator
/// edge(s). If multiple edges target the same block (e.g. a switch with two
/// cases pointing at the header) their args are concatenated; for the
/// loop-completeness check we only care about set membership.
fn edge_args(function: &Function, source: BlockId, target: BlockId) -> Vec<ValueId> {
    let Some(block) = function_block(function, source) else {
        return Vec::new();
    };
    terminator_edges(block)
        .into_iter()
        .filter(|(t, _)| *t == target)
        .flat_map(|(_, args)| args)
        .collect()
}

fn function_block(function: &Function, id: BlockId) -> Option<&Block> {
    function.blocks.iter().find(|b| b.id == id)
}

// A small helper so callers can introspect the computed loop set / dominators in
// tests without re-deriving them.
#[doc(hidden)]
pub mod test_support {
    use super::*;

    /// Expose back-edges for tests.
    pub fn back_edges_of(function: &Function) -> Vec<CfgEdge> {
        let cfg = Cfg::new(function);
        let dominators = Dominators::compute(&cfg);
        super::back_edges(&cfg, &dominators)
    }

    /// Expose `a dominates b` for tests.
    pub fn dominates(function: &Function, a: BlockId, b: BlockId) -> bool {
        let cfg = Cfg::new(function);
        let dominators = Dominators::compute(&cfg);
        dominators.dominates(a, b)
    }

    /// Expose live_out for tests.
    pub fn live_out_of(function: &Function, b: BlockId) -> BTreeMap<u32, ()> {
        let cfg = Cfg::new(function);
        let liveness = Liveness::compute(function, &cfg);
        liveness.live_out(b).map(|v| (v.index(), ())).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{
        BinOp, Block, BlockId, Constant, FuncId, FuncTyId, Function, ICmpOp, Inst, InstrNode, Ty,
        ValueId,
    };

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }
    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    fn empty_fn() -> Function {
        Function::new(FuncId::new(0), "test", FuncTyId::new(0), b(0))
    }

    /// Build the CORRECTLY-THREADED scalar loop (the `z1`/`z2` shape).
    ///
    /// Semantics modeled: `let mut acc = 0; let mut i = 0; while i < N { acc = acc +
    /// 1; i = i + 1 } return acc`. Both `acc` and `i` are loop-carried *scalars*
    /// that the bridge threads through header params and back-edge args — this is
    /// the shape that lowers correctly today.
    ///
    ///   bb0:                       ; seed acc0=0, i0=0
    ///       %0 = const i32 0       ; acc0
    ///       %1 = const i32 0       ; i0
    ///       br bb1(%0, %1)
    ///   bb1(%acc:i32, %i:i32):     ; header phi for BOTH carried scalars
    ///       %2 = const i32 10      ; N
    ///       %3 = icmp slt %i, %2
    ///       condbr %3, bb2, bb3
    ///   bb2:                       ; latch / body
    ///       %4 = const i32 1
    ///       %5 = add %acc, %4      ; acc' (in-loop redef)
    ///       %6 = add %i, %4        ; i'   (in-loop redef)
    ///       br bb1(%5, %6)         ; BOTH redefs threaded back -> COMPLETE
    ///   bb3:
    ///       return %acc
    fn threaded_scalar_loop() -> Function {
        let mut f = empty_fn();

        // bb0 (entry)
        let mut bb0 = Block::new(b(0));
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(0)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));

        // bb1 (header) with params %acc=v(10), %i=v(11)
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(3),
            else_args: vec![],
        }));

        // bb2 (latch / body)
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        bb2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        bb2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(4),
            })
            .with_result(v(6)),
        );
        // BOTH in-loop redefs threaded back to the header.
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(5), v(6)],
        }));

        // bb3 (exit)
        let mut bb3 = Block::new(b(3));
        bb3.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));

        f.blocks = vec![bb0, bb1, bb2, bb3];
        f
    }

    /// Build the #71 DROPPED-UPDATE loop shape.
    ///
    /// Semantics modeled: `let mut q = Pair{a:0}; let mut i = 0; while i < N { q.a =
    /// q.a + 1; i = i + 1 } return q.a`. The scalar `i` is correctly threaded, but
    /// the scalarized aggregate field `q.a` is NOT given a header param: its in-loop
    /// redefinition (`%5 = add q.a, 1`) is computed in the latch and then DROPPED on
    /// the back-edge. The header keeps the entry-path `q.a` (`%0`, which dominates
    /// the header — so plain SSA dominance is satisfied!), so the loop reads the
    /// stale value every iteration and the update is lost. This is exactly the #71
    /// miscompile.
    ///
    ///   bb0:
    ///       %0 = const i32 0       ; q.a (entry value, dominates header)
    ///       %1 = const i32 0       ; i0
    ///       br bb1(%1)             ; ONLY i is threaded
    ///   bb1(%i:i32):              ; header has a param for i but NOT for q.a
    ///       %2 = const i32 10
    ///       %3 = icmp slt %i, %2
    ///       condbr %3, bb2, bb3
    ///   bb2:
    ///       %4 = const i32 1
    ///       %5 = add %0, %4        ; q.a' computed but NEVER threaded back (DROPPED)
    ///       %6 = add %i, %4        ; i'
    ///       br bb1(%6)             ; only i' carried; %5 lost
    ///   bb3:
    ///       return %0             ; returns the STALE entry q.a
    fn dropped_aggregate_loop() -> Function {
        let mut f = empty_fn();

        // bb0
        let mut bb0 = Block::new(b(0));
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(0)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(1)],
        }));

        // bb1 (header) with param %i=v(11) only
        let mut bb1 = Block::new(b(1)).with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(3),
            else_args: vec![],
        }));

        // bb2 (latch)
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        // q.a' = q.a(entry %0) + 1  -- the dropped in-loop redefinition
        bb2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        bb2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(4),
            })
            .with_result(v(6)),
        );
        // Only i' is threaded; %5 (q.a') is silently dropped.
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(6)],
        }));

        // bb3 (exit) — returns stale entry q.a
        let mut bb3 = Block::new(b(3));
        bb3.body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));

        f.blocks = vec![bb0, bb1, bb2, bb3];
        f
    }

    // ----------------------------------------------------------------------------
    // Tests
    // ----------------------------------------------------------------------------

    /// LOCKS IN #71: the dropped scalarized-aggregate-field update must be REJECTED.
    /// The header keeps the entry value (SSA-dominance-clean), so only the
    /// loop-completeness invariant catches it. This is the structural, producer-
    /// agnostic analogue of the bridge's `loop_carried_aggregate_error` guard.
    #[test]
    fn rejects_71_dropped_aggregate_update() {
        let f = dropped_aggregate_loop();
        let result = check_function(&f);
        let violations = result.expect_err("expected #71 dropped-update loop to be rejected");
        assert!(
            violations.iter().any(|v| matches!(
                v,
                SsaViolation::LoopCarriedValueNotThreaded {
                    value,
                    def_block,
                    header,
                    latch,
                } if *value == v_lit(5) && *def_block == b(2) && *header == b(1) && *latch == b(2)
            )),
            "expected LoopCarriedValueNotThreaded for v5/bb2->bb1, got: {:?}",
            violations
        );
    }

    /// LOCKS IN the good z1/z2 shape: when every in-loop redefinition is threaded
    /// through a header param + back-edge arg, the checker ACCEPTS the function.
    /// Guards against the checker being over-eager (false-positive fail-closed,
    /// which would reject all real loops).
    #[test]
    fn accepts_threaded_scalar_loop() {
        let f = threaded_scalar_loop();
        let result = check_function(&f);
        assert!(
            result.is_ok(),
            "expected correctly-threaded scalar loop to pass, got: {:?}",
            result.err()
        );
    }

    /// The back-edge of both shapes must be discovered via dominators: bb2 -> bb1
    /// where bb1 dominates bb2.
    #[test]
    fn back_edge_detected_via_dominators() {
        let f = threaded_scalar_loop();
        let edges = test_support::back_edges_of(&f);
        assert_eq!(
            edges,
            vec![CfgEdge {
                source: b(2),
                target: b(1)
            }]
        );
        assert!(test_support::dominates(&f, b(1), b(2)));
        assert!(!test_support::dominates(&f, b(2), b(1)));
    }

    /// The dropped in-loop redefinition v5 must be LIVE across the latch's back-edge
    /// (it is used by the next iteration's `q.a + 1` via the header). This is the
    /// liveness fact the #71 check keys off of.
    #[test]
    fn dropped_value_is_live_across_back_edge() {
        let f = dropped_aggregate_loop();
        // v0 (entry q.a) is live out of the latch because the body re-reads it next
        // iteration; v5 is the *would-be* threaded value but is dropped. The key
        // assertion is that the header's CONTINUED use of v0 keeps v0 live across
        // the back-edge while v5 (defined-in-loop) is what *should* have replaced it.
        let live = test_support::live_out_of(&f, b(2));
        assert!(
            live.contains_key(&0),
            "entry q.a (v0) should be live out of the latch (stale carry): {:?}",
            live
        );
    }

    /// SSA well-formedness: a use of a value whose def does NOT dominate it (and is
    /// not a block param of the using block) is rejected with
    /// `UseNotDominatedByDef`. Guards the dominance core independent of loops.
    #[test]
    fn rejects_use_before_def_across_blocks() {
        let mut f = empty_fn();
        // bb0: define nothing relevant, branch to bb1.
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        }));
        // bb1: use v(7) which is defined ONLY in bb2 (does not dominate bb1).
        let mut bb1 = Block::new(b(1));
        bb1.body.push(
            InstrNode::new(Inst::UnOp {
                op: trust_ir::UnOp::Neg,
                ty: Ty::I32,
                operand: v(7),
            })
            .with_result(v(8)),
        );
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![v(8)] }));
        // bb2: defines v(7) but is unreachable from bb1's use site.
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(7)),
        );
        bb2.body
            .push(InstrNode::new(Inst::Return { values: vec![v(7)] }));
        // bb0 -> bb1 only (bb2 unreachable) so v7's def cannot dominate the use.
        f.blocks = vec![bb0, bb1, bb2];

        let violations = check_function(&f).expect_err("use-before-def should be rejected");
        assert!(
            violations.iter().any(|vio| matches!(
                vio,
                SsaViolation::UseNotDominatedByDef { value, use_block, .. }
                    if *value == v_lit(7) && *use_block == b(1)
            )),
            "expected UseNotDominatedByDef for v7 in bb1, got: {:?}",
            violations
        );
    }

    /// SSA well-formedness: a branch with the wrong number of edge arguments for the
    /// target block's params is rejected. Catches the structural counterpart of a
    /// mis-threaded header (e.g. forgetting to add the back-edge arg entirely).
    #[test]
    fn rejects_edge_arg_arity_mismatch() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        // target bb1 has ONE param but we pass ZERO args.
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        }));
        let mut bb1 = Block::new(b(1)).with_param(v(20), Ty::I32);
        bb1.body.push(InstrNode::new(Inst::Return {
            values: vec![v(20)],
        }));
        f.blocks = vec![bb0, bb1];

        let violations = check_function(&f).expect_err("arity mismatch should be rejected");
        assert!(
            violations.iter().any(|vio| matches!(
                vio,
                SsaViolation::EdgeArgArityMismatch { edge, passed, expected }
                    if edge.source == b(0) && edge.target == b(1) && *passed == 0 && *expected == 1
            )),
            "expected EdgeArgArityMismatch bb0->bb1, got: {:?}",
            violations
        );
    }

    /// A straight-line (loop-free) well-formed function passes cleanly — the
    /// checker introduces no false positives on the common case.
    #[test]
    fn accepts_straight_line_function() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(7),
            })
            .with_result(v(0)),
        );
        bb0.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(0),
            })
            .with_result(v(1)),
        );
        bb0.body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        f.blocks = vec![bb0];
        assert!(check_function(&f).is_ok());
    }

    /// Build the STALE-RETHREAD loop shape (finding #1, positional/dead form).
    ///
    /// Here `q.a` DOES get a header param (%qa), unlike `dropped_aggregate_loop`, but
    /// the latch re-threads the param UNCHANGED while the genuine update is computed
    /// and DROPPED (dead). So the loop reads the stale `q.a` forever even though a
    /// phi exists. The old liveness-keyed rule misses this because the dead update is
    /// never in `live_out`; the new same-type dropped-update check catches it.
    ///
    ///   bb0:
    ///       %0 = const i32 0        ; qa0
    ///       %1 = const i32 0        ; i0
    ///       br bb1(%0, %1)          ; both seeded
    ///   bb1(%qa:i32, %i:i32):       ; header HAS a param for qa (slot 0) and i
    ///       %2 = const i32 10
    ///       %3 = icmp slt %i, %2
    ///       condbr %3, bb2, bb3
    ///   bb2:
    ///       %4 = const i32 1
    ///       %5 = add %qa, %4        ; qa' computed but DEAD + DROPPED
    ///       %6 = add %i, %4         ; i'
    ///       br bb1(%qa, %6)         ; STALE: slot 0 re-threads %qa unchanged
    ///   bb3:
    ///       return %qa
    fn stale_rethread_loop() -> Function {
        let mut f = empty_fn();

        let mut bb0 = Block::new(b(0));
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(0)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));

        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(3),
            else_args: vec![],
        }));

        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        // qa' = qa + 1 -- the dropped (dead) in-loop redefinition of the header param.
        bb2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        bb2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(4),
            })
            .with_result(v(6)),
        );
        // STALE: slot 0 re-threads %qa (v10) unchanged; %5 is dropped.
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(10), v(6)],
        }));

        let mut bb3 = Block::new(b(3));
        bb3.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));

        f.blocks = vec![bb0, bb1, bb2, bb3];
        f
    }

    /// Build the SWAPPED-SLOT loop shape (finding #2).
    ///
    /// Identical to `threaded_scalar_loop` except the back-edge args are SWAPPED:
    /// `br bb1(%6, %5)` routes `i'` into the `acc` slot and `acc'` into the `i` slot.
    /// Both `%5` and `%6` are in the threaded set and share the same type, so the old
    /// set-membership / type check accepts it; the positional check rejects it.
    ///
    ///   bb2:
    ///       ...
    ///       br bb1(%6, %5)          ; SWAPPED: slot 0 gets i', slot 1 gets acc'
    fn swapped_slot_loop() -> Function {
        let mut f = threaded_scalar_loop();
        // bb2 is the latch (index 2 in the vec built by threaded_scalar_loop).
        let bb2 = f
            .blocks
            .iter_mut()
            .find(|blk| blk.id == b(2))
            .expect("latch bb2");
        let term = bb2.body.last_mut().expect("latch terminator");
        term.inst = Inst::Br {
            target: b(1),
            args: vec![v(6), v(5)], // swapped
        };
        f
    }

    /// Build the (D-inverse) DEAD-INVARIANT-TEMP loop shape — a CORRECT loop that the
    /// old type-blind fingerprint wrongly REJECTED (false positive #4).
    ///
    /// Same skeleton as `dropped_aggregate_loop`, but the dead in-loop temp reading
    /// the loop-invariant `%0` is a COMPARISON (`icmp eq`, a *bool*), not a same-type
    /// arithmetic update. `let _ = INVARIANT == 1;` is genuinely dead code over a
    /// genuine loop-invariant that is also returned; it must be ACCEPTED. The bool
    /// result is provably not the dropped i32 update of `%0`, so the same-type check
    /// declines to fire.
    ///
    ///   bb2:
    ///       %4 = const i32 1
    ///       %5 = icmp eq %0, %4    ; DEAD bool temp over the invariant (not an update)
    ///       %6 = add %i, %4        ; i'
    ///       br bb1(%6)
    ///   bb3:
    ///       return %0              ; the invariant is genuinely returned unchanged
    fn dead_invariant_temp_loop() -> Function {
        let mut f = empty_fn();

        let mut bb0 = Block::new(b(0));
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(0)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(1)],
        }));

        let mut bb1 = Block::new(b(1)).with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(3),
            else_args: vec![],
        }));

        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        // DEAD bool temp reading the loop-invariant %0: `let _ = INVARIANT == 1;`.
        bb2.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        bb2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(4),
            })
            .with_result(v(6)),
        );
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(6)],
        }));

        let mut bb3 = Block::new(b(3));
        bb3.body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));

        f.blocks = vec![bb0, bb1, bb2, bb3];
        f
    }

    /// REJECT (finding #1, stale-rethread): a header param re-threaded UNCHANGED
    /// while its genuine in-loop update is computed and dropped (dead). The dead
    /// update is never in `live_out`, so the old liveness rule missed it; the
    /// same-type dropped-update check now fails closed.
    #[test]
    fn rejects_stale_rethread_of_header_param() {
        let f = stale_rethread_loop();
        let violations = check_function(&f).expect_err("stale-rethread must be rejected");
        assert!(
            violations.iter().any(|v| matches!(
                v,
                SsaViolation::LoopCarriedValueNotThreaded {
                    value,
                    def_block,
                    header,
                    latch,
                } if *value == v_lit(5) && *def_block == b(2) && *header == b(1) && *latch == b(2)
            )),
            "expected LoopCarriedValueNotThreaded for the dropped update v5, got: {:?}",
            violations
        );
    }

    /// REJECT (finding #2, swapped slot): `br bb1(%6,%5)` routes each loop-carried
    /// variable's next value into the WRONG header-param slot. Both args are
    /// type-correct and "present", so only a POSITIONAL check catches it.
    #[test]
    fn rejects_swapped_slot_threading() {
        let f = swapped_slot_loop();
        let violations = check_function(&f).expect_err("swapped-slot threading must be rejected");
        assert!(
            violations.iter().any(|v| matches!(
                v,
                SsaViolation::LoopCarriedSlotMisthreaded {
                    header,
                    latch,
                    slot,
                    param,
                    arg,
                } if *header == b(1)
                    && *latch == b(2)
                    && *slot == 0
                    && *param == v_lit(10)
                    && *arg == v_lit(6)
            )),
            "expected LoopCarriedSlotMisthreaded for slot 0 (acc<-i'), got: {:?}",
            violations
        );
    }

    /// ACCEPT (finding #4 inverse): a correct loop with a DEAD in-loop temp that is a
    /// COMPARISON over a genuine loop-invariant whose value is also returned. The old
    /// type-blind fingerprint wrongly rejected this (it rejected ANY dead derived
    /// temp of a carried value); the same-type rule accepts it because a bool result
    /// is provably not the dropped i32 update of the invariant.
    #[test]
    fn accepts_dead_invariant_comparison_temp() {
        let f = dead_invariant_temp_loop();
        let result = check_function(&f);
        assert!(
            result.is_ok(),
            "expected a correct loop with a dead invariant-comparison temp to pass, got: {:?}",
            result.err()
        );
    }

    fn v_lit(n: u32) -> ValueId {
        ValueId::new(n)
    }
}
