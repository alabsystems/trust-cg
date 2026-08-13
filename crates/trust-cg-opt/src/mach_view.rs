// trust-cg-opt - OPT-1 spike: arch-neutral machine-IR view facade
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! OPT-1 decision-spike prototype: a small trait facade that lets ONE pass
//! (or analysis) run over BOTH machine-IR universes:
//!
//! - the AArch64-shaped [`trust_cg_ir::MachFunction`] (arena `insts: Vec<MachInst>`
//!   indexed by `InstId`, blocks carry `Vec<InstId>` + stored preds/succs,
//!   `MachInst.opcode` hard-typed [`trust_cg_ir::AArch64Opcode`]), and
//! - the x86 [`trust_cg_lower::X86ISelFunction`] (per-block inline
//!   `Vec<X86ISelInst>` in a `HashMap<Block, X86ISelBlock>`, successors only,
//!   no preds, `X86Opcode`).
//!
//! **STATUS: PRODUCTION — the shared CFG-analysis authority of the ADR
//! `docs/adr-opt-ir-universe-2026-07-02.md`. Default-ON consumers on x86:
//! `x86_branch_layout`, `x86_if_convert`, `x86_bounds_check_elim` (via
//! [`crate::generic_branch_layout`] / [`CfgAnalysis`]), and since 2026-07-18
//! the five migrated passes `x86_licm`, `x86_strength_reduce`,
//! `x86_vectorize`, `x86_cse`, `x86_sroa` (fc98b0cf — their private
//! preds/RPO/idom/dominates/natural-loops re-ports were deleted in favor of
//! this module). The aarch64 lane still runs its own `dom.rs`/`loops.rs`
//! (passes hand-maintain `block.preds`, so that seam needs an equivalence
//! gate, not a swap — tracked under X2/X12 in the superiority burndown).**
//!
//! # What the facade abstracts (cheap, uniform across both IRs)
//!
//! 1. CFG shape: entry, layout order, successors, instruction counts.
//! 2. Instruction classification at `(block, index)`: branch/terminator/
//!    return kinds, side effects, defined vreg, explicit branch targets.
//!    Both opcode universes deliberately mirror each other
//!    (`x86_64_ops.rs`: "Naming convention follows the AArch64 pattern") and
//!    share `InstFlags`/`VReg` from trust-cg-ir, so classification is a thin
//!    per-IR shim.
//! 3. The CFG analyses that today exist THREE times in this crate
//!    (`dom.rs`+`loops.rs` for MachFunction; re-ported privately inside
//!    `x86_licm.rs` AND `x86_cse.rs` for X86ISelFunction): predecessor map,
//!    RPO, Cooper/Harvey/Kennedy idom, natural-loop discovery. Here they are
//!    written ONCE, generically, against the view.
//!
//! # What the facade deliberately does NOT abstract (the ADR's port-first side)
//!
//! - Loop-carried value representation: MachFunction carries loop state in
//!   explicit `Phi` instructions; X86ISelFunction carries it as multi-def
//!   merge vregs written by edge-local copies in every predecessor
//!   (`define_block_params` / `select_move_reg`). A mutating transform that
//!   clones loop bodies (unroll) must rewrite these under two different
//!   disciplines — that is per-IR logic no thin facade removes.
//! - Operand/immediate construction and flags semantics (x86 ALU ops write
//!   RFLAGS; the AArch64 non-S forms do not) — rewrite legality is per-arch.
//!
//! Determinism: all analysis outputs are derived by iterating `layout_order`
//! and sorting by [`MachIrView::block_index`]; no HashMap iteration order
//! leaks into results.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

use trust_cg_ir::{MachFunction, MachOperand, VReg, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelOperand};

use crate::effects::x86_produces_value;

// ===========================================================================
// Terminator classification
// ===========================================================================

/// Arch-neutral classification of a block's final instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermKind<B> {
    /// Conditional branch with explicit block target(s).
    ///
    /// x86 `Jcc` carries ONE explicit target (the other successor is
    /// fall-through / a following `Jmp`); AArch64 `BCond` may carry both.
    /// The vector holds whatever block operands the instruction has, in
    /// operand order.
    CondBranch { targets: Vec<B> },
    /// Unconditional direct jump to a single explicit target
    /// (`Jmp` / `B`).
    Jump { target: B },
    /// Function return.
    Return,
    /// Block does not end in a terminator: control falls through in layout
    /// order (also reported for empty blocks).
    Fallthrough,
    /// A terminator whose targets are not expressible as explicit blocks
    /// (indirect branch `Br`, traps, ...). Fail-closed bucket: passes must
    /// not touch these blocks' control flow.
    Other,
}

// ===========================================================================
// The read view
// ===========================================================================

/// Read-only, arch-neutral view of a machine-IR function: CFG shape plus
/// per-instruction classification queries addressed by `(block, index)`.
///
/// `(block, index)` addressing is the ONLY instruction identity both IRs
/// share: MachFunction's `InstId` arena handles have no X86ISelFunction
/// counterpart (x86 insts live inline in their block).
pub trait MachIrView {
    /// Block identifier (`BlockId` for MachFunction, `Block` for
    /// X86ISelFunction). `Ord` is not required (the x86 `Block` newtype does
    /// not derive it); deterministic ordering goes through
    /// [`MachIrView::block_index`].
    type Block: Copy + Eq + Hash + Debug;

    /// Short arch/IR tag for diagnostics.
    fn ir_name(&self) -> &'static str;

    /// The function's entry block.
    fn entry_block(&self) -> Self::Block;

    /// Blocks in layout (emission) order.
    fn layout_order(&self) -> Vec<Self::Block>;

    /// Stable numeric identity of a block, for deterministic sorting.
    fn block_index(&self, block: Self::Block) -> u32;

    /// CFG successors of `block`.
    fn successors(&self, block: Self::Block) -> Vec<Self::Block>;

    /// Number of instructions in `block`.
    fn inst_count(&self, block: Self::Block) -> usize;

    // ---- instruction classification at (block, idx) ----

    /// True if the instruction is any branch.
    fn is_branch(&self, block: Self::Block, idx: usize) -> bool;

    /// True if the instruction ends a block.
    fn is_terminator(&self, block: Self::Block, idx: usize) -> bool;

    /// True for a conditional branch (has a fall-through path).
    fn is_conditional_branch(&self, block: Self::Block, idx: usize) -> bool;

    /// True for an unconditional branch (direct or indirect).
    fn is_unconditional_branch(&self, block: Self::Block, idx: usize) -> bool;

    /// True for a function return.
    fn is_return(&self, block: Self::Block, idx: usize) -> bool;

    /// True if the instruction has side effects (stores, calls, traps, ...).
    fn has_side_effects(&self, block: Self::Block, idx: usize) -> bool;

    /// The virtual register the instruction defines, if it produces a value
    /// into a VReg. (On x86, tied def-use opcodes like `AddRI` report their
    /// operand-0 def; the def is also a use — mutation passes must consult
    /// per-IR semantics, this query is for analyses.)
    fn defined_vreg(&self, block: Self::Block, idx: usize) -> Option<VReg>;

    /// Explicit block-target operands of a branch, in operand order.
    /// Empty for indirect branches.
    fn branch_targets(&self, block: Self::Block, idx: usize) -> Vec<Self::Block>;

    // ---- provided queries ----

    /// Classify the block's final instruction. See [`TermKind`].
    fn classify_terminator(&self, block: Self::Block) -> TermKind<Self::Block> {
        let n = self.inst_count(block);
        if n == 0 {
            return TermKind::Fallthrough;
        }
        let idx = n - 1;
        if self.is_return(block, idx) {
            return TermKind::Return;
        }
        if self.is_conditional_branch(block, idx) {
            return TermKind::CondBranch {
                targets: self.branch_targets(block, idx),
            };
        }
        if self.is_unconditional_branch(block, idx) {
            let targets = self.branch_targets(block, idx);
            if targets.len() == 1 {
                return TermKind::Jump { target: targets[0] };
            }
            // Indirect branch (`Br`) or malformed: no explicit target.
            return TermKind::Other;
        }
        if self.is_terminator(block, idx) {
            return TermKind::Other;
        }
        TermKind::Fallthrough
    }
}

// ===========================================================================
// The (minimal) edit view
// ===========================================================================

/// Minimal mutation surface layered over [`MachIrView`], sized for
/// layout-class passes (branch/jump edits). Deliberately NOT a general
/// transform API: cloning instructions, rewriting operands, and threading
/// loop-carried values stay per-IR (see the module docs and the ADR).
pub trait MachIrEdit: MachIrView {
    /// Remove the instruction at `(block, idx)` from the block's sequence.
    ///
    /// MachFunction: unlinks the `InstId` from the block, leaving the arena
    /// untouched (the crate-wide pass convention: "passes unlink InstIds from
    /// blocks but never compact the arena"). X86ISelFunction: removes the
    /// inline instruction.
    fn remove_inst(&mut self, block: Self::Block, idx: usize);
}

// ===========================================================================
// MachFunction (AArch64 universe) instantiation
// ===========================================================================

impl MachIrView for MachFunction {
    type Block = trust_cg_ir::BlockId;

    fn ir_name(&self) -> &'static str {
        "aarch64/MachFunction"
    }

    fn entry_block(&self) -> Self::Block {
        self.entry
    }

    fn layout_order(&self) -> Vec<Self::Block> {
        self.block_order.clone()
    }

    fn block_index(&self, block: Self::Block) -> u32 {
        block.0
    }

    fn successors(&self, block: Self::Block) -> Vec<Self::Block> {
        self.block(block).succs.clone()
    }

    fn inst_count(&self, block: Self::Block) -> usize {
        self.block(block).insts.len()
    }

    fn is_branch(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).flags.is_branch()
    }

    fn is_terminator(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).flags.is_terminator()
    }

    fn is_conditional_branch(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).opcode.is_conditional_branch()
    }

    fn is_unconditional_branch(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).opcode.is_unconditional_branch()
    }

    fn is_return(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).flags.is_return()
    }

    fn has_side_effects(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).flags.has_side_effects()
    }

    fn defined_vreg(&self, block: Self::Block, idx: usize) -> Option<VReg> {
        let inst = self.view_inst(block, idx);
        if !crate::effects::inst_produces_value(inst) {
            return None;
        }
        inst.operands.first().and_then(|op| op.as_vreg())
    }

    fn branch_targets(&self, block: Self::Block, idx: usize) -> Vec<Self::Block> {
        self.view_inst(block, idx)
            .operands
            .iter()
            .filter_map(|op| match op {
                MachOperand::Block(b) => Some(*b),
                _ => None,
            })
            .collect()
    }
}

/// Private accessor: resolve `(block, idx)` through the InstId arena.
trait MachFunctionViewExt {
    fn view_inst(&self, block: trust_cg_ir::BlockId, idx: usize) -> &trust_cg_ir::MachInst;
}

impl MachFunctionViewExt for MachFunction {
    fn view_inst(&self, block: trust_cg_ir::BlockId, idx: usize) -> &trust_cg_ir::MachInst {
        let inst_id = self.block(block).insts[idx];
        self.inst(inst_id)
    }
}

impl MachIrEdit for MachFunction {
    fn remove_inst(&mut self, block: Self::Block, idx: usize) {
        // Unlink from the block only; the arena is append-only by convention.
        self.block_mut(block).insts.remove(idx);
    }
}

// ===========================================================================
// X86ISelFunction (x86 universe) instantiation
// ===========================================================================

impl MachIrView for X86ISelFunction {
    type Block = Block;

    fn ir_name(&self) -> &'static str {
        "x86_64/X86ISelFunction"
    }

    fn entry_block(&self) -> Self::Block {
        // X86ISelFunction has no explicit entry field; ISel emits the entry
        // first in layout order (the same assumption x86_licm/x86_cse make).
        self.block_order[0]
    }

    fn layout_order(&self) -> Vec<Self::Block> {
        self.block_order.clone()
    }

    fn block_index(&self, block: Self::Block) -> u32 {
        block.0
    }

    fn successors(&self, block: Self::Block) -> Vec<Self::Block> {
        self.blocks
            .get(&block)
            .map(|b| b.successors.clone())
            .unwrap_or_default()
    }

    fn inst_count(&self, block: Self::Block) -> usize {
        self.blocks.get(&block).map(|b| b.insts.len()).unwrap_or(0)
    }

    fn is_branch(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).flags.is_branch()
    }

    fn is_terminator(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).flags.is_terminator()
    }

    fn is_conditional_branch(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).opcode == X86Opcode::Jcc
    }

    fn is_unconditional_branch(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).opcode == X86Opcode::Jmp
    }

    fn is_return(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).flags.is_return()
    }

    fn has_side_effects(&self, block: Self::Block, idx: usize) -> bool {
        self.view_inst(block, idx).flags.has_side_effects()
    }

    fn defined_vreg(&self, block: Self::Block, idx: usize) -> Option<VReg> {
        let inst = self.view_inst(block, idx);
        if !x86_produces_value(inst.opcode) {
            return None;
        }
        match inst.operands.first() {
            Some(X86ISelOperand::VReg(v)) => Some(*v),
            _ => None,
        }
    }

    fn branch_targets(&self, block: Self::Block, idx: usize) -> Vec<Self::Block> {
        self.view_inst(block, idx)
            .operands
            .iter()
            .filter_map(|op| match op {
                X86ISelOperand::Block(b) => Some(*b),
                _ => None,
            })
            .collect()
    }
}

/// Private accessor: resolve `(block, idx)` through the per-block inline Vec.
trait X86ViewExt {
    fn view_inst(&self, block: Block, idx: usize) -> &trust_cg_lower::X86ISelInst;
}

impl X86ViewExt for X86ISelFunction {
    fn view_inst(&self, block: Block, idx: usize) -> &trust_cg_lower::X86ISelInst {
        &self.blocks[&block].insts[idx]
    }
}

impl MachIrEdit for X86ISelFunction {
    fn remove_inst(&mut self, block: Self::Block, idx: usize) {
        if let Some(b) = self.blocks.get_mut(&block) {
            b.insts.remove(idx);
        }
    }
}

// ===========================================================================
// Generic CFG analyses (written once; today these exist 3x in this crate)
// ===========================================================================

/// A natural loop discovered on the generic CFG view.
#[derive(Debug, Clone)]
pub struct GenericLoop<B> {
    /// Loop header (target of the back-edge(s)).
    pub header: B,
    /// Back-edge source blocks, sorted by block index. Multiple latches per
    /// header are merged into one loop (same policy as `loops.rs`).
    pub latches: Vec<B>,
    /// All blocks in the loop body (includes header and latches).
    pub body: HashSet<B>,
    /// Unique non-loop predecessor of the header, if one exists.
    pub preheader: Option<B>,
    /// Nesting depth (outermost = 1).
    pub depth: u32,
}

/// Bundled CFG analysis results over any [`MachIrView`].
///
/// Predecessors are DERIVED from successors on both IRs (MachFunction stores
/// preds, but deriving keeps one ground truth and matches what x86_licm and
/// x86_cse each rebuild privately today).
#[derive(Debug, Clone)]
pub struct CfgAnalysis<B> {
    /// Derived predecessor map (reachable and unreachable blocks alike).
    pub preds: HashMap<B, Vec<B>>,
    /// Reverse postorder over reachable blocks, entry first.
    pub rpo: Vec<B>,
    /// Immediate dominators (Cooper/Harvey/Kennedy); entry maps to itself.
    /// Only reachable blocks are present.
    pub idom: HashMap<B, B>,
    /// Natural loops, sorted by header block index.
    pub loops: Vec<GenericLoop<B>>,
}

impl<B: Copy + Eq + Hash + Debug> CfgAnalysis<B> {
    /// Compute predecessors, RPO, idom, and natural loops for `view`.
    pub fn compute<V: MachIrView<Block = B>>(view: &V) -> Self {
        let preds = predecessor_map(view);
        let rpo = compute_rpo(view);
        let idom = compute_idom(view, &preds, &rpo);
        let loops = find_natural_loops(view, &preds, &idom);
        Self {
            preds,
            rpo,
            idom,
            loops,
        }
    }

    /// True if `a` dominates `b` (reflexive).
    pub fn dominates(&self, a: B, b: B) -> bool {
        dominates(a, b, &self.idom)
    }
}

/// Build the predecessor map by iterating layout order (deterministic).
pub fn predecessor_map<V: MachIrView>(view: &V) -> HashMap<V::Block, Vec<V::Block>> {
    let mut preds: HashMap<V::Block, Vec<V::Block>> = HashMap::new();
    for block in view.layout_order() {
        for succ in view.successors(block) {
            preds.entry(succ).or_default().push(block);
        }
    }
    preds
}

/// Reverse postorder over reachable blocks via iterative DFS from entry.
pub fn compute_rpo<V: MachIrView>(view: &V) -> Vec<V::Block> {
    let entry = view.entry_block();
    let mut visited: HashSet<V::Block> = HashSet::new();
    let mut postorder: Vec<V::Block> = Vec::new();
    let mut stack: Vec<(V::Block, usize)> = vec![(entry, 0)];
    visited.insert(entry);

    while let Some((block, next_succ_idx)) = stack.last_mut() {
        let block_id = *block;
        let succs = view.successors(block_id);
        if *next_succ_idx < succs.len() {
            let succ = succs[*next_succ_idx];
            *next_succ_idx += 1;
            if visited.insert(succ) {
                stack.push((succ, 0));
            }
        } else {
            postorder.push(block_id);
            stack.pop();
        }
    }

    postorder.reverse();
    postorder
}

/// Immediate dominators via Cooper/Harvey/Kennedy over the derived preds and
/// the given RPO. Mirrors `dom.rs` / `x86_licm.rs` exactly.
pub fn compute_idom<V: MachIrView>(
    view: &V,
    preds: &HashMap<V::Block, Vec<V::Block>>,
    rpo: &[V::Block],
) -> HashMap<V::Block, V::Block> {
    let entry = view.entry_block();
    let rpo_number: HashMap<V::Block, u32> = rpo
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, i as u32))
        .collect();

    let mut idom: HashMap<V::Block, V::Block> = HashMap::new();
    idom.insert(entry, entry);

    let empty: Vec<V::Block> = Vec::new();
    let mut changed = true;
    while changed {
        changed = false;
        for &block in rpo {
            if block == entry {
                continue;
            }
            let block_preds = preds.get(&block).unwrap_or(&empty);

            let mut new_idom: Option<V::Block> = None;
            for &pred in block_preds {
                if idom.contains_key(&pred) {
                    new_idom = Some(pred);
                    break;
                }
            }
            let Some(mut new_idom_val) = new_idom else {
                continue;
            };
            for &pred in block_preds {
                if pred == new_idom_val {
                    continue;
                }
                if idom.contains_key(&pred) {
                    new_idom_val = intersect(pred, new_idom_val, &idom, &rpo_number);
                }
            }
            if idom.get(&block) != Some(&new_idom_val) {
                idom.insert(block, new_idom_val);
                changed = true;
            }
        }
    }

    idom
}

/// Two-finger intersect from Cooper/Harvey/Kennedy.
fn intersect<B: Copy + Eq + Hash>(
    mut b1: B,
    mut b2: B,
    idom: &HashMap<B, B>,
    rpo_number: &HashMap<B, u32>,
) -> B {
    while b1 != b2 {
        let n1 = rpo_number.get(&b1).copied().unwrap_or(u32::MAX);
        let n2 = rpo_number.get(&b2).copied().unwrap_or(u32::MAX);
        if n1 > n2 {
            b1 = idom[&b1];
        } else {
            b2 = idom[&b2];
        }
    }
    b1
}

/// True if `a` dominates `b` (reflexive), by walking the idom chain.
pub fn dominates<B: Copy + Eq + Hash>(a: B, b: B, idom: &HashMap<B, B>) -> bool {
    if a == b {
        return true;
    }
    let mut current = b;
    loop {
        let dom = match idom.get(&current) {
            Some(&d) => d,
            None => return false,
        };
        if dom == a {
            return true;
        }
        if dom == current {
            return false; // reached entry
        }
        current = dom;
    }
}

/// Discover natural loops: a back-edge is a CFG edge `latch -> header` where
/// `header` dominates `latch`; the body is the reverse-reachable set from the
/// latch that stays out of the header. Multiple back-edges to one header are
/// merged. Depth = 1 + number of distinct strictly-containing loop bodies.
pub fn find_natural_loops<V: MachIrView>(
    view: &V,
    preds: &HashMap<V::Block, Vec<V::Block>>,
    idom: &HashMap<V::Block, V::Block>,
) -> Vec<GenericLoop<V::Block>> {
    type LoopAccumulator<B> = (Vec<B>, HashSet<B>);

    // header -> (latches, body)
    let mut raw: HashMap<V::Block, LoopAccumulator<V::Block>> = HashMap::new();

    for block in view.layout_order() {
        for succ in view.successors(block) {
            if dominates(succ, block, idom) {
                let body = loop_body(preds, succ, block);
                let entry = raw
                    .entry(succ)
                    .or_insert_with(|| (Vec::new(), HashSet::new()));
                entry.0.push(block);
                entry.1.extend(body);
            }
        }
    }

    if raw.is_empty() {
        return Vec::new();
    }

    let header_bodies: Vec<(V::Block, HashSet<V::Block>)> =
        raw.iter().map(|(h, (_, b))| (*h, b.clone())).collect();

    let mut loops: Vec<GenericLoop<V::Block>> = raw
        .into_iter()
        .map(|(header, (mut latches, body))| {
            latches.sort_by_key(|&b| view.block_index(b));
            latches.dedup();
            let preheader = find_preheader(preds, header, &body);
            let mut depth = 1u32;
            for (other_header, other_body) in &header_bodies {
                if *other_header == header {
                    continue;
                }
                if body.is_subset(other_body) && body.len() < other_body.len() {
                    depth += 1;
                }
            }
            GenericLoop {
                header,
                latches,
                body,
                preheader,
                depth,
            }
        })
        .collect();

    loops.sort_by_key(|lp| view.block_index(lp.header));
    loops
}

/// Reverse-reachability loop body: header + everything that reaches the latch
/// without passing through the header.
fn loop_body<B: Copy + Eq + Hash>(preds: &HashMap<B, Vec<B>>, header: B, latch: B) -> HashSet<B> {
    let mut body: HashSet<B> = HashSet::new();
    body.insert(header);
    body.insert(latch);
    if header == latch {
        return body;
    }
    let empty: Vec<B> = Vec::new();
    let mut worklist: VecDeque<B> = VecDeque::new();
    worklist.push_back(latch);
    while let Some(block) = worklist.pop_front() {
        for &pred in preds.get(&block).unwrap_or(&empty) {
            if body.insert(pred) {
                worklist.push_back(pred);
            }
        }
    }
    body
}

/// A preheader is the UNIQUE predecessor of the header outside the loop body.
fn find_preheader<B: Copy + Eq + Hash>(
    preds: &HashMap<B, Vec<B>>,
    header: B,
    body: &HashSet<B>,
) -> Option<B> {
    let empty: Vec<B> = Vec::new();
    let non_loop_preds: Vec<B> = preds
        .get(&header)
        .unwrap_or(&empty)
        .iter()
        .filter(|p| !body.contains(p))
        .copied()
        .collect();
    if non_loop_preds.len() == 1 {
        Some(non_loop_preds[0])
    } else {
        None
    }
}

// ===========================================================================
// Tests: the SAME analyses over hand-built functions of BOTH IRs
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::RegClass;
    use trust_cg_ir::x86_64_ops::X86CondCode;
    use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, Signature as A64Signature};
    use trust_cg_lower::function::Signature as X86Signature;
    use trust_cg_lower::types::Type as LirType;
    use trust_cg_lower::{X86ISelInst, X86ISelOperand};

    // -- twin counted-loop builders --------------------------------------
    //
    // Same CFG on both IRs:
    //
    //   b0 (preheader: iv = 0; jump b1)
    //   b1 (header: cmp iv, 10; cond-exit to b3)
    //   b2 (latch: iv += 1; jump b1)
    //   b3 (exit: ret)

    fn a64_vreg(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }

    pub(crate) fn make_a64_counted_loop() -> MachFunction {
        let mut f = MachFunction::new("a64_loop".to_string(), A64Signature::new(vec![], vec![]));
        let b0 = f.entry;
        let b1 = f.create_block();
        let b2 = f.create_block();
        let b3 = f.create_block();

        let v0 = a64_vreg(f.alloc_vreg());

        let mov = f.push_inst(MachInst::new(
            AArch64Opcode::MovI,
            vec![MachOperand::VReg(v0), MachOperand::Imm(0)],
        ));
        f.append_inst(b0, mov);
        let br0 = f.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(b1)],
        ));
        f.append_inst(b0, br0);

        let cmp = f.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(v0), MachOperand::Imm(10)],
        ));
        f.append_inst(b1, cmp);
        // BCond [body, exit] (dual explicit targets, dom.rs test convention).
        let bcond = f.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(b2), MachOperand::Block(b3)],
        ));
        f.append_inst(b1, bcond);

        let add = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(v0),
                MachOperand::VReg(v0),
                MachOperand::Imm(1),
            ],
        ));
        f.append_inst(b2, add);
        let br2 = f.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(b1)],
        ));
        f.append_inst(b2, br2);

        let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(b3, ret);

        f.add_edge(b0, b1);
        f.add_edge(b1, b2);
        f.add_edge(b1, b3);
        f.add_edge(b2, b1);
        f
    }

    pub(crate) fn make_x86_counted_loop() -> X86ISelFunction {
        let sig = X86Signature {
            params: vec![],
            returns: vec![LirType::I64],
        };
        let mut f = X86ISelFunction::new("x86_loop".to_string(), sig);
        let b0 = Block(0);
        let b1 = Block(1);
        let b2 = Block(2);
        let b3 = Block(3);
        for b in [b0, b1, b2, b3] {
            f.ensure_block(b);
        }
        let v0 = VReg::new(0, RegClass::Gpr64);
        f.next_vreg = 1;

        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(0)],
            ),
        );
        f.push_inst(
            b0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(b1)]),
        );

        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        // Jcc GE, exit — single explicit target, fallthrough to b2.
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::GE),
                    X86ISelOperand::Block(b3),
                ],
            ),
        );

        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(1)],
            ),
        );
        f.push_inst(
            b2,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(b1)]),
        );

        f.push_inst(b3, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b3, b2];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b1];
        f
    }

    /// Assert the analysis facts shared by the twin loops, generically.
    fn assert_counted_loop_analysis<V: MachIrView>(view: &V) {
        let order = view.layout_order();
        assert_eq!(order.len(), 4, "{}", view.ir_name());
        let (b0, b1, b2, b3) = (order[0], order[1], order[2], order[3]);

        let cfg = CfgAnalysis::compute(view);

        // RPO starts at entry.
        assert_eq!(cfg.rpo[0], view.entry_block(), "{}", view.ir_name());
        assert_eq!(cfg.rpo.len(), 4, "{}", view.ir_name());

        // Dominators.
        assert_eq!(cfg.idom[&b1], b0, "{}", view.ir_name());
        assert_eq!(cfg.idom[&b2], b1, "{}", view.ir_name());
        assert_eq!(cfg.idom[&b3], b1, "{}", view.ir_name());
        assert!(cfg.dominates(b1, b2), "{}", view.ir_name());
        assert!(!cfg.dominates(b2, b1), "{}", view.ir_name());

        // Exactly one natural loop: header b1, latch b2, preheader b0.
        assert_eq!(cfg.loops.len(), 1, "{}", view.ir_name());
        let lp = &cfg.loops[0];
        assert_eq!(lp.header, b1, "{}", view.ir_name());
        assert_eq!(lp.latches, vec![b2], "{}", view.ir_name());
        assert_eq!(lp.preheader, Some(b0), "{}", view.ir_name());
        assert_eq!(lp.depth, 1, "{}", view.ir_name());
        assert!(
            lp.body.contains(&b1) && lp.body.contains(&b2),
            "{}",
            view.ir_name()
        );
        assert_eq!(lp.body.len(), 2, "{}", view.ir_name());

        // Terminator classification.
        assert_eq!(
            view.classify_terminator(b0),
            TermKind::Jump { target: b1 },
            "{}",
            view.ir_name()
        );
        match view.classify_terminator(b1) {
            TermKind::CondBranch { targets } => {
                assert!(targets.contains(&b3), "{}", view.ir_name());
            }
            other => panic!("{}: header terminator {:?}", view.ir_name(), other),
        }
        assert_eq!(
            view.classify_terminator(b2),
            TermKind::Jump { target: b1 },
            "{}",
            view.ir_name()
        );
        assert_eq!(
            view.classify_terminator(b3),
            TermKind::Return,
            "{}",
            view.ir_name()
        );

        // Defined vregs: preheader iv init defines a vreg; cmp does not.
        assert!(view.defined_vreg(b0, 0).is_some(), "{}", view.ir_name());
        assert!(
            view.defined_vreg(b1, 0).is_none(),
            "cmp defines no vreg: {}",
            view.ir_name()
        );
    }

    #[test]
    fn counted_loop_analysis_matches_on_aarch64_machfunction() {
        let func = make_a64_counted_loop();
        assert_counted_loop_analysis(&func);
    }

    #[test]
    fn counted_loop_analysis_matches_on_x86_iselfunction() {
        let func = make_x86_counted_loop();
        assert_counted_loop_analysis(&func);
    }

    #[test]
    fn loop_free_function_has_no_loops_on_both_irs() {
        // aarch64: straight-line entry -> ret.
        let mut a64 = MachFunction::new("a64_line".to_string(), A64Signature::new(vec![], vec![]));
        let ret = a64.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        a64.append_inst(a64.entry, ret);
        assert!(CfgAnalysis::compute(&a64).loops.is_empty());

        // x86: straight-line entry -> ret.
        let sig = X86Signature {
            params: vec![],
            returns: vec![],
        };
        let mut x86 = X86ISelFunction::new("x86_line".to_string(), sig);
        let b0 = Block(0);
        x86.ensure_block(b0);
        x86.push_inst(b0, X86ISelInst::new(X86Opcode::Ret, vec![]));
        assert!(CfgAnalysis::compute(&x86).loops.is_empty());
    }

    #[test]
    fn nested_loops_report_depth_on_x86() {
        // b0 -> b1 (outer header) -> b2 (inner header/latch, self loop) -> b3
        // (outer latch) -> b1; b1 -> b4 exit.
        let sig = X86Signature {
            params: vec![],
            returns: vec![],
        };
        let mut f = X86ISelFunction::new("x86_nested".to_string(), sig);
        let blocks: Vec<Block> = (0..5).map(Block).collect();
        for &b in &blocks {
            f.ensure_block(b);
        }
        let (b0, b1, b2, b3, b4) = (blocks[0], blocks[1], blocks[2], blocks[3], blocks[4]);

        f.push_inst(
            b0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(b1)]),
        );
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(b4),
                ],
            ),
        );
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(b2),
                ],
            ),
        );
        f.push_inst(
            b3,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(b1)]),
        );
        f.push_inst(b4, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b4, b2];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b2, b3];
        f.blocks.get_mut(&b3).unwrap().successors = vec![b1];

        let cfg = CfgAnalysis::compute(&f);
        assert_eq!(cfg.loops.len(), 2);
        // Sorted by header index: outer (b1) first, inner (b2) second.
        assert_eq!(cfg.loops[0].header, b1);
        assert_eq!(cfg.loops[0].depth, 1);
        assert_eq!(cfg.loops[1].header, b2);
        assert_eq!(cfg.loops[1].depth, 2);
        assert_eq!(cfg.loops[1].latches, vec![b2], "self-loop latch");
    }

    #[test]
    fn remove_inst_unlinks_on_both_irs() {
        // aarch64: removing the preheader's iv-init leaves the branch.
        let mut a64 = make_a64_counted_loop();
        let b0 = MachIrView::entry_block(&a64);
        assert_eq!(MachIrView::inst_count(&a64, b0), 2);
        MachIrEdit::remove_inst(&mut a64, b0, 0);
        assert_eq!(MachIrView::inst_count(&a64, b0), 1);
        assert_eq!(
            a64.classify_terminator(b0),
            TermKind::Jump {
                target: a64.layout_order()[1]
            }
        );
        // Arena untouched (unlink-only convention).
        assert_eq!(a64.num_insts(), 7);

        // x86: same edit.
        let mut x86 = make_x86_counted_loop();
        let b0 = MachIrView::entry_block(&x86);
        assert_eq!(MachIrView::inst_count(&x86, b0), 2);
        MachIrEdit::remove_inst(&mut x86, b0, 0);
        assert_eq!(MachIrView::inst_count(&x86, b0), 1);
    }
}
