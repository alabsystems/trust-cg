// trust-cg-opt - Per-pass translation validation: symbolic region equivalence
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Symbolic equivalence of the regions a pass run changed.
//!
//! # Method
//!
//! Control flow is read from the instructions (branch operands and the
//! layout fallthrough), never from the `preds`/`succs` lists. A block is
//! *changed* when it exists in only one function, its instructions differ,
//! or its fallthrough successor differs. Every changed block that exists in
//! both functions is a *region head*. From a head, both functions are
//! executed symbolically ([`super::semantics`]) along every path, forking at
//! conditional branches, through the blocks that exist in only that function
//! (the region's *internal* blocks), until each path reaches a block that
//! exists in both (a *boundary*), returns, or aborts.
//!
//! The two executions are then compared as decision trees: for every
//! boundary block, the condition under which it is reached, and the value of
//! every location live into it (in the input function) and of the memory and
//! effect history, folded over the forks as `ite` terms; and likewise for
//! the returns and aborts. Equal normalized terms are the only acceptance.
//!
//! A load the output executes under a condition other than the one the
//! input executed the same load under (unless the input executed it on
//! every path from the head) is a speculated load, and is not accepted.
//!
//! # Why this shows preservation
//!
//! Invariant: on entry to every block the two functions agree on every
//! location live into that block in the input function, and on memory and
//! the effect history. An unchanged block preserves the invariant (the same
//! code reads only its upward-exposed uses, which are live into it). A head
//! is entered with the invariant, and the comparison shows the invariant at
//! each boundary it reaches and the same observable behavior at each exit.
//! The input-side terms of a head may only read locations live into it; this
//! is checked on every compared term, so a disagreement between the
//! liveness model and the instruction semantics cannot hide an input.
//!
//! Internal blocks must be entered only from inside their region, and the
//! region must be acyclic; loops, jump tables, invoke blocks and indirect
//! branches inside a changed region are not modeled and leave the run
//! unproved.
//!
//! Exception edges (each EH call site's invoke block to its landing pad)
//! are part of the CFG: a landing pad is reachable, so a changed pad is a
//! region head checked like any other, and everything live into a pad is
//! live through its whole invoke block (the exception leaves at the call,
//! before what the block writes after it). The exception-handling metadata
//! itself must be unchanged.

use std::collections::BTreeSet;

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use trust_cg_ir::regs::{X29, X30};
use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass};

use super::ValidationVerdict;
use super::semantics::{Exec, State, Unsupported, for_each_access, preg_loc};
use super::term::{Atom, Cmp, Loc, Term, TermArena, TermId};

/// Leaves a head's walk may reach before the run is left unproved.
const MAX_LEAVES: usize = 256;
/// Internal blocks a single path may cross.
const MAX_PATH_BLOCKS: usize = 64;

/// Callee-saved state a return must preserve: X19-X28, the frame pointer,
/// the link register, the stack pointer and the low halves of V8-V15.
fn return_preserved_locs() -> Vec<Loc> {
    let mut locs: Vec<Loc> = (19u8..=28).map(Loc::Gpr).collect();
    locs.extend([X29, X30].iter().filter_map(|p| preg_loc(*p)));
    locs.push(Loc::Sp);
    locs.extend((8u8..=15).map(Loc::Fpr));
    locs
}

/// How a block ends after its last conditional exit, read from its
/// instructions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Exit {
    /// Continues at a block: an explicit `B` or the layout fallthrough.
    Goto(BlockId),
    /// `RET`, or a tail call.
    Return { inst: InstId },
    /// A final `BRK`.
    Abort { inst: InstId },
}

/// One straight-line run of a block, optionally followed by a conditional
/// exit: `insts[start..end]` execute, then (when `branch` is set) the
/// conditional branch at `insts[end]` leaves for `branch` when taken.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Segment {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) branch: Option<BlockId>,
}

/// A block's control structure: straight-line segments separated by
/// conditional exits, then a final exit.
#[derive(Clone, Debug)]
pub(super) struct Shape {
    pub(super) segments: Vec<Segment>,
    pub(super) exit: Exit,
}

impl Shape {
    /// Every block control can leave for.
    pub(super) fn successors(&self) -> Vec<BlockId> {
        let mut out: Vec<BlockId> = self.segments.iter().filter_map(|s| s.branch).collect();
        if let Exit::Goto(t) = self.exit {
            out.push(t);
        }
        out
    }

    /// Whether the block is straight-line code continuing at one block.
    pub(super) fn single_successor(&self) -> Option<BlockId> {
        match (self.segments.as_slice(), &self.exit) {
            ([only], Exit::Goto(t)) if only.branch.is_none() => Some(*t),
            _ => None,
        }
    }
}

fn block_target(inst: &MachInst) -> Option<BlockId> {
    inst.operands.iter().rev().find_map(|op| match op {
        MachOperand::Block(b) => Some(*b),
        _ => None,
    })
}

fn is_conditional_branch(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::BCond
            | AArch64Opcode::Bcc
            | AArch64Opcode::Cbz
            | AArch64Opcode::Cbnz
            | AArch64Opcode::Tbz
            | AArch64Opcode::Tbnz
    )
}

/// Parse one block's control structure: conditional branches may appear
/// anywhere (each ends a segment); a `B`, `RET`, tail call or `BRK` must be
/// the block's last instruction (`NOP` padding aside); indirect branches and
/// jump tables are not modeled.
fn block_shape(
    func: &MachFunction,
    block: BlockId,
    next: Option<BlockId>,
) -> Result<Shape, String> {
    let insts = &func.block(block).insts;
    let mut segments = Vec::new();
    let mut start = 0;
    let mut exit = None;
    for (index, &id) in insts.iter().enumerate() {
        let inst = func.inst(id);
        if exit.is_some() {
            if matches!(inst.opcode, AArch64Opcode::Nop | AArch64Opcode::AlignNop) {
                continue;
            }
            return Err(format!(
                "block {} has inst {} ({:?}) after its final exit",
                block.0, id.0, inst.opcode
            ));
        }
        let target = || {
            block_target(inst).ok_or_else(|| format!("branch inst {} has no block target", id.0))
        };
        match inst.opcode {
            op if is_conditional_branch(op) => {
                segments.push(Segment {
                    start,
                    end: index,
                    branch: Some(target()?),
                });
                start = index + 1;
            }
            AArch64Opcode::B => {
                segments.push(Segment {
                    start,
                    end: index,
                    branch: None,
                });
                exit = Some(Exit::Goto(target()?));
            }
            AArch64Opcode::Ret | AArch64Opcode::TailCall => {
                segments.push(Segment {
                    start,
                    end: index,
                    branch: None,
                });
                exit = Some(Exit::Return { inst: id });
            }
            AArch64Opcode::Brk => {
                segments.push(Segment {
                    start,
                    end: index,
                    branch: None,
                });
                exit = Some(Exit::Abort { inst: id });
            }
            AArch64Opcode::Br => {
                return Err(format!("block {} ends in an indirect branch", block.0));
            }
            _ => {
                if inst
                    .operands
                    .iter()
                    .any(|op| matches!(op, MachOperand::Block(_) | MachOperand::JumpTableIndex(_)))
                {
                    return Err(format!(
                        "block {} inst {} ({:?}) names a block or jump table",
                        block.0, id.0, inst.opcode
                    ));
                }
            }
        }
    }
    let exit = match exit {
        Some(exit) => exit,
        None => {
            segments.push(Segment {
                start,
                end: insts.len(),
                branch: None,
            });
            Exit::Goto(
                next.ok_or_else(|| format!("block {} falls off the end of the layout", block.0))?,
            )
        }
    };
    Ok(Shape { segments, exit })
}

/// Every block an unparsed block may continue at: each block operand, each
/// jump table it names, and its layout successor.
fn conservative_successors(
    func: &MachFunction,
    block: BlockId,
    next: Option<BlockId>,
) -> Vec<BlockId> {
    let mut out = Vec::new();
    for &id in &func.block(block).insts {
        for op in &func.inst(id).operands {
            match op {
                MachOperand::Block(b) => out.push(*b),
                MachOperand::JumpTableIndex(i) => {
                    if let Some(table) = func.jump_tables.get(*i as usize) {
                        out.extend(table.targets.iter().copied());
                    }
                }
                _ => {}
            }
        }
    }
    out.extend(next);
    out.sort_unstable();
    out.dedup();
    out
}

/// The instruction-derived CFG of one function.
pub(super) struct Cfg {
    pub(super) shapes: HashMap<BlockId, Shape>,
    /// Blocks in layout order.
    pub(super) order: Vec<BlockId>,
    /// Fallthrough successor of each laid-out block.
    next: HashMap<BlockId, Option<BlockId>>,
    pub(super) preds: HashMap<BlockId, Vec<BlockId>>,
    /// Successors of every block (conservative for unparsed blocks).
    pub(super) succs: HashMap<BlockId, Vec<BlockId>>,
    pub(super) reachable: HashSet<BlockId>,
    /// Blocks whose shape could not be read (fatal only inside a region).
    pub(super) unparsed: HashMap<BlockId, String>,
    /// Exception edges: the landing pads of each invoke block, from the
    /// function's EH call sites. They are in `succs` (so a landing pad is
    /// reachable and a changed one is a region head), and liveness treats
    /// everything live into a pad as live throughout its invoke block. A
    /// region may not contain an invoke block: its walk does not follow the
    /// exception edge.
    pub(super) eh_succs: HashMap<BlockId, Vec<BlockId>>,
}

impl Cfg {
    pub(super) fn build(func: &MachFunction) -> Self {
        let order: Vec<BlockId> = func
            .block_order
            .iter()
            .copied()
            .filter(|b| (b.0 as usize) < func.blocks.len())
            .collect();
        let mut next = HashMap::default();
        for (i, &b) in order.iter().enumerate() {
            next.insert(b, order.get(i + 1).copied());
        }
        let mut shapes = HashMap::default();
        let mut unparsed = HashMap::default();
        let mut succs: HashMap<BlockId, Vec<BlockId>> = HashMap::default();
        for &b in &order {
            let fall = next.get(&b).copied().flatten();
            match block_shape(func, b, fall) {
                Ok(shape) => {
                    succs.insert(b, shape.successors());
                    shapes.insert(b, shape);
                }
                Err(e) => {
                    succs.insert(b, conservative_successors(func, b, fall));
                    unparsed.insert(b, e);
                }
            }
        }
        let mut eh_succs: HashMap<BlockId, Vec<BlockId>> = HashMap::default();
        for site in &func.eh_metadata.call_sites {
            let Some(pad) = site.landing_pad_block else {
                continue;
            };
            let Some(list) = succs.get_mut(&site.call_block) else {
                continue;
            };
            if !list.contains(&pad) {
                list.push(pad);
            }
            let pads = eh_succs.entry(site.call_block).or_default();
            if !pads.contains(&pad) {
                pads.push(pad);
            }
        }
        let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::default();
        for &b in &order {
            for &s in &succs[&b] {
                let list = preds.entry(s).or_default();
                if !list.contains(&b) {
                    list.push(b);
                }
            }
        }
        let mut reachable = HashSet::default();
        let mut stack = vec![func.entry];
        while let Some(b) = stack.pop() {
            if !reachable.insert(b) {
                continue;
            }
            if let Some(list) = succs.get(&b) {
                stack.extend(list.iter().copied());
            }
        }
        Self {
            shapes,
            order,
            next,
            preds,
            succs,
            reachable,
            unparsed,
            eh_succs,
        }
    }

    pub(super) fn present(&self, b: BlockId) -> bool {
        self.next.contains_key(&b)
    }

    /// The successors of `b` (none for a block outside the layout).
    pub(super) fn successors(&self, b: BlockId) -> &[BlockId] {
        self.succs.get(&b).map_or(&[], Vec::as_slice)
    }
}

pub(super) fn inst_eq(a: &MachInst, b: &MachInst) -> bool {
    a.opcode == b.opcode
        && a.flags.bits() == b.flags.bits()
        && a.operands == b.operands
        && a.implicit_defs == b.implicit_defs
        && a.implicit_uses == b.implicit_uses
}

/// Whether `b` is the same block in both functions: the same instructions
/// and, when it can fall through, the same layout successor.
fn same_block(before: &MachFunction, bc: &Cfg, after: &MachFunction, ac: &Cfg, b: BlockId) -> bool {
    let (x, y) = (&before.block(b).insts, &after.block(b).insts);
    if x.len() != y.len()
        || !x
            .iter()
            .zip(y.iter())
            .all(|(&i, &j)| inst_eq(before.inst(i), after.inst(j)))
    {
        return false;
    }
    match (bc.shapes.get(&b), ac.shapes.get(&b)) {
        (Some(bs), Some(as_)) => bs.exit == as_.exit || !matches!(bs.exit, Exit::Goto(_)),
        // An unparsed block is the same only if it would fall through to
        // the same block.
        _ => bc.next.get(&b) == ac.next.get(&b),
    }
}

/// The bank (`true` for SIMD/FP) each virtual register id `blocks` name is
/// named in (a compared register is one the region reads or writes).
fn vreg_banks(funcs: [(&MachFunction, &Cfg); 2], blocks: &HashSet<BlockId>) -> Banks {
    let mut banks = Banks::default();
    for (func, cfg) in funcs {
        for &b in blocks {
            if !cfg.present(b) {
                continue;
            }
            for &id in &func.block(b).insts {
                for op in &func.inst(id).operands {
                    if let MachOperand::VReg(v) = op {
                        banks.insert(v.id, !matches!(v.class, RegClass::Gpr64 | RegClass::Gpr32));
                    }
                }
            }
        }
    }
    banks
}

/// A dense set of interesting locations and the liveness of each of them.
///
/// Liveness is computed only for the locations some code of interest (the
/// changed regions, both functions) reads or writes. Any other location is
/// neither read nor written there, so it holds its region-entry value at
/// every region exit in both functions and needs no comparison.
pub(super) struct Liveness {
    index: HashMap<Loc, usize>,
    locs: Vec<Loc>,
    live_in: HashMap<BlockId, Vec<u64>>,
}

impl Liveness {
    /// Backward dataflow over `cfg` (the input function's) for `interest`.
    ///
    /// A parsed block is transferred segment by segment: a conditional exit
    /// joins its target's live-in to what the rest of the block needs. An
    /// unparsed block reads every location of interest (its conservative
    /// successors keep the graph complete); a branch target outside the
    /// layout reads everything too.
    pub(super) fn compute(func: &MachFunction, cfg: &Cfg, interest: &[Loc]) -> Self {
        let mut index: HashMap<Loc, usize> = HashMap::default();
        let mut locs = Vec::with_capacity(interest.len());
        for &loc in interest {
            if let std::collections::hash_map::Entry::Vacant(slot) = index.entry(loc) {
                slot.insert(locs.len());
                locs.push(loc);
            }
        }
        let words = locs.len().div_ceil(64).max(1);
        let mut full = vec![0u64; words];
        for i in 0..locs.len() {
            full[i / 64] |= 1 << (i % 64);
        }
        let bit = |loc: Loc| index.get(&loc).map(|&i| (i / 64, 1u64 << (i % 64)));
        // Per instruction: (reads, writes) over the interest set, computed
        // once for every instruction of a parsed block.
        let mut inst_sets: HashMap<InstId, (Vec<u64>, Vec<u64>)> = HashMap::default();
        for &b in cfg.shapes.keys() {
            for &id in &func.block(b).insts {
                let mut reads = vec![0u64; words];
                let mut writes = vec![0u64; words];
                for_each_access(func.inst(id), |loc, write| {
                    if let Some((w, m)) = bit(loc) {
                        if write {
                            writes[w] |= m;
                        } else {
                            reads[w] |= m;
                        }
                    }
                });
                inst_sets.insert(id, (reads, writes));
            }
        }
        let mut preserved = vec![0u64; words];
        for loc in return_preserved_locs() {
            if let Some((w, m)) = bit(loc) {
                preserved[w] |= m;
            }
        }
        let mut live_in: HashMap<BlockId, Vec<u64>> = HashMap::default();
        for &b in cfg.unparsed.keys() {
            live_in.insert(b, full.clone());
        }
        let target_live = |live_in: &HashMap<BlockId, Vec<u64>>, t: BlockId| -> Vec<u64> {
            if cfg.present(t) {
                live_in
                    .get(&t)
                    .cloned()
                    .unwrap_or_else(|| vec![0u64; words])
            } else {
                full.clone()
            }
        };
        let mut changed = true;
        while changed {
            changed = false;
            for &b in cfg.order.iter().rev() {
                let Some(shape) = cfg.shapes.get(&b) else {
                    continue;
                };
                let insts = &func.block(b).insts;
                // What the final exit needs.
                let mut live = match &shape.exit {
                    Exit::Goto(t) => target_live(&live_in, *t),
                    Exit::Return { inst } => {
                        let mut v = preserved.clone();
                        for (o, r) in v.iter_mut().zip(&inst_sets[inst].0) {
                            *o |= r;
                        }
                        v
                    }
                    Exit::Abort { inst } => inst_sets[inst].0.clone(),
                };
                for segment in shape.segments.iter().rev() {
                    if let Some(taken) = segment.branch {
                        // The branch itself only reads.
                        let branch = insts[segment.end];
                        let t = target_live(&live_in, taken);
                        for ((o, x), r) in live.iter_mut().zip(&t).zip(&inst_sets[&branch].0) {
                            *o |= x | r;
                        }
                    }
                    for &id in insts[segment.start..segment.end].iter().rev() {
                        let (reads, writes) = &inst_sets[&id];
                        for ((o, r), w) in live.iter_mut().zip(reads).zip(writes) {
                            *o = (*o & !w) | r;
                        }
                    }
                }
                // An exception leaves the invoke block mid-way, at its call:
                // whatever a landing pad reads is live through the whole
                // block, whatever the block writes after the call.
                for &pad in cfg.eh_succs.get(&b).into_iter().flatten() {
                    let t = target_live(&live_in, pad);
                    for (o, x) in live.iter_mut().zip(&t) {
                        *o |= x;
                    }
                }
                let entry = live_in.entry(b).or_insert_with(|| vec![0u64; words]);
                if *entry != live {
                    *entry = live;
                    changed = true;
                }
            }
        }
        Self {
            index,
            locs,
            live_in,
        }
    }

    /// Whether `loc` (which must be of interest) is live into `block`.
    /// Unknown locations and blocks answer `true`.
    pub(super) fn is_live(&self, block: BlockId, loc: Loc) -> bool {
        let Some(&i) = self.index.get(&loc) else {
            return true;
        };
        self.live_in
            .get(&block)
            .is_none_or(|bits| bits[i / 64] & (1 << (i % 64)) != 0)
    }

    /// The locations of interest live into `block`, in interest order.
    pub(super) fn live_locs(&self, block: BlockId) -> Vec<Loc> {
        match self.live_in.get(&block) {
            None => self.locs.clone(),
            Some(bits) => self
                .locs
                .iter()
                .enumerate()
                .filter(|(i, _)| bits[i / 64] & (1 << (i % 64)) != 0)
                .map(|(_, loc)| *loc)
                .collect(),
        }
    }

    /// Whether `loc` is one of the locations this liveness was computed for.
    pub(super) fn tracks(&self, loc: Loc) -> bool {
        self.index.contains_key(&loc)
    }
}

/// Every location `blocks`' instructions read or write (both functions),
/// plus NZCV and, when a block returns, the preserved registers.
fn region_interest(funcs: [(&MachFunction, &Cfg); 2], blocks: &HashSet<BlockId>) -> Vec<Loc> {
    let mut seen: HashSet<Loc> = HashSet::default();
    let mut out = Vec::new();
    let mut add = |loc: Loc| {
        if seen.insert(loc) {
            out.push(loc);
        }
    };
    add(Loc::Flags);
    let mut returns = false;
    for (func, cfg) in funcs {
        for &b in blocks {
            if !cfg.present(b) {
                continue;
            }
            for &id in &func.block(b).insts {
                for_each_access(func.inst(id), |loc, _| add(loc));
            }
            if matches!(
                cfg.shapes.get(&b).map(|s| &s.exit),
                Some(Exit::Return { .. })
            ) {
                returns = true;
            }
        }
    }
    if returns {
        for loc in return_preserved_locs() {
            add(loc);
        }
    }
    out
}

/// One path end of a walk.
enum Leaf {
    Boundary { block: BlockId, state: State },
    Return { world: TermId, loads: Vec<TermId> },
    Abort { world: TermId, loads: Vec<TermId> },
}

impl Leaf {
    fn loads(&self) -> &[TermId] {
        match self {
            Leaf::Boundary { state, .. } => &state.loads,
            Leaf::Return { loads, .. } | Leaf::Abort { loads, .. } => loads,
        }
    }
}

/// A walk's decision tree.
enum Tree {
    Leaf(Leaf),
    Fork {
        cond: TermId,
        then: Box<Tree>,
        els: Box<Tree>,
    },
}

/// What a fold over a tree computes at each leaf.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Probe {
    /// Reached `block`?
    Reach(BlockId),
    /// Value of a location at `block`.
    Value(BlockId, Loc),
    /// Returned?
    Returned,
    /// World at return.
    ReturnWorld,
    /// Aborted?
    Aborted,
    /// World at abort.
    AbortWorld,
    /// Executed the load term?
    Loaded(TermId),
}

/// Which register bank each virtual register id is named in.
type Banks = HashMap<u32, bool>;

fn fold(arena: &mut TermArena, tree: &Tree, probe: Probe, banks: &Banks) -> TermId {
    match tree {
        Tree::Fork { cond, then, els } => {
            let t = fold(arena, then, probe, banks);
            let e = fold(arena, els, probe, banks);
            arena.ite(*cond, t, e)
        }
        Tree::Leaf(leaf) => match (probe, leaf) {
            (Probe::Reach(b), Leaf::Boundary { block, .. }) => arena.boolean(*block == b),
            (Probe::Value(b, loc), Leaf::Boundary { block, state }) if *block == b => {
                let fpr = match loc {
                    Loc::VReg(id) => banks.get(&id).copied().unwrap_or(false),
                    _ => false,
                };
                state.final_value(arena, loc, fpr)
            }
            (Probe::Returned, Leaf::Return { .. }) | (Probe::Aborted, Leaf::Abort { .. }) => {
                arena.tru()
            }
            (Probe::ReturnWorld, Leaf::Return { world, .. })
            | (Probe::AbortWorld, Leaf::Abort { world, .. }) => *world,
            (Probe::Loaded(l), leaf) => arena.boolean(leaf.loads().contains(&l)),
            (Probe::Reach(_) | Probe::Returned | Probe::Aborted, _) => arena.fals(),
            _ => arena.bottom(),
        },
    }
}

fn leaves<'t>(tree: &'t Tree, out: &mut Vec<&'t Leaf>) {
    match tree {
        Tree::Leaf(leaf) => out.push(leaf),
        Tree::Fork { then, els, .. } => {
            leaves(then, out);
            leaves(els, out);
        }
    }
}

/// Symbolic walker over one function.
struct Walker<'f> {
    func: &'f MachFunction,
    cfg: &'f Cfg,
    /// Blocks that exist only in this function.
    internal: &'f HashSet<BlockId>,
    leaves: usize,
    examined: u64,
    visited: BTreeSet<BlockId>,
}

impl Walker<'_> {
    fn walk(
        &mut self,
        arena: &mut TermArena,
        block: BlockId,
        state: State,
        path: &mut Vec<BlockId>,
    ) -> Result<Tree, String> {
        let shape = self
            .cfg
            .shapes
            .get(&block)
            .ok_or_else(|| match self.cfg.unparsed.get(&block) {
                Some(e) => e.clone(),
                None => format!("block {} is not laid out", block.0),
            })?
            .clone();
        self.visited.insert(block);
        self.walk_segments(arena, block, &shape, 0, state, path)
    }

    /// Execute `shape`'s segments from `index` on, forking at each
    /// conditional exit, then its final exit.
    fn walk_segments(
        &mut self,
        arena: &mut TermArena,
        block: BlockId,
        shape: &Shape,
        index: usize,
        mut state: State,
        path: &mut Vec<BlockId>,
    ) -> Result<Tree, String> {
        let insts = &self.func.block(block).insts;
        let Some(segment) = shape.segments.get(index).copied() else {
            return self.walk_exit(arena, &shape.exit, state, path);
        };
        for &id in &insts[segment.start..segment.end] {
            let inst = self.func.inst(id);
            self.examined += 1;
            Exec::new(arena, &mut state)
                .step(inst)
                .map_err(|Unsupported(e)| format!("inst {} {:?}: {e}", id.0, inst.opcode))?;
        }
        let Some(taken) = segment.branch else {
            return self.walk_segments(arena, block, shape, index + 1, state, path);
        };
        let branch = insts[segment.end];
        self.examined += 1;
        let cond = Exec::new(arena, &mut state)
            .branch_condition(self.func.inst(branch))
            .map_err(|Unsupported(e)| format!("branch inst {}: {e}", branch.0))?;
        match arena.as_bool(cond) {
            Some(true) => self.continue_at(arena, taken, state, path),
            Some(false) => self.walk_segments(arena, block, shape, index + 1, state, path),
            None => {
                let then = self.continue_at(arena, taken, state.clone(), path)?;
                let els = self.walk_segments(arena, block, shape, index + 1, state, path)?;
                Ok(Tree::Fork {
                    cond,
                    then: Box::new(then),
                    els: Box::new(els),
                })
            }
        }
    }

    fn walk_exit(
        &mut self,
        arena: &mut TermArena,
        exit: &Exit,
        mut state: State,
        path: &mut Vec<BlockId>,
    ) -> Result<Tree, String> {
        match *exit {
            Exit::Goto(target) => self.continue_at(arena, target, state, path),
            Exit::Return { inst } => {
                self.examined += 1;
                let mut exec = Exec::new(arena, &mut state);
                let world = exec
                    .return_effect(self.func.inst(inst), &return_preserved_locs())
                    .map_err(|Unsupported(e)| format!("return inst {}: {e}", inst.0))?;
                self.leaf()?;
                Ok(Tree::Leaf(Leaf::Return {
                    world,
                    loads: state.loads,
                }))
            }
            Exit::Abort { inst } => {
                self.examined += 1;
                Exec::new(arena, &mut state)
                    .step(self.func.inst(inst))
                    .map_err(|Unsupported(e)| format!("abort inst {}: {e}", inst.0))?;
                self.leaf()?;
                Ok(Tree::Leaf(Leaf::Abort {
                    world: state.world,
                    loads: state.loads,
                }))
            }
        }
    }

    fn leaf(&mut self) -> Result<(), String> {
        self.leaves += 1;
        if self.leaves > MAX_LEAVES {
            return Err(format!("more than {MAX_LEAVES} paths through the region"));
        }
        Ok(())
    }

    fn continue_at(
        &mut self,
        arena: &mut TermArena,
        target: BlockId,
        state: State,
        path: &mut Vec<BlockId>,
    ) -> Result<Tree, String> {
        if !self.internal.contains(&target) {
            self.leaf()?;
            return Ok(Tree::Leaf(Leaf::Boundary {
                block: target,
                state,
            }));
        }
        if path.contains(&target) {
            return Err(format!(
                "the changed region loops through block {}",
                target.0
            ));
        }
        if path.len() >= MAX_PATH_BLOCKS {
            return Err(format!("a path crosses more than {MAX_PATH_BLOCKS} blocks"));
        }
        path.push(target);
        let tree = self.walk(arena, target, state, path);
        path.pop();
        tree
    }
}

/// Function-level facts a region check assumes are unchanged.
fn metadata_change(before: &MachFunction, after: &MachFunction) -> Option<&'static str> {
    if before.entry != after.entry {
        return Some("the entry block changed");
    }
    if before.stack_slots != after.stack_slots {
        return Some("the stack slots changed");
    }
    if (!before.jump_tables.is_empty() || !after.jump_tables.is_empty())
        && format!("{:?}", before.jump_tables) != format!("{:?}", after.jump_tables)
    {
        return Some("the jump tables changed");
    }
    if !same_eh_metadata(before, after) {
        return Some("the exception-handling metadata changed");
    }
    None
}

/// Whether the two functions carry the same exception-handling metadata
/// (personality, landing pads, call sites and type table).
pub(super) fn same_eh_metadata(before: &MachFunction, after: &MachFunction) -> bool {
    // Exhaustive, so a new metadata field cannot be left out silently.
    let trust_cg_ir::function::ExceptionHandlingMetadata {
        personality,
        landing_pads,
        call_sites,
        call_site_bindings,
        eh_type_table,
    } = &before.eh_metadata;
    let a = &after.eh_metadata;
    *personality == a.personality
        && *landing_pads == a.landing_pads
        && *call_sites == a.call_sites
        && *call_site_bindings == a.call_site_bindings
        && *eh_type_table == a.eh_type_table
}

/// Outcome of a region check.
pub(super) struct RegionOutcome {
    pub(super) verdict: ValidationVerdict,
    pub(super) examined: u64,
}

/// Check every changed region of `after` against `before`.
pub(super) fn validate_regions(before: &MachFunction, after: &MachFunction) -> RegionOutcome {
    let mut examined = 0u64;
    let verdict = match check(before, after, &mut examined) {
        Ok(()) => ValidationVerdict::Validated,
        Err(reason) => ValidationVerdict::Unproved(reason),
    };
    RegionOutcome { verdict, examined }
}

fn check(before: &MachFunction, after: &MachFunction, examined: &mut u64) -> Result<(), String> {
    if let Some(change) = metadata_change(before, after) {
        return Err(change.to_string());
    }
    let bc = Cfg::build(before);
    let ac = Cfg::build(after);

    let mut all: BTreeSet<BlockId> = BTreeSet::new();
    all.extend(bc.order.iter().copied());
    all.extend(ac.order.iter().copied());
    let mut heads = Vec::new();
    let mut only_before: HashSet<BlockId> = HashSet::default();
    let mut only_after: HashSet<BlockId> = HashSet::default();
    for &b in &all {
        match (bc.present(b), ac.present(b)) {
            (true, true) => {
                if !same_block(before, &bc, after, &ac, b)
                    && (bc.reachable.contains(&b) || ac.reachable.contains(&b))
                {
                    heads.push(b);
                }
            }
            (true, false) => {
                only_before.insert(b);
            }
            (false, true) => {
                only_after.insert(b);
            }
            (false, false) => {}
        }
    }
    if heads.is_empty() {
        // Only blocks unreachable in both, or layout without a fallthrough
        // change, can differ: nothing executes differently.
        let stray = only_before
            .iter()
            .find(|b| bc.reachable.contains(b))
            .or_else(|| only_after.iter().find(|b| ac.reachable.contains(b)));
        return match stray {
            Some(b) => Err(format!("block {} changed outside any region", b.0)),
            None => Ok(()),
        };
    }

    let mut region_blocks: HashSet<BlockId> = heads.iter().copied().collect();
    region_blocks.extend(only_before.iter().copied());
    region_blocks.extend(only_after.iter().copied());
    let interest = region_interest([(before, &bc), (after, &ac)], &region_blocks);
    let live = Liveness::compute(before, &bc, &interest);
    let banks = vreg_banks([(before, &bc), (after, &ac)], &region_blocks);
    let mut covered_before: HashSet<BlockId> = HashSet::default();
    let mut covered_after: HashSet<BlockId> = HashSet::default();
    let mut arena = TermArena::new();
    for &head in &heads {
        let mut walkers = [
            Walker {
                func: before,
                cfg: &bc,
                internal: &only_before,
                leaves: 0,
                examined: 0,
                visited: BTreeSet::new(),
            },
            Walker {
                func: after,
                cfg: &ac,
                internal: &only_after,
                leaves: 0,
                examined: 0,
                visited: BTreeSet::new(),
            },
        ];
        let mut trees = Vec::with_capacity(2);
        for walker in &mut walkers {
            let state = State::new(&mut arena, head.0);
            let tree = walker
                .walk(&mut arena, head, state, &mut vec![head])
                .map_err(|e| format!("region at block {}: {e}", head.0))?;
            *examined += walker.examined;
            trees.push(tree);
        }
        for (walker, cfg) in walkers.iter().zip([&bc, &ac]) {
            if let Some(b) = std::iter::once(&head)
                .chain(walker.visited.iter())
                .find(|b| cfg.eh_succs.contains_key(b))
            {
                return Err(format!(
                    "region at block {}: block {} is an invoke block, whose exception edge \
                     the region walk does not follow",
                    head.0, b.0
                ));
            }
        }
        for (walker, (cfg, covered)) in walkers
            .iter()
            .zip([(&bc, &mut covered_before), (&ac, &mut covered_after)])
        {
            for &b in &walker.visited {
                if b == head {
                    continue;
                }
                if let Some(p) = cfg
                    .preds
                    .get(&b)
                    .into_iter()
                    .flatten()
                    .find(|p| **p != head && !walker.visited.contains(p))
                {
                    return Err(format!(
                        "block {} of the region at block {} is also entered from block {}",
                        b.0, head.0, p.0
                    ));
                }
                covered.insert(b);
            }
        }
        compare(&mut arena, head, &trees[0], &trees[1], &live, &banks)?;
    }
    for (only, cfg, covered) in [
        (&only_before, &bc, &covered_before),
        (&only_after, &ac, &covered_after),
    ] {
        if let Some(b) = only
            .iter()
            .find(|b| cfg.reachable.contains(b) && !covered.contains(b))
        {
            return Err(format!("block {} changed outside any region", b.0));
        }
    }
    Ok(())
}

fn render_loc(loc: Loc) -> String {
    format!("{loc:?}")
}

/// A term rendering short enough for a diagnostic line.
fn short(arena: &TermArena, t: TermId) -> String {
    let full = arena.render(t);
    if full.chars().count() <= 160 {
        return full;
    }
    let head: String = full.chars().take(160).collect();
    format!("{head}...")
}

fn compare(
    arena: &mut TermArena,
    head: BlockId,
    before: &Tree,
    after: &Tree,
    live: &Liveness,
    banks: &Banks,
) -> Result<(), String> {
    let mut targets: BTreeSet<BlockId> = BTreeSet::new();
    let mut leaf_list = Vec::new();
    leaves(before, &mut leaf_list);
    leaves(after, &mut leaf_list);
    for leaf in &leaf_list {
        if let Leaf::Boundary { block, .. } = leaf {
            targets.insert(*block);
        }
    }
    let check_inputs = |arena: &TermArena, term: TermId, what: &str| -> Result<(), String> {
        let mut stack = vec![term];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let Term::Atom(Atom::Input { loc, .. }) = arena.get(t)
                && *loc != Loc::World
                && (!live.tracks(*loc) || !live.is_live(head, *loc))
            {
                return Err(format!(
                    "region at block {}: {what} reads {loc:?}, which the liveness model says is \
                     dead into the head",
                    head.0
                ));
            }
            stack.extend(arena.children(t));
        }
        Ok(())
    };
    let same = |arena: &mut TermArena, probe: Probe, what: String| -> Result<(), String> {
        let b = fold(arena, before, probe, banks);
        let a = fold(arena, after, probe, banks);
        if a != b {
            return Err(format!(
                "region at block {}: {what} differs: input {} vs output {}",
                head.0,
                short(arena, b),
                short(arena, a)
            ));
        }
        check_inputs(arena, b, &what)
    };
    for &target in &targets {
        same(
            arena,
            Probe::Reach(target),
            format!("reaching block {}", target.0),
        )?;
        let mut locs = live.live_locs(target);
        locs.push(Loc::World);
        for loc in locs {
            same(
                arena,
                Probe::Value(target, loc),
                format!("{} entering block {}", render_loc(loc), target.0),
            )?;
        }
    }
    same(arena, Probe::Returned, "returning".to_string())?;
    same(arena, Probe::ReturnWorld, "the state at return".to_string())?;
    same(arena, Probe::Aborted, "aborting".to_string())?;
    same(arena, Probe::AbortWorld, "the state at abort".to_string())?;

    // Speculation: every load the output executes, it executes under the
    // input's condition for it, or the input executes it on every path.
    let mut after_leaves = Vec::new();
    leaves(after, &mut after_leaves);
    let mut loads: BTreeSet<TermId> = BTreeSet::new();
    for leaf in after_leaves {
        loads.extend(leaf.loads().iter().copied());
    }
    let tru = arena.tru();
    for load in loads {
        let a = fold(arena, after, Probe::Loaded(load), banks);
        let b = fold(arena, before, Probe::Loaded(load), banks);
        if a != b && b != tru {
            return Err(format!(
                "region at block {}: the output speculates the load {} (executed under {} \
                 instead of {})",
                head.0,
                short(arena, load),
                short(arena, a),
                short(arena, b)
            ));
        }
    }
    Ok(())
}

/// The value the branch's condition holds for "taken", for a conditional
/// branch whose operands are `[cc, target]`, `[reg, target]` or
/// `[reg, bit, target]`.
pub(crate) fn branch_condition_term(
    arena: &mut TermArena,
    inst: &MachInst,
    flags: TermId,
    reg: &mut dyn FnMut(&mut TermArena, &MachOperand) -> Result<TermId, Unsupported>,
) -> Result<TermId, Unsupported> {
    let width = |op: &MachOperand| -> Option<u8> {
        match op {
            MachOperand::VReg(v) => match v.class {
                RegClass::Gpr64 => Some(64),
                RegClass::Gpr32 => Some(32),
                _ => None,
            },
            MachOperand::PReg(p) => match p.encoding() {
                0..=30 => Some(64),
                32..=62 => Some(32),
                _ => None,
            },
            _ => None,
        }
    };
    let unsupported = || Unsupported(format!("{:?} operand shape", inst.opcode));
    match inst.opcode {
        AArch64Opcode::BCond | AArch64Opcode::Bcc => {
            let cc = inst
                .operands
                .first()
                .and_then(MachOperand::as_imm)
                .filter(|cc| (0..=15).contains(cc))
                .ok_or_else(unsupported)?;
            Ok(arena.cond(cc as u8, flags))
        }
        AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
            let op = inst.operands.first().ok_or_else(unsupported)?;
            let w = width(op).ok_or_else(unsupported)?;
            let v = reg(arena, op)?;
            let zero = arena.konst(0);
            let is_zero = arena.cmp(Cmp::Eq, w, v, zero);
            Ok(if inst.opcode == AArch64Opcode::Cbz {
                is_zero
            } else {
                arena.bool_not(is_zero)
            })
        }
        AArch64Opcode::Tbz | AArch64Opcode::Tbnz => {
            let op = inst.operands.first().ok_or_else(unsupported)?;
            let w = width(op).ok_or_else(unsupported)?;
            let bit = inst
                .operands
                .get(1)
                .and_then(MachOperand::as_imm)
                .filter(|b| (0..i64::from(w)).contains(b))
                .ok_or_else(unsupported)?;
            let v = reg(arena, op)?;
            let m = arena.konst(1u64 << bit);
            let masked = arena.and(w, v, m);
            let zero = arena.konst(0);
            let is_zero = arena.cmp(Cmp::Eq, w, masked, zero);
            Ok(if inst.opcode == AArch64Opcode::Tbz {
                is_zero
            } else {
                arena.bool_not(is_zero)
            })
        }
        _ => Err(unsupported()),
    }
}
