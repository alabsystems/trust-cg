// trust-cg-verify/post_ra_value_flow/engine.rs - the comparison
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The comparison of a specification function with an implementation.
//!
//! # Anchors and paths
//!
//! Block ids survive every post-allocation stage (new blocks are appended),
//! so a block laid out in both functions is an **anchor**: the same program
//! point in both. Every other laid-out block is *inserted* (the
//! implementation's critical-edge, relaxation and frame blocks) or
//! *removed* (a specification trampoline the implementation bypassed); a
//! path from an anchor through such blocks to the next anchor may contain
//! moves, pure operations and storage accesses but no effect.
//!
//! # Per anchor
//!
//! Both bodies are executed symbolically from the anchor's entry states.
//! Effects are compared one-for-one in order (same operation, same input
//! terms); matched effects give their results the same terms. Then the two
//! decision trees (the terminator branches, through inserted or removed
//! blocks) are explored jointly over their condition atoms: under every
//! assignment both must reach the same anchor or both return (equal return
//! values) or tail-call (equal effect).
//!
//! # Joins: inferring where each value lives
//!
//! The entry state of an anchor is computed from all incoming edge states.
//! A specification location live into the anchor whose value is the same
//! (entry-rooted) term on every edge keeps it; otherwise it becomes a block
//! leaf, shared by every live location with the same per-edge value vector.
//! An implementation location (register or storage cell) takes the leaf of
//! the specification location whose per-edge vector it matches exactly (at
//! the specification location's width); otherwise it keeps a common
//! entry-rooted term, or a 64-bit location that is on every edge a common
//! base plus a constant multiple of one 64-bit specification leaf's edge
//! value takes `base + k·leaf` (an induction pointer, as late post-index
//! formation leaves one), or it becomes unknown. This infers the
//! allocator's location relation instead of trusting it: a value lives
//! where the implementation provably holds it on every incoming path.
//!
//! The fixpoint starts optimistically (edges not yet computed impose
//! nothing) and an anchor is re-processed whenever its entry states change.
//! When it settles, every leaf and every inferred location is checked
//! against every incoming edge under the final states, so the relation is
//! inductive: each anchor's verdict was computed from its final entry
//! states. An anchor whose processing stops keeps its last contributions,
//! so a stop cannot make the fixpoint oscillate; any stop refuses, and an
//! accepted comparison's anchors all replaced theirs on their final run.

use std::collections::{BTreeMap, BTreeSet};

use std::rc::Rc;
use trust_cg_ir::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachOperand};

use super::model::{
    Event, Exec, Exec1, ExecStop, LOC_NZCV, LOC_SP, LOC_V0, LOC_X18, NUM_PHYS, Place, Reg, Side,
    SideCtx, State, inst_reads, inst_writes, is_branch_opcode, loc_bits, loc_name, operand_reg,
};
use super::term::{Affine, Aux, OpKey, OpTag, TermArena, TermId};
use super::{Stage, ViolationKind};

/// Site id of block-entry unknowns.
const ENTRY_SITE: u32 = u32::MAX;
/// Site id of a block's decision-exploration unknowns.
const EXIT_SITE: u32 = u32::MAX - 1;
/// Widths at which a location's per-edge values are matched.
const WIDTHS: [u16; 6] = [128, 64, 32, 16, 8, 4];
/// Bound on fixpoint work: anchor re-processings per anchor.
const MAX_VISITS_PER_ANCHOR: u32 = 64;
/// Bound on distinct condition atoms in one decision exploration.
const MAX_ATOMS: usize = 12;

/// A comparison that could not be completed, or a violation found.
#[derive(Clone)]
pub(crate) enum Stop {
    Violation(ViolationKind, String),
    Unmodeled(String),
}

impl From<ExecStop> for Stop {
    fn from(stop: ExecStop) -> Self {
        match stop {
            ExecStop::Unmodeled(why) => Stop::Unmodeled(why),
            ExecStop::Violation(kind, detail) => Stop::Violation(kind, detail),
        }
    }
}

/// Work counters reported with a verdict.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Work {
    pub(crate) anchors: u32,
    pub(crate) unreachable_anchors: u32,
    pub(crate) visits: u32,
    pub(crate) effects: u32,
    pub(crate) spec_insts: u32,
    pub(crate) impl_insts: u32,
    pub(crate) terms: u32,
}

// ---------------------------------------------------------------------------
// Block shapes
// ---------------------------------------------------------------------------

/// Where a branch goes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Target {
    Block(BlockId),
}

/// One terminator branch.
#[derive(Clone, Debug)]
enum Branch {
    /// `B.cond` / `CBZ` / `CBNZ` / `TBZ` / `TBNZ`.
    Cond { inst: InstId, target: Target },
    /// `B`.
    Goto(Target),
    /// `BR` through a jump table.
    Indirect { inst: InstId },
    /// `RET`.
    Return { inst: InstId },
    /// A tail call.
    TailCall { inst: InstId },
    /// An unconditional trap ended the body: control does not continue.
    Halt,
}

/// One item of a block body: an instruction, or a conditional branch that
/// leaves the block early (a switch's bounds check) and otherwise falls
/// through to the rest of the body.
#[derive(Clone, Copy, Debug)]
enum Item {
    Inst(InstId),
    CondExit {
        inst: InstId,
        target: Target,
    },
    /// A static stack-probe loop (an inserted self-loop that lowers SP by
    /// `step` bytes per iteration, counted down in X16), summarized.
    Probe {
        block: BlockId,
        step: i64,
    },
}

/// A block split into its body and its terminator branches (the maximal
/// suffix of branch instructions).
#[derive(Clone, Debug)]
struct Shape {
    body: Vec<Item>,
    term: Vec<Branch>,
}

/// One function under comparison, with its layout facts.
struct Fn<'a> {
    ctx: SideCtx<'a>,
    /// Layout position of each laid-out block.
    layout_pos: Vec<Option<usize>>,
    /// First laid-out block starting at an instruction-unit offset (blocks
    /// with no encoded instruction occupy no bytes and fall through to the
    /// next; see [`Comparison::impl_falls_through_to`]).
    block_at: HashMap<i64, BlockId>,
    /// Instruction-unit offset of each laid-out non-pseudo instruction.
    inst_offset: HashMap<InstId, i64>,
    /// The laid-out block of each instruction.
    inst_block: HashMap<InstId, BlockId>,
    /// Landing pad of each block with an exception-handling call site: a
    /// call in the block that unwinds continues there.
    landing: HashMap<BlockId, BlockId>,
    shapes: Vec<Option<Result<Rc<Shape>, Stop>>>,
}

impl<'a> Fn<'a> {
    fn new(ctx: SideCtx<'a>) -> Result<Self, Stop> {
        let func = ctx.func;
        let nblocks = func.blocks.len();
        let mut layout_pos = vec![None; nblocks];
        let mut block_at = HashMap::default();
        let mut inst_offset = HashMap::default();
        let mut inst_block = HashMap::default();
        let mut offset = 0i64;
        for (pos, &b) in func.block_order.iter().enumerate() {
            let Some(block) = func.blocks.get(b.0 as usize) else {
                return Err(Stop::Violation(
                    ViolationKind::Malformed,
                    format!("layout names block {} outside the arena", b.0),
                ));
            };
            if layout_pos[b.0 as usize].is_some() {
                return Err(Stop::Violation(
                    ViolationKind::Malformed,
                    format!("block {} is laid out twice", b.0),
                ));
            }
            layout_pos[b.0 as usize] = Some(pos);
            block_at.entry(offset).or_insert(b);
            for &id in &block.insts {
                let Some(inst) = func.insts.get(id.0 as usize) else {
                    return Err(Stop::Violation(
                        ViolationKind::Malformed,
                        format!("block {} names instruction {} outside the arena", b.0, id.0),
                    ));
                };
                inst_block.insert(id, b);
                if !inst.is_pseudo() {
                    inst_offset.insert(id, offset);
                    offset += 1;
                }
            }
        }
        let mut landing = HashMap::default();
        for site in &func.eh_metadata.call_sites {
            if let Some(pad) = site.landing_pad_block
                && landing
                    .insert(site.call_block, pad)
                    .is_some_and(|p| p != pad)
            {
                return Err(Stop::Unmodeled(format!(
                    "block {} has call sites with different landing pads",
                    site.call_block.0
                )));
            }
        }
        Ok(Self {
            ctx,
            layout_pos,
            block_at,
            inst_offset,
            inst_block,
            landing,
            shapes: vec![None; nblocks],
        })
    }

    fn func(&self) -> &'a MachFunction {
        self.ctx.func
    }

    fn laid_out(&self, b: BlockId) -> bool {
        self.layout_pos
            .get(b.0 as usize)
            .is_some_and(|p| p.is_some())
    }

    fn next_in_layout(&self, b: BlockId) -> Option<BlockId> {
        let pos = self.layout_pos.get(b.0 as usize).copied().flatten()?;
        self.func().block_order.get(pos + 1).copied()
    }

    fn shape(&mut self, b: BlockId) -> Result<Rc<Shape>, Stop> {
        if self.shapes[b.0 as usize].is_none() {
            let shape = self.parse(b).map(Rc::new);
            self.shapes[b.0 as usize] = Some(shape);
        }
        match self.shapes[b.0 as usize].as_ref() {
            Some(Ok(shape)) => Ok(Rc::clone(shape)),
            Some(Err(stop)) => Err(stop.clone()),
            None => unreachable!("shape computed above"),
        }
    }

    /// Resolve a branch target operand (symbolic or resolved immediate).
    fn target(&self, inst: InstId, op: Option<&MachOperand>) -> Result<Target, Stop> {
        match op {
            Some(MachOperand::Block(t)) => {
                if self.laid_out(*t) {
                    Ok(Target::Block(*t))
                } else {
                    Err(Stop::Violation(
                        ViolationKind::Structure,
                        format!(
                            "branch {} targets block {} that is not laid out",
                            inst.0, t.0
                        ),
                    ))
                }
            }
            Some(MachOperand::Imm(k)) => {
                let here = self.inst_offset.get(&inst).copied().ok_or_else(|| {
                    Stop::Unmodeled(format!("resolved branch {} has no layout offset", inst.0))
                })?;
                let dest = here + k;
                self.block_at
                    .get(&dest)
                    .copied()
                    .map(Target::Block)
                    .ok_or_else(|| {
                        Stop::Violation(
                            ViolationKind::Structure,
                            format!(
                                "resolved branch {} lands at instruction offset {dest}, not at a block start",
                                inst.0
                            ),
                        )
                    })
            }
            other => Err(Stop::Unmodeled(format!(
                "branch {} has an unmodeled target operand {other:?}",
                inst.0
            ))),
        }
    }

    fn parse(&self, b: BlockId) -> Result<Shape, Stop> {
        use AArch64Opcode::*;
        let func = self.func();
        let insts = &func.blocks[b.0 as usize].insts;
        let in_record = |id: &InstId| self.ctx.trap_records.contains_key(id);
        let is_term = |id: &InstId| {
            let op = func.inst(*id).opcode;
            (is_branch_opcode(op) && !in_record(id)) || matches!(op, Nop | AlignNop)
        };
        // The terminator group: the maximal suffix of branches (and NOPs).
        let mut split = insts.len();
        while split > 0 && is_term(&insts[split - 1]) {
            split -= 1;
        }
        // Leading NOPs of the suffix stay in the body.
        while split < insts.len() && matches!(func.inst(insts[split]).opcode, Nop | AlignNop) {
            split += 1;
        }
        let mut body = Vec::with_capacity(split);
        for &id in &insts[..split] {
            let inst = func.inst(id);
            if is_branch_opcode(inst.opcode) && !in_record(&id) {
                let target = match inst.opcode {
                    BCond | Bcc | Cbz | Cbnz => self.target(id, inst.operands.get(1))?,
                    Tbz | Tbnz => self.target(id, inst.operands.get(2))?,
                    other => {
                        return Err(Stop::Unmodeled(format!(
                            "block {} has {other:?} before the end of its body",
                            b.0
                        )));
                    }
                };
                body.push(Item::CondExit { inst: id, target });
            } else {
                body.push(Item::Inst(id));
            }
        }
        let mut term = Vec::new();
        for &id in &insts[split..] {
            let inst = func.inst(id);
            let ops = &inst.operands;
            let branch = match inst.opcode {
                Nop | AlignNop => continue,
                B => Branch::Goto(self.target(id, ops.first())?),
                BCond | Bcc | Cbz | Cbnz => Branch::Cond {
                    inst: id,
                    target: self.target(id, ops.get(1))?,
                },
                Tbz | Tbnz => Branch::Cond {
                    inst: id,
                    target: self.target(id, ops.get(2))?,
                },
                Br => Branch::Indirect { inst: id },
                Ret => Branch::Return { inst: id },
                TailCall => Branch::TailCall { inst: id },
                other => {
                    return Err(Stop::Unmodeled(format!(
                        "block {} has {other:?} after its first terminator branch",
                        b.0
                    )));
                }
            };
            term.push(branch);
        }
        if term.is_empty()
            && insts[..split]
                .last()
                .is_some_and(|id| is_unconditional_trap(func.inst(*id).opcode))
        {
            term.push(Branch::Halt);
        }
        Ok(Shape { body, term })
    }
}

// ---------------------------------------------------------------------------
// The comparison
// ---------------------------------------------------------------------------

/// Edge key: `(predecessor anchor, path id)`.
type EdgeKey = (u32, u32);

/// An outgoing edge of a processed anchor: its target, its key, and the
/// (specification, implementation) states it carries.
type OutEdge = (BlockId, EdgeKey, (State, State));

/// Leaf of one function's decision tree.
#[derive(Clone)]
enum Leaf {
    Anchor {
        target: BlockId,
        state: State,
        path: Vec<u32>,
    },
    /// A return or tail call (`tail`), judged at the leaf pair.
    Exit {
        inst: InstId,
        state: State,
        tail: bool,
    },
    /// An unconditional trap.
    Halt,
}

/// A cursor's next need.
enum Step {
    Leaf(Leaf),
    /// The decision needs the value of an atom (`arity` outcomes).
    Need(TermId, u32),
}

pub(crate) struct Comparison<'a> {
    pub(crate) arena: TermArena,
    spec: Fn<'a>,
    imp: Fn<'a>,
    anchor: Vec<bool>,
    rpo: Vec<BlockId>,
    rpo_index: HashMap<BlockId, usize>,
    live_in: HashMap<BlockId, Vec<Place>>,
    /// Specification values live out of each block or read by its
    /// terminators (sorted): what its decisions and edges carry.
    live_out: HashMap<BlockId, Vec<Place>>,
    /// Incoming edge states of each anchor.
    edges: HashMap<BlockId, BTreeMap<EdgeKey, (State, State)>>,
    /// Targets each anchor contributed edges to (for replacement).
    contributed: HashMap<BlockId, BTreeSet<BlockId>>,
    entry_states: HashMap<BlockId, (State, State)>,
    /// The latest verdict of each anchor.
    verdicts: HashMap<BlockId, Option<Stop>>,
    pub(crate) work: Work,
    /// Frame-storage obligations checked at the implementation's exits.
    callee_saved_exit_check: bool,
    /// The implementation's initial state (after any pre-entry path).
    impl_initial: Option<State>,
    spec_initial: Option<State>,
}

impl<'a> Comparison<'a> {
    pub(crate) fn new(
        spec: SideCtx<'a>,
        imp: SideCtx<'a>,
        stage: Stage,
        spec_initial_sp: Option<i64>,
    ) -> Result<Self, Stop> {
        for function in [spec.func, imp.func] {
            crate::aarch64_jump_table_address::validate_expansions(function)
                .map_err(Stop::Unmodeled)?;
        }
        let mut arena =
            TermArena::with_capacity(4 * (spec.func.insts.len() + imp.func.insts.len()) + 512);
        let spec = Fn::new(spec)?;
        let imp = Fn::new(imp)?;
        let nblocks = spec.func().blocks.len();
        let mut anchor = vec![false; nblocks.max(imp.func().blocks.len())];
        for &b in &spec.func().block_order {
            if imp.laid_out(b) {
                anchor[b.0 as usize] = true;
            }
        }
        let callee_saved_exit_check = matches!(stage, Stage::FrameLayout | Stage::Composed);
        let mut this = Self {
            spec_initial: None,
            impl_initial: None,
            arena: TermArena::default(),
            spec,
            imp,
            anchor,
            rpo: Vec::new(),
            rpo_index: HashMap::default(),
            live_in: HashMap::default(),
            live_out: HashMap::default(),
            edges: HashMap::default(),
            contributed: HashMap::default(),
            entry_states: HashMap::default(),
            verdicts: HashMap::default(),
            work: Work::default(),
            callee_saved_exit_check,
        };
        // Initial states: every physical location holds its entry value; SP
        // is the CFA (the specification's SP is the post-prologue SP when the
        // implementation has a frame the specification does not).
        let mut phys = Vec::with_capacity(NUM_PHYS);
        for loc in 0..NUM_PHYS as u16 {
            phys.push(arena.entry(loc, loc_bits(loc)));
        }
        let cfa = arena.cfa();
        let mut impl_phys = phys.clone();
        impl_phys[LOC_SP as usize] = cfa;
        let mut spec_phys = phys;
        spec_phys[LOC_SP as usize] = match spec_initial_sp {
            Some(offset) => arena.lin(cfa, offset),
            None => cfa,
        };
        this.arena = arena;
        this.spec_initial = Some(State::new(spec_phys));
        this.impl_initial = Some(State::new(impl_phys));
        Ok(this)
    }

    fn is_anchor(&self, b: BlockId) -> bool {
        self.anchor.get(b.0 as usize).copied().unwrap_or(false)
    }

    fn side(&mut self, side: Side) -> &mut Fn<'a> {
        match side {
            Side::Spec => &mut self.spec,
            Side::Impl => &mut self.imp,
        }
    }

    // -- setup -------------------------------------------------------------

    /// Successor anchors of anchor `b` in the specification, through
    /// removed blocks.
    fn spec_anchor_succs(&mut self, b: BlockId) -> Result<Vec<BlockId>, Stop> {
        let mut out = Vec::new();
        let mut seen = HashSet::default();
        let mut stack = vec![b];
        let mut first = true;
        while let Some(blk) = stack.pop() {
            if !first && self.is_anchor(blk) {
                if !out.contains(&blk) {
                    out.push(blk);
                }
                continue;
            }
            first = false;
            if !seen.insert(blk) {
                continue;
            }
            for t in self.block_targets(Side::Spec, blk)? {
                stack.push(t);
            }
        }
        out.sort();
        Ok(out)
    }

    /// Every block a block's terminator may transfer to.
    fn block_targets(&mut self, side: Side, b: BlockId) -> Result<Vec<BlockId>, Stop> {
        let shape = self.side(side).shape(b)?;
        let mut out = Vec::new();
        if let Some(&pad) = self.side(side).landing.get(&b) {
            out.push(pad);
        }
        for item in &shape.body {
            if let Item::CondExit {
                target: Target::Block(t),
                ..
            } = item
            {
                out.push(*t);
            }
        }
        let mut falls = true;
        for br in &shape.term {
            match br {
                Branch::Cond {
                    target: Target::Block(t),
                    ..
                } => out.push(*t),
                Branch::Goto(Target::Block(t)) => {
                    out.push(*t);
                    falls = false;
                }
                Branch::Indirect { inst } => {
                    let f = self.side(side).func();
                    let table = indirect_table(f, b, *inst)?;
                    out.extend(f.jump_tables[table].targets.iter().copied());
                    falls = false;
                }
                Branch::Return { .. } | Branch::TailCall { .. } | Branch::Halt => falls = false,
            }
            if !falls {
                break;
            }
        }
        if falls {
            match self.side(side).next_in_layout(b) {
                Some(next) => out.push(next),
                None => {
                    return Err(Stop::Unmodeled(format!(
                        "block {} falls off the end of the function",
                        b.0
                    )));
                }
            }
        }
        Ok(out)
    }

    fn setup(&mut self) -> Result<(), Stop> {
        let entry = self.spec.func().entry;
        if !self.is_anchor(entry) {
            return Err(Stop::Violation(
                ViolationKind::Structure,
                format!(
                    "the specification entry block {} is not laid out in the implementation",
                    entry.0
                ),
            ));
        }
        // Reverse postorder over the anchor graph.
        let mut visited = HashSet::default();
        let mut post = Vec::new();
        let mut stack: Vec<(BlockId, Vec<BlockId>, usize)> = Vec::new();
        visited.insert(entry);
        let succs = self.spec_anchor_succs(entry)?;
        stack.push((entry, succs, 0));
        while let Some((b, succs, i)) = stack.last_mut() {
            if *i < succs.len() {
                let s = succs[*i];
                *i += 1;
                if visited.insert(s) {
                    let ss = self.spec_anchor_succs(s)?;
                    stack.push((s, ss, 0));
                }
            } else {
                post.push(*b);
                stack.pop();
            }
        }
        post.reverse();
        self.rpo_index = post.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        self.rpo = post;
        self.work.anchors = self.rpo.len() as u32;
        self.work.unreachable_anchors = self
            .spec
            .func()
            .block_order
            .iter()
            .filter(|b| self.is_anchor(**b) && !self.rpo_index.contains_key(b))
            .count() as u32;
        self.compute_spec_liveness()?;
        Ok(())
    }

    /// Backward liveness over the specification's laid-out blocks, as
    /// bitsets over physical locations and virtual register ids.
    fn compute_spec_liveness(&mut self) -> Result<(), Stop> {
        let order: Vec<BlockId> = self.spec.func().block_order.clone();
        let index_of: HashMap<BlockId, usize> =
            order.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        let max_vreg = {
            let func = self.spec.func();
            let mut max = 0u32;
            for &b in &order {
                for &id in &func.blocks[b.0 as usize].insts {
                    for op in &func.inst(id).operands {
                        if let MachOperand::VReg(v) = op {
                            max = max.max(v.id + 1);
                        }
                    }
                }
            }
            max
        };
        let bits = NUM_PHYS + max_vreg as usize;
        let words = bits.div_ceil(64);
        let key = |p: Place| -> usize {
            match p {
                Place::Phys(l) => l as usize,
                Place::Virt(v) => NUM_PHYS + v as usize,
            }
        };
        let place = |k: usize| -> Place {
            if k < NUM_PHYS {
                Place::Phys(k as u16)
            } else {
                Place::Virt((k - NUM_PHYS) as u32)
            }
        };
        let set = |vec: &mut [u64], k: usize| vec[k / 64] |= 1u64 << (k % 64);
        let clear = |vec: &mut [u64], k: usize| vec[k / 64] &= !(1u64 << (k % 64));
        let n = order.len();
        let mut succs: Vec<Vec<usize>> = Vec::with_capacity(n);
        let mut gen_bits = vec![0u64; n * words];
        let mut kill_bits = vec![0u64; n * words];
        let mut term_reads: Vec<Vec<usize>> = Vec::with_capacity(n);
        for (bi, &b) in order.iter().enumerate() {
            let targets = match self.block_targets(Side::Spec, b) {
                Ok(t) => t,
                // An unreachable block's shape does not matter.
                Err(Stop::Unmodeled(_)) if !self.rpo_index.contains_key(&b) => Vec::new(),
                Err(e) => return Err(e),
            };
            succs.push(
                targets
                    .iter()
                    .filter_map(|t| index_of.get(t).copied())
                    .collect(),
            );
            let func = self.spec.func();
            let gen_b = &mut gen_bits[bi * words..(bi + 1) * words];
            let kill_b = &mut kill_bits[bi * words..(bi + 1) * words];
            let mut terms = Vec::new();
            let insts = &func.blocks[b.0 as usize].insts;
            let mut in_terminators = true;
            for &id in insts.iter().rev() {
                let inst = func.inst(id);
                if in_terminators && is_branch_opcode(inst.opcode) {
                    inst_reads(inst, |p| terms.push(key(p)));
                } else {
                    in_terminators = false;
                }
                let mut written = Vec::new();
                inst_writes(inst, |p| written.push(p));
                if inst.opcode == AArch64Opcode::Copy
                    || inst.opcode == AArch64Opcode::Nop
                    || is_branch_opcode(inst.opcode)
                {
                    // Moves and NOPs: their implicit lists are metadata.
                    written.clear();
                    if let Some(Some(Ok(Reg::View(v)))) = inst.operands.first().map(operand_reg)
                        && inst.opcode == AArch64Opcode::Copy
                    {
                        written.push(v.place);
                    }
                }
                for p in written {
                    let k = key(p);
                    clear(gen_b, k);
                    set(kill_b, k);
                }
                if inst.opcode == AArch64Opcode::Copy {
                    if let Some(Some(Ok(Reg::View(v)))) = inst.operands.get(1).map(operand_reg) {
                        set(gen_b, key(v.place));
                    }
                } else if inst.opcode != AArch64Opcode::Nop {
                    inst_reads(inst, |p| set(gen_b, key(p)));
                }
            }
            term_reads.push(terms);
        }
        let mut live_in = vec![0u64; n * words];
        let mut out = vec![0u64; words];
        let mut changed = true;
        let mut rounds = 0;
        while changed {
            changed = false;
            rounds += 1;
            if rounds > 4 * n + 16 {
                return Err(Stop::Unmodeled(
                    "specification liveness did not converge".into(),
                ));
            }
            for bi in (0..n).rev() {
                out.iter_mut().for_each(|w| *w = 0);
                for &si in &succs[bi] {
                    for (w, &l) in out.iter_mut().zip(&live_in[si * words..(si + 1) * words]) {
                        *w |= l;
                    }
                }
                let base = bi * words;
                for k in 0..words {
                    let new = gen_bits[base + k] | (out[k] & !kill_bits[base + k]);
                    if new != live_in[base + k] {
                        live_in[base + k] = new;
                        changed = true;
                    }
                }
            }
        }
        // SP is live everywhere: every call reads it (stack-passed
        // arguments sit at the SP the callee is entered with) and, before
        // frame lowering, so does every exit.
        let sp = key(Place::Phys(LOC_SP));
        for bi in 0..n {
            set(&mut live_in[bi * words..(bi + 1) * words], sp);
        }
        let collect = |vec: &[u64]| -> Vec<Place> {
            let mut places = Vec::new();
            for (wi, &w) in vec.iter().enumerate() {
                let mut w = w;
                while w != 0 {
                    let bit = w.trailing_zeros() as usize;
                    places.push(place(wi * 64 + bit));
                    w &= w - 1;
                }
            }
            places
        };
        for (bi, &b) in order.iter().enumerate() {
            out.iter_mut().for_each(|w| *w = 0);
            for &si in &succs[bi] {
                for (w, &l) in out.iter_mut().zip(&live_in[si * words..(si + 1) * words]) {
                    *w |= l;
                }
            }
            for &k in &term_reads[bi] {
                set(&mut out, k);
            }
            // `collect` yields places in bitset order: physical locations
            // first, then virtual registers by id — `Place`'s order.
            self.live_out.insert(b, collect(&out));
            self.live_in
                .insert(b, collect(&live_in[bi * words..(bi + 1) * words]));
        }
        Ok(())
    }

    // -- the fixpoint ------------------------------------------------------

    pub(crate) fn run(&mut self) -> Result<(), Stop> {
        self.setup()?;
        let entry = self.spec.func().entry;
        // The implementation's pre-entry path (blocks frame lowering put in
        // front of the specification's entry).
        let impl_entry = self.imp.func().entry;
        let impl_initial = self.impl_initial.take().expect("initial state");
        let impl_start = if impl_entry == entry {
            impl_initial
        } else {
            self.pre_entry(impl_entry, impl_initial, entry)?
        };
        let spec_start = self.spec_initial.take().expect("initial state");
        self.edges
            .entry(entry)
            .or_default()
            .insert((u32::MAX, 0), (spec_start, impl_start));

        let mut worklist: BTreeSet<usize> = BTreeSet::new();
        worklist.insert(self.rpo_index[&entry]);
        let mut visits: HashMap<BlockId, u32> = HashMap::default();
        while let Some(index) = worklist.pop_first() {
            let b = self.rpo[index];
            let count = visits.entry(b).or_insert(0);
            *count += 1;
            if *count > MAX_VISITS_PER_ANCHOR {
                return Err(Stop::Unmodeled(format!(
                    "no fixpoint at block {} after {MAX_VISITS_PER_ANCHOR} visits",
                    b.0
                )));
            }
            self.work.visits += 1;
            let states = self.join(b);
            if self.entry_states.get(&b) == Some(&states) && self.verdicts.contains_key(&b) {
                continue;
            }
            self.entry_states.insert(b, states.clone());
            let (verdict, succ_edges) = match self.process(b, states) {
                Ok(edges) => (None, edges),
                Err(stop) => (Some(stop), Vec::new()),
            };
            let failed = verdict.is_some();
            self.verdicts.insert(b, verdict);
            if failed {
                // The anchor's stop already decides the comparison (any stop
                // refuses). Its last successful contributions stay: dropping
                // them would hand its successors fewer edges, re-validate
                // the anchor under the narrower entry state and oscillate
                // instead of reporting the stop. An anchor whose final
                // processing succeeds has replaced them, so an accepted
                // comparison never rests on a stale edge.
                continue;
            }
            // Replace this anchor's contributions.
            if let Some(old) = self.contributed.remove(&b) {
                for t in old {
                    if let Some(map) = self.edges.get_mut(&t) {
                        map.retain(|k, _| k.0 != b.0);
                    }
                    if let Some(&i) = self.rpo_index.get(&t) {
                        worklist.insert(i);
                    }
                }
            }
            let mut targets = BTreeSet::new();
            for (target, key, states) in succ_edges {
                self.edges.entry(target).or_default().insert(key, states);
                targets.insert(target);
                if let Some(&i) = self.rpo_index.get(&target) {
                    worklist.insert(i);
                }
            }
            self.contributed.insert(b, targets);
        }
        self.work.terms = self.arena.len() as u32;
        // The verdict: the first stop in layout order.
        for &b in &self.rpo {
            if let Some(Some(stop)) = self.verdicts.remove(&b) {
                return Err(stop);
            }
        }
        Ok(())
    }

    /// Execute the implementation's straight-line pre-entry blocks.
    fn pre_entry(
        &mut self,
        start: BlockId,
        mut state: State,
        entry: BlockId,
    ) -> Result<State, Stop> {
        let mut b = start;
        let mut seen = HashSet::default();
        loop {
            if b == entry {
                return Ok(state);
            }
            if self.is_anchor(b) || !seen.insert(b) {
                return Err(Stop::Violation(
                    ViolationKind::Structure,
                    format!(
                        "the implementation's entry path reaches block {} before the entry block {}",
                        b.0, entry.0
                    ),
                ));
            }
            let shape = self.imp.shape(b)?;
            self.exec_transparent(Side::Impl, b, &shape.body, &mut state)?;
            let targets = self.block_targets(Side::Impl, b)?;
            match targets.as_slice() {
                [next] if shape.term.iter().all(|t| matches!(t, Branch::Goto(_))) => b = *next,
                _ => {
                    return Err(Stop::Unmodeled(format!(
                        "the implementation's pre-entry block {} branches conditionally",
                        b.0
                    )));
                }
            }
        }
    }

    /// The entry states of anchor `b` from its incoming edges.
    fn join(&mut self, b: BlockId) -> (State, State) {
        let edge_map = self.edges.remove(&b).unwrap_or_default();
        let states = self.join_edges(b, &edge_map);
        self.edges.insert(b, edge_map);
        states
    }

    fn join_edges(
        &mut self,
        b: BlockId,
        edge_map: &BTreeMap<EdgeKey, (State, State)>,
    ) -> (State, State) {
        let edges: Vec<&(State, State)> = edge_map.values().collect();
        let side_spec = Side::Spec as u8;
        let side_impl = Side::Impl as u8;

        // One incoming edge: both states continue unchanged (a term valid at
        // the predecessor's exit is valid here), the specification's pruned
        // to the values live into `b`.
        if let [(s, i)] = edges.as_slice() {
            let mut spec = s.clone();
            let live = self.live_in.get(&b);
            spec.virt
                .retain(|v, _| live.is_some_and(|l| l.binary_search(&Place::Virt(*v)).is_ok()));
            spec.written = (0..NUM_PHYS as u16).map(loc_bits).collect();
            let mut imp = i.clone();
            imp.written = (0..NUM_PHYS as u16).map(loc_bits).collect();
            return (spec, imp);
        }

        let live = self.live_in.get(&b).cloned().unwrap_or_default();

        // Specification locations: live registers, then every storage cell
        // present on all edges. Each gets a common entry-rooted term or a
        // leaf shared with every location of the same per-edge vector.
        enum SpecLoc {
            Place(Place),
            Cell((TermId, i64), u16),
        }
        let mut locs: Vec<(SpecLoc, Option<Vec<TermId>>)> = live
            .iter()
            .map(|&p| {
                let vec: Option<Vec<TermId>> = edges
                    .iter()
                    .map(|(s, _)| match p {
                        Place::Phys(l) => Some(s.phys[l as usize]),
                        Place::Virt(v) => s.virt.get(&v).copied(),
                    })
                    .collect();
                (SpecLoc::Place(p), vec)
            })
            .collect();
        if !edges.is_empty() {
            let keys: BTreeSet<(TermId, i64)> = edges
                .iter()
                .flat_map(|(s, _)| s.cells.keys().copied())
                .collect();
            for key in keys {
                let cells: Option<Vec<_>> = edges
                    .iter()
                    .map(|(s, _)| s.cells.get(&key).copied())
                    .collect();
                let Some(cells) = cells else { continue };
                let bytes = cells[0].bytes;
                if cells.iter().any(|c| c.bytes != bytes) {
                    continue;
                }
                let vec = cells.iter().map(|c| c.value).collect();
                locs.push((SpecLoc::Cell(key, bytes), Some(vec)));
            }
        }
        let loc_width: Vec<u16> = locs
            .iter()
            .map(|(_, vec)| {
                vec.as_ref().map_or(0, |v| {
                    v.iter().map(|&t| self.arena.bits(t)).max().unwrap_or(0)
                })
            })
            .collect();
        // Widest first, so a narrower location can reuse a wider leaf.
        let mut order: Vec<usize> = (0..locs.len()).collect();
        order.sort_by(|&x, &y| loc_width[y].cmp(&loc_width[x]));
        let mut widths: Vec<u16> = order
            .iter()
            .map(|&k| loc_width[k])
            .filter(|&w| w > 0)
            .collect();
        widths.dedup();
        let mut table = EntryTable::default();
        // The 64-bit specification leaves of this join with their per-edge
        // values (candidates for an implementation induction relation).
        let mut leaf_vecs: Vec<(TermId, Vec<TermId>)> = Vec::new();
        let mut spec_phys = Vec::with_capacity(NUM_PHYS);
        for loc in 0..NUM_PHYS as u16 {
            spec_phys.push(self.arena.unknown(
                side_spec,
                b.0,
                ENTRY_SITE,
                u64::from(loc),
                loc_bits(loc),
            ));
        }
        let mut spec = State::new(spec_phys);
        for index in order {
            let (loc, vec) = &locs[index];
            let value = match vec {
                None => {
                    let SpecLoc::Place(place) = loc else { continue };
                    let bits = match place {
                        Place::Phys(l) => loc_bits(*l),
                        Place::Virt(_) => 64,
                    };
                    self.arena.unknown(
                        side_spec,
                        b.0,
                        ENTRY_SITE,
                        0x8000_0000_0000_0000 | place_key(*place),
                        bits,
                    )
                }
                Some(vec) if vec.is_empty() => continue,
                Some(vec) => {
                    let w = vec.iter().map(|&t| self.arena.bits(t)).max().unwrap_or(0);
                    let vec: Vec<TermId> = vec.iter().map(|&t| self.arena.resize(w, t)).collect();
                    // A value common to every edge and valid everywhere
                    // stays, before any leaf whose low bits share the
                    // vector is reused: the implementation side keeps such
                    // a value too (`impl_join_value`), so both decide on
                    // the same term. (Taking the low half of a wider
                    // location's leaf instead is true but loses the
                    // constant the implementation still has.)
                    let common = vec[0];
                    if vec.iter().all(|&t| t == common)
                        && self.arena.rooted(common)
                        && !self.arena.is_unknown(common)
                    {
                        if table.lookup(&mut self.arena, w, &vec).is_none() {
                            table.insert(&mut self.arena, &widths, w, vec, common);
                        }
                        common
                    } else if let Some(t) = table.lookup(&mut self.arena, w, &vec) {
                        t
                    } else {
                        let value = self.arena.leaf(b.0, index as u32, w);
                        if w == 64 {
                            leaf_vecs.push((value, vec.clone()));
                        }
                        table.insert(&mut self.arena, &widths, w, vec, value);
                        value
                    }
                }
            };
            match loc {
                SpecLoc::Place(Place::Phys(l)) => spec.phys[*l as usize] = value,
                SpecLoc::Place(Place::Virt(v)) => {
                    spec.virt.insert(*v, value);
                }
                SpecLoc::Cell(key, bytes) => {
                    spec.cells.insert(
                        *key,
                        super::model::Cell {
                            value,
                            bytes: *bytes,
                        },
                    );
                }
            }
        }

        let leaves: Vec<LeafSteps> = leaf_vecs
            .into_iter()
            .map(|(leaf, vec)| {
                let forms: Vec<Affine> = vec.iter().map(|&t| self.arena.affine(t)).collect();
                let step = (1..forms.len()).find_map(|e| {
                    let ds = forms[e].minus_scaled(&forms[0], 1);
                    (!ds.atoms.is_empty() || ds.constant != 0).then_some((e, ds))
                });
                LeafSteps { leaf, forms, step }
            })
            .collect();

        if trace_enabled() {
            for (index, (loc, vec)) in locs.iter().enumerate() {
                let name = match loc {
                    SpecLoc::Place(Place::Phys(l)) => loc_name(*l),
                    SpecLoc::Place(Place::Virt(v)) => format!("v{v}"),
                    SpecLoc::Cell(k, _) => format!("cell{:?}", k),
                };
                let rendered: Vec<String> = vec
                    .iter()
                    .flatten()
                    .map(|&t| self.arena.render(t))
                    .collect();
                eprintln!("[vf-trace] bb{} spec #{index} {name}: {rendered:?}", b.0);
            }
            for loc in 0..NUM_PHYS as u16 {
                let rendered: Vec<String> = edges
                    .iter()
                    .map(|(_, i)| self.arena.render(i.phys[loc as usize]))
                    .collect();
                eprintln!("[vf-trace] bb{} impl {}: {rendered:?}", b.0, loc_name(loc));
            }
        }

        // Implementation: every register and every storage cell present on
        // all edges, matched against the specification's vectors.
        let mut impl_phys = Vec::with_capacity(NUM_PHYS);
        for loc in 0..NUM_PHYS as u16 {
            let vec: Vec<TermId> = edges.iter().map(|(_, i)| i.phys[loc as usize]).collect();
            let v = self.impl_join_value(
                b,
                &vec,
                loc_bits(loc),
                u64::from(loc),
                (&table, &widths, &leaves),
                side_impl,
            );
            impl_phys.push(v);
        }
        let mut imp = State::new(impl_phys);
        // The stack below `touched_low` is untouched on every path.
        spec.touched_low = edges.iter().map(|(s, _)| s.touched_low).min().unwrap_or(0);
        imp.touched_low = edges.iter().map(|(_, i)| i.touched_low).min().unwrap_or(0);
        if !edges.is_empty() {
            let keys: BTreeSet<(TermId, i64)> = edges
                .iter()
                .flat_map(|(_, i)| i.cells.keys().copied())
                .collect();
            for key in keys {
                let cells: Option<Vec<_>> = edges
                    .iter()
                    .map(|(_, i)| i.cells.get(&key).copied())
                    .collect();
                let Some(cells) = cells else { continue };
                let bytes = cells[0].bytes;
                if cells.iter().any(|c| c.bytes != bytes) {
                    continue;
                }
                let vec: Vec<TermId> = cells.iter().map(|c| c.value).collect();
                let slot = 0x4000_0000_0000_0000 ^ (u64::from(key.0.0) << 24) ^ (key.1 as u64);
                let v = self.impl_join_value(
                    b,
                    &vec,
                    bytes * 8,
                    slot,
                    (&table, &widths, &leaves),
                    side_impl,
                );
                imp.cells
                    .insert(key, super::model::Cell { value: v, bytes });
            }
        }
        (spec, imp)
    }

    fn impl_join_value(
        &mut self,
        b: BlockId,
        vec: &[TermId],
        bits: u16,
        slot: u64,
        (table, widths, leaves): (&EntryTable, &[u16], &[LeafSteps]),
        side: u8,
    ) -> TermId {
        if vec.is_empty() {
            return self.arena.unknown(side, b.0, ENTRY_SITE, slot, bits);
        }
        // A value common to every edge and valid everywhere stays (a
        // specification location with the same vector got the same value).
        let first = vec[0];
        if vec.iter().all(|&t| t == first) && self.arena.rooted(first) {
            return first;
        }
        // An edge value the implementation alone produced (an unknown)
        // matches no specification vector at any width.
        if vec.iter().any(|&t| self.arena.is_unknown(t)) {
            return self.arena.unknown(side, b.0, ENTRY_SITE, slot, bits);
        }
        for &w in widths.iter().filter(|&&w| w <= bits) {
            if let Some(t) = table.lookup(&mut self.arena, w, vec) {
                return if w == bits {
                    t
                } else {
                    self.arena.widen_keyed(t, bits, side, b.0, ENTRY_SITE, slot)
                };
            }
        }
        // The widest low part every edge agrees on (the callee-saved low
        // halves of V8-V15 across a call).
        for &w in WIDTHS.iter().filter(|&&w| w < bits) {
            let low = self.arena.trunc(w, first);
            if self.arena.is_unknown(low) {
                continue;
            }
            let agree = vec.iter().all(|&t| self.arena.trunc(w, t) == low);
            if agree && self.arena.rooted(low) {
                return self
                    .arena
                    .widen_keyed(low, bits, side, b.0, ENTRY_SITE, slot);
            }
        }
        if bits == 64
            && let Some(t) = induction_value(&mut self.arena, vec, table, leaves)
        {
            return t;
        }
        self.arena.unknown(side, b.0, ENTRY_SITE, slot, bits)
    }

    // -- one anchor --------------------------------------------------------

    /// Execute a body that must contain no effect and no early exit (an
    /// inserted or removed block on a path between anchors).
    fn exec_transparent(
        &mut self,
        side: Side,
        b: BlockId,
        body: &[Item],
        state: &mut State,
    ) -> Result<(), Stop> {
        let (arena, f) = match side {
            Side::Spec => (&mut self.arena, &self.spec),
            Side::Impl => (&mut self.arena, &self.imp),
        };
        let who = match side {
            Side::Spec => "removed specification",
            Side::Impl => "inserted implementation",
        };
        for (site, item) in body.iter().enumerate() {
            let id = match *item {
                Item::Inst(id) => id,
                Item::CondExit { inst, .. } => {
                    return Err(Stop::Unmodeled(format!(
                        "{who} block {} has an early conditional exit (instruction {})",
                        b.0, inst.0
                    )));
                }
                Item::Probe { .. } => {
                    return Err(Stop::Unmodeled(format!(
                        "{who} block {} holds a nested probe loop",
                        b.0
                    )));
                }
            };
            let mut ex = Exec1 {
                arena,
                ctx: &f.ctx,
                block: b.0,
                site: site as u32,
            };
            match ex.exec(state, id)? {
                Exec::Applied => {}
                Exec::Event(e) | Exec::Pair(e, _) => {
                    let inst = f.ctx.func.inst(e.inst);
                    return Err(Stop::Violation(
                        ViolationKind::EffectMismatch,
                        format!(
                            "{who} block {} on a path between blocks performs an effect: {:?} {:?}",
                            b.0, inst.opcode, inst.operands
                        ),
                    ));
                }
            }
            check_reserved(side, &f.ctx, id)?;
        }
        Ok(())
    }
}

/// X18 is the Darwin platform register: the implementation never writes it.
fn check_reserved(side: Side, ctx: &SideCtx<'_>, id: InstId) -> Result<(), Stop> {
    if side != Side::Impl || !ctx.reserved_x18 {
        return Ok(());
    }
    let func = ctx.func;
    let inst = func.inst(id);
    let mut writes_x18 = false;
    inst_writes(inst, |p| writes_x18 |= p == Place::Phys(LOC_X18));
    let call = matches!(
        inst.opcode,
        AArch64Opcode::Bl | AArch64Opcode::BL | AArch64Opcode::Blr | AArch64Opcode::BLR
    );
    if writes_x18 && !call {
        return Err(Stop::Violation(
            ViolationKind::ReservedRegister,
            format!(
                "the implementation writes the reserved platform register x18: {:?} {:?}",
                inst.opcode, inst.operands
            ),
        ));
    }
    Ok(())
}

/// The next thing one function's body does.
enum Next {
    Event(Box<Event>),
    CondExit { inst: InstId, target: Target },
    End,
}

/// Where a decision walk starts.
#[derive(Clone, Copy)]
enum Start {
    /// At the terminators of a block whose body already ran.
    AfterBody(BlockId),
    /// Entering a block (its body runs first).
    Enter(BlockId),
}

impl Comparison<'_> {
    /// Advance one function's body to its next effect or early exit.
    fn next_item(
        &mut self,
        side: Side,
        b: BlockId,
        body: &[Item],
        pos: &mut usize,
        state: &mut State,
        pending: &mut Option<Box<Event>>,
    ) -> Result<Next, Stop> {
        if let Some(e) = pending.take() {
            return Ok(Next::Event(e));
        }
        while *pos < body.len() {
            let id = match body[*pos] {
                Item::Inst(id) => id,
                Item::CondExit { inst, target } => {
                    *pos += 1;
                    return Ok(Next::CondExit { inst, target });
                }
                Item::Probe { block, step } => {
                    *pos += 1;
                    self.apply_probe(side, block, step, state)?;
                    continue;
                }
            };
            let site = *pos as u32;
            let f = match side {
                Side::Spec => &self.spec,
                Side::Impl => &self.imp,
            };
            let mut ex = Exec1 {
                arena: &mut self.arena,
                ctx: &f.ctx,
                block: b.0,
                site,
            };
            let result = ex.exec(state, id)?;
            check_reserved(side, &f.ctx, id)?;
            match side {
                Side::Spec => self.work.spec_insts += 1,
                Side::Impl => self.work.impl_insts += 1,
            }
            match result {
                Exec::Applied => *pos += 1,
                Exec::Pair(first, second) => {
                    *pos += 1;
                    *pending = Some(second);
                    return Ok(Next::Event(first));
                }
                Exec::Event(e) => {
                    let span = e.span.max(1);
                    // A recorded expansion must be contiguous in the body.
                    if span > 1 {
                        let rec = &f.ctx.func.trap_expansions[f.ctx.trap_records[&id].0];
                        let contiguous = body.get(*pos..*pos + span).is_some_and(|items| {
                            items
                                .iter()
                                .zip(&rec.insts)
                                .all(|(item, want)| matches!(item, Item::Inst(id) if id == want))
                        });
                        if !contiguous {
                            return Err(Stop::Violation(
                                ViolationKind::Structure,
                                format!(
                                    "trap expansion of {:?} at block {} is not contiguous in its block",
                                    rec.carrier.opcode, b.0
                                ),
                            ));
                        }
                    }
                    *pos += span;
                    return Ok(Next::Event(e));
                }
            }
        }
        Ok(Next::End)
    }

    fn describe(&self, side: Side, id: InstId) -> String {
        let f = match side {
            Side::Spec => &self.spec,
            Side::Impl => &self.imp,
        };
        let inst = f.ctx.func.inst(id);
        format!("{:?} {:?}", inst.opcode, inst.operands)
    }

    fn compare_events(
        &mut self,
        b: BlockId,
        ordinal: u32,
        se: &Event,
        ie: &Event,
    ) -> Result<(), Stop> {
        let same_shape = se.key == ie.key
            && se.args.len() == ie.args.len()
            && se.outputs.len() == ie.outputs.len()
            && se
                .outputs
                .iter()
                .zip(&ie.outputs)
                .all(|(a, c)| a.bits == c.bits)
            && se.flags_out == ie.flags_out;
        if !same_shape {
            return Err(Stop::Violation(
                ViolationKind::EffectMismatch,
                format!(
                    "block {} effect #{ordinal} differs: specification {} vs implementation {}",
                    b.0,
                    self.describe(Side::Spec, se.inst),
                    self.describe(Side::Impl, ie.inst),
                ),
            ));
        }
        for (i, (&sa, &ia)) in se.args.iter().zip(&ie.args).enumerate() {
            // Judge each argument at the width the specification wrote it.
            let (sa, ia) = match se.arg_widths.get(i) {
                Some(&w) if w < self.arena.bits(sa) => {
                    (self.arena.trunc(w, sa), self.arena.trunc(w, ia))
                }
                _ => (sa, ia),
            };
            if sa != ia {
                let (ds, di) = self.arena.first_difference(sa, ia);
                return Err(Stop::Violation(
                    ViolationKind::ValueMismatch,
                    format!(
                        "block {} effect #{ordinal} ({}) input {i}: the specification computes {} but the implementation {}; they first differ at {} vs {} (implementation {})",
                        b.0,
                        self.describe(Side::Spec, se.inst),
                        self.arena.render(sa),
                        self.arena.render(ia),
                        self.arena.render(ds),
                        self.arena.render(di),
                        self.describe(Side::Impl, ie.inst),
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Process anchor `b` from its entry states: compare its effects and
    /// decisions, and return its outgoing edges.
    fn process(
        &mut self,
        b: BlockId,
        (mut s, mut i): (State, State),
    ) -> Result<Vec<OutEdge>, Stop> {
        let s_shape = self.spec.shape(b)?;
        let (i_body, i_end) = self.impl_chain(b)?;
        let i_shape = Shape {
            body: i_body,
            term: Vec::new(),
        };
        let (mut sp, mut ip) = (0usize, 0usize);
        let mut ordinal = 0u32;
        let mut out = Vec::new();
        let mut seen: HashMap<(Vec<u32>, Vec<u32>, u32), u32> = HashMap::default();
        let mut exits = 0u32;
        let (mut s_pending, mut i_pending) = (None, None);
        let mut s_next: Option<Next> = None;
        loop {
            let se = match s_next.take() {
                Some(next) => next,
                None => self.next_item(
                    Side::Spec,
                    b,
                    &s_shape.body,
                    &mut sp,
                    &mut s,
                    &mut s_pending,
                )?,
            };
            let ie = self.next_item(
                Side::Impl,
                b,
                &i_shape.body,
                &mut ip,
                &mut i,
                &mut i_pending,
            )?;
            // An early exit only the implementation has, whose condition is
            // decided not taken (the stack protector's compare of the canary
            // with the guard), changes nothing.
            if let Next::CondExit { inst, .. } = &ie
                && !matches!(se, Next::CondExit { .. })
                && self.never_taken(Side::Impl, b, *inst, &i)?
            {
                s_next = Some(se);
                continue;
            }
            match (se, ie) {
                (Next::End, Next::End) => break,
                (Next::Event(se), Next::Event(ie)) => {
                    self.compare_events(b, ordinal, &se, &ie)?;
                    self.work.effects += 1;
                    if se.clobber == super::model::Clobber::Call {
                        self.unwind_edges(b, ordinal, &se, &ie, &s, &i, &mut out, &mut seen)?;
                    }
                    let site = ordinal;
                    for (side, state, e) in [(Side::Spec, &mut s, &se), (Side::Impl, &mut i, &ie)] {
                        let f = match side {
                            Side::Spec => &self.spec,
                            Side::Impl => &self.imp,
                        };
                        let mut ex = Exec1 {
                            arena: &mut self.arena,
                            ctx: &f.ctx,
                            block: b.0,
                            site: 0x8000_0000 | site,
                        };
                        ex.apply_event(state, e, ordinal);
                    }
                    ordinal += 1;
                }
                (
                    Next::CondExit {
                        inst: si,
                        target: Target::Block(st),
                    },
                    Next::CondExit {
                        inst: ii,
                        target: Target::Block(it),
                    },
                ) => {
                    let (sa, sneg) = self.cond_atom(Side::Spec, b, si, &s)?;
                    let (ia, ineg) = self.cond_atom(Side::Impl, b, ii, &i)?;
                    if sa != ia || sneg != ineg {
                        return Err(Stop::Violation(
                            ViolationKind::ControlMismatch,
                            format!(
                                "block {}: early exit tests {} in the specification ({}) but {} in the implementation ({})",
                                b.0,
                                self.arena.render(sa),
                                self.describe(Side::Spec, si),
                                self.arena.render(ia),
                                self.describe(Side::Impl, ii),
                            ),
                        ));
                    }
                    let mut pairs = Vec::new();
                    self.explore(
                        b,
                        (Start::Enter(st), &s),
                        (Start::Enter(it), &i),
                        &mut Vec::new(),
                        &mut pairs,
                    )?;
                    self.collect_pairs(b, exits, pairs, &mut out, &mut seen)?;
                    exits += 1;
                }
                (Next::Event(se), _) => {
                    return Err(Stop::Violation(
                        ViolationKind::EffectMismatch,
                        format!(
                            "block {} effect #{ordinal} ({}) is missing from the implementation",
                            b.0,
                            self.describe(Side::Spec, se.inst)
                        ),
                    ));
                }
                (_, Next::Event(ie)) => {
                    return Err(Stop::Violation(
                        ViolationKind::EffectMismatch,
                        format!(
                            "block {} effect #{ordinal} ({}) is not in the specification",
                            b.0,
                            self.describe(Side::Impl, ie.inst)
                        ),
                    ));
                }
                _ => {
                    return Err(Stop::Violation(
                        ViolationKind::ControlMismatch,
                        format!(
                            "block {}: an early conditional exit in one function has no counterpart in the other",
                            b.0
                        ),
                    ));
                }
            }
        }
        // The terminators. Only values live out of the block (or read by
        // its terminators) travel further.
        if let Some(keep) = self.live_out.get(&b) {
            s.virt
                .retain(|v, _| keep.binary_search(&Place::Virt(*v)).is_ok());
        }
        let mut pairs = Vec::new();
        self.explore(
            b,
            (Start::AfterBody(b), &s),
            (i_end, &i),
            &mut Vec::new(),
            &mut pairs,
        )?;
        self.collect_pairs(b, exits, pairs, &mut out, &mut seen)?;
        Ok(out)
    }

    /// The exceptional edge of a matched call: when the block holding either
    /// call has a landing pad, both must, and both continue there with the
    /// state after the call's clobbers and the unwinder's X0/X1.
    #[allow(clippy::too_many_arguments)]
    fn unwind_edges(
        &mut self,
        b: BlockId,
        ordinal: u32,
        se: &Event,
        ie: &Event,
        s: &State,
        i: &State,
        out: &mut Vec<OutEdge>,
        seen: &mut HashMap<(Vec<u32>, Vec<u32>, u32), u32>,
    ) -> Result<(), Stop> {
        let pad_of = |f: &Fn<'_>, id: InstId| {
            f.inst_block
                .get(&id)
                .and_then(|blk| f.landing.get(blk))
                .copied()
        };
        let (sp, ip) = (pad_of(&self.spec, se.inst), pad_of(&self.imp, ie.inst));
        let (sp, ip) = match (sp, ip) {
            (None, None) => return Ok(()),
            (Some(sp), Some(ip)) => (sp, ip),
            _ => {
                return Err(Stop::Violation(
                    ViolationKind::Structure,
                    format!(
                        "block {} effect #{ordinal}: only one function's call has a landing pad",
                        b.0
                    ),
                ));
            }
        };
        let mut states = [s.clone(), i.clone()];
        for (side, state) in [Side::Spec, Side::Impl].into_iter().zip(states.iter_mut()) {
            let f = match side {
                Side::Spec => &self.spec,
                Side::Impl => &self.imp,
            };
            let mut ex = Exec1 {
                arena: &mut self.arena,
                ctx: &f.ctx,
                block: b.0,
                site: 0x4000_0000 | ordinal,
            };
            ex.apply_unwind(state, ordinal);
        }
        let [s_unwind, i_unwind] = states;
        let mut pairs = Vec::new();
        self.explore(
            b,
            (Start::Enter(sp), &s_unwind),
            (Start::Enter(ip), &i_unwind),
            &mut Vec::new(),
            &mut pairs,
        )?;
        self.collect_pairs(b, 0x8000_0000 | ordinal, pairs, out, seen)
    }

    /// Judge the leaf pairs of one decision exploration and turn the anchor
    /// pairs into outgoing edges.
    fn collect_pairs(
        &mut self,
        b: BlockId,
        exit: u32,
        pairs: Vec<(Leaf, Leaf)>,
        out: &mut Vec<OutEdge>,
        seen: &mut HashMap<(Vec<u32>, Vec<u32>, u32), u32>,
    ) -> Result<(), Stop> {
        for (sl, il) in pairs {
            match (sl, il) {
                (
                    Leaf::Anchor {
                        target: st,
                        state: ss,
                        path: sp,
                    },
                    Leaf::Anchor {
                        target: it,
                        state: is,
                        path: ip,
                    },
                ) => {
                    // The two targets are one program point of the
                    // implementation when the blocks between them do
                    // nothing there; the edge goes to the specification's.
                    if st != it
                        && !self.impl_falls_through_to(it, st)
                        && !self.impl_falls_through_to(st, it)
                    {
                        return Err(Stop::Violation(
                            ViolationKind::ControlMismatch,
                            format!(
                                "block {}: under the same conditions the specification continues at block {} and the implementation at block {}",
                                b.0, st.0, it.0
                            ),
                        ));
                    }
                    let next = seen.len() as u32;
                    let id = *seen.entry((sp, ip, exit)).or_insert(next);
                    out.push((st, (b.0, id), (ss, is)));
                }
                (
                    Leaf::Exit {
                        inst: sinst,
                        state: sstate,
                        tail: st,
                    },
                    Leaf::Exit {
                        inst: iinst,
                        state: istate,
                        tail: it,
                    },
                ) => {
                    if st != it {
                        return Err(Stop::Violation(
                            ViolationKind::ControlMismatch,
                            format!(
                                "block {}: one function returns where the other tail-calls",
                                b.0
                            ),
                        ));
                    }
                    // Both exits are judged at the specification's ABI sinks.
                    let sinks: Vec<trust_cg_ir::PReg> =
                        self.spec.func().inst(sinst).implicit_uses.to_vec();
                    let se = self.exit_event(Side::Spec, b, sinst, &sstate, st, &sinks)?;
                    let ie = self.exit_event(Side::Impl, b, iinst, &istate, it, &sinks)?;
                    self.compare_events(b, u32::MAX, &se, &ie)?;
                    self.work.effects += 1;
                    if self.callee_saved_exit_check {
                        self.check_exit_obligations(b, &istate)?;
                    }
                }
                (Leaf::Halt, Leaf::Halt) => {}
                (Leaf::Halt, _) | (_, Leaf::Halt) => {
                    return Err(Stop::Violation(
                        ViolationKind::ControlMismatch,
                        format!(
                            "block {}: one function traps where the other continues",
                            b.0
                        ),
                    ));
                }
                (Leaf::Anchor { target, .. }, Leaf::Exit { .. }) => {
                    return Err(Stop::Violation(
                        ViolationKind::ControlMismatch,
                        format!(
                            "block {}: the specification continues at block {} where the implementation leaves the function",
                            b.0, target.0
                        ),
                    ));
                }
                (Leaf::Exit { .. }, Leaf::Anchor { target, .. }) => {
                    return Err(Stop::Violation(
                        ViolationKind::ControlMismatch,
                        format!(
                            "block {}: the implementation continues at block {} where the specification leaves the function",
                            b.0, target.0
                        ),
                    ));
                }
            }
        }
        Ok(())
    }

    /// Whether entering the implementation's block `from` reaches `to`
    /// with nothing executed on the way: every block from `from` up to `to`
    /// in layout holds only no-op pseudo instructions (`NOP` markers of
    /// deleted copies, alignment padding) and no terminator, so it falls
    /// through to the next (a resolved branch to an empty block's address
    /// is a branch to the block laid out after it, which starts at the same
    /// address).
    fn impl_falls_through_to(&self, from: BlockId, to: BlockId) -> bool {
        let func = self.imp.func();
        let mut b = from;
        for _ in 0..func.block_order.len() {
            if b == to {
                return true;
            }
            let Some(block) = func.blocks.get(b.0 as usize) else {
                return false;
            };
            let no_op = block.insts.iter().all(|&id| {
                func.insts.get(id.0 as usize).is_some_and(|inst| {
                    matches!(inst.opcode, AArch64Opcode::Nop | AArch64Opcode::AlignNop)
                })
            });
            if !no_op {
                return false;
            }
            match self.imp.next_in_layout(b) {
                Some(next) => b = next,
                None => return false,
            }
        }
        false
    }

    /// At an implementation exit after frame lowering: SP is the CFA again,
    /// X19-X29, the return address and the low halves of V8-V15 hold their
    /// entry values.
    fn check_exit_obligations(&mut self, b: BlockId, state: &State) -> Result<(), Stop> {
        let cfa = self.arena.cfa();
        if state.phys[LOC_SP as usize] != cfa {
            return Err(Stop::Violation(
                ViolationKind::FrameMismatch,
                format!(
                    "block {}: SP at the exit is {}, not the entry SP",
                    b.0,
                    self.arena.render(state.phys[LOC_SP as usize])
                ),
            ));
        }
        for loc in (19u16..=30).chain(LOC_V0 + 8..LOC_V0 + 16) {
            let entry = self.arena.entry(loc, loc_bits(loc));
            let (have, want) = if loc >= LOC_V0 {
                let h = self.arena.trunc(64, state.phys[loc as usize]);
                (h, self.arena.trunc(64, entry))
            } else {
                (state.phys[loc as usize], entry)
            };
            if have != want {
                return Err(Stop::Violation(
                    ViolationKind::FrameMismatch,
                    format!(
                        "block {}: {} at the exit holds {}, not its value on entry",
                        b.0,
                        loc_name(loc),
                        self.arena.render(have)
                    ),
                ));
            }
        }
        Ok(())
    }

    // -- decisions ---------------------------------------------------------

    /// Explore both functions' decision trees jointly from the given starts,
    /// branching on every condition atom either one needs.
    fn explore(
        &mut self,
        b: BlockId,
        spec: (Start, &State),
        imp: (Start, &State),
        assumptions: &mut Vec<(TermId, u32)>,
        out: &mut Vec<(Leaf, Leaf)>,
    ) -> Result<(), Stop> {
        let sl = self.advance(Side::Spec, b, spec.0, spec.1.clone(), assumptions)?;
        let il = self.advance(Side::Impl, b, imp.0, imp.1.clone(), assumptions)?;
        let need = match (&sl, &il) {
            (Step::Need(a, n), _) | (_, Step::Need(a, n)) => Some((*a, *n)),
            _ => None,
        };
        if let Some((atom, arity)) = need {
            if assumptions.len() >= MAX_ATOMS {
                return Err(Stop::Unmodeled(format!(
                    "block {}: more than {MAX_ATOMS} branch conditions in one decision",
                    b.0
                )));
            }
            for v in 0..arity {
                assumptions.push((atom, v));
                self.explore(b, spec, imp, assumptions, out)?;
                assumptions.pop();
            }
            return Ok(());
        }
        match (sl, il) {
            (Step::Leaf(sl), Step::Leaf(il)) => out.push((sl, il)),
            _ => unreachable!("needs handled above"),
        }
        Ok(())
    }

    /// Walk one function's decision tree from `start` under `assumptions`,
    /// through inserted or removed blocks, to the next anchor or exit.
    fn advance(
        &mut self,
        side: Side,
        anchor: BlockId,
        start: Start,
        mut state: State,
        assumptions: &[(TermId, u32)],
    ) -> Result<Step, Stop> {
        let (mut b, mut run_body) = match start {
            Start::AfterBody(b) => (b, false),
            Start::Enter(t) => {
                if self.is_anchor(t) {
                    return Ok(Step::Leaf(Leaf::Anchor {
                        target: t,
                        state,
                        path: Vec::new(),
                    }));
                }
                (t, true)
            }
        };
        let mut path: Vec<u32> = Vec::new();
        if run_body {
            path.push(b.0);
        }
        loop {
            if run_body && let Some((step, exit)) = self.probe_loop(side, b)? {
                self.apply_probe(side, b, step, &mut state)?;
                if self.is_anchor(exit) {
                    return Ok(Step::Leaf(Leaf::Anchor {
                        target: exit,
                        state,
                        path,
                    }));
                }
                if path.contains(&exit.0) || path.len() > 64 {
                    return Err(Stop::Unmodeled(format!(
                        "a loop through inserted or removed blocks after block {}",
                        anchor.0
                    )));
                }
                path.push(exit.0);
                b = exit;
                continue;
            }
            let shape = self.side(side).shape(b)?;
            if run_body {
                self.exec_transparent(side, b, &shape.body, &mut state)?;
            }
            run_body = true;
            let mut next: Option<BlockId> = None;
            for br in &shape.term {
                match br {
                    Branch::Cond {
                        inst,
                        target: Target::Block(t),
                    } => {
                        let (atom, negated) = self.cond_atom(side, b, *inst, &state)?;
                        let value = match self.arena.const_value(atom) {
                            // A decided condition (a compare of equal values).
                            Some(v) => v as u32,
                            None => match assumptions.iter().find(|(a, _)| *a == atom) {
                                None => return Ok(Step::Need(atom, 2)),
                                Some(&(_, v)) => v,
                            },
                        };
                        let holds = (value == 1) != negated;
                        if holds {
                            next = Some(*t);
                            break;
                        }
                    }
                    Branch::Goto(Target::Block(t)) => {
                        next = Some(*t);
                        break;
                    }
                    Branch::Indirect { inst } => {
                        let func = self.side(side).func();
                        let table = indirect_table(func, b, *inst)?;
                        let targets = func.jump_tables[table].targets.clone();
                        let atom = self.indirect_atom(side, b, *inst, &state, table)?;
                        match assumptions.iter().find(|(a, _)| *a == atom) {
                            None => return Ok(Step::Need(atom, targets.len() as u32)),
                            Some(&(_, v)) => match targets.get(v as usize) {
                                Some(t) => {
                                    next = Some(*t);
                                    break;
                                }
                                None => {
                                    return Err(Stop::Violation(
                                        ViolationKind::ControlMismatch,
                                        format!("block {}: jump tables of different lengths", b.0),
                                    ));
                                }
                            },
                        }
                    }
                    Branch::Return { inst } | Branch::TailCall { inst } => {
                        let tail = matches!(br, Branch::TailCall { .. });
                        return Ok(Step::Leaf(Leaf::Exit {
                            inst: *inst,
                            state,
                            tail,
                        }));
                    }
                    Branch::Halt => return Ok(Step::Leaf(Leaf::Halt)),
                }
            }
            let t = match next {
                Some(t) => t,
                None => match self.side(side).next_in_layout(b) {
                    Some(t) => t,
                    None => {
                        return Err(Stop::Unmodeled(format!(
                            "block {} falls off the end of the function",
                            b.0
                        )));
                    }
                },
            };
            if self.is_anchor(t) {
                return Ok(Step::Leaf(Leaf::Anchor {
                    target: t,
                    state,
                    path,
                }));
            }
            if path.contains(&t.0) || path.len() > 64 {
                return Err(Stop::Unmodeled(format!(
                    "a loop through inserted or removed blocks after block {}",
                    anchor.0
                )));
            }
            path.push(t.0);
            b = t;
        }
    }

    /// The implementation's body for anchor `b`: `b`'s body, continued
    /// through inserted blocks the implementation reaches unconditionally
    /// (frame lowering's split of a block around a stack-probe loop), and
    /// the block whose terminators end it.
    fn impl_chain(&mut self, b: BlockId) -> Result<(Vec<Item>, Start), Stop> {
        let shape = self.imp.shape(b)?;
        let mut body = shape.body.clone();
        let mut last = b;
        let mut seen = HashSet::default();
        seen.insert(b);
        loop {
            let shape = self.imp.shape(last)?;
            let next = match shape.term.as_slice() {
                [] => self.imp.next_in_layout(last),
                [Branch::Goto(Target::Block(t))] => Some(*t),
                _ => None,
            };
            let Some(t) = next else { break };
            if self.is_anchor(t) || !seen.insert(t) {
                break;
            }
            if let Some((step, exit)) = self.probe_loop(Side::Impl, t)? {
                body.push(Item::Probe { block: t, step });
                if self.is_anchor(exit) || !seen.insert(exit) {
                    // The summarized loop exits to `exit`: the decision walk
                    // continues there.
                    return Ok((body, Start::Enter(exit)));
                }
                let exit_shape = self.imp.shape(exit)?;
                body.extend(exit_shape.body.iter().copied());
                last = exit;
                continue;
            }
            let t_shape = self.imp.shape(t)?;
            body.extend(t_shape.body.iter().copied());
            last = t;
        }
        Ok((body, Start::AfterBody(last)))
    }

    /// `Some((step, exit))` when `b` is a static stack-probe loop of `side`:
    /// `SUB SP, SP, #a` (once or more), `STR XZR, [SP]`, `SUBS X16, X16, #1`,
    /// `B.NE b`, falling through to `exit`.
    fn probe_loop(&mut self, side: Side, b: BlockId) -> Result<Option<(i64, BlockId)>, Stop> {
        use AArch64Opcode::*;
        let f = self.side(side);
        let func = f.func();
        let insts: Vec<InstId> = func.blocks[b.0 as usize]
            .insts
            .iter()
            .copied()
            .filter(|id| !matches!(func.inst(*id).opcode, Nop | AlignNop))
            .collect();
        let n = insts.len();
        if n < 4 {
            return Ok(None);
        }
        let sp = |op: &MachOperand| {
            matches!(op, MachOperand::Special(trust_cg_ir::SpecialReg::SP))
                || matches!(op, MachOperand::PReg(p) if p.encoding() == 31)
        };
        let x16 = |op: &MachOperand| matches!(op, MachOperand::PReg(p) if p.encoding() == 16);
        let mut step = 0i64;
        for &id in &insts[..n - 3] {
            let inst = func.inst(id);
            match (inst.opcode, inst.operands.as_slice()) {
                (SubRI, [d, s, MachOperand::Imm(a)]) if sp(d) && sp(s) && *a > 0 => step += a,
                _ => return Ok(None),
            }
        }
        let store = func.inst(insts[n - 3]);
        let is_probe_store = store.opcode == StrRI
            && matches!(
                store.operands.as_slice(),
                [MachOperand::PReg(z), base]
                    | [MachOperand::PReg(z), base, MachOperand::Imm(0)]
                    if z.encoding() == 160 && sp(base)
            )
            || store.opcode == StrRI
                && matches!(
                    store.operands.as_slice(),
                    [MachOperand::PReg(z), MachOperand::MemOp { base, offset: 0 }]
                        if z.encoding() == 160 && base.encoding() == 31
                );
        let count = func.inst(insts[n - 2]);
        let is_count = count.opcode == SubsRI
            && matches!(
                count.operands.as_slice(),
                [d, s, MachOperand::Imm(1)] if x16(d) && x16(s)
            );
        let branch = insts[n - 1];
        let back = func.inst(branch);
        let is_back = back.opcode == BCond
            && back.operands.first() == Some(&MachOperand::Imm(1))
            && f.target(branch, back.operands.get(1))? == Target::Block(b);
        if !(is_probe_store && is_count && is_back) || step == 0 {
            return Ok(None);
        }
        let Some(exit) = f.next_in_layout(b) else {
            return Ok(None);
        };
        Ok(Some((step, exit)))
    }

    /// The effect of a probe loop on `state`: X16 (a known positive count)
    /// iterations lower SP by `step` each; X16 ends zero; NZCV is unknown.
    fn apply_probe(
        &mut self,
        side: Side,
        b: BlockId,
        step: i64,
        state: &mut State,
    ) -> Result<(), Stop> {
        let count = state.phys[16];
        let Some(n) = self.arena.const_value(count) else {
            return Err(Stop::Unmodeled(format!(
                "the probe loop at block {} has no constant iteration count",
                b.0
            )));
        };
        let n = i64::try_from(n).ok().filter(|n| *n >= 1).ok_or_else(|| {
            Stop::Unmodeled(format!("the probe loop at block {} runs {n} times", b.0))
        })?;
        let sp = state.phys[LOC_SP as usize];
        // The probes write zero at each lowered SP; the highest at `SP -
        // step`. Like an inline probe, the loop may only write memory no
        // earlier write touched (frame lowering runs it in the prologue,
        // over the frame it is allocating).
        if self.side(side).ctx.frame_storage.is_some() {
            let (base, old) = self.arena.split_lin(sp);
            let fresh = matches!(self.arena.get(base), super::term::Term::Cfa)
                && old.saturating_sub(step).saturating_add(8) <= state.touched_low;
            if !fresh {
                return Err(Stop::Violation(
                    ViolationKind::FrameMismatch,
                    format!(
                        "the stack-probe loop at block {} writes below {} over memory an earlier write may have touched (nothing is untouched at or above CFA{:+})",
                        b.0,
                        self.arena.render(sp),
                        state.touched_low
                    ),
                ));
            }
        }
        state.phys[LOC_SP as usize] = self.arena.lin(sp, -(step * n));
        state.phys[16] = self.arena.constant(64, 0);
        state.phys[LOC_NZCV as usize] = self.arena.unknown(
            side as u8,
            b.0,
            EXIT_SITE,
            u64::from(LOC_NZCV),
            loc_bits(LOC_NZCV),
        );
        // The probes wrote zero below the old SP: no cell there survives.
        let cfa = self.arena.cfa();
        let (base, offset) = self.arena.split_lin(state.phys[LOC_SP as usize]);
        if base == cfa {
            super::model::Exec1::invalidate(state, base, offset, step.saturating_mul(n));
            state.touched_low = state.touched_low.min(offset);
        }
        Ok(())
    }

    /// The condition atom a conditional branch tests, and whether the branch
    /// is taken when the atom is false (`B.NE`, `CBNZ`, `TBNZ`).
    fn cond_atom(
        &mut self,
        side: Side,
        b: BlockId,
        id: InstId,
        state: &State,
    ) -> Result<(TermId, bool), Stop> {
        use AArch64Opcode::*;
        let func = self.side(side).func();
        let inst = func.inst(id);
        let ops = inst.operands.clone();
        let opcode = inst.opcode;
        let reg_term = |this: &mut Self, op: Option<&MachOperand>| -> Result<TermId, Stop> {
            match op.and_then(operand_reg) {
                Some(Ok(Reg::View(v))) => {
                    let f = match side {
                        Side::Spec => &this.spec,
                        Side::Impl => &this.imp,
                    };
                    let mut ex = Exec1 {
                        arena: &mut this.arena,
                        ctx: &f.ctx,
                        block: b.0,
                        site: EXIT_SITE,
                    };
                    Ok(ex.read(state, v))
                }
                Some(Ok(Reg::Zero(bits))) => Ok(this.arena.constant(bits, 0)),
                _ => Err(Stop::Unmodeled(format!(
                    "{opcode:?} at block {} tests an unmodeled operand",
                    b.0
                ))),
            }
        };
        match opcode {
            BCond | Bcc => {
                let Some(MachOperand::Imm(cc)) = ops.first() else {
                    return Err(Stop::Unmodeled(format!(
                        "{opcode:?} at block {} without a condition code",
                        b.0
                    )));
                };
                let cc = *cc & 0xF;
                if cc >= 14 {
                    // AL/NV: always taken. Model as an atom that the
                    // constant `true` decides.
                    let key = self.arena.op_id(OpKey {
                        tag: OpTag::CondFlags,
                        aux: vec![Aux::Imm(0, 14)],
                    });
                    let t = self.arena.op_term(key, &[], 0, 1);
                    return Ok((t, false));
                }
                let flags = state.phys[LOC_NZCV as usize];
                if let Some(decided) = self.compare_of_equal_values(flags, cc) {
                    return Ok((self.arena.constant(1, u128::from(decided)), false));
                }
                let key = self.arena.op_id(OpKey {
                    tag: OpTag::CondFlags,
                    aux: vec![Aux::Imm(0, cc & !1)],
                });
                Ok((self.arena.op_term(key, &[flags], 0, 1), cc & 1 == 1))
            }
            Cbz | Cbnz => {
                let t = reg_term(self, ops.first())?;
                let key = self.arena.op_id(OpKey {
                    tag: OpTag::CondZero,
                    aux: Vec::new(),
                });
                Ok((self.arena.op_term(key, &[t], 0, 1), opcode == Cbnz))
            }
            Tbz | Tbnz => {
                let t = reg_term(self, ops.first())?;
                let Some(MachOperand::Imm(bit)) = ops.get(1) else {
                    return Err(Stop::Unmodeled(format!(
                        "{opcode:?} at block {} without a bit number",
                        b.0
                    )));
                };
                let key = self.arena.op_id(OpKey {
                    tag: OpTag::CondBit,
                    aux: vec![Aux::Imm(1, *bit)],
                });
                // `TBZ` branches when the bit is zero: the atom is "bit is zero".
                Ok((self.arena.op_term(key, &[t], 0, 1), opcode == Tbnz))
            }
            _ => Err(Stop::Unmodeled(format!(
                "{opcode:?} is not a conditional branch"
            ))),
        }
    }

    /// Whether a conditional branch's condition is decided false here.
    fn never_taken(
        &mut self,
        side: Side,
        b: BlockId,
        inst: InstId,
        state: &State,
    ) -> Result<bool, Stop> {
        let (atom, negated) = self.cond_atom(side, b, inst, state)?;
        Ok(self
            .arena
            .const_value(atom)
            .is_some_and(|v| (v == 1) == negated))
    }

    /// The value of condition `cc` on the flags of a compare (`CMP`/`SUBS`)
    /// of two equal values: `a - b = 0`, no borrow, no overflow.
    fn compare_of_equal_values(&self, flags: TermId, cc: i64) -> Option<bool> {
        use AArch64Opcode::*;
        let super::term::Term::Op { op, args, .. } = self.arena.get(flags) else {
            return None;
        };
        let key = self.arena.op(*op);
        let compare = [CmpRR, CMPXrr, CMPWrr, SubsRR]
            .iter()
            .any(|c| key.tag == OpTag::Inst(*c as u16));
        if !compare || args.len() != 2 || args[0] != args[1] {
            return None;
        }
        // N=0, Z=1, C=1, V=0.
        Some(match cc {
            0 | 2 | 5 | 7 | 9 | 10 | 13 => true,
            1 | 3 | 4 | 6 | 8 | 11 | 12 => false,
            _ => return None,
        })
    }

    fn indirect_atom(
        &mut self,
        side: Side,
        b: BlockId,
        id: InstId,
        state: &State,
        table: usize,
    ) -> Result<TermId, Stop> {
        let func = self.side(side).func();
        let inst = func.inst(id);
        let Some(Some(Ok(Reg::View(v)))) = inst.operands.first().map(operand_reg) else {
            return Err(Stop::Unmodeled(format!(
                "indirect branch at block {} through an unmodeled operand",
                b.0
            )));
        };
        let f = match side {
            Side::Spec => &self.spec,
            Side::Impl => &self.imp,
        };
        let mut ex = Exec1 {
            arena: &mut self.arena,
            ctx: &f.ctx,
            block: b.0,
            site: EXIT_SITE,
        };
        let t = ex.read(state, v);
        let key = self.arena.op_id(OpKey {
            tag: OpTag::IndirectTarget,
            aux: vec![Aux::JumpTable(0, table as u32)],
        });
        Ok(self.arena.op_term(key, &[t], 0, 64))
    }

    /// The effect of a return or tail call: its implicit uses (the ABI
    /// return or argument registers) and operands.
    fn exit_event(
        &mut self,
        side: Side,
        b: BlockId,
        id: InstId,
        state: &State,
        tail: bool,
        sinks: &[trust_cg_ir::PReg],
    ) -> Result<Box<Event>, Stop> {
        let f = match side {
            Side::Spec => &self.spec,
            Side::Impl => &self.imp,
        };
        let inst = f.ctx.func.inst(id);
        let mut ex = Exec1 {
            arena: &mut self.arena,
            ctx: &f.ctx,
            block: b.0,
            site: EXIT_SITE,
        };
        let mut args = Vec::new();
        let mut arg_widths = Vec::new();
        let mut aux = Vec::new();
        for (pos, op) in inst.operands.iter().enumerate() {
            match op {
                MachOperand::Symbol(s) => aux.push(Aux::Sym(pos as u8, s.clone(), false)),
                MachOperand::ExactModuleSymbol(s) => aux.push(Aux::Sym(pos as u8, s.clone(), true)),
                MachOperand::Imm(_) | MachOperand::Block(_) => {}
                _ => match operand_reg(op) {
                    // RET's link-register operand is where control returns,
                    // not a returned value: the frame stage checks it holds
                    // the entry return address.
                    Some(Ok(Reg::View(v))) if !tail && v.place == Place::Phys(30) => {}
                    Some(Ok(Reg::View(v))) => {
                        aux.push(Aux::View(pos as u8, v.bits, v.fpr));
                        args.push(ex.read(state, v));
                        arg_widths.push(v.bits);
                    }
                    _ => {
                        return Err(Stop::Unmodeled(format!(
                            "{:?} at block {} with an unmodeled operand {op:?}",
                            inst.opcode, b.0
                        )));
                    }
                },
            }
        }
        let mut implicit: Vec<_> = sinks.to_vec();
        implicit.sort_unstable();
        implicit.dedup();
        for p in implicit {
            aux.push(Aux::Implicit(p.encoding()));
            match super::model::preg_reg(p) {
                Some(Reg::View(v)) => {
                    args.push(ex.read(state, v));
                    // A tail call's argument is observed at the width it
                    // was written through; a return value at its sink's.
                    let written = match v.place {
                        Place::Phys(loc) if tail => state.written[loc as usize],
                        _ => v.bits,
                    };
                    arg_widths.push(v.bits.min(written));
                }
                Some(Reg::Zero(_)) => {}
                None => {
                    return Err(Stop::Unmodeled(format!(
                        "{:?} at block {} with an unmodeled implicit use {p:?}",
                        inst.opcode, b.0
                    )));
                }
            }
        }
        // Before frame lowering both functions run on the entry SP, so an
        // exit carries SP as an argument (a tail call's callee finds its
        // stack arguments there); after it the exit obligations require the
        // implementation's SP to be the CFA again.
        if !self.callee_saved_exit_check {
            aux.push(Aux::Implicit(0x4000 | LOC_SP));
            args.push(state.phys[LOC_SP as usize]);
            arg_widths.push(64);
        }
        let key = self.arena.op_id(OpKey {
            tag: if tail { OpTag::TailCall } else { OpTag::Ret },
            aux,
        });
        Ok(Box::new(Event {
            key,
            args,
            outputs: Vec::new(),
            flags_out: false,
            writebacks: Vec::new(),
            clobber: super::model::Clobber::None,
            store: None,
            opaque_write: true,
            junk_after: Vec::new(),
            arg_widths,
            inst: id,
            span: 1,
        }))
    }
}

/// An implementation value that is, on every edge, a common base plus a
/// constant multiple of one specification leaf's edge value: `vec[e] =
/// A + k·S[e]` (a pointer that advances `k` bytes per unit step of an
/// induction variable, as late post-index formation leaves it). `A` is
/// computed per edge as the affine difference `vec[e] - k·S[e]` and must
/// be the same term on every edge and valid at the join (entry-rooted,
/// or the value of a specification location with that vector), so `A +
/// k·leaf` holds on every incoming path by construction. `k` is read
/// off one edge's steps; a wrong guess only fails to find a relation.
fn induction_value(
    arena: &mut TermArena,
    vec: &[TermId],
    table: &EntryTable,
    leaves: &[LeafSteps],
) -> Option<TermId> {
    if leaves.is_empty() || vec.len() < 2 || vec.iter().any(|&t| arena.bits(t) != 64) {
        return None;
    }
    let forms: Vec<Affine> = vec.iter().map(|&t| arena.affine(t)).collect();
    for leaf in leaves {
        if leaf.forms.len() != forms.len() {
            continue;
        }
        let k = match &leaf.step {
            // An induction step: `k` relates the two steps.
            Some((e, ds)) => forms[*e].minus_scaled(&forms[0], 1).ratio_to(ds),
            // A value common to every edge (not entry-rooted): `k`
            // relates the coefficients of its first non-rooted atom.
            None => leaf.forms[0]
                .atoms
                .iter()
                .find(|&&(atom, _)| !arena.rooted(atom))
                .and_then(|&(atom, coef)| {
                    let at = forms[0]
                        .atoms
                        .binary_search_by_key(&atom, |&(a, _)| a)
                        .ok()?;
                    let (num, den) = (forms[0].atoms[at].1 as i64, coef as i64);
                    if den == 0 || num.checked_rem(den)? != 0 {
                        return None;
                    }
                    num.checked_div(den).map(|k| k as u64)
                }),
        };
        let Some(k) = k else {
            continue;
        };
        if k == 0 {
            continue;
        }
        let base = forms[0].minus_scaled(&leaf.forms[0], k);
        if (1..forms.len()).any(|e| forms[e].minus_scaled(&leaf.forms[e], k) != base) {
            continue;
        }
        let base = arena.affine_term(base);
        let base = if arena.rooted(base) && !arena.is_unknown(base) {
            base
        } else if let Some(t) = table.lookup(arena, 64, &vec![base; forms.len()]) {
            t
        } else {
            continue;
        };
        if let Some(value) = arena.add_scaled64(base, leaf.leaf, k) {
            return Some(value);
        }
    }
    None
}

fn place_key(p: Place) -> u64 {
    match p {
        Place::Phys(l) => u64::from(l),
        Place::Virt(v) => (1 << 32) | u64::from(v),
    }
}

/// The jump table an indirect branch at the end of block `b` dispatches
/// through: the one `ADR ..., JumpTableIndex(i)` in the block.
fn indirect_table(func: &MachFunction, b: BlockId, br: InstId) -> Result<usize, Stop> {
    let mut found = None;
    for &id in &func.blocks[b.0 as usize].insts {
        if let Some(i) = func.jump_table_at_address(id) {
            if found.is_some_and(|f| f != i) {
                return Err(Stop::Unmodeled(format!(
                    "indirect branch {} at block {}: several jump tables in one block",
                    br.0, b.0
                )));
            }
            found = Some(i);
        }
    }
    match found {
        Some(i) if (i as usize) < func.jump_tables.len() => Ok(i as usize),
        _ => Err(Stop::Unmodeled(format!(
            "indirect branch {} at block {} has no jump table in its block",
            br.0, b.0
        ))),
    }
}

/// A 64-bit specification leaf of a join, for induction relations: the
/// affine form of its value on each edge, and the first edge whose value
/// differs from the first edge's (with that difference), if any (a leaf
/// whose value is the same on every edge but not entry-rooted has none).
struct LeafSteps {
    leaf: TermId,
    forms: Vec<Affine>,
    step: Option<(usize, Affine)>,
}

/// The specification's per-edge value vectors at one join, indexed for
/// lookup at a width by the first edge's value.
#[derive(Default)]
struct EntryTable {
    /// `(width, per-edge values, entry value)`.
    entries: Vec<(u16, Vec<TermId>, TermId)>,
    /// `(width, first edge's value truncated to it)` to entries of at least
    /// that width.
    index: HashMap<(u16, TermId), Vec<usize>>,
}

impl EntryTable {
    /// Record a specification location of width `w` with per-edge values
    /// `vec` and entry value `value`, findable at every width in `widths`
    /// not above `w`.
    fn insert(
        &mut self,
        arena: &mut TermArena,
        widths: &[u16],
        w: u16,
        vec: Vec<TermId>,
        value: TermId,
    ) {
        let k = self.entries.len();
        for &w2 in widths.iter().filter(|&&w2| w2 <= w) {
            let first = arena.trunc(w2, vec[0]);
            self.index.entry((w2, first)).or_default().push(k);
        }
        self.entries.push((w, vec, value));
    }

    /// The entry value (truncated to `w`) of a location whose low `w` bits
    /// equal `vec`'s on every edge.
    fn lookup(&self, arena: &mut TermArena, w: u16, vec: &[TermId]) -> Option<TermId> {
        let first = arena.resize(w, vec[0]);
        let candidates = self.index.get(&(w, first))?;
        'next: for &k in candidates {
            let (ew, evec, value) = &self.entries[k];
            if evec.len() != vec.len() {
                continue;
            }
            for (&a, &b) in evec.iter().zip(vec) {
                if arena.trunc(w, a) != arena.resize(w, b) {
                    continue 'next;
                }
            }
            return Some(if *ew == w {
                *value
            } else {
                arena.trunc(w, *value)
            });
        }
        None
    }
}

/// Unconditional traps: control does not continue past them.
fn is_unconditional_trap(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        Brk | TrapOverflow | TrapBoundsCheck | TrapNull | TrapDivZero | TrapShiftRange
    )
}

/// `TRUST_CG_POST_RA_VALUE_FLOW_TRACE`: print every join's per-edge values
/// (development aid; changes no verdict).
fn trace_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TRUST_CG_POST_RA_VALUE_FLOW_TRACE").is_some())
}

#[cfg(test)]
mod induction_tests {
    use super::*;

    /// A 64-bit specification leaf of a two-edge join whose edge values step
    /// by one (`x0`, `x0 + 1`).
    fn stepping_leaf(arena: &mut TermArena) -> (Vec<TermId>, LeafSteps) {
        let x0 = arena.entry(0, 64);
        let edges = vec![x0, arena.lin(x0, 1)];
        let leaf = arena.leaf(7, 0, 64);
        let forms: Vec<Affine> = edges.iter().map(|&t| arena.affine(t)).collect();
        let step = Some((1, forms[1].minus_scaled(&forms[0], 1)));
        (edges, LeafSteps { leaf, forms, step })
    }

    /// An implementation location holding `base + 8·edge` on each edge.
    fn pointer(arena: &mut TermArena, base: TermId, edges: &[TermId]) -> Vec<TermId> {
        edges
            .iter()
            .map(|&t| arena.add_scaled64(base, t, 8).expect("64-bit terms"))
            .collect()
    }

    #[test]
    fn an_induction_pointer_needs_a_base_valid_at_the_join() {
        let mut arena = TermArena::default();
        let (edges, steps) = stepping_leaf(&mut arena);
        let leaves = std::slice::from_ref(&steps);
        let empty = EntryTable::default();
        // An entry-rooted base: the location is `base + 8·leaf`.
        let rooted = arena.entry(1, 64);
        let vec = pointer(&mut arena, rooted, &edges);
        let want = arena.add_scaled64(rooted, steps.leaf, 8);
        assert!(want.is_some());
        assert_eq!(induction_value(&mut arena, &vec, &empty, leaves), want);
        // A base common to both edges that is neither entry-rooted nor the
        // value of a specification location (another join's leaf, an
        // unknown) relates nothing.
        let foreign = arena.leaf(3, 2, 64);
        let unknown = arena.unknown(Side::Impl as u8, 3, 0, 9, 64);
        for base in [foreign, unknown] {
            let vec = pointer(&mut arena, base, &edges);
            assert_eq!(
                induction_value(&mut arena, &vec, &empty, leaves),
                None,
                "{}",
                arena.render(base)
            );
        }
        // The same base held by a specification location on every edge:
        // the location's entry value stands for it.
        let mut table = EntryTable::default();
        let held = arena.leaf(7, 1, 64);
        table.insert(&mut arena, &[64], 64, vec![foreign, foreign], held);
        let vec = pointer(&mut arena, foreign, &edges);
        let want = arena.add_scaled64(held, steps.leaf, 8);
        assert!(want.is_some());
        assert_eq!(induction_value(&mut arena, &vec, &table, leaves), want);
    }
}
