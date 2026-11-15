// trust-cg-irmid/passes/range.rs - unsigned-range rules
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The range rules: the native lanes' LIR unsigned-range simplification
//! (`trust_cg_opt::lir_unsigned_range`) ported to `trust_ir::Function`, with
//! facts from dominating branches, block-parameter intervals (loop induction
//! ranges among them) and `switch` folding.
//!
//! A value's fact is an interval of its raw bit pattern, read unsigned at the
//! width of its type, derived from its definition by the LIR pass's rows
//! (constants, `and` bounded by either operand, `zext`, non-wrapping `add`
//! and `mul`, a decided compare, a decided overflow flag) and by the rows
//! trust-ir's forward propagation states for the same forms (`sub`, `trunc`,
//! `sext`, `select`), plus a shift or remainder by a known amount, a `zext`
//! of a value without a fact (its source type's full range) and a `bitcast`
//! between integers of one width (the identity on the bits); a cast to an
//! integer of the same width (`zext u32` to a wasm32 `usize`) is the
//! identity on the bits. Where `trust_ir::propagate` derives a fact for the
//! result (fixed-width integers, and pointer-width ones at this target's
//! width), it narrows the pass's own: the two are each sound, so their
//! intersection is, and a disjoint pair is a contradiction the pass reads as
//! no fact. It never adds a fact the pass's own rows do not derive.
//!
//! **Where a fact holds.** A trust-ir function is SSA: a value has one
//! definition, every read follows it, and its definition's fact holds
//! wherever it is read. A block entered by exactly one edge (counting every
//! edge of every terminator), the `then` or `else` edge of a `condbr` whose
//! two targets differ, knows more: the condition is `true` (or `false`)
//! there, and when the condition is an `icmp` of integers the compared values
//! lie in the intervals the compare leaves them (`refine`: `x < y` bounds `x`
//! below `hi(y)` and `y` above `lo(x)`, `x == y` intersects them, `x != c`
//! drops `c` from an end; a signed predicate splits each interval at the
//! sign boundary and refines the halves). Those facts hold in every block
//! the edge's target dominates and nowhere else: never across a join another
//! edge reaches. They are read through the dominator tree: a value's fact in
//! a block is the refinement of the nearest dominating guard that names it,
//! else its definition's, and a definition's operands are read in the block
//! that defines it. A lookup does not walk the dominator path: the guarded
//! blocks whose condition may name each value (or relate each pair) are
//! indexed by their dominator-tree preorder spans ([`Chain`]), which yields
//! the dominating ones nearest first in logarithmic steps; an index entry
//! whose guard names nothing in a round (its edge ruled out) is passed over,
//! and one missing would only leave a farther, weaker fact. The compare
//! itself is recorded too, as a relation of its two operands, and an `icmp`
//! of the same two values (either order) that every pair satisfying the
//! relation decides is decided (`implied`: a table over the five ways two
//! values can compare unsigned and signed).
//!
//! **Block parameters.** A parameter's fact is an inductive invariant: an
//! interval that contains, on every edge into its block, the fact of the
//! argument the edge passes (refined by the edge's own `condbr` condition,
//! and nothing from an edge that condition rules out). For a loop header
//! that is an induction range: the initial value lies in it, and the step
//! keeps it there under the dominating exit test (`i < n` with `n <= N`
//! bounds `i + 1` by `N`). The invariants are found by interval iteration in
//! reverse postorder: a loop header's parameter grows as its edges' hull,
//! and is widened when a back edge brings a value outside it (to the signed
//! maximum, then the unsigned one; down to the sign boundary, then zero);
//! two narrowing rounds follow. They are kept only once a last derivation
//! under all of them confirms every edge; a parameter an edge breaks loses
//! its interval and the check repeats (a bounded number of times, after
//! which no parameter keeps one).
//!
//! The rules, as in the LIR pass: an `icmp` its operands' intervals decide
//! becomes `const bool` (every predicate, not only `ult`; signed predicates
//! when each interval stays on one side of the sign boundary), and one a
//! dominating compare of the same operands decides too; an
//! `add`/`sub`/`mul.overflow` that cannot overflow becomes the plain
//! arithmetic and `const bool false` (the LIR pass's checked unsigned add and
//! multiply, here also the subtraction and the signed forms over
//! non-negative operands); a `select` on a decided condition becomes a
//! `copy` of its arm; an `assert` of a condition decided true goes; a
//! `condbr` on a decided condition becomes a `br`; a `switch` drops the cases
//! outside its value's interval, takes a remaining case as its default when
//! the cases cover the interval, and becomes a `br` when one edge is left;
//! and the blocks the folded branches leave unreachable are removed. The
//! witness names each rewrite's rule and the interval of every operand it
//! reads in the rewrite's block, and the block-parameter invariants; the
//! checker (`trust_cg_verify::trust_ir_mid_tv`, `trust_ir_mid_tv_range.rs`)
//! derives its own facts under those invariants, checks each invariant on
//! every edge, and refuses a premise its facts do not imply.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{
    PassWitness, RangeInvariant, RangePremise, RangeRewrite, RangeRule, RangeWitness,
};
use trust_ir::propagate::derive_result_fact_with_representation;
use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, OverflowOp, Pred,
    PredTable, SwitchCase, Ty, ValueId,
};

use super::{MidPass, PassContext, drop_names, int_shape, value_types};
use crate::cfg::TrustIrCfg;

pub(crate) struct RangeRules;

/// The evidence name of the range rules.
pub(crate) const RANGE_NAME: &str = "range";

/// Which fact sources the pass uses. Every one is on in the pipeline; the
/// crate's tests switch them off one at a time to attribute a fold to the
/// source that made it possible.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RangeSources {
    /// Facts and relations from dominating branches.
    pub guards: bool,
    /// Block-parameter invariants.
    pub invariants: bool,
    /// `switch` folding.
    pub switch: bool,
}

impl RangeSources {
    pub(crate) const ALL: Self = Self {
        guards: true,
        invariants: true,
        switch: true,
    };
}

#[cfg(test)]
thread_local! {
    /// The sources the pass uses on this thread (tests only).
    pub(crate) static RANGE_SOURCES: std::cell::Cell<RangeSources> =
        const { std::cell::Cell::new(RangeSources::ALL) };
}

fn sources() -> RangeSources {
    #[cfg(test)]
    {
        RANGE_SOURCES.with(std::cell::Cell::get)
    }
    #[cfg(not(test))]
    {
        RangeSources::ALL
    }
}

/// Ascending rounds of the block-parameter iteration before it gives up
/// (every parameter then has no interval).
const MAX_ASCENDING_ROUNDS: usize = 12;
/// Narrowing rounds after the ascending ones.
const NARROWING_ROUNDS: usize = 2;
/// Confirmation rounds (each drops the parameters an edge breaks) before
/// the pass gives every parameter up.
const MAX_CONFIRM_ROUNDS: usize = 6;

/// An unsigned interval of raw values at a width (the LIR pass's
/// `UIntRange`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct UIntRange {
    lo: u128,
    hi: u128,
    width: u32,
}

impl UIntRange {
    fn exact(value: u128, width: u32) -> Self {
        Self {
            lo: value,
            hi: value,
            width,
        }
    }

    fn full(width: u32) -> Self {
        Self {
            lo: 0,
            hi: unsigned_max(width),
            width,
        }
    }

    fn exact_value(self) -> Option<u128> {
        (self.lo == self.hi).then_some(self.lo)
    }

    /// Both facts at once; `None` when they are disjoint or of other widths.
    fn intersect(self, other: Self) -> Option<Self> {
        if self.width != other.width {
            return None;
        }
        let (lo, hi) = (self.lo.max(other.lo), self.hi.min(other.hi));
        (lo <= hi).then_some(Self {
            lo,
            hi,
            width: self.width,
        })
    }

    /// The smallest interval holding both.
    fn hull(self, other: Self) -> Self {
        Self {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
            width: self.width,
        }
    }

    fn contains(self, other: Self) -> bool {
        self.width == other.width && self.lo <= other.lo && other.hi <= self.hi
    }
}

fn unsigned_max(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// `(width, signed)` of a scalar the rules read: an integer (pointer-width
/// ones at `pointer_bits`), or `bool` as one unsigned bit.
fn scalar_shape(ty: &Ty, pointer_bits: u32) -> Option<(u32, bool)> {
    if *ty == Ty::Bool {
        Some((1, false))
    } else {
        int_shape(ty, pointer_bits)
    }
}

/// The fixed-width type trust-ir's propagation reads a pointer-width integer
/// as at `pointer_bits` (it states no fact for `usize`/`isize` itself).
fn representation(ty: &Ty, pointer_bits: u32) -> Option<Ty> {
    match (ty, pointer_bits) {
        (Ty::Usize, 32) => Some(Ty::U32),
        (Ty::Usize, 64) => Some(Ty::U64),
        (Ty::Isize, 32) => Some(Ty::I32),
        (Ty::Isize, 64) => Some(Ty::I64),
        _ => None,
    }
}

/// `op lhs, rhs` holds (at `width`): what a dominating branch establishes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Relation {
    op: ICmpOp,
    lhs: ValueId,
    rhs: ValueId,
    width: u32,
}

/// What a block's one incoming edge establishes on entry.
#[derive(Debug, Clone, Default)]
struct Guard {
    refined: Vec<(ValueId, UIntRange)>,
    relations: Vec<Relation>,
}

/// The intervals a condition leaves its operands (and itself).
type Refined = Vec<(ValueId, UIntRange)>;

/// The argument fact an edge passes.
enum EdgeFact {
    /// The edge's own condition contradicts the facts: it is never taken.
    Never,
    Fact(UIntRange),
    Unknown,
}

/// The state of a block parameter in the iteration: absent while no edge
/// has reached it, `None` with no interval.
type ParamState = HashMap<ValueId, Option<UIntRange>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Round {
    /// Each parameter takes the hull of its edges' arguments, widened at a
    /// loop header that grows.
    Widen,
    /// Each parameter takes the hull of its edges' arguments when that is
    /// inside its interval.
    Narrow,
    /// The parameters keep their state.
    Fixed,
}

/// The function's facts and the typing and dominance they were derived
/// with.
struct Facts<'f> {
    func: &'f Function,
    pointer_bits: u32,
    sources: RangeSources,
    types: HashMap<ValueId, Ty>,
    /// Values defined more than once (malformed input): no fact.
    repeated: HashSet<ValueId>,
    positions: HashMap<BlockId, usize>,
    /// Reachable blocks in reverse postorder.
    order: Vec<BlockId>,
    rank: HashMap<BlockId, usize>,
    /// Each reachable block's dominator-tree span: its preorder number and
    /// the largest one in its subtree. `a` dominates `b` exactly when `b`'s
    /// number lies in `a`'s span.
    span: HashMap<BlockId, Span>,
    /// The block defining each value (parameters included).
    def_block: HashMap<ValueId, BlockId>,
    /// The single-result instruction defining each value.
    sole: HashMap<ValueId, &'f Inst>,
    /// Every edge into each block: its source and the edge's index among
    /// the source terminator's successor edges.
    incoming: HashMap<BlockId, Vec<(BlockId, usize)>>,
    /// The blocks entered by exactly one edge, the `then` (`true`) or `else`
    /// edge of a `condbr` with two distinct targets in that predecessor.
    guarded_by: HashMap<BlockId, (BlockId, bool)>,
    /// The guarded blocks whose guard may refine each value: every block
    /// whose condition names it where [`Facts::condition`] may (the
    /// condition, and an integer compare's operands), whatever the facts.
    named: HashMap<ValueId, Chain>,
    /// The guarded blocks whose guard may relate each pair of values
    /// (keyed in [`pair`] order).
    related: HashMap<(ValueId, ValueId), Chain>,
    guards: HashMap<BlockId, Guard>,
    /// Each value's fact: its definition's, or its parameter invariant.
    facts: HashMap<ValueId, UIntRange>,
    /// Blocks a round has visited.
    visited: HashSet<BlockId>,
}

impl<'f> Facts<'f> {
    fn new(func: &'f Function, pointer_bits: u32, sources: RangeSources) -> Self {
        let mut types = value_types(func);
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let (Inst::Overflow { ty, .. }, [value, flag]) =
                (&node.inst, node.results.as_slice())
            {
                types.insert(*value, ty.clone());
                types.insert(*flag, Ty::Bool);
            }
        }
        let mut seen = HashSet::new();
        let mut repeated = HashSet::new();
        let mut def_block = HashMap::new();
        let mut sole = HashMap::new();
        for block in &func.blocks {
            for (value, _) in &block.params {
                if !seen.insert(*value) {
                    repeated.insert(*value);
                }
                def_block.insert(*value, block.id);
            }
            for node in &block.body {
                for value in &node.results {
                    if !seen.insert(*value) {
                        repeated.insert(*value);
                    }
                    def_block.insert(*value, block.id);
                }
                if let [result] = node.results.as_slice() {
                    sole.insert(*result, &node.inst);
                }
            }
        }
        let (order, idom) = TrustIrCfg::new(func).rpo_and_idom();
        let rank: HashMap<BlockId, usize> =
            order.iter().enumerate().map(|(i, b)| (*b, i)).collect();
        let positions: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let mut incoming: HashMap<BlockId, Vec<(BlockId, usize)>> = HashMap::new();
        for block in &func.blocks {
            if let Some(last) = block.body.last() {
                for (k, edge) in last.inst.successor_edges().iter().enumerate() {
                    incoming.entry(edge.target).or_default().push((block.id, k));
                }
            }
        }
        let mut guarded_by = HashMap::new();
        if sources.guards {
            for (target, edges) in &incoming {
                let [(pred, k)] = edges.as_slice() else {
                    continue;
                };
                if *target == func.entry || !rank.contains_key(target) {
                    continue;
                }
                let Some(&pi) = positions.get(pred) else {
                    continue;
                };
                if let Some(Inst::CondBr {
                    then_target,
                    else_target,
                    ..
                }) = func.blocks[pi].body.last().map(|n| &n.inst)
                    && then_target != else_target
                {
                    guarded_by.insert(*target, (*pred, *k == 0));
                }
            }
        }
        let span = dominator_spans(&order, &idom);
        let mut this = Self {
            func,
            pointer_bits,
            sources,
            types,
            repeated,
            positions,
            order,
            rank,
            span,
            def_block,
            sole,
            incoming,
            guarded_by,
            named: HashMap::new(),
            related: HashMap::new(),
            guards: HashMap::new(),
            facts: HashMap::new(),
            visited: HashSet::new(),
        };
        let mut named: HashMap<ValueId, Vec<(BlockId, Span)>> = HashMap::new();
        let mut related: HashMap<(ValueId, ValueId), Vec<(BlockId, Span)>> = HashMap::new();
        for (&id, &(pred, _)) in &this.guarded_by {
            let Some(&span) = this.span.get(&id) else {
                continue;
            };
            let Some(Inst::CondBr { cond, .. }) = this
                .positions
                .get(&pred)
                .and_then(|&pi| func.blocks[pi].body.last())
                .map(|n| &n.inst)
            else {
                continue;
            };
            if !this.defined_over(*cond, pred) {
                continue;
            }
            let mut names = vec![*cond];
            if let Some(Inst::ICmp { ty, lhs, rhs, .. }) = this.sole.get(cond).copied()
                && scalar_shape(ty, pointer_bits).is_some()
                && this.defined_over(*lhs, pred)
                && this.defined_over(*rhs, pred)
            {
                names.push(*lhs);
                if rhs != lhs {
                    names.push(*rhs);
                }
                related
                    .entry(pair(*lhs, *rhs))
                    .or_default()
                    .push((id, span));
            }
            for value in names {
                named.entry(value).or_default().push((id, span));
            }
        }
        this.named = named.into_iter().map(|(k, m)| (k, Chain::new(m))).collect();
        this.related = related
            .into_iter()
            .map(|(k, m)| (k, Chain::new(m)))
            .collect();
        this
    }

    /// The facts of `func`: block-parameter invariants found and confirmed
    /// (when the invariant source is on), then every value's.
    fn derive(func: &'f Function, pointer_bits: u32, sources: RangeSources) -> (Self, ParamState) {
        let mut this = Self::new(func, pointer_bits, sources);
        let mut state = ParamState::new();
        if !sources.invariants {
            this.round(&mut state, Round::Fixed);
            return (this, state);
        }
        let mut settled = false;
        for _ in 0..MAX_ASCENDING_ROUNDS {
            if !this.round(&mut state, Round::Widen) {
                settled = true;
                break;
            }
        }
        if settled {
            for _ in 0..NARROWING_ROUNDS {
                this.round(&mut state, Round::Narrow);
            }
        } else {
            for fact in state.values_mut() {
                *fact = None;
            }
        }
        for _ in 0..MAX_CONFIRM_ROUNDS {
            this.round(&mut state, Round::Fixed);
            let broken = this.broken_invariants(&state);
            if broken.is_empty() {
                return (this, state);
            }
            for param in broken {
                state.insert(param, None);
            }
        }
        for fact in state.values_mut() {
            *fact = None;
        }
        this.round(&mut state, Round::Fixed);
        (this, state)
    }

    /// One pass over the reachable blocks in reverse postorder: each block's
    /// parameters (under `round`), its guard and its definitions' facts.
    /// Whether some parameter's state changed.
    fn round(&mut self, state: &mut ParamState, round: Round) -> bool {
        let mut changed = false;
        for bi in 0..self.order.len() {
            let id = self.order[bi];
            let Some(&pos) = self.positions.get(&id) else {
                continue;
            };
            if self.sources.invariants && id != self.func.entry {
                changed |= self.update_params(id, pos, state, round);
            }
            self.guard(id);
            self.visited.insert(id);
            let func = self.func;
            for node in &func.blocks[pos].body {
                self.define(id, node);
            }
        }
        changed
    }

    /// Recompute the parameters of block `id` from its incoming edges.
    fn update_params(
        &mut self,
        id: BlockId,
        pos: usize,
        state: &mut ParamState,
        round: Round,
    ) -> bool {
        let func = self.func;
        let block = &func.blocks[pos];
        let my_rank = self.rank[&id];
        let edges = self.incoming.get(&id).cloned().unwrap_or_default();
        let header = edges
            .iter()
            .any(|(s, _)| self.rank.get(s).is_some_and(|&r| r >= my_rank));
        let mut changed = false;
        for (i, (param, ty)) in block.params.iter().enumerate() {
            let Some((width, signed)) = scalar_shape(ty, self.pointer_bits) else {
                continue;
            };
            if self.repeated.contains(param) {
                continue;
            }
            let old = state.get(param).copied();
            let new = if round == Round::Fixed {
                old
            } else {
                // The hull of every edge's argument, and of the back edges'.
                let mut hull: Option<Option<UIntRange>> = None;
                let mut back: Option<Option<UIntRange>> = None;
                for &(source, k) in &edges {
                    if !self.rank.contains_key(&source) || !self.visited.contains(&source) {
                        continue;
                    }
                    let fact = match self.edge_arg(source, k, i, width) {
                        EdgeFact::Never => continue,
                        EdgeFact::Fact(f) => Some(f),
                        EdgeFact::Unknown => None,
                    };
                    let join = |acc: Option<Option<UIntRange>>| {
                        Some(match (acc, fact) {
                            (None, f) => f,
                            (Some(Some(h)), Some(f)) => Some(h.hull(f)),
                            _ => None,
                        })
                    };
                    hull = join(hull);
                    if self.rank[&source] >= my_rank {
                        back = join(back);
                    }
                }
                // An interval of the whole type says nothing: no interval.
                let whole = |h: Option<Option<UIntRange>>| {
                    h.map(|h| h.filter(|f| *f != UIntRange::full(width)))
                };
                let (hull, back) = (whole(hull), whole(back));
                match (round, old, hull) {
                    (_, old, None) => old,
                    // At a loop header the interval only grows while
                    // ascending; it is widened when a back edge brings a
                    // value outside it (growth from outside the loop is
                    // taken as it is).
                    (Round::Widen, Some(Some(o)), Some(Some(n))) if header => {
                        if o.contains(n) {
                            Some(Some(o))
                        } else if back.is_none_or(|b| b.is_some_and(|b| o.contains(b))) {
                            Some(Some(o.hull(n)))
                        } else {
                            Some(widen(o, o.hull(n), signed))
                                .map(|w| (w != UIntRange::full(width)).then_some(w))
                        }
                    }
                    (Round::Narrow, Some(Some(o)), Some(Some(n))) if !o.contains(n) => {
                        Some(Some(o))
                    }
                    (Round::Narrow, Some(Some(o)), Some(None)) => Some(Some(o)),
                    (Round::Widen, Some(None), _) => Some(None),
                    (_, _, Some(n)) => Some(n),
                }
            };
            if new != old {
                changed = true;
                match new {
                    Some(n) => {
                        state.insert(*param, n);
                    }
                    None => {
                        state.remove(param);
                    }
                }
            }
            match new.flatten() {
                Some(fact) => self.facts.insert(*param, fact),
                None => self.facts.remove(param),
            };
        }
        changed
    }

    /// The parameters whose interval some reachable edge's argument leaves.
    fn broken_invariants(&self, state: &ParamState) -> Vec<ValueId> {
        let mut broken = Vec::new();
        for id in &self.order {
            if *id == self.func.entry {
                continue;
            }
            let block = &self.func.blocks[self.positions[id]];
            let edges = self.incoming.get(id).cloned().unwrap_or_default();
            for (i, (param, _)) in block.params.iter().enumerate() {
                let Some(Some(inv)) = state.get(param) else {
                    continue;
                };
                let holds = edges.iter().all(|&(source, k)| {
                    !self.rank.contains_key(&source)
                        || match self.edge_arg(source, k, i, inv.width) {
                            EdgeFact::Never => true,
                            EdgeFact::Fact(f) => inv.contains(f),
                            EdgeFact::Unknown => false,
                        }
                });
                if !holds {
                    broken.push(*param);
                }
            }
        }
        broken
    }

    /// The fact of the `i`-th argument the `k`-th edge of `source` passes,
    /// refined by that edge's `condbr` condition.
    fn edge_arg(&self, source: BlockId, k: usize, i: usize, width: u32) -> EdgeFact {
        let Some(&pos) = self.positions.get(&source) else {
            return EdgeFact::Unknown;
        };
        let Some(last) = self.func.blocks[pos].body.last() else {
            return EdgeFact::Unknown;
        };
        let edges = last.inst.successor_edges();
        let Some(edge) = edges.get(k) else {
            return EdgeFact::Unknown;
        };
        let target_params = self
            .positions
            .get(&edge.target)
            .map_or(0, |&t| self.func.blocks[t].params.len());
        if edge.args.len() != target_params {
            return EdgeFact::Unknown;
        }
        let Some(&arg) = edge.args.get(i) else {
            return EdgeFact::Unknown;
        };
        let mut fact = self.fact_at(arg, source, width);
        if self.sources.guards
            && let Inst::CondBr { cond, .. } = &last.inst
            && let Some((refined, _)) = self.condition(*cond, source, k == 0)
        {
            match refined {
                None => return EdgeFact::Never,
                Some(list) => {
                    for (value, r) in list {
                        if value == arg && r.width == width {
                            fact = Some(match fact {
                                Some(f) => match f.intersect(r) {
                                    Some(f) => f,
                                    None => return EdgeFact::Never,
                                },
                                None => r,
                            });
                        }
                    }
                }
            }
        }
        match fact {
            Some(f) => EdgeFact::Fact(f),
            None => EdgeFact::Unknown,
        }
    }

    /// What `cond` being `holds` establishes at the end of block `at`: the
    /// refined intervals (`None`: it cannot be `holds`) and the relation.
    /// `None` when `cond` is not a value a refinement may name there.
    fn condition(
        &self,
        cond: ValueId,
        at: BlockId,
        holds: bool,
    ) -> Option<(Option<Refined>, Option<Relation>)> {
        if !self.defined_over(cond, at) {
            return None;
        }
        let mut refined = vec![(cond, UIntRange::exact(u128::from(holds), 1))];
        if let Some(own) = self.fact_at(cond, at, 1)
            && own.intersect(refined[0].1).is_none()
        {
            return Some((None, None));
        }
        let Some(Inst::ICmp { op, ty, lhs, rhs }) = self.sole.get(&cond).copied() else {
            return Some((Some(refined), None));
        };
        let Some((width, _)) = scalar_shape(ty, self.pointer_bits) else {
            return Some((Some(refined), None));
        };
        if !self.defined_over(*lhs, at) || !self.defined_over(*rhs, at) {
            return Some((Some(refined), None));
        }
        let op = if holds { *op } else { negate(*op) };
        let relation = Relation {
            op,
            lhs: *lhs,
            rhs: *rhs,
            width,
        };
        let a = self
            .fact_at(*lhs, at, width)
            .unwrap_or(UIntRange::full(width));
        let b = self
            .fact_at(*rhs, at, width)
            .unwrap_or(UIntRange::full(width));
        let Some((a2, b2)) = refine(op, a, b) else {
            return Some((None, Some(relation)));
        };
        if lhs == rhs {
            let Some(both) = a2.intersect(b2) else {
                return Some((None, Some(relation)));
            };
            refined.push((*lhs, both));
        } else {
            refined.push((*lhs, a2));
            refined.push((*rhs, b2));
        }
        Some((Some(refined), Some(relation)))
    }

    /// Whether `value` has one definition, in a block dominating `at`.
    fn defined_over(&self, value: ValueId, at: BlockId) -> bool {
        if self.repeated.contains(&value) {
            return false;
        }
        let Some(&def) = self.def_block.get(&value) else {
            return false;
        };
        def == at
            || matches!(
                (self.span.get(&def), self.span.get(&at)),
                (Some(d), Some(a)) if d.contains(*a)
            )
    }

    /// Compute the guard of block `id` from its one incoming edge.
    fn guard(&mut self, id: BlockId) {
        let Some(&(pred, then)) = self.guarded_by.get(&id) else {
            return;
        };
        let Some(&pos) = self.positions.get(&pred) else {
            return;
        };
        let Some(Inst::CondBr { cond, .. }) = self.func.blocks[pos].body.last().map(|n| &n.inst)
        else {
            return;
        };
        let mut guard = Guard::default();
        if let Some((Some(refined), relation)) = self.condition(*cond, pred, then) {
            guard.refined = refined;
            guard.relations.extend(relation);
        }
        self.guards.insert(id, guard);
    }

    /// The guards of `chain`'s blocks that dominate `at`, nearest first.
    fn guards_over<'a>(
        &'a self,
        chain: Option<&'a Chain>,
        at: BlockId,
    ) -> impl Iterator<Item = &'a Guard> + 'a {
        let over = match (chain, self.span.get(&at)) {
            (Some(chain), Some(&span)) => Some(chain.over(span)),
            _ => None,
        };
        over.into_iter()
            .flatten()
            .filter_map(|block| self.guards.get(&block))
    }

    /// The fact of `value` at width `width` in block `at`.
    fn fact_at(&self, value: ValueId, at: BlockId, width: u32) -> Option<UIntRange> {
        for guard in self.guards_over(self.named.get(&value), at) {
            if let Some((_, fact)) = guard.refined.iter().find(|(v, _)| *v == value) {
                return Some(*fact).filter(|f| f.width == width);
            }
        }
        self.facts
            .get(&value)
            .copied()
            .filter(|fact| fact.width == width)
    }

    /// The outcome of `op lhs, rhs` at `width` a dominating relation of the
    /// same two values decides in block `at`.
    fn implied_at(
        &self,
        op: ICmpOp,
        lhs: ValueId,
        rhs: ValueId,
        width: u32,
        at: BlockId,
    ) -> Option<bool> {
        self.guards_over(self.related.get(&pair(lhs, rhs)), at)
            .flat_map(|g| g.relations.iter())
            .filter(|r| r.width == width)
            .find_map(|r| {
                if r.lhs == lhs && r.rhs == rhs {
                    implied(r.op, op, false)
                } else if r.lhs == rhs && r.rhs == lhs {
                    implied(r.op, op, true)
                } else {
                    None
                }
            })
    }

    /// Record the facts `node` (in block `at`) defines.
    fn define(&mut self, at: BlockId, node: &InstrNode) {
        match (node.results.as_slice(), &node.inst) {
            ([value, flag], Inst::Overflow { op, ty, lhs, rhs }) => {
                let facts = self.overflow_facts(at, *op, ty, *lhs, *rhs);
                let (value_fact, flag_fact) = match facts {
                    Some((v, f)) => (v, Some(f)),
                    None => (None, None),
                };
                self.set(*value, value_fact);
                self.set(*flag, flag_fact);
            }
            ([result], inst) => {
                let own = self.own_fact(at, inst);
                let fact = match (own, self.propagated(at, *result, inst)) {
                    (Some(own), Some(propagated)) => own.intersect(propagated),
                    (own, _) => own,
                };
                self.set(*result, fact);
            }
            _ => {}
        }
    }

    fn set(&mut self, value: ValueId, fact: Option<UIntRange>) {
        match fact {
            Some(fact) if !self.repeated.contains(&value) => {
                self.facts.insert(value, fact);
            }
            _ => {
                self.facts.remove(&value);
            }
        }
    }

    /// The fact trust-ir's forward propagation derives for `result`, read
    /// back as a raw interval (a non-negative result only).
    fn propagated(&self, at: BlockId, result: ValueId, inst: &Inst) -> Option<UIntRange> {
        let ty = self.types.get(&result)?;
        let (width, _) = scalar_shape(ty, self.pointer_bits)?;
        let repr = representation(ty, self.pointer_bits);
        let table = PredTable::new(&[], &[]);
        let operand_fact = |value: ValueId| -> Pred {
            let Some(ty) = self.types.get(&value) else {
                return Pred::Top;
            };
            let Some((width, signed)) = scalar_shape(ty, self.pointer_bits) else {
                return Pred::Top;
            };
            let Some(fact) = self.fact_at(value, at, width) else {
                return Pred::Top;
            };
            // The value of a raw pattern: itself when unsigned, or when signed
            // and below the sign bit.
            let max = if signed {
                unsigned_max(width - 1)
            } else {
                unsigned_max(width)
            };
            match (i128::try_from(fact.lo), i128::try_from(fact.hi)) {
                (Ok(lo), Ok(hi)) if fact.hi <= max => Pred::interval(lo, hi).unwrap_or(Pred::Top),
                _ => Pred::Top,
            }
        };
        let derived =
            derive_result_fact_with_representation(&table, inst, repr.as_ref(), &operand_fact);
        match derived {
            Pred::Interval { lo, hi } if lo >= 0 && lo <= hi => {
                let (lo, hi) = (lo as u128, hi as u128);
                (hi <= unsigned_max(width)).then_some(UIntRange { lo, hi, width })
            }
            _ => None,
        }
    }

    /// The LIR pass's rows and their extensions (the module documentation),
    /// the operands read in block `at`.
    fn own_fact(&self, at: BlockId, inst: &Inst) -> Option<UIntRange> {
        let pb = self.pointer_bits;
        let get = |value: ValueId, width: u32| self.fact_at(value, at, width);
        match inst {
            Inst::Const { ty, value } => {
                let (width, _) = scalar_shape(ty, pb)?;
                match value {
                    Constant::Int(v) if width > 1 => {
                        Some(UIntRange::exact((*v as u128) & unsigned_max(width), width))
                    }
                    Constant::Bool(b) if width == 1 => Some(UIntRange::exact(u128::from(*b), 1)),
                    _ => None,
                }
            }
            Inst::Copy { ty, operand } => {
                let (width, _) = scalar_shape(ty, pb)?;
                (self.types.get(operand) == Some(ty))
                    .then(|| get(*operand, width))
                    .flatten()
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                let (width, _) = int_shape(ty, pb)?;
                let lhs = get(*lhs, width);
                let rhs = get(*rhs, width);
                match op {
                    BinOp::And => band_fact(lhs, rhs, width),
                    BinOp::Add => plain_arithmetic_fact(lhs?, rhs?, width, false),
                    BinOp::Mul => plain_arithmetic_fact(lhs?, rhs?, width, true),
                    BinOp::Sub => {
                        let (lhs, rhs) = (lhs?, rhs?);
                        (lhs.lo >= rhs.hi).then(|| UIntRange {
                            lo: lhs.lo - rhs.hi,
                            hi: lhs.hi - rhs.lo,
                            width,
                        })
                    }
                    BinOp::LShr => {
                        let amount = rhs?.exact_value()?;
                        if amount >= u128::from(width) {
                            return None;
                        }
                        let lhs = lhs.unwrap_or(UIntRange::full(width));
                        Some(UIntRange {
                            lo: lhs.lo >> amount,
                            hi: lhs.hi >> amount,
                            width,
                        })
                    }
                    BinOp::URem => {
                        let rhs = rhs?;
                        if rhs.lo == 0 {
                            return None;
                        }
                        let hi = lhs
                            .map_or(unsigned_max(width), |lhs| lhs.hi)
                            .min(rhs.hi - 1);
                        Some(UIntRange { lo: 0, hi, width })
                    }
                    _ => None,
                }
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let (from, _) = scalar_shape(src_ty, pb)?;
                let (to, _) = int_shape(dst_ty, pb)?;
                let source = get(*operand, from);
                match op {
                    // `uextend`: the operand's fact, or its type's full range.
                    CastOp::ZExt if to >= from => {
                        let source = source.unwrap_or(UIntRange::full(from));
                        Some(UIntRange {
                            width: to,
                            ..source
                        })
                    }
                    CastOp::Trunc if to <= from => {
                        let source = source?;
                        (source.hi <= unsigned_max(to)).then_some(UIntRange {
                            width: to,
                            ..source
                        })
                    }
                    CastOp::SExt if to >= from && from > 1 => {
                        let source = source?;
                        (source.hi <= unsigned_max(from - 1)).then_some(UIntRange {
                            width: to,
                            ..source
                        })
                    }
                    // Between integers of one width: the bits unchanged.
                    CastOp::Bitcast if to == from && int_shape(src_ty, pb).is_some() => source,
                    _ => None,
                }
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                let (width, _) = scalar_shape(ty, pb)?;
                match get(*cond, 1).and_then(UIntRange::exact_value) {
                    Some(1) => get(*then_val, width),
                    Some(_) => get(*else_val, width),
                    None => {
                        let a = get(*then_val, width)?;
                        let b = get(*else_val, width)?;
                        Some(a.hull(b))
                    }
                }
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let (width, _) = scalar_shape(ty, pb)?;
                let decided = match (get(*lhs, width), get(*rhs, width)) {
                    (Some(a), Some(b)) => fold_compare(*op, width, a, b),
                    _ => None,
                }
                .or_else(|| self.implied_at(*op, *lhs, *rhs, width, at));
                Some(match decided {
                    Some(value) => UIntRange::exact(u128::from(value), 1),
                    None => UIntRange {
                        lo: 0,
                        hi: 1,
                        width: 1,
                    },
                })
            }
            _ => None,
        }
    }

    /// The value's and the flag's facts of an overflow instruction its
    /// operands' facts in block `at` decide (the LIR pass's
    /// `checked_arithmetic_range`).
    fn overflow_facts(
        &self,
        at: BlockId,
        op: OverflowOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Option<(Option<UIntRange>, UIntRange)> {
        let (width, signed) = int_shape(ty, self.pointer_bits)?;
        let lhs = self.fact_at(lhs, at, width)?;
        let rhs = self.fact_at(rhs, at, width)?;
        checked_arithmetic_range(op, width, signed, lhs, rhs)
            .map(|value| (value, UIntRange::exact(0, 1)))
    }
}

/// A block's dominator-tree span: its preorder number and the largest
/// number in its subtree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Span {
    pre: u32,
    last: u32,
}

impl Span {
    /// Whether the block of `self` dominates the block of `other`.
    fn contains(self, other: Span) -> bool {
        self.pre <= other.pre && other.pre <= self.last
    }
}

/// The spans of the reachable blocks `order` (reverse postorder, entry
/// first) in the dominator tree `idom` (the entry its own, or absent).
fn dominator_spans(order: &[BlockId], idom: &HashMap<BlockId, BlockId>) -> HashMap<BlockId, Span> {
    let reachable: HashSet<BlockId> = order.iter().copied().collect();
    let mut children: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for id in order.iter().skip(1) {
        if let Some(&up) = idom.get(id)
            && up != *id
            && reachable.contains(&up)
        {
            children.entry(up).or_default().push(*id);
        }
    }
    let mut spans = HashMap::new();
    let Some(&root) = order.first() else {
        return spans;
    };
    // Iterative preorder; a block's span closes when its children have.
    let mut next = 0u32;
    let mut stack: Vec<(BlockId, usize)> = vec![(root, 0)];
    spans.insert(root, Span { pre: 0, last: 0 });
    while let Some((block, child)) = stack.pop() {
        match children.get(&block).and_then(|c| c.get(child)) {
            Some(&kid) => {
                stack.push((block, child + 1));
                next += 1;
                spans.insert(
                    kid,
                    Span {
                        pre: next,
                        last: next,
                    },
                );
                stack.push((kid, 0));
            }
            None => {
                if let Some(span) = spans.get_mut(&block) {
                    span.last = next;
                }
            }
        }
    }
    spans
}

/// The key of an unordered pair of values.
fn pair(a: ValueId, b: ValueId) -> (ValueId, ValueId) {
    if a <= b { (a, b) } else { (b, a) }
}

/// No member.
const NO_MEMBER: u32 = u32::MAX;

/// A set of reachable blocks indexed to list, nearest first, the members
/// that dominate a given block, without walking the dominator path: the
/// members dominating one block form a chain, each member's parent is the
/// nearest member dominating it, and `up[k][i]` is member `i`'s ancestor
/// `2^k` parents up.
#[derive(Debug, Clone)]
struct Chain {
    /// Members in preorder.
    blocks: Vec<BlockId>,
    spans: Vec<Span>,
    up: Vec<Vec<u32>>,
}

impl Chain {
    fn new(mut members: Vec<(BlockId, Span)>) -> Self {
        members.sort_by_key(|(_, s)| s.pre);
        members.dedup_by_key(|(b, _)| *b);
        let spans: Vec<Span> = members.iter().map(|(_, s)| *s).collect();
        // Spans nest or are disjoint: in preorder, a member's parent is the
        // innermost open span containing it.
        let mut parent = Vec::with_capacity(spans.len());
        let mut open: Vec<usize> = Vec::new();
        for (i, span) in spans.iter().enumerate() {
            while open.last().is_some_and(|&top| !spans[top].contains(*span)) {
                open.pop();
            }
            parent.push(open.last().map_or(NO_MEMBER, |&top| top as u32));
            open.push(i);
        }
        let mut up = vec![parent];
        while let Some(level) = up.last()
            && level.iter().any(|&p| p != NO_MEMBER)
        {
            let next = level
                .iter()
                .map(|&p| {
                    if p == NO_MEMBER {
                        NO_MEMBER
                    } else {
                        level[p as usize]
                    }
                })
                .collect();
            up.push(next);
        }
        Self {
            blocks: members.into_iter().map(|(b, _)| b).collect(),
            spans,
            up,
        }
    }

    /// The members dominating the block of span `at`, nearest first. Every
    /// member dominating it dominates the last member numbered at or before
    /// it in preorder (that member's number lies inside its span), so the
    /// nearest is that member or, lifting it past its member ancestors that
    /// do not dominate `at`, the parent of the last of those.
    fn over(&self, at: Span) -> impl Iterator<Item = BlockId> + '_ {
        let holds = |i: usize| self.spans[i].contains(at);
        let before = self.spans.partition_point(|s| s.pre <= at.pre);
        let mut next = match before.checked_sub(1) {
            None => NO_MEMBER,
            Some(i) if holds(i) => i as u32,
            Some(mut i) => {
                for level in self.up.iter().rev() {
                    let j = level[i];
                    if j != NO_MEMBER && !holds(j as usize) {
                        i = j as usize;
                    }
                }
                self.up[0][i]
            }
        };
        std::iter::from_fn(move || {
            let i = usize::try_from(next).ok().filter(|_| next != NO_MEMBER)?;
            next = self.up[0][i];
            Some(self.blocks[i])
        })
    }
}

/// `old` widened to cover `new`: a bound that grows jumps to the signed
/// maximum (or the sign boundary going down) when both stay on that side,
/// else to the type's end.
fn widen(old: UIntRange, new: UIntRange, signed: bool) -> UIntRange {
    let width = old.width;
    let half = if width >= 2 { 1u128 << (width - 1) } else { 1 };
    let mut out = old;
    if new.hi > old.hi {
        out.hi = if signed && width >= 2 && new.hi < half {
            half - 1
        } else {
            unsigned_max(width)
        };
    }
    if new.lo < old.lo {
        out.lo = if signed && width >= 2 && new.lo >= half {
            half
        } else {
            0
        };
    }
    out
}

/// The predicate that holds when `op` does not.
fn negate(op: ICmpOp) -> ICmpOp {
    match op {
        ICmpOp::Eq => ICmpOp::Ne,
        ICmpOp::Ne => ICmpOp::Eq,
        ICmpOp::Ult => ICmpOp::Uge,
        ICmpOp::Ule => ICmpOp::Ugt,
        ICmpOp::Ugt => ICmpOp::Ule,
        ICmpOp::Uge => ICmpOp::Ult,
        ICmpOp::Slt => ICmpOp::Sge,
        ICmpOp::Sle => ICmpOp::Sgt,
        ICmpOp::Sgt => ICmpOp::Sle,
        ICmpOp::Sge => ICmpOp::Slt,
    }
}

/// The intervals of `x` in `a` and `y` in `b` for which `op x, y` holds:
/// the hull of each side's values that have a partner; `None` when no pair
/// does. A signed predicate on a one-bit operand leaves both unchanged.
fn refine(op: ICmpOp, a: UIntRange, b: UIntRange) -> Option<(UIntRange, UIntRange)> {
    let swap = |r: Option<(UIntRange, UIntRange)>| r.map(|(x, y)| (y, x));
    match op {
        ICmpOp::Eq | ICmpOp::Ne | ICmpOp::Ult | ICmpOp::Ule => refine_unsigned(op, a, b),
        ICmpOp::Ugt => swap(refine_unsigned(ICmpOp::Ult, b, a)),
        ICmpOp::Uge => swap(refine_unsigned(ICmpOp::Ule, b, a)),
        ICmpOp::Slt => refine_signed(false, a, b),
        ICmpOp::Sle => refine_signed(true, a, b),
        ICmpOp::Sgt => swap(refine_signed(false, b, a)),
        ICmpOp::Sge => swap(refine_signed(true, b, a)),
    }
}

/// [`refine`] for `eq`, `ne`, `ult` and `ule`.
fn refine_unsigned(op: ICmpOp, a: UIntRange, b: UIntRange) -> Option<(UIntRange, UIntRange)> {
    let (x, y) = match op {
        ICmpOp::Ult => {
            if b.hi == 0 || a.lo == unsigned_max(a.width) {
                return None;
            }
            (
                UIntRange {
                    hi: a.hi.min(b.hi - 1),
                    ..a
                },
                UIntRange {
                    lo: b.lo.max(a.lo + 1),
                    ..b
                },
            )
        }
        ICmpOp::Ule => (
            UIntRange {
                hi: a.hi.min(b.hi),
                ..a
            },
            UIntRange {
                lo: b.lo.max(a.lo),
                ..b
            },
        ),
        ICmpOp::Eq => {
            let both = a.intersect(b)?;
            (both, both)
        }
        ICmpOp::Ne => {
            let drop = |r: UIntRange, other: UIntRange| -> Option<UIntRange> {
                match other.exact_value() {
                    Some(c) if r.lo == c && r.hi == c => None,
                    Some(c) if r.lo == c => Some(UIntRange { lo: c + 1, ..r }),
                    Some(c) if r.hi == c => Some(UIntRange { hi: c - 1, ..r }),
                    _ => Some(r),
                }
            };
            (drop(a, b)?, drop(b, a)?)
        }
        _ => return Some((a, b)),
    };
    (x.lo <= x.hi && y.lo <= y.hi).then_some((x, y))
}

/// [`refine`] for `slt` (`or_equal`: `sle`): each interval split at the sign
/// boundary; two halves on one side compare as their raw patterns do, and
/// a negative half is below every non-negative one.
fn refine_signed(or_equal: bool, a: UIntRange, b: UIntRange) -> Option<(UIntRange, UIntRange)> {
    let width = a.width;
    if width < 2 {
        return Some((a, b));
    }
    let half = 1u128 << (width - 1);
    // The halves of `r`: `(piece, negative)`.
    let halves = |r: UIntRange| -> Vec<(UIntRange, bool)> {
        let mut out = Vec::new();
        if r.lo < half {
            out.push((
                UIntRange {
                    hi: r.hi.min(half - 1),
                    ..r
                },
                false,
            ));
        }
        if r.hi >= half {
            out.push((
                UIntRange {
                    lo: r.lo.max(half),
                    ..r
                },
                true,
            ));
        }
        out
    };
    let unsigned = if or_equal { ICmpOp::Ule } else { ICmpOp::Ult };
    let mut out: Option<(UIntRange, UIntRange)> = None;
    for (pa, na) in halves(a) {
        for (pb, nb) in halves(b) {
            let kept = match (na, nb) {
                (x, y) if x == y => refine_unsigned(unsigned, pa, pb),
                // A negative value is below every non-negative one.
                (true, false) => Some((pa, pb)),
                _ => None,
            };
            if let Some((x, y)) = kept {
                out = Some(match out {
                    None => (x, y),
                    Some((hx, hy)) => (hx.hull(x), hy.hull(y)),
                });
            }
        }
    }
    out
}

/// The ways two values compare: `(unsigned, signed)` order of `x` to `y`.
/// Every one occurs at every width of two bits or more.
const ORDERS: [(Ordering, Ordering); 5] = [
    (Ordering::Equal, Ordering::Equal),
    (Ordering::Less, Ordering::Less),
    (Ordering::Less, Ordering::Greater),
    (Ordering::Greater, Ordering::Less),
    (Ordering::Greater, Ordering::Greater),
];

fn holds(op: ICmpOp, (u, s): (Ordering, Ordering)) -> bool {
    match op {
        ICmpOp::Eq => u == Ordering::Equal,
        ICmpOp::Ne => u != Ordering::Equal,
        ICmpOp::Ult => u == Ordering::Less,
        ICmpOp::Ule => u != Ordering::Greater,
        ICmpOp::Ugt => u == Ordering::Greater,
        ICmpOp::Uge => u != Ordering::Less,
        ICmpOp::Slt => s == Ordering::Less,
        ICmpOp::Sle => s != Ordering::Greater,
        ICmpOp::Sgt => s == Ordering::Greater,
        ICmpOp::Sge => s != Ordering::Less,
    }
}

/// The value of `query x, y` wherever `known x, y` holds (`swapped`: wherever
/// `known y, x` holds), when it is the same for every way `x` and `y` can
/// compare.
fn implied(known: ICmpOp, query: ICmpOp, swapped: bool) -> Option<bool> {
    let mut outcome = None;
    for order in ORDERS {
        let seen = if swapped {
            (order.0.reverse(), order.1.reverse())
        } else {
            order
        };
        if !holds(known, seen) {
            continue;
        }
        let value = holds(query, order);
        match outcome {
            None => outcome = Some(value),
            Some(v) if v != value => return None,
            Some(_) => {}
        }
    }
    outcome
}

/// `and`: at most the smaller bound of the operands that have one.
fn band_fact(lhs: Option<UIntRange>, rhs: Option<UIntRange>, width: u32) -> Option<UIntRange> {
    let hi = match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => lhs.hi.min(rhs.hi),
        (Some(bound), None) | (None, Some(bound)) => bound.hi,
        (None, None) => return None,
    };
    Some(UIntRange { lo: 0, hi, width })
}

/// `add` / `mul` whose upper bound does not wrap.
fn plain_arithmetic_fact(
    lhs: UIntRange,
    rhs: UIntRange,
    width: u32,
    multiply: bool,
) -> Option<UIntRange> {
    let (lo, hi) = if multiply {
        (lhs.lo.checked_mul(rhs.lo)?, lhs.hi.checked_mul(rhs.hi)?)
    } else {
        (lhs.lo.checked_add(rhs.lo)?, lhs.hi.checked_add(rhs.hi)?)
    };
    (hi <= unsigned_max(width)).then_some(UIntRange { lo, hi, width })
}

/// `Some(value fact)` when no pair of operands overflows `op` (unsigned; or
/// signed over non-negative operands); the value's fact is `None` where it
/// may be negative.
fn checked_arithmetic_range(
    op: OverflowOp,
    width: u32,
    signed: bool,
    lhs: UIntRange,
    rhs: UIntRange,
) -> Option<Option<UIntRange>> {
    let limit = if signed {
        let smax = unsigned_max(width - 1);
        if lhs.hi > smax || rhs.hi > smax {
            return None;
        }
        smax
    } else {
        unsigned_max(width)
    };
    match op {
        OverflowOp::AddOverflow => {
            let hi = lhs.hi.checked_add(rhs.hi)?;
            (hi <= limit).then_some(Some(UIntRange {
                lo: lhs.lo + rhs.lo,
                hi,
                width,
            }))
        }
        OverflowOp::MulOverflow => {
            let hi = lhs.hi.checked_mul(rhs.hi)?;
            (hi <= limit).then_some(Some(UIntRange {
                lo: lhs.lo * rhs.lo,
                hi,
                width,
            }))
        }
        OverflowOp::SubOverflow => {
            let value = (lhs.lo >= rhs.hi).then(|| UIntRange {
                lo: lhs.lo - rhs.hi,
                hi: lhs.hi - rhs.lo,
                width,
            });
            // Two non-negative signed values never overflow a difference.
            (signed || value.is_some()).then_some(value)
        }
    }
}

/// The value of `icmp op` on every pair of the intervals' values, when they
/// all agree (the LIR pass's `fold_unsigned_less_than`, for every
/// predicate).
fn fold_compare(op: ICmpOp, width: u32, lhs: UIntRange, rhs: UIntRange) -> Option<bool> {
    if lhs.lo > lhs.hi || rhs.lo > rhs.hi {
        return None;
    }
    let signed = matches!(op, ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge);
    let ((a0, a1), (b0, b1)) = if signed {
        if width < 2 {
            return None;
        }
        // An order-preserving map of the signed values into `u128`.
        let bias = |v: i128| (v as u128) ^ (1u128 << 127);
        let (a, b) = (as_signed(lhs)?, as_signed(rhs)?);
        ((bias(a.0), bias(a.1)), (bias(b.0), bias(b.1)))
    } else {
        ((lhs.lo, lhs.hi), (rhs.lo, rhs.hi))
    };
    let (yes, no) = match op {
        ICmpOp::Eq => (a0 == a1 && b0 == b1 && a0 == b0, a1 < b0 || b1 < a0),
        ICmpOp::Ne => (a1 < b0 || b1 < a0, a0 == a1 && b0 == b1 && a0 == b0),
        ICmpOp::Ult | ICmpOp::Slt => (a1 < b0, a0 >= b1),
        ICmpOp::Ule | ICmpOp::Sle => (a1 <= b0, a0 > b1),
        ICmpOp::Ugt | ICmpOp::Sgt => (a0 > b1, a1 <= b0),
        ICmpOp::Uge | ICmpOp::Sge => (a0 >= b1, a1 < b0),
    };
    if yes {
        Some(true)
    } else if no {
        Some(false)
    } else {
        None
    }
}

/// The signed values of a raw interval that stays on one side of the sign
/// boundary.
fn as_signed(range: UIntRange) -> Option<(i128, i128)> {
    let width = range.width;
    let half = 1u128 << (width - 1);
    let value = |raw: u128| -> i128 {
        if width >= 128 || raw < half {
            raw as i128
        } else {
            raw as i128 - (1i128 << width)
        }
    };
    (range.hi < half || range.lo >= half).then(|| (value(range.lo), value(range.hi)))
}

/// Whether the integer `value` is a value of `(width, signed)`.
fn fits(value: i128, width: u32, signed: bool) -> bool {
    if width >= 128 {
        return signed || value >= 0;
    }
    if signed {
        let half = 1i128 << (width - 1);
        (-half..half).contains(&value)
    } else {
        value >= 0 && value < (1i128 << width)
    }
}

fn premise(value: ValueId, fact: UIntRange) -> RangePremise {
    RangePremise {
        value,
        lo: fact.lo,
        hi: fact.hi,
    }
}

/// `node` with `inst` and `results`, every other field kept.
fn replaced(node: &InstrNode, inst: Inst, results: Vec<ValueId>) -> InstrNode {
    let mut out = node.clone();
    out.inst = inst;
    out.results = results;
    out
}

impl MidPass for RangeRules {
    fn name(&self) -> &'static str {
        RANGE_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let candidate = func.blocks.iter().flat_map(|b| &b.body).any(|n| {
            matches!(
                n.inst,
                Inst::ICmp { .. }
                    | Inst::Overflow { .. }
                    | Inst::Select { .. }
                    | Inst::Assert { .. }
                    | Inst::CondBr { .. }
                    | Inst::Switch { .. }
            )
        });
        if !candidate {
            return None;
        }
        let sources = sources();
        let (facts, state) = Facts::derive(func, cx.pointer_bits, sources);
        let mut witness = RangeWitness::default();
        let mut replacements: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
        let mut folded_branch = false;
        for id in &facts.order {
            let Some(&bi) = facts.positions.get(id) else {
                continue;
            };
            for (ni, node) in func.blocks[bi].body.iter().enumerate() {
                let Some((rule, premises, nodes)) = plan(&facts, *id, node) else {
                    continue;
                };
                folded_branch |= matches!(rule, RangeRule::CondBr | RangeRule::Switch);
                witness.rewrites.push(RangeRewrite {
                    block: *id,
                    index: ni,
                    rule,
                    premises,
                });
                replacements.insert((bi, ni), nodes);
            }
        }
        if witness.rewrites.is_empty() {
            return None;
        }
        for id in &facts.order {
            let block = &func.blocks[facts.positions[id]];
            for (param, _) in &block.params {
                if let Some(Some(fact)) = state.get(param) {
                    witness.invariants.push(RangeInvariant {
                        block: *id,
                        param: *param,
                        lo: fact.lo,
                        hi: fact.hi,
                    });
                }
            }
        }
        let mut out = func.clone();
        let rewritten: HashSet<usize> = replacements.keys().map(|&(b, _)| b).collect();
        for (bi, block) in out.blocks.iter_mut().enumerate() {
            if !rewritten.contains(&bi) {
                continue;
            }
            let body = std::mem::take(&mut block.body);
            block.body = body
                .into_iter()
                .enumerate()
                .flat_map(|(ni, node)| replacements.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
                .collect();
        }
        if folded_branch {
            let reachable: HashSet<BlockId> = TrustIrCfg::new(&out).rpo().into_iter().collect();
            let mut removed_values = HashSet::new();
            for block in &out.blocks {
                if reachable.contains(&block.id) || block.id == out.entry {
                    continue;
                }
                witness.removed_blocks.push(block.id);
                removed_values.extend(block.params.iter().map(|(v, _)| *v));
                for node in &block.body {
                    removed_values.extend(node.results.iter().copied());
                }
            }
            let doomed: HashSet<BlockId> = witness.removed_blocks.iter().copied().collect();
            out.blocks.retain(|b| !doomed.contains(&b.id));
            drop_names(&mut out, &removed_values);
        }
        Some((out, PassWitness::Range(witness)))
    }
}

/// The rule `node` (in block `at`) admits under `facts`: its name, premises
/// and replacement.
fn plan(
    facts: &Facts<'_>,
    at: BlockId,
    node: &InstrNode,
) -> Option<(RangeRule, Vec<RangePremise>, Vec<InstrNode>)> {
    let pb = facts.pointer_bits;
    let get = |value: ValueId, width: u32| facts.fact_at(value, at, width);
    match (&node.inst, node.results.as_slice()) {
        (Inst::ICmp { op, ty, lhs, rhs }, [_]) => {
            let (width, _) = scalar_shape(ty, pb)?;
            let constant = |value: bool| {
                vec![replaced(
                    node,
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(value),
                    },
                    node.results.clone(),
                )]
            };
            if let (Some(a), Some(b)) = (get(*lhs, width), get(*rhs, width))
                && let Some(value) = fold_compare(*op, width, a, b)
            {
                return Some((
                    RangeRule::ICmp,
                    vec![premise(*lhs, a), premise(*rhs, b)],
                    constant(value),
                ));
            }
            let value = facts.implied_at(*op, *lhs, *rhs, width, at)?;
            Some((RangeRule::ICmpImplied, Vec::new(), constant(value)))
        }
        (Inst::Overflow { op, ty, lhs, rhs }, [value, flag]) => {
            let (width, signed) = int_shape(ty, pb)?;
            let (a, b) = (get(*lhs, width)?, get(*rhs, width)?);
            checked_arithmetic_range(*op, width, signed, a, b)?;
            let (rule, arithmetic) = match op {
                OverflowOp::AddOverflow => (RangeRule::AddOverflow, BinOp::Add),
                OverflowOp::SubOverflow => (RangeRule::SubOverflow, BinOp::Sub),
                OverflowOp::MulOverflow => (RangeRule::MulOverflow, BinOp::Mul),
            };
            Some((
                rule,
                vec![premise(*lhs, a), premise(*rhs, b)],
                vec![
                    replaced(
                        node,
                        Inst::BinOp {
                            op: arithmetic,
                            ty: ty.clone(),
                            lhs: *lhs,
                            rhs: *rhs,
                        },
                        vec![*value],
                    ),
                    replaced(
                        node,
                        Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(false),
                        },
                        vec![*flag],
                    ),
                ],
            ))
        }
        (
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            },
            [_],
        ) => {
            let c = get(*cond, 1)?;
            let chosen = match c.exact_value()? {
                1 => *then_val,
                _ => *else_val,
            };
            if facts.types.get(&chosen) != Some(ty) {
                return None;
            }
            Some((
                RangeRule::Select,
                vec![premise(*cond, c)],
                vec![replaced(
                    node,
                    Inst::Copy {
                        ty: ty.clone(),
                        operand: chosen,
                    },
                    node.results.clone(),
                )],
            ))
        }
        (Inst::Assert { cond, .. }, []) => {
            let c = get(*cond, 1)?;
            (c.exact_value()? == 1).then(|| (RangeRule::Assert, vec![premise(*cond, c)], vec![]))
        }
        (
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            },
            [],
        ) => {
            let c = get(*cond, 1)?;
            let (target, args) = match c.exact_value()? {
                1 => (*then_target, then_args.clone()),
                _ => (*else_target, else_args.clone()),
            };
            Some((
                RangeRule::CondBr,
                vec![premise(*cond, c)],
                vec![replaced(node, Inst::Br { target, args }, Vec::new())],
            ))
        }
        (
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                ..
            },
            [],
        ) if facts.sources.switch => {
            let (width, signed) = int_shape(facts.types.get(value)?, pb)?;
            let fact = get(*value, width)?;
            let inst = narrowed_switch(*value, *default, default_args, cases, width, signed, fact)?;
            Some((
                RangeRule::Switch,
                vec![premise(*value, fact)],
                vec![replaced(node, inst, Vec::new())],
            ))
        }
        _ => None,
    }
}

/// The `switch` on `value` with only the cases inside `fact` (a value of
/// `(width, signed)`), whose default is a remaining case's edge when the
/// cases cover `fact`, or the `br` along its one edge; `None` when that is
/// the switch as it is, or a case is not an integer of the value's type.
fn narrowed_switch(
    value: ValueId,
    default: BlockId,
    default_args: &[ValueId],
    cases: &[SwitchCase],
    width: u32,
    signed: bool,
    fact: UIntRange,
) -> Option<Inst> {
    let mut kept: Vec<&SwitchCase> = Vec::new();
    let mut covered = HashSet::new();
    for case in cases {
        let Constant::Int(c) = case.value else {
            return None;
        };
        if !fits(c, width, signed) {
            return None;
        }
        let raw = (c as u128) & unsigned_max(width);
        if (fact.lo..=fact.hi).contains(&raw) {
            kept.push(case);
            covered.insert(raw);
        }
    }
    let span = fact.hi - fact.lo;
    let default_dead = u128::try_from(covered.len()).is_ok_and(|n| n > 0 && n - 1 == span);
    let edge = |target: BlockId, args: &[ValueId]| Inst::Br {
        target,
        args: args.to_vec(),
    };
    if kept.is_empty() {
        return Some(edge(default, default_args));
    }
    if default_dead {
        let (last, rest) = kept.split_last()?;
        if rest
            .iter()
            .all(|c| c.target == last.target && c.args == last.args)
        {
            return Some(edge(last.target, &last.args));
        }
        return Some(Inst::Switch {
            value,
            default: last.target,
            default_args: last.args.clone(),
            cases: rest.iter().map(|c| (*c).clone()).collect(),
            exhaustive_enum_unreachable: false,
        });
    }
    if kept.len() == cases.len() {
        return None;
    }
    Some(Inst::Switch {
        value,
        default,
        default_args: default_args.to_vec(),
        cases: kept.into_iter().cloned().collect(),
        exhaustive_enum_unreachable: false,
    })
}

#[cfg(test)]
pub(crate) mod decisions {
    //! The decision functions and the guard index, for the crate's
    //! brute-force tests.
    use std::collections::HashMap;

    use super::{BlockId, ICmpOp, UIntRange};

    pub(crate) fn refine(
        op: ICmpOp,
        width: u32,
        a: (u128, u128),
        b: (u128, u128),
    ) -> Option<((u128, u128), (u128, u128))> {
        let iv = |(lo, hi): (u128, u128)| UIntRange { lo, hi, width };
        super::refine(op, iv(a), iv(b)).map(|(x, y)| ((x.lo, x.hi), (y.lo, y.hi)))
    }

    pub(crate) fn implied(known: ICmpOp, query: ICmpOp, swapped: bool) -> Option<bool> {
        super::implied(known, query, swapped)
    }

    /// The `members` dominating `at`, nearest first, by the guard index, in
    /// the tree whose node `i > 0` has the parent `parent[i - 1] < i`.
    pub(crate) fn dominating_members(parent: &[usize], members: &[usize], at: usize) -> Vec<usize> {
        let id = |i: usize| BlockId::new(i as u32);
        let order: Vec<BlockId> = (0..=parent.len()).map(id).collect();
        let mut idom: HashMap<BlockId, BlockId> = HashMap::new();
        idom.insert(id(0), id(0));
        for (i, &p) in parent.iter().enumerate() {
            idom.insert(id(i + 1), id(p));
        }
        let spans = super::dominator_spans(&order, &idom);
        let chain = super::Chain::new(members.iter().map(|&m| (id(m), spans[&id(m)])).collect());
        chain
            .over(spans[&id(at)])
            .map(|b| order.iter().position(|o| *o == b).unwrap_or(usize::MAX))
            .collect()
    }
}
