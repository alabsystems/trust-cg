// trust-cg-verify/trust_ir_mid_tv_range.rs - the unsigned-range rules' checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the range rules ([`RangeWitness`]), the trust-ir form of
//! the native lanes' LIR unsigned-range simplification
//! (`trust-cg-opt/src/lir_unsigned_range.rs`).
//!
//! **Facts.** A fact is a closed interval `[lo, hi]` of a value's RAW bit
//! pattern, read unsigned at the width of its type (an integer at the module's
//! pointer width for `isize`/`usize`, one bit for `bool`). This module derives
//! the facts of the SOURCE itself, in reverse postorder of its own walk from
//! the entry, from each value's single definition, its operands read in the
//! block that defines it:
//!
//! | definition | fact |
//! |---|---|
//! | `const` (integer, `bool`) | the constant, masked to the width (the interpreter's `from_i128`) |
//! | `copy T x`, `x` of type `T` | `x`'s |
//! | `and` | `[0, min(hi)]` over the operands with a fact |
//! | `add` / `mul` | `[lo0 + lo1, hi0 + hi1]` / `[lo0 * lo1, hi0 * hi1]` when `hi` does not wrap |
//! | `sub` | `[lo0 - hi1, hi0 - lo1]` when `lo0 >= hi1` |
//! | `lshr x, k` (`k` a fact `[k, k]`, `k < width`) | `x`'s (or the width's) bounds shifted |
//! | `urem x, y` (`y >= 1`) | `[0, min(hi(x), hi(y) - 1)]` |
//! | `zext` (to an equal or wider integer) | the operand's (or its type's full range), at the new width |
//! | `trunc` (to an equal or narrower integer) | the operand's, when its `hi` fits the new width |
//! | `sext` (to an equal or wider integer) | the operand's, when its `hi` is non-negative at its width |
//! | `bitcast` between integers of one width | the operand's (the bits are kept) |
//! | `select` | the chosen arm's when the condition is a fact `[c, c]`, else the hull of both arms' |
//! | `icmp` of scalars | `[c, c]` when the operands' facts, or a dominating compare of the same operands (below), decide it, else `[0, 1]` |
//! | `add/sub/mul.overflow` | when the operands' facts exclude overflow: the flag `[0, 0]`, and the value as `add`/`sub`/`mul` |
//!
//! Loads, calls and every other form have no fact; a block parameter has
//! the interval the witness claims for it, or none. Each row is a property
//! of the defined value on every execution (the interpreter's integer
//! operations, compares and casts fault on a poison operand, so a value with
//! a fact is never poison: `copy` and `select` only move values that have
//! one).
//!
//! **Guards.** A block other than the entry entered by exactly one edge
//! (counting every edge of every terminator, unwind edges included), the
//! `then` (`else`) edge of a `condbr` whose two targets differ, knows its
//! condition is `true` (`false`): the condition's fact there is `[1, 1]`
//! (`[0, 0]`), and when the condition is an `icmp` of scalars the compared
//! values lie in the hull of their values that satisfy it (`narrow_by`:
//! `eq`, `ne`, `ult` and `ule` directly, the signed predicates in biased
//! coordinates, the others by swapping operands), and the compare itself
//! holds as a relation of the two values. Each named value must be defined
//! once, in a block dominating the predecessor. In a block the edge's
//! target dominates (by this module's own dominator tree), the latest
//! binding of each named value is the one the condition was computed from:
//! a later binding would come from a re-execution of its definition after
//! the target, on a path that avoids the target, which dominance rules out.
//! So a value's fact in a block is the refinement of the nearest dominating
//! guard naming it, else its own; nothing flows across a join that another
//! edge reaches. The guards naming each value (relating each pair) are
//! indexed as they are found, in reverse postorder, by the preorder numbers
//! of this module's dominator tree, so the nearest dominating one is found
//! without walking the dominator path ([`GuardIndex`]). An `icmp` of the
//! same two values (either order) is decided by a dominating relation when
//! every 2-bit pair satisfying the relation gives it one outcome
//! (`implication`: every way two values compare unsigned and signed at once
//! occurs among 2-bit values).
//!
//! **Invariants.** The witness may claim an interval for a parameter of a
//! reachable block other than the entry. The facts are derived with every
//! claim assumed, and then every claim is checked on every edge from a
//! reachable block into its block: the argument's fact at the edge's source,
//! narrowed by the edge's own `condbr` condition, must lie inside the claim
//! (an edge that condition rules out is never taken and binds nothing). By
//! induction on the execution every claim holds on every entry to its block:
//! the function's entry binds no claimed parameter, and each edge passes an
//! argument whose fact (derived from bindings that satisfy their facts by
//! the hypothesis) lies inside the claim. A loop header's parameter with an
//! initial value and a back-edge step under a dominating exit test is an
//! induction range of this kind: the claim holds at entry and the step keeps
//! it under the test.
//!
//! **Rules.** Each rewrite names an instruction of the SOURCE, the rule it
//! applies and the PREMISES it relies on: one interval per operand the rule
//! reads, in operand order. A premise is accepted when this module's own
//! fact for that operand, in the rewrite's block, lies inside it; the rule's
//! precondition is then decided on the premises alone:
//!
//! * `icmp` → `const bool c`, when every pair of values in the operands'
//!   intervals compares to `c` (signed predicates on integers whose intervals
//!   each stay on one side of the sign boundary; `bool` operands compare
//!   unsigned);
//! * `icmp_implied` (no premises) → `const bool c`, when a dominating guard's
//!   relation of the same two operands decides the compare to `c`;
//! * `add.overflow` / `sub.overflow` / `mul.overflow` → `add` / `sub` / `mul`
//!   defining the value and `const bool false` defining the flag, when no
//!   pair overflows: unsigned, `hi0 + hi1` / `hi0 * hi1` within the width or
//!   `lo0 >= hi1`; signed, both operands non-negative and `hi0 + hi1` /
//!   `hi0 * hi1` at most the signed maximum (a difference of two
//!   non-negative values never overflows). The interpreter computes the value
//!   of both forms with the same wrapping operation;
//! * `select` → `copy` of the arm a condition `[c, c]` selects;
//! * `assert` of a condition `[1, 1]` → removed;
//! * `condbr` on a condition `[c, c]` → `br` along the edge it selects (its
//!   arguments unchanged);
//! * `switch` on an integer in `[lo, hi]` (every case an integer of its
//!   type) → the cases inside the interval, in order; when their values cover
//!   the interval the default is never taken and the last of them becomes
//!   the default; a `br` when no case is left (the default's edge) or every
//!   remaining edge is one; refused when nothing changes. The rewritten
//!   `switch` claims no exhaustiveness.
//!
//! Each replacement keeps the node's other fields (span, proof material) and
//! its result values. A rewrite is EXACT: a value with a fact is never
//! poison and executes its definition first, so the replaced instruction
//! computes the constant (or arm, or edge) the rule names on every execution
//! that reaches it, and raises nothing (an `assert` that passes does
//! nothing). After the rewrites, the witness may remove blocks unreachable
//! from the entry, whose values no remaining instruction uses.
//!
//! The rebuilt target is exactly the source with the replacements and the
//! removals; [`super::check_pass`] compares it with the claimed target.
//!
//! **Solver obligations.** [`range_obligations`] states each claimed
//! rewrite as an obligation over its premises — `NOT(lhs = rhs)` under the
//! premise intervals (an `icmp_implied` under its dominating relation, a
//! `switch` as the edge each side selects), both sides encoded from the
//! instruction semantics of `trust_ir_semantics` — and [`range_fact_lemmas`]
//! states each fact row, each overflow decision, nine of the compare
//! decisions, the guard narrowings, the induction step and three
//! implications as lemmas over symbolic bounds at one width, with a control
//! that drops its side condition (the compare decisions without a lemma, the
//! narrowing and the implication as whole functions are checked against
//! brute force at small widths by this module's tests). The obligations of the `select`, `assert` and
//! `condbr` rules restate only that a condition in `[k, k]` is `k`: the
//! fact behind the premise is this module's structural check. They go to the `ay` solver through
//! [`crate::ay_bridge::verify_with_ay`] (only an UNSAT answer supports one,
//! and only a certified one is a proof) or to the in-process evaluator
//! ([`crate::lowering_proof::verify_by_evaluation_with_config`], exhaustive
//! where the inputs fit its enumeration). The compile-time check above does
//! not call them, as the wasm32 lane's local validation runs without solver
//! residuals: a compile's evidence for a kept rewrite is this structural
//! check and the interpreter differential, and the lemmas are evidence about
//! the rules, not about one compile.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use trust_cg_lower::instructions::{IntCC, Opcode};
use trust_cg_lower::types::Type;
use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, OverflowOp, Ty,
    ValueId,
};

use super::{
    Defs, MidTvError, WitnessVerdict, block_positions, dominator_tree, drop_names, fits,
    incoming_edges, int_shape, reachable, used_values,
};
use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;
use crate::trust_ir_semantics::{
    encode_trust_ir_binop, encode_trust_ir_icmp, encode_trust_ir_select, encode_trust_ir_sextend,
    encode_trust_ir_uextend, try_encode_trust_ir_bitwise_binop, try_encode_trust_ir_shift,
};

/// The rule a range rewrite applies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RangeRule {
    /// `icmp` decided by its operands' intervals → `const bool`.
    ICmp,
    /// `add.overflow` that cannot overflow → `add` + `const bool false`.
    AddOverflow,
    /// `sub.overflow` that cannot overflow → `sub` + `const bool false`.
    SubOverflow,
    /// `mul.overflow` that cannot overflow → `mul` + `const bool false`.
    MulOverflow,
    /// `select` on a decided condition → `copy` of the selected arm.
    Select,
    /// `assert` of a condition decided true → removed.
    Assert,
    /// `condbr` on a decided condition → `br` along the selected edge.
    CondBr,
    /// `icmp` decided by a dominating compare of the same two operands →
    /// `const bool` (no premises: the checker finds the compare itself).
    ICmpImplied,
    /// `switch` whose value's interval excludes cases (or covers every
    /// remaining one) → the `switch` without them, or a `br`.
    Switch,
}

impl RangeRule {
    /// Every rule, in evidence order.
    pub const ALL: [RangeRule; 9] = [
        RangeRule::ICmp,
        RangeRule::AddOverflow,
        RangeRule::SubOverflow,
        RangeRule::MulOverflow,
        RangeRule::Select,
        RangeRule::Assert,
        RangeRule::CondBr,
        RangeRule::ICmpImplied,
        RangeRule::Switch,
    ];

    /// Stable name for evidence.
    pub const fn as_str(self) -> &'static str {
        match self {
            RangeRule::ICmp => "icmp",
            RangeRule::AddOverflow => "add_overflow",
            RangeRule::SubOverflow => "sub_overflow",
            RangeRule::MulOverflow => "mul_overflow",
            RangeRule::Select => "select",
            RangeRule::Assert => "assert",
            RangeRule::CondBr => "condbr",
            RangeRule::ICmpImplied => "icmp_implied",
            RangeRule::Switch => "switch",
        }
    }
}

/// An interval `[lo, hi]` claimed for the raw bit pattern of `value`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RangePremise {
    pub value: ValueId,
    pub lo: u128,
    pub hi: u128,
}

/// One rewrite: the instruction at `(block, index)` of the SOURCE, the rule,
/// and one premise per operand the rule reads, in operand order (`lhs, rhs`
/// for `icmp` and the overflow rules, the value for `switch`, the condition
/// for the others, none for `icmp_implied`), each about the operand in that
/// block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeRewrite {
    pub block: BlockId,
    pub index: usize,
    pub rule: RangeRule,
    pub premises: Vec<RangePremise>,
}

/// An interval `[lo, hi]` claimed for the raw bit pattern of parameter
/// `param` of `block` on every entry to the block: an inductive invariant,
/// checked on every edge into the block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RangeInvariant {
    pub block: BlockId,
    pub param: ValueId,
    pub lo: u128,
    pub hi: u128,
}

/// The range rules' claim: the rewrites, the blocks removed after them
/// (unreachable once the `condbr` and `switch` rewrites are applied), and
/// the block-parameter invariants the facts behind the premises assume.
/// This witness, its parts and the obligation and lemma builders below are
/// new public surface of the mid-end's evidence, pending the owner's
/// sign-off: additive, used only by `trust-cg-irmid` and this module's
/// tests.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RangeWitness {
    pub rewrites: Vec<RangeRewrite>,
    pub removed_blocks: Vec<BlockId>,
    pub invariants: Vec<RangeInvariant>,
}

impl RangeWitness {
    /// Number of claimed rewrites and removed blocks (an invariant is a
    /// premise, not a rewrite).
    pub fn rewrite_count(&self) -> usize {
        self.rewrites.len() + self.removed_blocks.len()
    }

    /// The claimed rewrites per rule name, the removed blocks under
    /// `removed_block`, and the invariants under `param_interval`.
    pub fn counts(&self) -> BTreeMap<&'static str, usize> {
        let mut counts = BTreeMap::new();
        for rewrite in &self.rewrites {
            *counts.entry(rewrite.rule.as_str()).or_default() += 1;
        }
        if !self.removed_blocks.is_empty() {
            counts.insert("removed_block", self.removed_blocks.len());
        }
        if !self.invariants.is_empty() {
            counts.insert("param_interval", self.invariants.len());
        }
        counts
    }
}

// ---------------------------------------------------------------------------
// Facts
// ---------------------------------------------------------------------------

/// A raw unsigned interval at a width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Iv {
    lo: u128,
    hi: u128,
    bits: u32,
}

impl Iv {
    fn exact(value: u128, bits: u32) -> Self {
        Self {
            lo: value,
            hi: value,
            bits,
        }
    }

    fn full(bits: u32) -> Self {
        Self {
            lo: 0,
            hi: mask(bits),
            bits,
        }
    }

    fn value(self) -> Option<u128> {
        (self.lo == self.hi).then_some(self.lo)
    }
}

/// The largest raw value at `bits`.
fn mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// `(bits, signed)` of a scalar the rules read: an integer (pointer-width
/// ones at `pointer_bits`), or `bool` as one unsigned bit. Vectors, `char`,
/// refinements and every other type have none.
fn scalar(ty: &Ty, pointer_bits: u32) -> Option<(u32, bool)> {
    if *ty == Ty::Bool {
        Some((1, false))
    } else {
        int_shape(ty, pointer_bits)
    }
}

/// This module's typing: [`Defs::value_type`], and the value (`ty`) and
/// flag (`bool`) of an overflow instruction.
struct Types<'f> {
    defs: Defs<'f>,
    overflow: HashMap<ValueId, Ty>,
}

impl<'f> Types<'f> {
    fn of(func: &'f Function) -> Self {
        let mut overflow = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let (Inst::Overflow { ty, .. }, [value, flag]) =
                (&node.inst, node.results.as_slice())
            {
                overflow.entry(*value).or_insert_with(|| ty.clone());
                overflow.entry(*flag).or_insert(Ty::Bool);
            }
        }
        Self {
            defs: Defs::of(func),
            overflow,
        }
    }

    fn value_type(&self, value: ValueId) -> Option<Ty> {
        self.defs
            .value_type(value)
            .or_else(|| self.overflow.get(&value).cloned())
    }
}

/// The intervals a condition leaves itself and its compare's operands.
type Narrowed = Vec<(ValueId, Iv)>;

/// `op lhs, rhs` at `bits` holds: a dominating branch's compare.
#[derive(Debug, Clone, Copy)]
struct Rel {
    op: ICmpOp,
    lhs: ValueId,
    rhs: ValueId,
    bits: u32,
}

/// The dominator tree `idom` (by position, `usize::MAX` unreachable) of
/// the reachable blocks `order` numbered in preorder: each block's number
/// and the largest number in its subtree.
fn tree_numbers(order: &[usize], idom: &[usize], entry: usize) -> Vec<Option<(u32, u32)>> {
    let mut kids: Vec<Vec<usize>> = vec![Vec::new(); idom.len()];
    for &b in order {
        if b != entry && idom[b] != usize::MAX {
            kids[idom[b]].push(b);
        }
    }
    let mut numbers = vec![None; idom.len()];
    if idom.get(entry).is_none_or(|&d| d == usize::MAX) {
        return numbers;
    }
    let mut count = 0u32;
    numbers[entry] = Some((0, 0));
    let mut walk = vec![(entry, 0usize)];
    while let Some((b, next)) = walk.pop() {
        if let Some(&kid) = kids[b].get(next) {
            walk.push((b, next + 1));
            count += 1;
            numbers[kid] = Some((count, count));
            walk.push((kid, 0));
        } else if let Some((_, last)) = numbers[b].as_mut() {
            *last = count;
        }
    }
    numbers
}

/// Whether block `a` dominates block `b` (both by position), by their
/// preorder numbers; `false` when either is unreachable.
fn dominates(tree: &[Option<(u32, u32)>], a: usize, b: usize) -> bool {
    match (
        tree.get(a).copied().flatten(),
        tree.get(b).copied().flatten(),
    ) {
        (Some((pa, la)), Some((pb, _))) => pa <= pb && pb <= la,
        _ => false,
    }
}

/// The guarded blocks naming one key, added in reverse postorder (so every
/// block dominating an added one was added before it), indexed to list the
/// ones dominating a block, nearest first, without walking the dominator
/// path.
#[derive(Debug, Default)]
struct GuardIndex {
    /// Member by preorder number.
    by_number: BTreeMap<u32, usize>,
    /// Each member's block position.
    blocks: Vec<usize>,
    /// Each member's dominating members `1, 2, 4, ...` steps up.
    jumps: Vec<Vec<usize>>,
}

impl GuardIndex {
    fn add(&mut self, tree: &[Option<(u32, u32)>], block: usize) {
        let Some((number, _)) = tree.get(block).copied().flatten() else {
            return;
        };
        if self.by_number.contains_key(&number) {
            return;
        }
        let mut jumps = Vec::new();
        let mut up = self.nearest(tree, block);
        while let Some(m) = up {
            let k = jumps.len();
            jumps.push(m);
            up = self.jumps[m].get(k).copied();
        }
        self.by_number.insert(number, self.blocks.len());
        self.blocks.push(block);
        self.jumps.push(jumps);
    }

    /// The nearest member dominating block `at` (`at` itself included).
    /// Every member dominating `at` dominates the last member numbered at or
    /// before it (whose subtree then holds `at`'s number), so the answer is
    /// that member or the first of its dominating members that dominates
    /// `at`; the jumps find it in logarithmic steps.
    fn nearest(&self, tree: &[Option<(u32, u32)>], at: usize) -> Option<usize> {
        let (number, _) = tree.get(at).copied().flatten()?;
        let (_, &last) = self.by_number.range(..=number).next_back()?;
        let covers = |m: usize| dominates(tree, self.blocks[m], at);
        if covers(last) {
            return Some(last);
        }
        let mut m = last;
        for k in (0..self.jumps[m].len()).rev() {
            if let Some(&j) = self.jumps[m].get(k)
                && !covers(j)
            {
                m = j;
            }
        }
        self.jumps[m].first().copied()
    }

    /// The members dominating block `at` (itself included), nearest first.
    fn over<'a>(
        &'a self,
        tree: &'a [Option<(u32, u32)>],
        at: usize,
    ) -> impl Iterator<Item = usize> + 'a {
        let mut next = self.nearest(tree, at);
        std::iter::from_fn(move || {
            let m = next?;
            next = self.jumps[m].first().copied();
            Some(self.blocks[m])
        })
    }
}

/// The facts of one SOURCE function under a witness's invariants (the
/// module documentation): definitions' facts, the guards of the blocks one
/// conditional edge enters, and the dominator tree they are read through,
/// all by this module's own walks.
struct Env<'f> {
    func: &'f Function,
    pointer_bits: u32,
    types: Types<'f>,
    positions: HashMap<BlockId, usize>,
    /// Every incoming edge of each block, by position.
    preds: Vec<Vec<usize>>,
    /// Reachable blocks in reverse postorder, by position.
    order: Vec<usize>,
    /// Immediate dominators by position (`usize::MAX`: unreachable).
    idom: Vec<usize>,
    entry: usize,
    /// The block defining each value defined once.
    home: HashMap<ValueId, usize>,
    /// Values defined more than once (malformed input): no fact.
    twice: HashSet<ValueId>,
    /// The single-result instruction defining each value.
    sole: HashMap<ValueId, &'f Inst>,
    /// What each block's one conditional incoming edge establishes.
    refined: Vec<Vec<(ValueId, Iv)>>,
    relations: Vec<Vec<Rel>>,
    /// Each reachable block's preorder number in the dominator tree and the
    /// largest number in its subtree, by position.
    tree: Vec<Option<(u32, u32)>>,
    /// The guarded blocks refining each value, and relating each pair of
    /// values (the pair in ascending order).
    refining: HashMap<ValueId, GuardIndex>,
    relating: HashMap<(ValueId, ValueId), GuardIndex>,
    /// Each value's fact from its definition, or its claimed invariant.
    facts: HashMap<ValueId, Iv>,
}

impl<'f> Env<'f> {
    /// Derive the facts of `func` with the parameters of `invariants`
    /// assumed (each must name a parameter of a reachable block other than
    /// the entry, once, inside its type's range); the invariants themselves
    /// are checked by [`Env::check_invariants`].
    fn derive(
        func: &'f Function,
        pointer_bits: u32,
        invariants: &[RangeInvariant],
    ) -> Result<Self, MidTvError> {
        let positions = block_positions(func);
        let preds = incoming_edges(func, &positions);
        let n = func.blocks.len();
        let (order, idom) =
            dominator_tree(func, &positions, &preds).ok_or(MidTvError::TargetDiffers {
                detail: "the source's entry is not a block".to_string(),
            })?;
        let entry = positions[&func.entry];
        let mut home = HashMap::new();
        let mut twice = HashSet::new();
        let mut sole = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            let defined = block.params.iter().map(|(v, _)| *v).chain(
                block
                    .body
                    .iter()
                    .flat_map(|node| node.results.iter().copied()),
            );
            for value in defined {
                if home.insert(value, bi).is_some() {
                    twice.insert(value);
                }
            }
            for node in &block.body {
                if let [result] = node.results.as_slice() {
                    sole.entry(*result).or_insert(&node.inst);
                }
            }
        }
        for value in &twice {
            home.remove(value);
        }
        let mut env = Self {
            func,
            pointer_bits,
            types: Types::of(func),
            positions,
            preds,
            order,
            idom,
            entry,
            home,
            twice,
            sole,
            refined: vec![Vec::new(); n],
            relations: vec![Vec::new(); n],
            tree: Vec::new(),
            refining: HashMap::new(),
            relating: HashMap::new(),
            facts: HashMap::new(),
        };
        env.tree = tree_numbers(&env.order, &env.idom, env.entry);
        let mut claimed = HashSet::new();
        for inv in invariants {
            let bad = |why: &'static str| MidTvError::RangeInvariant {
                block: inv.block,
                value: inv.param,
                why,
            };
            let bi = *env
                .positions
                .get(&inv.block)
                .ok_or(bad("the block is not in the source"))?;
            if bi == env.entry || env.idom[bi] == usize::MAX {
                return Err(bad("the block is the entry or unreachable"));
            }
            let ty = func.blocks[bi]
                .params
                .iter()
                .find(|(v, _)| *v == inv.param)
                .map(|(_, ty)| ty)
                .ok_or(bad("the value is not a parameter of the block"))?;
            let (bits, _) = scalar(ty, pointer_bits).ok_or(bad("the parameter is not a scalar"))?;
            if inv.lo > inv.hi || inv.hi > mask(bits) {
                return Err(bad("the interval is empty or outside the type"));
            }
            if env.twice.contains(&inv.param) || !claimed.insert(inv.param) {
                return Err(bad("the parameter is claimed twice or defined twice"));
            }
            env.facts.insert(
                inv.param,
                Iv {
                    lo: inv.lo,
                    hi: inv.hi,
                    bits,
                },
            );
        }
        for k in 0..env.order.len() {
            let bi = env.order[k];
            env.guard(bi);
            // Every block dominating `bi` precedes it in reverse postorder,
            // so its guard is already indexed.
            let mut refining = std::mem::take(&mut env.refining);
            for (value, _) in &env.refined[bi] {
                refining.entry(*value).or_default().add(&env.tree, bi);
            }
            env.refining = refining;
            let mut relating = std::mem::take(&mut env.relating);
            for rel in &env.relations[bi] {
                let key = if rel.lhs <= rel.rhs {
                    (rel.lhs, rel.rhs)
                } else {
                    (rel.rhs, rel.lhs)
                };
                relating.entry(key).or_default().add(&env.tree, bi);
            }
            env.relating = relating;
            for node in &func.blocks[bi].body {
                env.define(bi, node);
            }
        }
        Ok(env)
    }

    /// Whether `value` is defined once, in a block dominating block `at`.
    fn dominated_by_definition(&self, value: ValueId, at: usize) -> bool {
        let Some(&def) = self.home.get(&value) else {
            return false;
        };
        def == at || dominates(&self.tree, def, at)
    }

    /// The fact of `value` at `bits` in block `at`: the refinement of the
    /// nearest dominating guard naming it, else its own.
    fn fact_at(&self, value: ValueId, at: usize, bits: u32) -> Option<Iv> {
        if let Some(g) = self
            .refining
            .get(&value)
            .and_then(|index| index.over(&self.tree, at).next())
            && let Some((_, iv)) = self.refined[g].iter().find(|(v, _)| *v == value)
        {
            return Some(*iv).filter(|iv| iv.bits == bits);
        }
        at_bits(&self.facts, value, bits)
    }

    /// The outcome of `op lhs, rhs` at `bits` that a dominating guard's
    /// compare of the same two values decides in block `at`.
    fn implied_at(
        &self,
        op: ICmpOp,
        lhs: ValueId,
        rhs: ValueId,
        bits: u32,
        at: usize,
    ) -> Option<bool> {
        self.implying(op, lhs, rhs, bits, at).map(|(_, _, c)| c)
    }

    /// The nearest dominating guard's compare that decides `op lhs, rhs` at
    /// `bits` in block `at`: the compare, whether its operands are swapped,
    /// and the outcome.
    fn implying(
        &self,
        op: ICmpOp,
        lhs: ValueId,
        rhs: ValueId,
        bits: u32,
        at: usize,
    ) -> Option<(Rel, bool, bool)> {
        let key = if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) };
        let index = self.relating.get(&key)?;
        for g in index.over(&self.tree, at) {
            for rel in &self.relations[g] {
                if rel.bits != bits {
                    continue;
                }
                for swapped in [false, true] {
                    let same = if swapped {
                        (rel.lhs, rel.rhs) == (rhs, lhs)
                    } else {
                        (rel.lhs, rel.rhs) == (lhs, rhs)
                    };
                    if same && let Some(c) = implication(rel.op, op, swapped) {
                        return Some((*rel, swapped, c));
                    }
                }
            }
        }
        None
    }

    /// What `cond` being `holds` establishes at the end of block `at`, when
    /// `cond` is defined over it: `None` inside when it cannot be `holds`,
    /// else the intervals it leaves (itself, and an integer compare's two
    /// operands), and the compare as a relation.
    fn condition(
        &self,
        cond: ValueId,
        at: usize,
        holds: bool,
    ) -> Option<(Option<Narrowed>, Option<Rel>)> {
        if !self.dominated_by_definition(cond, at) {
            return None;
        }
        let truth = Iv::exact(u128::from(holds), 1);
        if let Some(own) = self.fact_at(cond, at, 1)
            && (truth.lo < own.lo || truth.lo > own.hi)
        {
            return Some((None, None));
        }
        let mut out = vec![(cond, truth)];
        let Some(Inst::ICmp { op, ty, lhs, rhs }) = self.sole.get(&cond).copied() else {
            return Some((Some(out), None));
        };
        let Some((bits, _)) = scalar(ty, self.pointer_bits) else {
            return Some((Some(out), None));
        };
        if !self.dominated_by_definition(*lhs, at) || !self.dominated_by_definition(*rhs, at) {
            return Some((Some(out), None));
        }
        let op = if holds { *op } else { opposite(*op) };
        let rel = Rel {
            op,
            lhs: *lhs,
            rhs: *rhs,
            bits,
        };
        let a = self.fact_at(*lhs, at, bits).unwrap_or(Iv::full(bits));
        let b = self.fact_at(*rhs, at, bits).unwrap_or(Iv::full(bits));
        let Some((x, y)) = narrow_by(op, a, b) else {
            return Some((None, Some(rel)));
        };
        if lhs == rhs {
            let lo = x.lo.max(y.lo);
            let hi = x.hi.min(y.hi);
            if lo > hi {
                return Some((None, Some(rel)));
            }
            out.push((*lhs, Iv { lo, hi, bits }));
        } else {
            out.push((*lhs, x));
            out.push((*rhs, y));
        }
        Some((Some(out), Some(rel)))
    }

    /// The guard of block `bi`: what its one incoming edge establishes, when
    /// that edge is the `then` or `else` edge of a `condbr` whose targets
    /// differ.
    fn guard(&mut self, bi: usize) {
        if bi == self.entry {
            return;
        }
        let [p] = self.preds[bi].as_slice() else {
            return;
        };
        let p = *p;
        let id = self.func.blocks[bi].id;
        let Some(Inst::CondBr {
            cond,
            then_target,
            else_target,
            ..
        }) = self.func.blocks[p].body.last().map(|n| &n.inst)
        else {
            return;
        };
        if then_target == else_target {
            return;
        }
        if let Some((Some(refined), rel)) = self.condition(*cond, p, *then_target == id) {
            self.refined[bi] = refined;
            self.relations[bi] = rel.into_iter().collect();
        }
    }

    /// Record the facts `node`, in block `at`, defines.
    fn define(&mut self, at: usize, node: &InstrNode) {
        match (node.results.as_slice(), &node.inst) {
            (
                [value, flag],
                Inst::Overflow {
                    op, ty, lhs, rhs, ..
                },
            ) => {
                if let Some((bits, signed)) = int_shape(ty, self.pointer_bits)
                    && let (Some(a), Some(b)) =
                        (self.fact_at(*lhs, at, bits), self.fact_at(*rhs, at, bits))
                    && let Some((value_fact, flag_fact)) = overflow_facts(*op, bits, signed, a, b)
                {
                    if let Some(fact) = value_fact
                        && !self.twice.contains(value)
                    {
                        self.facts.insert(*value, fact);
                    }
                    if !self.twice.contains(flag) {
                        self.facts.insert(*flag, flag_fact);
                    }
                }
            }
            ([result], inst) if !self.twice.contains(result) => {
                if let Some(fact) = self.fact_of(at, inst) {
                    self.facts.insert(*result, fact);
                }
            }
            _ => {}
        }
    }

    /// The fact the single-result `inst`, in block `at`, defines (the module
    /// documentation's table).
    fn fact_of(&self, at: usize, inst: &Inst) -> Option<Iv> {
        let pointer_bits = self.pointer_bits;
        let get = |value: ValueId, bits: u32| self.fact_at(value, at, bits);
        match inst {
            Inst::Const { ty, value } => {
                let (bits, _) = scalar(ty, pointer_bits)?;
                match value {
                    Constant::Int(v) if bits > 1 => {
                        Some(Iv::exact((*v as u128) & mask(bits), bits))
                    }
                    Constant::Bool(b) if bits == 1 => Some(Iv::exact(u128::from(*b), 1)),
                    _ => None,
                }
            }
            Inst::Copy { ty, operand } => {
                let (bits, _) = scalar(ty, pointer_bits)?;
                if self.types.value_type(*operand).as_ref() != Some(ty) {
                    return None;
                }
                get(*operand, bits)
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                let (bits, _) = int_shape(ty, pointer_bits)?;
                let a = get(*lhs, bits);
                let b = get(*rhs, bits);
                match op {
                    BinOp::And => {
                        let hi = match (a, b) {
                            (Some(a), Some(b)) => a.hi.min(b.hi),
                            (Some(x), None) | (None, Some(x)) => x.hi,
                            (None, None) => return None,
                        };
                        Some(Iv { lo: 0, hi, bits })
                    }
                    BinOp::Add => {
                        let (a, b) = (a?, b?);
                        let hi = a.hi.checked_add(b.hi)?;
                        (hi <= mask(bits)).then(|| Iv {
                            lo: a.lo + b.lo,
                            hi,
                            bits,
                        })
                    }
                    BinOp::Mul => {
                        let (a, b) = (a?, b?);
                        let hi = a.hi.checked_mul(b.hi)?;
                        (hi <= mask(bits)).then(|| Iv {
                            lo: a.lo * b.lo,
                            hi,
                            bits,
                        })
                    }
                    BinOp::Sub => {
                        let (a, b) = (a?, b?);
                        (a.lo >= b.hi).then(|| Iv {
                            lo: a.lo - b.hi,
                            hi: a.hi - b.lo,
                            bits,
                        })
                    }
                    BinOp::LShr => {
                        let k = b?.value()?;
                        if k >= u128::from(bits) {
                            return None;
                        }
                        let a = a.unwrap_or(Iv::full(bits));
                        Some(Iv {
                            lo: a.lo >> k,
                            hi: a.hi >> k,
                            bits,
                        })
                    }
                    BinOp::URem => {
                        let b = b?;
                        if b.lo == 0 {
                            return None;
                        }
                        let hi = a.map_or(mask(bits), |a| a.hi).min(b.hi - 1);
                        Some(Iv { lo: 0, hi, bits })
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
                let (src_bits, _) = scalar(src_ty, pointer_bits)?;
                let (dst_bits, _) = int_shape(dst_ty, pointer_bits)?;
                match op {
                    CastOp::ZExt if dst_bits >= src_bits => {
                        let a = get(*operand, src_bits).unwrap_or(Iv::full(src_bits));
                        Some(Iv {
                            bits: dst_bits,
                            ..a
                        })
                    }
                    CastOp::Trunc if dst_bits <= src_bits => {
                        let a = get(*operand, src_bits)?;
                        (a.hi <= mask(dst_bits)).then_some(Iv {
                            bits: dst_bits,
                            ..a
                        })
                    }
                    CastOp::SExt if dst_bits >= src_bits && src_bits > 1 => {
                        let a = get(*operand, src_bits)?;
                        (a.hi <= mask(src_bits - 1)).then_some(Iv {
                            bits: dst_bits,
                            ..a
                        })
                    }
                    // Between two integers of one width the bits are kept.
                    CastOp::Bitcast
                        if dst_bits == src_bits && int_shape(src_ty, pointer_bits).is_some() =>
                    {
                        get(*operand, src_bits)
                    }
                    _ => None,
                }
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                let (bits, _) = scalar(ty, pointer_bits)?;
                match get(*cond, 1).and_then(Iv::value) {
                    Some(1) => get(*then_val, bits),
                    Some(_) => get(*else_val, bits),
                    None => {
                        let a = get(*then_val, bits)?;
                        let b = get(*else_val, bits)?;
                        Some(Iv {
                            lo: a.lo.min(b.lo),
                            hi: a.hi.max(b.hi),
                            bits,
                        })
                    }
                }
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let (bits, _) = scalar(ty, pointer_bits)?;
                let by_intervals = match (get(*lhs, bits), get(*rhs, bits)) {
                    (Some(a), Some(b)) => decide_icmp(*op, bits, a, b),
                    _ => None,
                };
                let decided = by_intervals.or_else(|| self.implied_at(*op, *lhs, *rhs, bits, at));
                Some(match decided {
                    Some(c) => Iv::exact(u128::from(c), 1),
                    None => Iv {
                        lo: 0,
                        hi: 1,
                        bits: 1,
                    },
                })
            }
            _ => None,
        }
    }

    /// The fact of the `i`-th argument the `k`-th successor edge of block
    /// `source` passes, refined by that edge's `condbr` condition:
    /// `Ok(None)` when the condition rules the edge out.
    fn edge_argument(
        &self,
        source: usize,
        k: usize,
        i: usize,
        bits: u32,
    ) -> Result<Option<Iv>, &'static str> {
        let last = self.func.blocks[source]
            .body
            .last()
            .ok_or("the source block has no terminator")?;
        let edges = last.inst.successor_edges();
        let edge = edges.get(k).ok_or("no such edge")?;
        let params = self
            .positions
            .get(&edge.target)
            .map_or(0, |&t| self.func.blocks[t].params.len());
        if edge.args.len() != params {
            return Err("an edge does not bind every parameter");
        }
        let arg = edge.args[i];
        let mut fact = self.fact_at(arg, source, bits);
        if let Inst::CondBr { cond, .. } = &last.inst
            && let Some((refined, _)) = self.condition(*cond, source, k == 0)
        {
            let Some(refined) = refined else {
                return Ok(None);
            };
            for (value, iv) in refined {
                if value != arg || iv.bits != bits {
                    continue;
                }
                fact = Some(match fact {
                    None => iv,
                    Some(f) => {
                        let (lo, hi) = (f.lo.max(iv.lo), f.hi.min(iv.hi));
                        if lo > hi {
                            return Ok(None);
                        }
                        Iv { lo, hi, bits }
                    }
                });
            }
        }
        fact.map(Some).ok_or("an argument has no interval")
    }

    /// Every claimed invariant holds on every edge from a reachable block
    /// into its block: the argument's fact there (under every invariant,
    /// the edge's own condition included) lies inside it. By induction on
    /// the execution, each holds on every entry to its block.
    fn check_invariants(&self, invariants: &[RangeInvariant]) -> Result<(), MidTvError> {
        let mut claims: HashMap<usize, Vec<(usize, RangeInvariant)>> = HashMap::new();
        for inv in invariants {
            let bi = self.positions[&inv.block];
            let i = self.func.blocks[bi]
                .params
                .iter()
                .position(|(v, _)| *v == inv.param)
                .expect("checked by derive");
            claims.entry(bi).or_default().push((i, *inv));
        }
        for &source in &self.order {
            let Some(last) = self.func.blocks[source].body.last() else {
                continue;
            };
            for (k, edge) in last.inst.successor_edges().iter().enumerate() {
                let Some(&target) = self.positions.get(&edge.target) else {
                    continue;
                };
                for (i, inv) in claims.get(&target).into_iter().flatten() {
                    let bad = |why: &'static str| MidTvError::RangeInvariant {
                        block: inv.block,
                        value: inv.param,
                        why,
                    };
                    let bits = self.facts[&inv.param].bits;
                    match self.edge_argument(source, k, *i, bits) {
                        Ok(None) => {}
                        Ok(Some(f)) if inv.lo <= f.lo && f.hi <= inv.hi => {}
                        Ok(Some(_)) => {
                            return Err(bad("an edge passes an argument outside the interval"));
                        }
                        Err(why) => return Err(bad(why)),
                    }
                }
            }
        }
        Ok(())
    }
}

/// The fact of `value` at width `bits`, if it has one at that width.
fn at_bits(facts: &HashMap<ValueId, Iv>, value: ValueId, bits: u32) -> Option<Iv> {
    facts.get(&value).copied().filter(|fact| fact.bits == bits)
}

/// The predicate true exactly where `op` is false.
fn opposite(op: ICmpOp) -> ICmpOp {
    match op {
        ICmpOp::Eq => ICmpOp::Ne,
        ICmpOp::Ne => ICmpOp::Eq,
        ICmpOp::Ult => ICmpOp::Uge,
        ICmpOp::Uge => ICmpOp::Ult,
        ICmpOp::Ule => ICmpOp::Ugt,
        ICmpOp::Ugt => ICmpOp::Ule,
        ICmpOp::Slt => ICmpOp::Sge,
        ICmpOp::Sge => ICmpOp::Slt,
        ICmpOp::Sle => ICmpOp::Sgt,
        ICmpOp::Sgt => ICmpOp::Sle,
    }
}

/// The values `x` of `a` and `y` of `b` with `op x, y` true, as the hull of
/// each side's (`None` when there is no such pair). `eq`, `ne`, `ult` and
/// `ule` directly (the other unsigned and signed predicates swap their
/// operands into `ult`/`ule`/`slt`/`sle`); `slt`/`sle` in the biased
/// coordinates `raw ^ 2^(bits-1)`, where signed order is unsigned order: an
/// interval crossing the sign boundary is two biased intervals, each pair is
/// narrowed unsigned and the survivors map back. A signed predicate on one
/// bit narrows nothing.
fn narrow_by(op: ICmpOp, a: Iv, b: Iv) -> Option<(Iv, Iv)> {
    let flip = |pair: Option<(Iv, Iv)>| pair.map(|(x, y)| (y, x));
    match op {
        ICmpOp::Ugt => flip(narrow_by(ICmpOp::Ult, b, a)),
        ICmpOp::Uge => flip(narrow_by(ICmpOp::Ule, b, a)),
        ICmpOp::Sgt => flip(narrow_by(ICmpOp::Slt, b, a)),
        ICmpOp::Sge => flip(narrow_by(ICmpOp::Sle, b, a)),
        ICmpOp::Slt | ICmpOp::Sle if a.bits < 2 => Some((a, b)),
        ICmpOp::Slt | ICmpOp::Sle => {
            let unsigned = if op == ICmpOp::Slt {
                ICmpOp::Ult
            } else {
                ICmpOp::Ule
            };
            let sign = 1u128 << (a.bits - 1);
            // The biased intervals of `iv` (biasing is its own inverse).
            let biased = |iv: Iv| -> Vec<Iv> {
                if iv.lo < sign && iv.hi >= sign {
                    vec![
                        Iv {
                            lo: iv.lo ^ sign,
                            hi: mask(iv.bits),
                            bits: iv.bits,
                        },
                        Iv {
                            lo: 0,
                            hi: iv.hi ^ sign,
                            bits: iv.bits,
                        },
                    ]
                } else {
                    vec![Iv {
                        lo: iv.lo ^ sign,
                        hi: iv.hi ^ sign,
                        bits: iv.bits,
                    }]
                }
            };
            let back = |iv: Iv| Iv {
                lo: iv.lo ^ sign,
                hi: iv.hi ^ sign,
                bits: iv.bits,
            };
            let mut xs: Vec<Iv> = Vec::new();
            let mut ys: Vec<Iv> = Vec::new();
            for pa in biased(a) {
                for pb in biased(b) {
                    if let Some((x, y)) = narrow_by(unsigned, pa, pb) {
                        xs.push(back(x));
                        ys.push(back(y));
                    }
                }
            }
            let hull = |v: &[Iv]| -> Option<Iv> {
                Some(Iv {
                    lo: v.iter().map(|iv| iv.lo).min()?,
                    hi: v.iter().map(|iv| iv.hi).max()?,
                    bits: a.bits,
                })
            };
            Some((hull(&xs)?, hull(&ys)?))
        }
        ICmpOp::Ult => {
            if a.lo >= b.hi {
                return None;
            }
            Some((
                Iv {
                    hi: a.hi.min(b.hi - 1),
                    ..a
                },
                Iv {
                    lo: b.lo.max(a.lo + 1),
                    ..b
                },
            ))
        }
        ICmpOp::Ule => {
            if a.lo > b.hi {
                return None;
            }
            Some((
                Iv {
                    hi: a.hi.min(b.hi),
                    ..a
                },
                Iv {
                    lo: b.lo.max(a.lo),
                    ..b
                },
            ))
        }
        ICmpOp::Eq => {
            let (lo, hi) = (a.lo.max(b.lo), a.hi.min(b.hi));
            (lo <= hi).then_some((Iv { lo, hi, ..a }, Iv { lo, hi, ..b }))
        }
        ICmpOp::Ne => {
            // An endpoint equal to the other side's only value goes.
            let trim = |r: Iv, other: Iv| -> Option<Iv> {
                if other.lo != other.hi {
                    return Some(r);
                }
                let c = other.lo;
                match (r.lo == c, r.hi == c) {
                    (true, true) => None,
                    (true, false) => Some(Iv { lo: c + 1, ..r }),
                    (false, true) => Some(Iv { hi: c - 1, ..r }),
                    (false, false) => Some(r),
                }
            };
            Some((trim(a, b)?, trim(b, a)?))
        }
    }
}

/// The value of `query x, y` on every pair of 2-bit values where `known x,
/// y` (`swapped`: `known y, x`) holds, when they all agree. Every way two
/// values can compare unsigned and signed at once (equal; less or greater
/// in each order) occurs among 2-bit values, so an outcome common to all of
/// them holds at every width of two bits or more; at one bit fewer of those
/// ways occur, so it holds there too.
fn implication(known: ICmpOp, query: ICmpOp, swapped: bool) -> Option<bool> {
    let compare = |op: ICmpOp, x: u128, y: u128| {
        decide_icmp(op, 2, Iv::exact(x, 2), Iv::exact(y, 2)).expect("exact intervals decide")
    };
    let mut outcome = None;
    for x in 0..4u128 {
        for y in 0..4u128 {
            let premise = if swapped {
                compare(known, y, x)
            } else {
                compare(known, x, y)
            };
            if !premise {
                continue;
            }
            let value = compare(query, x, y);
            match outcome {
                None => outcome = Some(value),
                Some(v) if v != value => return None,
                Some(_) => {}
            }
        }
    }
    outcome
}

/// The facts of an overflow instruction's value and flag, when its
/// operands' facts exclude overflow (the value's only where it is an
/// unsigned interval: a signed difference may be negative).
fn overflow_facts(
    op: OverflowOp,
    bits: u32,
    signed: bool,
    a: Iv,
    b: Iv,
) -> Option<(Option<Iv>, Iv)> {
    if !cannot_overflow(op, bits, signed, a, b) {
        return None;
    }
    let value = match op {
        OverflowOp::AddOverflow => Some(Iv {
            lo: a.lo + b.lo,
            hi: a.hi + b.hi,
            bits,
        }),
        OverflowOp::MulOverflow => Some(Iv {
            lo: a.lo * b.lo,
            hi: a.hi * b.hi,
            bits,
        }),
        OverflowOp::SubOverflow => (a.lo >= b.hi).then(|| Iv {
            lo: a.lo - b.hi,
            hi: a.hi - b.lo,
            bits,
        }),
    };
    Some((value, Iv::exact(0, 1)))
}

/// Whether no pair of values in `a` and `b` overflows `op` at `bits`
/// (`signed` selects the interpreter's signed or unsigned flag).
fn cannot_overflow(op: OverflowOp, bits: u32, signed: bool, a: Iv, b: Iv) -> bool {
    if !signed {
        return match op {
            OverflowOp::AddOverflow => a.hi.checked_add(b.hi).is_some_and(|hi| hi <= mask(bits)),
            OverflowOp::SubOverflow => a.lo >= b.hi,
            OverflowOp::MulOverflow => a.hi.checked_mul(b.hi).is_some_and(|hi| hi <= mask(bits)),
        };
    }
    // Both operands non-negative: their raw patterns are their values.
    let smax = mask(bits - 1);
    if a.hi > smax || b.hi > smax {
        return false;
    }
    match op {
        OverflowOp::AddOverflow => a.hi.checked_add(b.hi).is_some_and(|hi| hi <= smax),
        OverflowOp::SubOverflow => true,
        OverflowOp::MulOverflow => a.hi.checked_mul(b.hi).is_some_and(|hi| hi <= smax),
    }
}

/// The interval of signed values a raw interval at `bits` holds, when it
/// does not straddle the sign boundary.
fn signed_interval(iv: Iv) -> Option<(i128, i128)> {
    let bits = iv.bits;
    let half = 1u128 << (bits - 1);
    let to_signed = |raw: u128| -> i128 {
        if bits >= 128 {
            raw as i128
        } else if raw >= half {
            raw as i128 - (1i128 << bits)
        } else {
            raw as i128
        }
    };
    if iv.hi < half || iv.lo >= half {
        Some((to_signed(iv.lo), to_signed(iv.hi)))
    } else {
        None
    }
}

/// The outcome of `icmp op` on every pair of values in `a` and `b` at
/// `bits`, when they all agree. Signed predicates read integers only (`bits >
/// 1`), and each interval must stay on one side of the sign boundary.
fn decide_icmp_raw(op: ICmpOp, bits: u32, a: (u128, u128), b: (u128, u128)) -> Option<bool> {
    decide_icmp(
        op,
        bits,
        Iv {
            lo: a.0,
            hi: a.1,
            bits,
        },
        Iv {
            lo: b.0,
            hi: b.1,
            bits,
        },
    )
}

fn decide_icmp(op: ICmpOp, bits: u32, a: Iv, b: Iv) -> Option<bool> {
    fn order<T: Ord + Copy>(op: ICmpOp, a: (T, T), b: (T, T)) -> Option<bool> {
        let ((a0, a1), (b0, b1)) = (a, b);
        let (always, never) = match op {
            ICmpOp::Eq => (a0 == a1 && b0 == b1 && a0 == b0, a1 < b0 || b1 < a0),
            ICmpOp::Ne => (a1 < b0 || b1 < a0, a0 == a1 && b0 == b1 && a0 == b0),
            ICmpOp::Ult | ICmpOp::Slt => (a1 < b0, a0 >= b1),
            ICmpOp::Ule | ICmpOp::Sle => (a1 <= b0, a0 > b1),
            ICmpOp::Ugt | ICmpOp::Sgt => (a0 > b1, a1 <= b0),
            ICmpOp::Uge | ICmpOp::Sge => (a0 >= b1, a1 < b0),
        };
        if always {
            Some(true)
        } else if never {
            Some(false)
        } else {
            None
        }
    }
    if a.lo > a.hi || b.lo > b.hi {
        return None;
    }
    match op {
        ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge => {
            if bits < 2 {
                return None;
            }
            order(op, signed_interval(a)?, signed_interval(b)?)
        }
        _ => order(op, (a.lo, a.hi), (b.lo, b.hi)),
    }
}

// ---------------------------------------------------------------------------
// The rewrite check
// ---------------------------------------------------------------------------

/// The premise intervals of `rewrite` for `operands`, each containing this
/// module's fact of its operand (at `bits`) in the rewrite's block `at`.
fn premises(
    env: &Env<'_>,
    at: usize,
    rewrite: &RangeRewrite,
    operands: &[(ValueId, u32)],
) -> Result<Vec<Iv>, MidTvError> {
    if rewrite.premises.len() != operands.len() {
        return Err(MidTvError::RangeUndecided {
            block: rewrite.block,
            index: rewrite.index,
            why: "the premises do not name the rule's operands",
        });
    }
    let mut out = Vec::new();
    for (premise, &(operand, bits)) in rewrite.premises.iter().zip(operands) {
        if premise.value != operand {
            return Err(MidTvError::RangeUndecided {
                block: rewrite.block,
                index: rewrite.index,
                why: "the premises do not name the rule's operands",
            });
        }
        let derived = env.fact_at(operand, at, bits);
        let holds = derived.is_some_and(|fact| {
            premise.lo <= premise.hi && premise.lo <= fact.lo && fact.hi <= premise.hi
        });
        if !holds {
            return Err(MidTvError::RangePremise {
                value: operand,
                claimed: (premise.lo, premise.hi),
                derived: derived.map(|fact| (fact.lo, fact.hi)),
            });
        }
        out.push(Iv {
            lo: premise.lo,
            hi: premise.hi,
            bits,
        });
    }
    Ok(out)
}

/// `node` with `inst` in place of its instruction and `results` as its
/// results, every other field kept.
fn replaced(node: &InstrNode, inst: Inst, results: Vec<ValueId>) -> InstrNode {
    let mut out = node.clone();
    out.inst = inst;
    out.results = results;
    out
}

/// The terminator a `switch` on a value of `(bits, signed)` in `[lo, hi]`
/// (the premise) becomes: its cases outside the interval dropped (each an
/// integer of the value's type, or the rule does not apply); when the
/// remaining cases' values cover the interval, the default is never taken
/// and the last remaining case becomes it (a value matching that case
/// first now reaches it as the default); and a `br` when one edge is left.
/// `Err` when the rule does not apply or changes nothing.
fn switch_after(inst: &Inst, bits: u32, signed: bool, interval: Iv) -> Result<Inst, &'static str> {
    let Inst::Switch {
        value,
        default,
        default_args,
        cases,
        ..
    } = inst
    else {
        return Err("the instruction is not the rule's form");
    };
    let mut inside = Vec::new();
    let mut values = BTreeSet::new();
    for case in cases {
        let Constant::Int(c) = case.value else {
            return Err("a case is not an integer constant");
        };
        if !fits(c, bits, signed) {
            return Err("a case is not a value of the switched type");
        }
        let raw = (c as u128) & mask(bits);
        if interval.lo <= raw && raw <= interval.hi {
            inside.push(case.clone());
            values.insert(raw);
        }
    }
    let covered = u128::try_from(values.len()).unwrap_or(u128::MAX);
    let default_dead = covered > 0 && covered - 1 == interval.hi - interval.lo;
    let Some(last) = inside.last().cloned() else {
        return Ok(Inst::Br {
            target: *default,
            args: default_args.clone(),
        });
    };
    if default_dead {
        inside.pop();
        if inside
            .iter()
            .all(|c| c.target == last.target && c.args == last.args)
        {
            return Ok(Inst::Br {
                target: last.target,
                args: last.args,
            });
        }
        return Ok(Inst::Switch {
            value: *value,
            default: last.target,
            default_args: last.args,
            cases: inside,
            exhaustive_enum_unreachable: false,
        });
    }
    if inside.len() == cases.len() {
        return Err("the interval excludes no case and not the default");
    }
    Ok(Inst::Switch {
        value: *value,
        default: *default,
        default_args: default_args.clone(),
        cases: inside,
        exhaustive_enum_unreachable: false,
    })
}

/// The replacement of the source node `node` (in block `at`) that
/// `rewrite` claims, after checking the rule's shape and its precondition
/// on the premises.
fn rewrite_node(
    env: &Env<'_>,
    at: usize,
    rewrite: &RangeRewrite,
    node: &InstrNode,
) -> Result<Vec<InstrNode>, MidTvError> {
    let pointer_bits = env.pointer_bits;
    let undecided = |why: &'static str| MidTvError::RangeUndecided {
        block: rewrite.block,
        index: rewrite.index,
        why,
    };
    let overflow_op = match rewrite.rule {
        RangeRule::AddOverflow => Some(OverflowOp::AddOverflow),
        RangeRule::SubOverflow => Some(OverflowOp::SubOverflow),
        RangeRule::MulOverflow => Some(OverflowOp::MulOverflow),
        _ => None,
    };
    let constant = |c: bool| {
        vec![replaced(
            node,
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(c),
            },
            node.results.clone(),
        )]
    };
    match (rewrite.rule, &node.inst, node.results.as_slice()) {
        (RangeRule::ICmp, Inst::ICmp { op, ty, lhs, rhs }, [_]) => {
            let (bits, _) = scalar(ty, pointer_bits).ok_or(undecided("not a scalar compare"))?;
            let p = premises(env, at, rewrite, &[(*lhs, bits), (*rhs, bits)])?;
            let c = decide_icmp(*op, bits, p[0], p[1])
                .ok_or(undecided("the premises do not decide the compare"))?;
            Ok(constant(c))
        }
        (RangeRule::ICmpImplied, Inst::ICmp { op, ty, lhs, rhs }, [_]) => {
            let (bits, _) = scalar(ty, pointer_bits).ok_or(undecided("not a scalar compare"))?;
            premises(env, at, rewrite, &[])?;
            let c = env
                .implied_at(*op, *lhs, *rhs, bits, at)
                .ok_or(undecided("no dominating compare decides the compare"))?;
            Ok(constant(c))
        }
        (
            _,
            Inst::Overflow {
                op, ty, lhs, rhs, ..
            },
            [value, flag],
        ) if overflow_op == Some(*op) => {
            let (bits, signed) =
                int_shape(ty, pointer_bits).ok_or(undecided("not an integer overflow"))?;
            let p = premises(env, at, rewrite, &[(*lhs, bits), (*rhs, bits)])?;
            if !cannot_overflow(*op, bits, signed, p[0], p[1]) {
                return Err(undecided("the premises do not exclude overflow"));
            }
            let arithmetic = match op {
                OverflowOp::AddOverflow => BinOp::Add,
                OverflowOp::SubOverflow => BinOp::Sub,
                OverflowOp::MulOverflow => BinOp::Mul,
            };
            Ok(vec![
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
            ])
        }
        (
            RangeRule::Select,
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            },
            [_],
        ) => {
            let p = premises(env, at, rewrite, &[(*cond, 1)])?;
            let chosen = match p[0].value() {
                Some(1) => *then_val,
                Some(0) => *else_val,
                _ => return Err(undecided("the condition is not decided")),
            };
            if env.types.value_type(chosen).as_ref() != Some(ty) {
                return Err(undecided("the selected arm's type is not the select's"));
            }
            Ok(vec![replaced(
                node,
                Inst::Copy {
                    ty: ty.clone(),
                    operand: chosen,
                },
                node.results.clone(),
            )])
        }
        (RangeRule::Assert, Inst::Assert { cond, .. }, []) => {
            let p = premises(env, at, rewrite, &[(*cond, 1)])?;
            if p[0].value() != Some(1) {
                return Err(undecided("the condition is not decided true"));
            }
            Ok(Vec::new())
        }
        (
            RangeRule::CondBr,
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            },
            [],
        ) => {
            let p = premises(env, at, rewrite, &[(*cond, 1)])?;
            let (target, args) = match p[0].value() {
                Some(1) => (*then_target, then_args.clone()),
                Some(0) => (*else_target, else_args.clone()),
                _ => return Err(undecided("the condition is not decided")),
            };
            Ok(vec![replaced(node, Inst::Br { target, args }, Vec::new())])
        }
        (RangeRule::Switch, inst @ Inst::Switch { value, .. }, []) => {
            let ty = env
                .types
                .value_type(*value)
                .ok_or(undecided("the switched value's type is unknown"))?;
            let (bits, signed) = int_shape(&ty, pointer_bits)
                .ok_or(undecided("the switched value is not an integer"))?;
            let p = premises(env, at, rewrite, &[(*value, bits)])?;
            let after = switch_after(inst, bits, signed, p[0]).map_err(undecided)?;
            Ok(vec![replaced(node, after, Vec::new())])
        }
        _ => Err(undecided("the instruction is not the rule's form")),
    }
}

pub(super) fn rebuild_range(
    _module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &RangeWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let env = Env::derive(source, pointer_bits, &witness.invariants)?;
    env.check_invariants(&witness.invariants)?;
    let mut replacements: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
    for rewrite in &witness.rewrites {
        let no_instruction = MidTvError::NoInstruction {
            block: rewrite.block,
            index: rewrite.index,
        };
        let Some(&bi) = env.positions.get(&rewrite.block) else {
            return Err(no_instruction);
        };
        let Some(node) = source.blocks[bi].body.get(rewrite.index) else {
            return Err(no_instruction);
        };
        if env.idom[bi] == usize::MAX {
            return Err(MidTvError::RangeUndecided {
                block: rewrite.block,
                index: rewrite.index,
                why: "the block is unreachable",
            });
        }
        let nodes = rewrite_node(&env, bi, rewrite, node)?;
        if replacements.insert((bi, rewrite.index), nodes).is_some() {
            return Err(MidTvError::RangeUndecided {
                block: rewrite.block,
                index: rewrite.index,
                why: "the instruction is rewritten twice",
            });
        }
    }
    let mut expected = source.clone();
    let rewritten: HashSet<usize> = replacements.keys().map(|&(b, _)| b).collect();
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
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
    // Blocks unreachable once the branches are folded.
    let live = reachable(&expected);
    let doomed: HashSet<BlockId> = witness.removed_blocks.iter().copied().collect();
    if doomed.len() != witness.removed_blocks.len() {
        return Err(MidTvError::TargetDiffers {
            detail: "a block is removed twice".to_string(),
        });
    }
    let mut removed_values = HashSet::new();
    for id in &doomed {
        if live.contains(id) || *id == expected.entry {
            return Err(MidTvError::ReachableBlockRemoved { block: *id });
        }
        let Some(block) = expected.blocks.iter().find(|b| b.id == *id) else {
            return Err(MidTvError::ReachableBlockRemoved { block: *id });
        };
        removed_values.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            removed_values.extend(node.results.iter().copied());
        }
    }
    if !doomed.is_empty() {
        expected.blocks.retain(|b| !doomed.contains(&b.id));
        if let Some(value) = used_values(&expected).intersection(&removed_values).next() {
            return Err(MidTvError::RemovedValueUsed { value: *value });
        }
        drop_names(&mut expected, &removed_values);
    }
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.rewrite_count(),
            refinements: 0,
        },
    ))
}

// ---------------------------------------------------------------------------
// Solver obligations
// ---------------------------------------------------------------------------

fn lower_type(bits: u32) -> Type {
    match bits {
        1 => Type::B1,
        8 => Type::I8,
        16 => Type::I16,
        32 => Type::I32,
        64 => Type::I64,
        _ => Type::I128,
    }
}

fn int_cc(op: ICmpOp) -> IntCC {
    trust_cg_lower::instructions::intcc_of_icmp(op)
}

/// A one-bit `1` exactly when `cond` holds.
fn bit(cond: SmtExpr) -> SmtExpr {
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// `lo <= x <= hi`, unsigned, at `x`'s width.
fn within(x: &SmtExpr, bits: u32, lo: u64, hi: u64) -> Vec<SmtExpr> {
    vec![
        SmtExpr::bv_const(lo, bits).bvule(x.clone()),
        x.clone().bvule(SmtExpr::bv_const(hi, bits)),
    ]
}

/// The interpreter's overflow flag of `op` on `x`, `y` at `bits` (one bit):
/// the exact sum, difference or product leaves the width's range.
fn overflow_flag(op: OverflowOp, signed: bool, bits: u32, x: SmtExpr, y: SmtExpr) -> SmtExpr {
    match (op, signed) {
        (OverflowOp::AddOverflow, false) => x.zero_ext(1).bvadd(y.zero_ext(1)).extract(bits, bits),
        (OverflowOp::SubOverflow, false) => bit(x.bvult(y)),
        (OverflowOp::MulOverflow, false) => {
            let wide = x.zero_ext(bits).bvmul(y.zero_ext(bits));
            bit(wide
                .extract(2 * bits - 1, bits)
                .eq_expr(SmtExpr::bv_const(0, bits))
                .not_expr())
        }
        (OverflowOp::AddOverflow, true) => {
            let exact = x.clone().sign_ext(1).bvadd(y.clone().sign_ext(1));
            bit(exact.eq_expr(x.bvadd(y).sign_ext(1)).not_expr())
        }
        (OverflowOp::SubOverflow, true) => {
            let exact = x.clone().sign_ext(1).bvsub(y.clone().sign_ext(1));
            bit(exact.eq_expr(x.bvsub(y).sign_ext(1)).not_expr())
        }
        (OverflowOp::MulOverflow, true) => {
            let exact = x.clone().sign_ext(bits).bvmul(y.clone().sign_ext(bits));
            bit(exact.eq_expr(x.bvmul(y).sign_ext(bits)).not_expr())
        }
    }
}

/// One solver obligation per claimed rewrite: under its premises (each
/// operand a fresh variable constrained to its claimed interval), the
/// replaced instruction's result equals the replacement's — the `icmp`'s bit
/// and the constant, the overflow instruction's flag and value and `false`
/// with the plain arithmetic, the `select` and the chosen arm, the
/// condition of an `assert` or `condbr` and the constant the rule reads.
/// Rewrites of operands wider than 64 bits are refused here (the constants
/// of the encoding are 64-bit). The premises themselves are this module's
/// structural check; [`range_fact_lemmas`] states the rows that derive them.
pub fn range_obligations(
    pointer_bits: u32,
    source: &Function,
    witness: &RangeWitness,
) -> Result<Vec<ProofObligation>, MidTvError> {
    let env = Env::derive(source, pointer_bits, &witness.invariants)?;
    let positions = block_positions(source);
    let mut out = Vec::new();
    for rewrite in &witness.rewrites {
        let undecided = |why: &'static str| MidTvError::RangeUndecided {
            block: rewrite.block,
            index: rewrite.index,
            why,
        };
        let node = positions
            .get(&rewrite.block)
            .and_then(|&bi| source.blocks[bi].body.get(rewrite.index))
            .ok_or(MidTvError::NoInstruction {
                block: rewrite.block,
                index: rewrite.index,
            })?;
        let bound = |i: usize| -> Result<(u64, u64), MidTvError> {
            let p = rewrite
                .premises
                .get(i)
                .ok_or(undecided("the premises do not name the rule's operands"))?;
            match (u64::try_from(p.lo), u64::try_from(p.hi)) {
                (Ok(lo), Ok(hi)) => Ok((lo, hi)),
                _ => Err(undecided("a premise is wider than the encoding")),
            }
        };
        let name = format!(
            "irmid range {} at {}:{}",
            rewrite.rule.as_str(),
            rewrite.block,
            rewrite.index
        );
        let obligation = match &node.inst {
            Inst::ICmp { op, ty, lhs, rhs } if rewrite.rule == RangeRule::ICmpImplied => {
                let (bits, _) = scalar(ty, pointer_bits).ok_or(undecided("not a scalar"))?;
                if bits > 64 {
                    return Err(undecided("an operand is wider than the encoding"));
                }
                let (rel, swapped, decided) = env
                    .implying(*op, *lhs, *rhs, bits, positions[&rewrite.block])
                    .ok_or(undecided("no dominating compare decides the compare"))?;
                let (x, y) = (SmtExpr::var("x", bits), SmtExpr::var("y", bits));
                let (p, q) = if swapped {
                    (y.clone(), x.clone())
                } else {
                    (x.clone(), y.clone())
                };
                let known = encode_trust_ir_icmp(&int_cc(rel.op), lower_type(bits), p, q)
                    .eq_expr(SmtExpr::bv_const(1, 1));
                obligation(
                    name,
                    encode_trust_ir_icmp(&int_cc(*op), lower_type(bits), x, y),
                    SmtExpr::bv_const(u64::from(decided), 1),
                    vec![("x".into(), bits), ("y".into(), bits)],
                    vec![known],
                )
            }
            Inst::Switch { value, .. } => {
                let ty = env
                    .types
                    .value_type(*value)
                    .ok_or(undecided("the switched value's type is unknown"))?;
                let (bits, signed) =
                    int_shape(&ty, pointer_bits).ok_or(undecided("not an integer"))?;
                if bits > 64 {
                    return Err(undecided("an operand is wider than the encoding"));
                }
                let k = bound(0)?;
                let interval = Iv {
                    lo: u128::from(k.0),
                    hi: u128::from(k.1),
                    bits,
                };
                let after = switch_after(&node.inst, bits, signed, interval).map_err(undecided)?;
                let x = SmtExpr::var("x", bits);
                obligation(
                    name,
                    selected_edge(&node.inst, &node.inst, bits, &x)
                        .ok_or(undecided("the switch has too many edges to encode"))?,
                    selected_edge(&node.inst, &after, bits, &x)
                        .ok_or(undecided("the switch has too many edges to encode"))?,
                    vec![("x".into(), bits)],
                    within(&x, bits, k.0, k.1),
                )
            }
            Inst::ICmp { op, ty, .. } => {
                let (bits, _) = scalar(ty, pointer_bits).ok_or(undecided("not a scalar"))?;
                if bits > 64 {
                    return Err(undecided("an operand is wider than the encoding"));
                }
                let (x, y) = (SmtExpr::var("x", bits), SmtExpr::var("y", bits));
                let (a, b) = (bound(0)?, bound(1)?);
                let mut pre = within(&x, bits, a.0, a.1);
                pre.extend(within(&y, bits, b.0, b.1));
                let source_bit = encode_trust_ir_icmp(&int_cc(*op), lower_type(bits), x, y);
                let decided = decide_icmp_raw(
                    *op,
                    bits,
                    (u128::from(a.0), u128::from(a.1)),
                    (u128::from(b.0), u128::from(b.1)),
                )
                .ok_or(undecided("the premises do not decide the compare"))?;
                obligation(
                    name,
                    source_bit,
                    SmtExpr::bv_const(u64::from(decided), 1),
                    vec![("x".into(), bits), ("y".into(), bits)],
                    pre,
                )
            }
            Inst::Overflow { op, ty, .. } => {
                let (bits, signed) =
                    int_shape(ty, pointer_bits).ok_or(undecided("not an integer"))?;
                if bits > 64 {
                    return Err(undecided("an operand is wider than the encoding"));
                }
                let (x, y) = (SmtExpr::var("x", bits), SmtExpr::var("y", bits));
                let (a, b) = (bound(0)?, bound(1)?);
                let mut pre = within(&x, bits, a.0, a.1);
                pre.extend(within(&y, bits, b.0, b.1));
                let arithmetic = match op {
                    OverflowOp::AddOverflow => Opcode::Iadd,
                    OverflowOp::SubOverflow => Opcode::Isub,
                    OverflowOp::MulOverflow => Opcode::Imul,
                };
                let value =
                    encode_trust_ir_binop(&arithmetic, lower_type(bits), x.clone(), y.clone());
                let flag = overflow_flag(*op, signed, bits, x, y);
                // flag :: value, against false :: value.
                obligation(
                    name,
                    flag.concat(value.clone()),
                    SmtExpr::bv_const(0, 1).concat(value),
                    vec![("x".into(), bits), ("y".into(), bits)],
                    pre,
                )
            }
            Inst::Select { .. } => {
                let c = SmtExpr::var("c", 1);
                let (a, b) = (SmtExpr::var("a", 8), SmtExpr::var("b", 8));
                let k = bound(0)?;
                let chosen = if k == (1, 1) { a.clone() } else { b.clone() };
                obligation(
                    name,
                    encode_trust_ir_select(c.clone(), a, b),
                    chosen,
                    vec![("c".into(), 1), ("a".into(), 8), ("b".into(), 8)],
                    within(&c, 1, k.0, k.1),
                )
            }
            Inst::Assert { .. } | Inst::CondBr { .. } => {
                let c = SmtExpr::var("c", 1);
                let k = bound(0)?;
                if k.0 != k.1 {
                    return Err(undecided("the condition is not decided"));
                }
                obligation(
                    name,
                    c.clone(),
                    SmtExpr::bv_const(k.0, 1),
                    vec![("c".into(), 1)],
                    within(&c, 1, k.0, k.1),
                )
            }
            _ => return Err(undecided("the instruction is not the rule's form")),
        };
        out.push(obligation);
    }
    Ok(out)
}

/// The edge `term` (the source `switch`, or what it became) takes on `x`,
/// as the 16-bit index of its `(target, arguments)` among the source
/// switch's edges: the first case whose value `x` is, else the default.
fn selected_edge(source: &Inst, term: &Inst, bits: u32, x: &SmtExpr) -> Option<SmtExpr> {
    let edges: Vec<(BlockId, &[ValueId])> = source
        .successor_edges()
        .iter()
        .map(|e| (e.target, e.args))
        .collect();
    let index = |target: BlockId, args: &[ValueId]| -> Option<SmtExpr> {
        let i = edges.iter().position(|(t, a)| *t == target && *a == args)?;
        let i = u64::try_from(i).ok().filter(|&i| i < 1 << 16)?;
        Some(SmtExpr::bv_const(i, 16))
    };
    match term {
        Inst::Br { target, args } => index(*target, args),
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            let mut out = index(*default, default_args)?;
            for case in cases.iter().rev() {
                let Constant::Int(c) = case.value else {
                    return None;
                };
                let raw = u64::try_from((c as u128) & mask(bits)).ok()?;
                out = SmtExpr::ite(
                    x.clone().eq_expr(SmtExpr::bv_const(raw, bits)),
                    index(case.target, &case.args)?,
                    out,
                );
            }
            Some(out)
        }
        _ => None,
    }
}

fn obligation(
    name: String,
    lhs: SmtExpr,
    rhs: SmtExpr,
    inputs: Vec<(String, u32)>,
    preconditions: Vec<SmtExpr>,
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr: lhs,
        aarch64_expr: rhs,
        inputs,
        preconditions,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    }
}

/// One lemma of the rules at a width: a fact row or a decision, over
/// symbolic operands `x`, `y` and symbolic interval bounds.
#[derive(Debug, Clone)]
pub struct RangeLemma {
    /// The row or decision it states (`fact:and`, `decide:add_overflow`, …).
    pub name: &'static str,
    /// The lemma, its precondition in place.
    pub obligation: ProofObligation,
    /// The same statement without the precondition the row or decision
    /// relies on: a negative control the solver must refute.
    pub control: ProofObligation,
}

/// The lemmas of the fact rows, the overflow decisions, nine compare
/// decisions (`ult` both ways, `ule`/`ugt`/`uge` true, `eq` false, `ne`
/// true, `slt` on non-negative intervals and on a negative one below a
/// non-negative one), the guard refinements (`ult`, `ule`, `eq`, `ne`, and
/// signed order equal to unsigned order on either side of the sign
/// boundary), the induction step and three implications of a dominating
/// compare, at `bits` (`3 <= bits <= 64`): for symbolic `x` in `[a0, a1]`
/// and `y` in `[b0, b1]`, each row's interval contains its result, and each
/// decision's outcome is the instruction's; the extension rows are stated
/// from the low `bits / 2` bits. Each comes with the control that drops its
/// side condition. A lemma's inputs are the variables it mentions.
pub fn range_fact_lemmas(bits: u32) -> Vec<RangeLemma> {
    let v = |name: &str| SmtExpr::var(name, bits);
    let (x, y) = (v("x"), v("y"));
    let (a0, a1, b0, b1) = (v("a0"), v("a1"), v("b0"), v("b1"));
    let le = |p: &SmtExpr, q: &SmtExpr| p.clone().bvule(q.clone());
    // `x` in `[a0, a1]`, `y` in `[b0, b1]`.
    let in_a = vec![le(&a0, &x), le(&x, &a1)];
    let in_b = vec![le(&b0, &y), le(&y, &b1)];
    let both: Vec<SmtExpr> = in_a.iter().chain(&in_b).cloned().collect();
    let one = SmtExpr::bv_const(1, 1);
    // The claim under `base` and `side`, and its control under `base` alone;
    // the inputs are the variables they mention (`c` is one bit).
    let lemma = |name: &'static str, claim: SmtExpr, base: Vec<SmtExpr>, side: Vec<SmtExpr>| {
        let mut with = base.clone();
        with.extend(side);
        let mut names = claim.free_vars();
        for p in &with {
            names.extend(p.free_vars());
        }
        names.sort();
        names.dedup();
        let inputs: Vec<(String, u32)> = names
            .into_iter()
            .map(|n| {
                let width = if n == "c" { 1 } else { bits };
                (n, width)
            })
            .collect();
        RangeLemma {
            name,
            obligation: obligation(
                format!("irmid range lemma {name} at {bits} bits"),
                bit(claim.clone()),
                one.clone(),
                inputs.clone(),
                with,
            ),
            control: obligation(
                format!("irmid range control {name} at {bits} bits"),
                bit(claim),
                one.clone(),
                inputs,
                base,
            ),
        }
    };
    // `p + q` does not wrap.
    let no_carry = |p: &SmtExpr, q: &SmtExpr| {
        p.clone()
            .zero_ext(1)
            .bvadd(q.clone().zero_ext(1))
            .extract(bits, bits)
            .eq_expr(SmtExpr::bv_const(0, 1))
    };
    // `p * q` does not wrap.
    let no_wide = |p: &SmtExpr, q: &SmtExpr| {
        p.clone()
            .zero_ext(bits)
            .bvmul(q.clone().zero_ext(bits))
            .extract(2 * bits - 1, bits)
            .eq_expr(SmtExpr::bv_const(0, bits))
    };
    let smax = SmtExpr::bv_const(mask(bits - 1) as u64, bits);
    let nonneg = |p: &SmtExpr| p.clone().bvule(smax.clone());
    let in_result =
        |r: SmtExpr, lo: SmtExpr, hi: SmtExpr| SmtExpr::and_expr(lo.bvule(r.clone()), r.bvule(hi));
    let and =
        try_encode_trust_ir_bitwise_binop(&Opcode::Band, lower_type(bits), x.clone(), y.clone())
            .expect("band encodes");
    let add = encode_trust_ir_binop(&Opcode::Iadd, lower_type(bits), x.clone(), y.clone());
    let sub = encode_trust_ir_binop(&Opcode::Isub, lower_type(bits), x.clone(), y.clone());
    let mul = encode_trust_ir_binop(&Opcode::Imul, lower_type(bits), x.clone(), y.clone());
    let lshr = try_encode_trust_ir_shift(&Opcode::Ushr, lower_type(bits), x.clone(), y.clone())
        .expect("ushr encodes");
    let urem = encode_trust_ir_binop(&Opcode::Urem, lower_type(bits), x.clone(), y.clone());
    let half = bits / 2;
    let narrow = SmtExpr::bv_const(mask(half) as u64, bits);
    let c = SmtExpr::var("c", 1);
    let flag = |op, signed| overflow_flag(op, signed, bits, x.clone(), y.clone());
    let zero_flag = |f: SmtExpr| f.eq_expr(SmtExpr::bv_const(0, 1));
    let icmp = |cc: IntCC| {
        encode_trust_ir_icmp(&cc, lower_type(bits), x.clone(), y.clone()).eq_expr(one.clone())
    };
    let not_icmp = |cc: IntCC| {
        encode_trust_ir_icmp(&cc, lower_type(bits), x.clone(), y.clone())
            .eq_expr(SmtExpr::bv_const(0, 1))
    };
    let raw_icmp = |cc: IntCC| encode_trust_ir_icmp(&cc, lower_type(bits), x.clone(), y.clone());
    let lt = |p: &SmtExpr, q: &SmtExpr| p.clone().bvult(q.clone());
    vec![
        // and: [0, min(hi)] — with one bounded operand.
        lemma(
            "fact:and",
            and.clone().bvule(a1.clone()),
            vec![],
            vec![le(&x, &a1)],
        ),
        lemma(
            "fact:add",
            in_result(
                add,
                a0.clone().bvadd(b0.clone()),
                a1.clone().bvadd(b1.clone()),
            ),
            both.clone(),
            vec![no_carry(&a1, &b1)],
        ),
        lemma(
            "fact:mul",
            in_result(
                mul,
                a0.clone().bvmul(b0.clone()),
                a1.clone().bvmul(b1.clone()),
            ),
            both.clone(),
            vec![no_wide(&a1, &b1)],
        ),
        lemma(
            "fact:sub",
            in_result(
                sub,
                a0.clone().bvsub(b1.clone()),
                a1.clone().bvsub(b0.clone()),
            ),
            both.clone(),
            vec![le(&b1, &a0)],
        ),
        // lshr by `y` in [b0, b0] (an exact amount below the width).
        lemma(
            "fact:lshr",
            in_result(
                lshr,
                a0.clone().bvlshr(y.clone()),
                a1.clone().bvlshr(y.clone()),
            ),
            vec![lt(&y, &SmtExpr::bv_const(u64::from(bits), bits))],
            in_a.clone(),
        ),
        lemma(
            "fact:urem",
            SmtExpr::and_expr(urem.clone().bvule(a1.clone()), urem.bvult(b1.clone())),
            vec![le(&x, &a1), le(&y, &b1)],
            vec![le(&SmtExpr::bv_const(1, bits), &y)],
        ),
        // zext from the low half: the operand's interval at the full width,
        // inside the half's full range.
        lemma(
            "fact:zext",
            SmtExpr::and_expr(
                in_result(
                    encode_trust_ir_uextend(half, bits, x.clone().extract(half - 1, 0)),
                    a0.clone(),
                    a1.clone(),
                ),
                encode_trust_ir_uextend(half, bits, x.clone().extract(half - 1, 0))
                    .bvule(narrow.clone()),
            ),
            vec![],
            vec![
                le(&a0, &x.clone().extract(half - 1, 0).zero_ext(bits - half)),
                le(&x.clone().extract(half - 1, 0).zero_ext(bits - half), &a1),
            ],
        ),
        // trunc to the low half of a value whose bound fits it.
        lemma(
            "fact:trunc",
            in_result(
                x.clone().extract(half - 1, 0).zero_ext(bits - half),
                a0.clone(),
                a1.clone(),
            ),
            in_a.clone(),
            vec![le(&a1, &narrow)],
        ),
        // sext from the low half of a value non-negative at that width.
        lemma(
            "fact:sext",
            in_result(
                encode_trust_ir_sextend(half, bits, x.clone().extract(half - 1, 0)),
                a0.clone(),
                a1.clone(),
            ),
            vec![
                le(&a0, &x.clone().extract(half - 1, 0).zero_ext(bits - half)),
                le(&x.clone().extract(half - 1, 0).zero_ext(bits - half), &a1),
            ],
            vec![le(&a1, &SmtExpr::bv_const(mask(half - 1) as u64, bits))],
        ),
        lemma(
            "fact:select",
            in_result(
                encode_trust_ir_select(c.clone(), x.clone(), y.clone()),
                SmtExpr::ite(lt(&a0, &b0), a0.clone(), b0.clone()),
                SmtExpr::ite(lt(&a1, &b1), b1.clone(), a1.clone()),
            ),
            in_a.clone(),
            in_b.clone(),
        ),
        lemma(
            "decide:add_overflow",
            zero_flag(flag(OverflowOp::AddOverflow, false)),
            both.clone(),
            vec![no_carry(&a1, &b1)],
        ),
        lemma(
            "decide:sub_overflow",
            zero_flag(flag(OverflowOp::SubOverflow, false)),
            both.clone(),
            vec![le(&b1, &a0)],
        ),
        lemma(
            "decide:mul_overflow",
            zero_flag(flag(OverflowOp::MulOverflow, false)),
            both.clone(),
            vec![no_wide(&a1, &b1)],
        ),
        lemma(
            "decide:signed_add_overflow",
            zero_flag(flag(OverflowOp::AddOverflow, true)),
            both.clone(),
            vec![
                nonneg(&a1),
                nonneg(&b1),
                no_carry(&a1, &b1),
                nonneg(&a1.clone().bvadd(b1.clone())),
            ],
        ),
        lemma(
            "decide:signed_sub_overflow",
            zero_flag(flag(OverflowOp::SubOverflow, true)),
            both.clone(),
            vec![nonneg(&a1), nonneg(&b1)],
        ),
        lemma(
            "decide:signed_mul_overflow",
            zero_flag(flag(OverflowOp::MulOverflow, true)),
            both.clone(),
            vec![
                nonneg(&a1),
                nonneg(&b1),
                no_wide(&a1, &b1),
                nonneg(&a1.clone().bvmul(b1.clone())),
            ],
        ),
        lemma(
            "decide:ult_true",
            icmp(IntCC::UnsignedLessThan),
            both.clone(),
            vec![lt(&a1, &b0)],
        ),
        lemma(
            "decide:ult_false",
            not_icmp(IntCC::UnsignedLessThan),
            both.clone(),
            vec![le(&b1, &a0)],
        ),
        lemma(
            "decide:ule_true",
            icmp(IntCC::UnsignedLessThanOrEqual),
            both.clone(),
            vec![le(&a1, &b0)],
        ),
        lemma(
            "decide:ugt_true",
            icmp(IntCC::UnsignedGreaterThan),
            both.clone(),
            vec![lt(&b1, &a0)],
        ),
        lemma(
            "decide:uge_true",
            icmp(IntCC::UnsignedGreaterThanOrEqual),
            both.clone(),
            vec![le(&b1, &a0)],
        ),
        lemma(
            "decide:eq_false",
            not_icmp(IntCC::Equal),
            both.clone(),
            vec![lt(&a1, &b0)],
        ),
        lemma(
            "decide:ne_true",
            icmp(IntCC::NotEqual),
            both.clone(),
            vec![lt(&b1, &a0)],
        ),
        // Two non-negative intervals compare signed as they do unsigned.
        lemma(
            "decide:slt_true",
            icmp(IntCC::SignedLessThan),
            both.clone(),
            vec![nonneg(&a1), nonneg(&b1), lt(&a1, &b0)],
        ),
        // A negative interval is below a non-negative one.
        lemma(
            "decide:slt_mixed",
            icmp(IntCC::SignedLessThan),
            both.clone(),
            vec![lt(&smax, &a0), nonneg(&b1)],
        ),
        // A branch's compare leaves `x < y`: `x <= hi(y) - 1`, `y >= lo(x) + 1`.
        lemma(
            "guard:ult",
            SmtExpr::and_expr(
                le(&x, &b1.clone().bvsub(SmtExpr::bv_const(1, bits))),
                le(&a0.clone().bvadd(SmtExpr::bv_const(1, bits)), &y),
            ),
            both.clone(),
            vec![lt(&x, &y)],
        ),
        lemma(
            "guard:ule",
            SmtExpr::and_expr(le(&x, &b1), le(&a0, &y)),
            both.clone(),
            vec![le(&x, &y)],
        ),
        lemma(
            "guard:eq",
            SmtExpr::and_expr(
                SmtExpr::and_expr(le(&b0, &x), le(&x, &b1)),
                SmtExpr::and_expr(le(&a0, &y), le(&y, &a1)),
            ),
            both.clone(),
            vec![x.clone().eq_expr(y.clone())],
        ),
        // `x != y` with `y` exactly `b0`: `x` is not `b0` (an end drops it).
        lemma(
            "guard:ne",
            x.clone().eq_expr(b0.clone()).not_expr(),
            vec![y.clone().eq_expr(b0.clone())],
            vec![x.clone().eq_expr(y.clone()).not_expr()],
        ),
        // On one side of the sign boundary signed order is unsigned order.
        lemma(
            "guard:signed_nonneg_order",
            raw_icmp(IntCC::SignedLessThan).eq_expr(raw_icmp(IntCC::UnsignedLessThan)),
            vec![],
            vec![nonneg(&x), nonneg(&y)],
        ),
        lemma(
            "guard:signed_negative_order",
            raw_icmp(IntCC::SignedLessThan).eq_expr(raw_icmp(IntCC::UnsignedLessThan)),
            vec![],
            vec![lt(&smax, &x), lt(&smax, &y)],
        ),
        // The induction step: `x >= a0` and `x < y <= b1` keep `x + b0`
        // (a step `b0 >= 1` that does not carry past `b1 - 1`) inside
        // `[a0 + b0, b1 - 1 + b0]`; without the exit test it wraps.
        lemma(
            "induction:step",
            in_result(
                x.clone().bvadd(b0.clone()),
                a0.clone().bvadd(b0.clone()),
                b1.clone()
                    .bvsub(SmtExpr::bv_const(1, bits))
                    .bvadd(b0.clone()),
            ),
            vec![
                le(&a0, &x),
                le(&y, &b1),
                le(&SmtExpr::bv_const(1, bits), &b0),
                no_carry(&b1.clone().bvsub(SmtExpr::bv_const(1, bits)), &b0),
            ],
            vec![lt(&x, &y)],
        ),
        // A dominating compare decides one of the same operands.
        lemma(
            "implied:ult_ule",
            icmp(IntCC::UnsignedLessThanOrEqual),
            vec![],
            vec![lt(&x, &y)],
        ),
        lemma(
            "implied:ult_not_ugt",
            not_icmp(IntCC::UnsignedGreaterThan),
            vec![],
            vec![lt(&x, &y)],
        ),
        lemma(
            "implied:eq_sle_swapped",
            encode_trust_ir_icmp(
                &IntCC::SignedLessThanOrEqual,
                lower_type(bits),
                y.clone(),
                x.clone(),
            )
            .eq_expr(one.clone()),
            vec![],
            vec![x.clone().eq_expr(y.clone())],
        ),
    ]
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_range_tests.rs"]
mod tests;
