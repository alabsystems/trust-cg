// crates/trust-cg-eqsat/src/elaborate.rs - placement and emission of the chosen forms, operand remap and claims
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Elaboration (section 6) and the claims of section 7.1.
//!
//! * Skeleton instructions keep their block, order, results and every field
//!   but their value operands; graph instructions and see-through copies are
//!   removed.
//! * Every chosen node needed by a skeleton operand is emitted once (two
//!   chosen nodes with the same operator and the same emitted operands are
//!   one instruction), in the deepest block that defines one of its
//!   operands (the entry block if none), right after its last operand's
//!   definition there (after a leading `LandingPad`), so it dominates every
//!   use. A graph node is total on defined operands (section 2.3), so
//!   hoisting it is sound.
//! * An emitted node reuses the `ValueId`, span and scope of the input graph
//!   instruction that created it, when there is one and its `ValueId` is not
//!   taken; otherwise it gets a fresh `ValueId` above every id the input
//!   mentions.
//! * An operand at a literal-sensitive position (section 2.5: the lane index
//!   of `ExtractElement` and `InsertElement`, both operands of
//!   `PtrFromParts`, the operand of `Resume`) whose remapped value a `Const`
//!   defines that the input did not have there, or a `Resume` operand that
//!   would be a literal or a landing pad's selector (trust-ir's `Resume`
//!   rule (c)), is read through a fresh see-through `Copy` placed right
//!   before its instruction instead (`literal_guards`), charged as a copy.
//! * A pinned instruction (`InstClass::Pinned`, on the selector trace of an
//!   exhaustive switch; `selector` module doc) is kept in place like a
//!   skeleton instruction, its operands remapped, its cost charged; it keeps
//!   its result, which no emitted node reuses. A skeleton or pinned operand
//!   whose root is pinned reads the pinned instruction's result; its output
//!   term is the pinned operator over its operands' output terms, proved by
//!   `Congr` over their proofs.
//! * For every skeleton operand whose output term differs from its input
//!   term, a claim proves `(input term, output term)`: the operand's entry
//!   proof (input term to the canonical term of its Id) followed by the
//!   extraction proof (canonical term to the chosen form), or for a pinned
//!   root its `Congr` proof. The proofs are built from recorded rule matches
//!   and hash-cons explanations only. Two operands with one conclusion share
//!   one claim.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{Block, Constant, Function, Inst, InstrNode, ValueId};

use crate::derivation::{ProofRef, TermRef};
use crate::eval;
use crate::extract::Choice;
use crate::graph::{Entry, Id, Node};
use crate::proof::{EngineResult, invariant};
use crate::remap;
use crate::rewrite::Engine;
use crate::to_graph::{InstClass, PinnedForm, Reading, resume_refused_values};
use crate::vocab::{CONST_COST, COPY_COST, OpDesc, ScalarTy};

/// The elaborated body.
pub(crate) struct Elaborated {
    pub(crate) function: Function,
    pub(crate) cost_after: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum EmitKey {
    Const(ScalarTy, u128),
    Op(OpDesc, Vec<ValueId>),
}

/// The canonical trust-ir spelling of `Const(ty, residue)`.
pub(crate) fn constant_spelling(ty: ScalarTy, width: u32, residue: u128) -> Constant {
    if ty.is_bool() {
        Constant::Bool(residue == 1)
    } else if ty.is_signed() {
        Constant::Int(eval::signed(residue, width))
    } else {
        Constant::u128(residue)
    }
}

struct Emitter<'a, 'e, 'r> {
    function: &'a Function,
    reading: &'a Reading,
    engine: &'e mut Engine<'r>,
    choices: &'a [Choice],
    /// Emitted value per chosen member.
    emitted: BTreeMap<Id, ValueId>,
    /// The `Const` instruction of every emitted constant, by its value.
    consts: BTreeMap<ValueId, Inst>,
    by_key: BTreeMap<EmitKey, ValueId>,
    /// Location of emitted values: (block, slot).
    locs: BTreeMap<ValueId, (usize, i64)>,
    /// Emitted instructions per block, per slot (in emission order).
    pending: Vec<BTreeMap<i64, Vec<InstrNode>>>,
    reused: BTreeSet<ValueId>,
    next_fresh: u32,
    cost_after: u64,
}

impl Emitter<'_, '_, '_> {
    fn choice(&self, id: Id) -> EngineResult<Choice> {
        match self.choices.get(id.index()) {
            Some(choice) => Ok(*choice),
            None => invariant("an Id without an extraction choice"),
        }
    }

    fn start_slot(&self, block: usize) -> i64 {
        let leading_pad = self
            .function
            .blocks
            .get(block)
            .and_then(|b| b.body.first())
            .is_some_and(|node| matches!(node.inst, Inst::LandingPad { .. }));
        if leading_pad { 0 } else { -1 }
    }

    fn loc(&self, value: ValueId) -> EngineResult<(usize, i64)> {
        if let Some(loc) = self.locs.get(&value) {
            return Ok(*loc);
        }
        let def = self.reading.value(value)?;
        Ok((def.block, def.slot))
    }

    /// Where a node over `operands` goes.
    fn anchor(&self, operands: &[ValueId]) -> EngineResult<(usize, i64)> {
        let cfg = &self.reading.cfg;
        let mut deepest: Option<usize> = None;
        let mut locs = Vec::with_capacity(operands.len());
        for operand in operands {
            let (block, slot) = self.loc(*operand)?;
            locs.push((block, slot));
            deepest = Some(match deepest {
                Some(current) if cfg.depth(current) >= cfg.depth(block) => current,
                _ => block,
            });
        }
        let Some(block) = deepest else {
            return Ok((cfg.entry, self.start_slot(cfg.entry)));
        };
        let mut slot = self.start_slot(block);
        for (operand_block, operand_slot) in locs {
            if !cfg.dominates(operand_block, block) {
                return invariant("the operands of a chosen node are not on one dominator chain");
            }
            if operand_block == block {
                slot = slot.max(operand_slot);
            }
        }
        Ok((block, slot))
    }

    fn fresh_value(&mut self) -> EngineResult<ValueId> {
        let value = ValueId(self.next_fresh);
        match self.next_fresh.checked_add(1) {
            Some(next) => self.next_fresh = next,
            None => return invariant("the ValueId space is exhausted"),
        }
        Ok(value)
    }

    /// Emit the chosen member `member`, whose operand Ids already have values.
    fn emit(&mut self, member: Id, values: &BTreeMap<Id, ValueId>) -> EngineResult<ValueId> {
        if let Some(value) = self.emitted.get(&member) {
            return Ok(*value);
        }
        let node = match self.engine.graph.entry(member)? {
            Entry::Node(node) => node.clone(),
            _ => return invariant("a chosen member that is not a concrete node"),
        };
        let (key, inst, operands, cost, is_const) = match &node {
            Node::Leaf { value, .. } => {
                self.emitted.insert(member, *value);
                return Ok(*value);
            }
            Node::Const { ty, residue } => {
                let Some(width) = self.engine.widths.width(*ty) else {
                    return invariant("a constant of a type outside the graph");
                };
                let inst = Inst::Const {
                    ty: ty.to_ty(),
                    value: constant_spelling(*ty, width, *residue),
                };
                (
                    EmitKey::Const(*ty, *residue),
                    inst,
                    Vec::new(),
                    CONST_COST,
                    true,
                )
            }
            Node::Op { desc, args } => {
                let mut operands = Vec::with_capacity(args.len());
                for arg in args {
                    match values.get(arg) {
                        Some(value) => operands.push(*value),
                        None => return invariant("an operand Id emitted out of order"),
                    }
                }
                let inst = build_inst(*desc, &operands)?;
                (
                    EmitKey::Op(*desc, operands.clone()),
                    inst,
                    operands,
                    desc.cost(),
                    false,
                )
            }
        };
        if let Some(value) = self.by_key.get(&key) {
            self.emitted.insert(member, *value);
            return Ok(*value);
        }
        let (block, slot) = self.anchor(&operands)?;
        // Reuse the input instruction's ValueId, span and scope when this
        // node was created by it.
        let mut span = None;
        let mut scope = None;
        let mut reuse = None;
        if let Some(&(origin_block, origin_index)) = self.reading.origins.get(&member)
            && let Some(original) = self
                .function
                .blocks
                .get(origin_block)
                .and_then(|b| b.body.get(origin_index))
            && let [result] = original.results.as_slice()
            && !self.reused.contains(result)
        {
            reuse = Some(*result);
            span = original.span;
            scope = original.scope;
        }
        let value = match reuse {
            Some(value) => {
                self.reused.insert(value);
                value
            }
            None => self.fresh_value()?,
        };
        if is_const {
            self.consts.insert(value, inst.clone());
        }
        let mut instr = InstrNode::new(inst).with_result(value);
        instr.span = span;
        instr.scope = scope;
        match self.pending.get_mut(block) {
            Some(slots) => slots.entry(slot).or_default().push(instr),
            None => return invariant("an anchor outside the function"),
        }
        self.locs.insert(value, (block, slot));
        self.by_key.insert(key, value);
        self.emitted.insert(member, value);
        self.cost_after = self.cost_after.saturating_add(cost);
        Ok(value)
    }
}

/// The trust-ir instruction of `desc` over `operands`.
fn build_inst(desc: OpDesc, operands: &[ValueId]) -> EngineResult<Inst> {
    let operand = |index: usize| -> EngineResult<ValueId> {
        match operands.get(index) {
            Some(value) => Ok(*value),
            None => invariant("an operator emitted with too few operands"),
        }
    };
    Ok(match desc {
        OpDesc::Bin(op, ty) => Inst::BinOp {
            op: op.to_ir(),
            ty: ty.to_ty(),
            lhs: operand(0)?,
            rhs: operand(1)?,
        },
        OpDesc::Un(op, ty) => Inst::UnOp {
            op: op.to_ir(),
            ty: ty.to_ty(),
            operand: operand(0)?,
        },
        OpDesc::Cmp(pred, ty) => Inst::ICmp {
            op: pred.to_ir(),
            ty: ty.to_ty(),
            lhs: operand(0)?,
            rhs: operand(1)?,
        },
        OpDesc::Cast(op, src, dst) => Inst::Cast {
            op: op.to_ir(),
            src_ty: src.to_ty(),
            dst_ty: dst.to_ty(),
            operand: operand(0)?,
        },
        OpDesc::Select(ty) => Inst::Select {
            ty: ty.to_ty(),
            cond: operand(0)?,
            then_val: operand(1)?,
            else_val: operand(2)?,
        },
    })
}

/// Elaborate the chosen forms into a body and record the claims in the
/// engine's proof table.
pub(crate) fn elaborate(
    function: &Function,
    reading: &Reading,
    engine: &mut Engine<'_>,
    choices: &[Choice],
) -> EngineResult<Elaborated> {
    // Skeleton and pinned operands, per instruction, in visit order. An
    // operand whose root is pinned reads the pinned instruction, whose own
    // operands are visited with it.
    let mut needed: BTreeSet<Id> = BTreeSet::new();
    for (block_index, block) in function.blocks.iter().enumerate() {
        for (position, node) in block.body.iter().enumerate() {
            if kept(class_of(reading, block_index, position)) {
                for operand in remap::operands(&node.inst) {
                    let def = reading.value(operand)?;
                    if reading.pinned.contains_key(&def.root) {
                        continue;
                    }
                    if let Some(id) = def.id {
                        needed.insert(id);
                    }
                }
            }
        }
    }
    // Close over the chosen members' operands (all older Ids).
    let mut work: Vec<Id> = needed.iter().copied().collect();
    while let Some(id) = work.pop() {
        let Some(choice) = choices.get(id.index()) else {
            return invariant("an Id without an extraction choice");
        };
        if let Entry::Node(Node::Op { args, .. }) = engine.graph.entry(choice.member)? {
            for arg in args {
                if needed.insert(*arg) {
                    work.push(*arg);
                }
            }
        }
    }

    let mut emitter = Emitter {
        function,
        reading,
        engine,
        choices,
        emitted: BTreeMap::new(),
        consts: BTreeMap::new(),
        by_key: BTreeMap::new(),
        locs: BTreeMap::new(),
        pending: vec![BTreeMap::new(); function.blocks.len()],
        // A pinned instruction keeps its result in place.
        reused: reading.pinned.keys().copied().collect(),
        next_fresh: reading.fresh_base,
        cost_after: 0,
    };
    let (refused, _) = resume_refused_values(function);
    // Every `Const` instruction of the input, by its result.
    let mut input_consts: BTreeMap<ValueId, &Inst> = BTreeMap::new();
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        if let (Inst::Const { .. }, [result]) = (&node.inst, node.results.as_slice()) {
            input_consts.insert(*result, &node.inst);
        }
    }
    let mut values: BTreeMap<Id, ValueId> = BTreeMap::new();
    let mut out_terms: BTreeMap<Id, TermRef> = BTreeMap::new();
    let mut extraction: BTreeMap<Id, ProofRef> = BTreeMap::new();
    let mut sides: BTreeMap<Id, ProofRef> = BTreeMap::new();
    // Ascending Id order: every member's operands are older, so they are done.
    for &id in &needed {
        let choice = emitter.choice(id)?;
        let value = emitter.emit(choice.member, &values)?;
        values.insert(id, value);

        // canon(id) -> canon(member) along the chosen sides.
        let to_member = side_proof(&mut emitter, &mut sides, id, choice.member)?;
        let (term, proof) = match emitter.engine.graph.entry(choice.member)?.clone() {
            Entry::Node(Node::Op { desc, args }) => {
                let mut terms = Vec::with_capacity(args.len());
                let mut proofs = Vec::with_capacity(args.len());
                for arg in &args {
                    match (out_terms.get(arg), extraction.get(arg)) {
                        (Some(term), Some(proof)) => {
                            terms.push(*term);
                            proofs.push(*proof);
                        }
                        _ => return invariant("an operand Id extracted out of order"),
                    }
                }
                let term = emitter.engine.prover.op(desc, &terms);
                let inner = emitter.engine.prover.congr(desc, &proofs)?;
                let proof = emitter.engine.prover.trans(to_member, inner)?;
                (term, proof)
            }
            Entry::Node(_) => (emitter.engine.graph.canon(choice.member)?, to_member),
            _ => return invariant("a chosen member that is not a concrete node"),
        };
        out_terms.insert(id, term);
        extraction.insert(id, proof);
    }

    let pinned = pinned_terms(&mut emitter, &values, &out_terms, &extraction)?;

    // Skeleton remap and claims, then the blocks.
    let mut blocks = Vec::with_capacity(function.blocks.len());
    let mut defined: BTreeSet<ValueId> = BTreeSet::new();
    let mut claimed: BTreeSet<(TermRef, TermRef)> = BTreeSet::new();
    for (block_index, block) in function.blocks.iter().enumerate() {
        let mut slots = emitter
            .pending
            .get_mut(block_index)
            .map(std::mem::take)
            .unwrap_or_default();
        let mut body = slots.remove(&-1).unwrap_or_default();
        for (position, node) in block.body.iter().enumerate() {
            let class = class_of(reading, block_index, position);
            let skeleton = matches!(class, Some(InstClass::Skeleton { .. }));
            if kept(class) {
                let mut new_operands = Vec::new();
                for operand in remap::operands(&node.inst) {
                    let def = reading.value(operand)?;
                    if let Some(&(input, output, proof)) = pinned.get(&def.root) {
                        new_operands.push(def.root);
                        if skeleton && def.term != Some(input) {
                            return invariant("a pinned operand whose term is not its root's");
                        }
                        if skeleton && input != output && claimed.insert((input, output)) {
                            emitter.engine.prover.claim(proof);
                        }
                        continue;
                    }
                    match def.id {
                        Some(id) => {
                            let Some(value) = values.get(&id) else {
                                return invariant("a skeleton operand without an emitted value");
                            };
                            new_operands.push(*value);
                            if !skeleton {
                                continue;
                            }
                            let (Some(input), Some(entry), Some(output), Some(extracted)) = (
                                def.term,
                                def.entry,
                                out_terms.get(&id).copied(),
                                extraction.get(&id).copied(),
                            ) else {
                                return invariant("a graph operand without its terms");
                            };
                            if input != output && claimed.insert((input, output)) {
                                let claim = emitter.engine.prover.trans(entry, extracted)?;
                                let conclusion = emitter.engine.prover.conclusion(claim)?;
                                if conclusion.lhs != input || conclusion.rhs != output {
                                    return invariant("a claim that does not conclude its operand");
                                }
                                emitter.engine.prover.claim(claim);
                            }
                        }
                        None => new_operands.push(def.root),
                    }
                }
                let mut out = node.clone();
                if !remap::replace_operands(&mut out.inst, &new_operands) {
                    return invariant("the operand walks disagree on a kept instruction");
                }
                if skeleton {
                    let guards =
                        literal_guards(&mut emitter, &input_consts, &refused, node, &mut out)?;
                    body.extend(guards);
                } else {
                    let form = node.results.first().and_then(|r| reading.pinned.get(r));
                    let cost = match form {
                        Some(PinnedForm::Op(desc, _)) => desc.cost(),
                        Some(PinnedForm::Const) => CONST_COST,
                        None => return invariant("a pinned instruction without its form"),
                    };
                    emitter.cost_after = emitter.cost_after.saturating_add(cost);
                }
                body.push(out);
            }
            let slot = i64::try_from(position).unwrap_or(i64::MAX);
            if let Some(list) = slots.remove(&slot) {
                if !kept(class) {
                    return invariant("a node anchored after a removed instruction");
                }
                body.extend(list);
            }
        }
        if !slots.is_empty() {
            return invariant("a node anchored outside its block");
        }
        for (value, _) in &block.params {
            defined.insert(*value);
        }
        for node in &body {
            defined.extend(node.results.iter().copied());
        }
        blocks.push(Block {
            id: block.id,
            params: block.params.clone(),
            body,
        });
    }

    let mut output = function.clone();
    output.blocks = blocks;
    if let Some(names) = &mut output.value_names {
        names.retain(|(value, _)| defined.contains(value));
    }
    Ok(Elaborated {
        function: output,
        cost_after: emitter.cost_after,
    })
}

/// The literal-sensitive operand positions of section 2.5, as (input operand,
/// output operand) pairs: trust-ir's validator reads these through the
/// instruction that defines them. The lane index of `ExtractElement` and
/// `InsertElement` and both operands of `PtrFromParts` are looked up in
/// `const_int_values` (a `Const` there is range-checked); a `Resume` operand
/// is refused when a literal defines it (rule (c)). `out` is `input` with
/// its value operands replaced, so the two are the same instruction kind.
fn literal_sensitive<'o>(
    input: &Inst,
    out: &'o mut Inst,
) -> EngineResult<Vec<(ValueId, &'o mut ValueId)>> {
    if std::mem::discriminant(input) != std::mem::discriminant(out) {
        return invariant("a remapped skeleton instruction changed its kind");
    }
    Ok(match (input, out) {
        (Inst::ExtractElement { index: before, .. }, Inst::ExtractElement { index: after, .. })
        | (Inst::InsertElement { index: before, .. }, Inst::InsertElement { index: after, .. })
        | (Inst::Resume { exn: before }, Inst::Resume { exn: after }) => vec![(*before, after)],
        (
            Inst::PtrFromParts {
                data: data_before,
                metadata: metadata_before,
                ..
            },
            Inst::PtrFromParts {
                data: data_after,
                metadata: metadata_after,
                ..
            },
        ) => vec![
            (*data_before, data_after),
            (*metadata_before, metadata_after),
        ],
        _ => Vec::new(),
    })
}

/// Section 6: at a literal-sensitive position (`literal_sensitive`) the
/// output operand may be defined by a `Const` instruction only when the input
/// operand is defined by an equal `Const` instruction, and a `Resume` operand
/// may not be any literal or a landing pad's selector
/// (`to_graph::resume_refused_values`; the input passed that rule, since
/// `to_graph::read` declines otherwise). Extracting a constant or removing a
/// see-through copy can hand such a position a value that breaks this. Then
/// a fresh see-through `Copy` of the remapped value, at the input operand's
/// type (the terms are equal, so the types are), becomes the operand and is
/// placed right before the instruction with its span and scope: the
/// operand's term is unchanged, so no claim changes, and each copy is charged
/// at `COPY_COST`. Returns the copies in operand order.
///
/// The output definition of a remapped value is its emitted instruction when
/// it was emitted (`Emitter::consts` holds the constants), and its input
/// definition otherwise (a leaf keeps its instruction).
fn literal_guards(
    emitter: &mut Emitter<'_, '_, '_>,
    input_consts: &BTreeMap<ValueId, &Inst>,
    refused: &BTreeSet<ValueId>,
    input: &InstrNode,
    out: &mut InstrNode,
) -> EngineResult<Vec<InstrNode>> {
    let resume = matches!(input.inst, Inst::Resume { .. });
    let (span, scope) = (out.span, out.scope);
    let mut guards = Vec::new();
    for (before, after) in literal_sensitive(&input.inst, &mut out.inst)? {
        let output_const = if emitter.locs.contains_key(after) {
            emitter.consts.get(after)
        } else {
            input_consts.get(after).copied()
        };
        let input_const = input_consts.get(&before).copied();
        let new_const = output_const.is_some_and(|inst| input_const != Some(inst));
        if !new_const && !(resume && refused.contains(after)) {
            continue;
        }
        let ty = emitter.reading.value(before)?.ty.clone();
        if emitter.engine.widths.scalar(&ty).is_none() {
            return invariant("a literal-sensitive operand rewritten at a type outside the graph");
        }
        let value = emitter.fresh_value()?;
        let mut copy = InstrNode::new(Inst::Copy {
            ty,
            operand: *after,
        })
        .with_result(value);
        copy.span = span;
        copy.scope = scope;
        *after = value;
        emitter.cost_after = emitter.cost_after.saturating_add(COPY_COST);
        guards.push(copy);
    }
    Ok(guards)
}

/// The proof `canon(id) -> canon(member)` along the chosen sides of `id`'s
/// tree, memoized per Id in `sides`: a `b` side adds `Trans(just, rest)` and
/// an `a` side is its child's proof (same canonical term), so every union
/// adds at most one `Trans` and Ids whose chosen paths end alike share them.
/// The walk is iterative: it descends to the first Id already known (or the
/// member) and composes back up.
fn side_proof(
    emitter: &mut Emitter<'_, '_, '_>,
    sides: &mut BTreeMap<Id, ProofRef>,
    id: Id,
    member: Id,
) -> EngineResult<ProofRef> {
    let mut path: Vec<(Id, Option<ProofRef>)> = Vec::new();
    let mut cur = id;
    let mut proof = loop {
        if let Some(known) = sides.get(&cur) {
            break *known;
        }
        match emitter.engine.graph.entry(cur)? {
            Entry::Node(_) => {
                if cur != member {
                    return invariant("the recorded sides do not lead to the chosen member");
                }
                let term = emitter.engine.graph.canon(cur)?;
                let refl = emitter.engine.prover.refl(term)?;
                sides.insert(cur, refl);
                break refl;
            }
            Entry::Union { a, b, just } | Entry::Directed { a, b, just } => {
                let (a, b, just) = (*a, *b, *just);
                if emitter.choice(cur)?.left {
                    path.push((cur, None));
                    cur = a;
                } else {
                    path.push((cur, Some(just)));
                    cur = b;
                }
            }
        }
    };
    for (above, step) in path.into_iter().rev() {
        if let Some(step) = step {
            proof = emitter.engine.prover.trans(step, proof)?;
        }
        sides.insert(above, proof);
    }
    let conclusion = emitter.engine.prover.conclusion(proof)?;
    if conclusion.lhs != emitter.engine.graph.canon(id)?
        || conclusion.rhs != emitter.engine.graph.canon(member)?
    {
        return invariant("the recorded sides do not lead to the chosen member");
    }
    Ok(proof)
}

/// The input term, output term and proof of every pinned value, memoized:
/// a pinned operator's output term is the operator over its operands' output
/// terms (a pinned operand's own, else its Id's extracted term), proved by
/// `Congr` over the operands' proofs (`entry` then extraction); a pinned
/// constant is itself. Pinned values are visited operands first with an
/// explicit stack, so a long trace does not recurse.
fn pinned_terms(
    emitter: &mut Emitter<'_, '_, '_>,
    values: &BTreeMap<Id, ValueId>,
    out_terms: &BTreeMap<Id, TermRef>,
    extraction: &BTreeMap<Id, ProofRef>,
) -> EngineResult<BTreeMap<ValueId, (TermRef, TermRef, ProofRef)>> {
    let reading = emitter.reading;
    let mut done: BTreeMap<ValueId, (TermRef, TermRef, ProofRef)> = BTreeMap::new();
    for &start in reading.pinned.keys() {
        let mut stack = vec![start];
        // A pinned value is pushed once per pinned operand of a pinned
        // instruction (at most three) and popped once per push, so an acyclic
        // walk ends within the bound; it stops a (malformed) cycle.
        let mut budget = reading.pinned.len().saturating_mul(8).saturating_add(8);
        while let Some(&top) = stack.last() {
            budget = match budget.checked_sub(1) {
                Some(left) => left,
                None => return invariant("the pinned values form a cycle"),
            };
            if done.contains_key(&top) {
                stack.pop();
                continue;
            }
            let def = reading.value(top)?;
            let Some(input) = def.term else {
                return invariant("a pinned value without its term");
            };
            let args = match reading.pinned.get(&top) {
                Some(PinnedForm::Op(desc, args)) => Some((*desc, args)),
                Some(PinnedForm::Const) => None,
                None => return invariant("a pinned operand that is not pinned"),
            };
            let Some((desc, args)) = args else {
                let refl = emitter.engine.prover.refl(input)?;
                done.insert(top, (input, input, refl));
                stack.pop();
                continue;
            };
            let mut missing = false;
            let mut outs = Vec::with_capacity(args.len());
            let mut proofs = Vec::with_capacity(args.len());
            for arg in args {
                let arg_def = reading.value(*arg)?;
                if reading.pinned.contains_key(&arg_def.root) {
                    match done.get(&arg_def.root) {
                        Some(&(_, output, proof)) => {
                            outs.push(output);
                            proofs.push(proof);
                        }
                        None => {
                            stack.push(arg_def.root);
                            missing = true;
                        }
                    }
                    continue;
                }
                let (Some(id), Some(entry)) = (arg_def.id, arg_def.entry) else {
                    return invariant("a pinned operand without an Id");
                };
                let (Some(output), Some(extracted), true) = (
                    out_terms.get(&id).copied(),
                    extraction.get(&id).copied(),
                    values.contains_key(&id),
                ) else {
                    return invariant("a pinned operand without its extracted form");
                };
                outs.push(output);
                proofs.push(emitter.engine.prover.trans(entry, extracted)?);
            }
            if missing {
                continue;
            }
            let output = emitter.engine.prover.op(desc, &outs);
            let proof = emitter.engine.prover.congr(desc, &proofs)?;
            let conclusion = emitter.engine.prover.conclusion(proof)?;
            if conclusion.lhs != input || conclusion.rhs != output {
                return invariant("a pinned value's proof does not conclude its terms");
            }
            done.insert(top, (input, output, proof));
            stack.pop();
        }
    }
    Ok(done)
}

/// Whether elaboration keeps the instruction in place.
fn kept(class: Option<InstClass>) -> bool {
    matches!(class, Some(InstClass::Skeleton { .. } | InstClass::Pinned))
}

fn class_of(reading: &Reading, block: usize, position: usize) -> Option<InstClass> {
    reading
        .classes
        .get(block)
        .and_then(|list| list.get(position))
        .copied()
}
