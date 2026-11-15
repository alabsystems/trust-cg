// crates/trust-cg-eqsat/src/to_graph.rs - body reader: eligibility, classification, leaves and graph construction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reading a function body into the e-graph (sections 2-4 and 6).
//!
//! * Eligibility (section 2.5) is checked first; each refusal is a typed
//!   [`Decline`].
//! * Blocks are visited in dominator-tree preorder, instructions in body
//!   order; the hash-cons map is scoped to the dominator subtree.
//! * Classification (sections 2.2-2.4): an instruction of a graph form is a
//!   **graph instruction** exactly when every operand is *defined*; a
//!   graph-form instruction with a maybe-poison operand is a skeleton
//!   ("frontier") instruction; a `Copy` at a scalar graph type is
//!   see-through; everything else is skeleton.
//! * Defined values: graph-instruction results, see-through copies of a
//!   defined value, results of skeleton `BinOp`/`UnOp`/`ICmp`/`FCmp`/`Cast`/
//!   `Overflow`. Everything else (block parameters, loads, calls, `Undef`,
//!   skeleton `Select`, ...) may be poison and never becomes a graph operand.
//! * Leaves are named by position (section 4): `Param(block, i)` and
//!   `Result(block, k, j)` with `k` the skeleton ordinal in the block.
//! * A graph instruction on the selector trace of an exhaustive switch is
//!   **pinned** (`selector`): a graph instruction for the graph, the leaves
//!   and the derivation, and kept in place by elaboration.
//!
//! * Availability (section 4): a value is available where its definition
//!   dominates the use, except a result of a terminator, which is defined on
//!   its normal edge only: available in that terminator's own normal-edge
//!   arguments, and in the blocks its normal successor S dominates when the
//!   normal edge dominates S ([`Cfg::normal_edge_dominates`]).
//!
//! An ill-typed graph-form instruction (an operand whose type differs from
//! the operator's), a use its definition does not make available, a doubly
//! defined value, a result count that disagrees with `InstrNode::result_tys`
//! a `LandingPad` that is not the first instruction of its block, or a
//! `Resume` that breaks trust-ir's rule (c) (a literal or a selector operand,
//! or no `LandingPad` in the body) is a [`Decline::Unsupported`]: the reader
//! does not guess at invalid IR.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{BlockId, Constant, EdgeKind, Function, Inst, Module, Ty, ValueId};

use crate::Decline;
use crate::cfg::Cfg;
use crate::derivation::{ProofRef, TermRef};
use crate::eval;
use crate::graph::{Id, LeafPos};
use crate::proof::EngineError;
use crate::remap;
use crate::rewrite::Engine;
use crate::selector;
use crate::vocab::{
    BinOpCode, CONST_COST, COPY_COST, CastOpCode, CmpPred, GraphWidths, OpDesc, ScalarTy, UnOpCode,
};

/// Where a value is available (section 4, "Availability").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Avail {
    /// Where its definition `(block, slot)` dominates the use.
    Dominance,
    /// A result of a terminator whose normal edge does not dominate the
    /// normal successor: only in that terminator's own normal-edge
    /// arguments, which the reader checks at the terminator.
    OwnNormalEdge,
}

/// What the reader knows about one value.
#[derive(Debug, Clone)]
pub(crate) struct ValueDef {
    /// Defining block (index). For a result of a terminator whose normal
    /// edge dominates its normal successor S, this is S: the value is
    /// available exactly in the blocks S dominates (and in the terminator's
    /// own normal-edge arguments), and a node over it is placed in S.
    pub(crate) block: usize,
    /// Defining position: `-1` for a block parameter or a terminator result
    /// defined on the edge into `block`, else the instruction index in the
    /// block body.
    pub(crate) slot: i64,
    /// Where the value is available.
    pub(crate) avail: Avail,
    /// Declared type.
    pub(crate) ty: Ty,
    /// The graph Id: set exactly for a defined value (section 2.3) of a
    /// scalar graph type.
    pub(crate) id: Option<Id>,
    /// The term of the value as written (section 4), for a scalar graph type.
    pub(crate) term: Option<TermRef>,
    /// A proof `term -> canon(id)`, when `id` is set.
    pub(crate) entry: Option<ProofRef>,
    /// The value an opaque use is rewritten to: the value itself, or for a
    /// see-through copy the root of its operand.
    pub(crate) root: ValueId,
}

/// The class of one instruction of the input body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InstClass {
    /// A graph instruction (removed; its value lives in the graph).
    Graph,
    /// A see-through copy (removed).
    Copy,
    /// A graph instruction on the selector trace of an exhaustive switch
    /// (`selector`): its value is in the graph as a graph instruction's is,
    /// and the instruction is also kept in place with its operands remapped.
    Pinned,
    /// A skeleton instruction with its ordinal in the block.
    Skeleton { ordinal: u32 },
}

/// The graph form of a pinned instruction ([`InstClass::Pinned`]).
#[derive(Debug, Clone)]
pub(crate) enum PinnedForm {
    /// An operator over its operands, in the operator's order.
    Op(OpDesc, Vec<ValueId>),
    /// A graph constant.
    Const,
}

/// A body read into the graph.
pub(crate) struct Reading {
    pub(crate) cfg: Cfg,
    pub(crate) values: BTreeMap<ValueId, ValueDef>,
    /// Per block (index), per instruction.
    pub(crate) classes: Vec<Vec<InstClass>>,
    /// The result of every pinned instruction, with its graph form.
    pub(crate) pinned: BTreeMap<ValueId, PinnedForm>,
    /// Operator/constant nodes created fresh by a graph instruction: the
    /// instruction's (block index, instruction index).
    pub(crate) origins: BTreeMap<Id, (usize, usize)>,
    pub(crate) graph_instructions: usize,
    pub(crate) see_through_copies: usize,
    pub(crate) skeleton_instructions: usize,
    pub(crate) frontier_instructions: usize,
    pub(crate) cost_before: u64,
    /// One past the largest `ValueId` the function mentions.
    pub(crate) fresh_base: u32,
}

impl Reading {
    pub(crate) fn value(&self, value: ValueId) -> Result<&ValueDef, EngineError> {
        self.values
            .get(&value)
            .ok_or_else(|| EngineError(format!("value {} was never read", value.0)))
    }
}

/// Section 2.5: the functions both crates refuse.
pub(crate) fn eligibility(module: &Module, function: &Function) -> Result<(), Decline> {
    if function.blocks.is_empty() {
        return Err(Decline::NoBody);
    }
    if !function.proofs.is_empty() {
        return Err(Decline::FunctionProofs);
    }
    if function.summary.is_some() {
        return Err(Decline::Summary);
    }
    if function.body_gate.is_some() {
        return Err(Decline::BodyGate);
    }
    if function.source_provenance.is_some() {
        return Err(Decline::SourceProvenance);
    }
    if function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .any(|node| !node.proofs.is_empty() || node.proof_context.is_some())
    {
        return Err(Decline::InstructionProofs);
    }
    // Spec modules carry obligations of their own, and an obligation naming
    // no function could be about any function: both refuse every function
    // (fail-closed, as trust-cg-irmid does). An obligation names a function
    // by `function` or by its site.
    if !module.spec_modules.is_empty() {
        return Err(Decline::SpecModules);
    }
    // trust-ir-build's `validate_refinements` (run only when the module has
    // predicates) derives each value's fact from its defining instruction, so
    // any graph rewrite can change its verdict: refuse every function.
    if !module.predicates.is_empty() {
        return Err(Decline::RefinementPredicates);
    }
    if module.proof_obligations.iter().any(|obligation| {
        obligation.function == Some(function.id)
            || obligation
                .site
                .is_some_and(|site| site.function == function.id)
    }) {
        return Err(Decline::ModuleObligation);
    }
    if module
        .proof_obligations
        .iter()
        .any(|obligation| obligation.function.is_none() && obligation.site.is_none())
    {
        return Err(Decline::UnscopedObligation);
    }
    Ok(())
}

/// A graph form of an instruction (section 2.2), before the definedness test.
enum Form {
    Op(OpDesc, Vec<ValueId>),
    Const(ScalarTy, u128),
}

fn unsupported(message: impl Into<String>) -> Decline {
    Decline::Unsupported(message.into())
}

/// The kinds whose results are defined (section 2.3).
fn defines_results(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Overflow { .. }
    )
}

struct Reader<'a, 'r> {
    module: &'a Module,
    function: &'a Function,
    engine: &'a mut Engine<'r>,
    widths: GraphWidths,
    cfg: Cfg,
    values: BTreeMap<ValueId, ValueDef>,
    classes: Vec<Vec<InstClass>>,
    origins: BTreeMap<Id, (usize, usize)>,
    /// Values on the selector trace of an exhaustive switch (`selector`).
    trace_members: BTreeSet<ValueId>,
    pinned: BTreeMap<ValueId, PinnedForm>,
    graph_instructions: usize,
    see_through_copies: usize,
    skeleton_instructions: usize,
    frontier_instructions: usize,
    cost_before: u64,
}

/// Read `function` into `engine` (eligibility, then classification and graph
/// construction in dominator preorder).
pub(crate) fn read(
    module: &Module,
    function: &Function,
    engine: &mut Engine<'_>,
) -> Result<Reading, Decline> {
    eligibility(module, function)?;
    let cfg = Cfg::build(function)?;
    resume_operands(function)?;
    let widths = engine.widths;
    let mut reader = Reader {
        module,
        function,
        engine,
        widths,
        classes: function
            .blocks
            .iter()
            .map(|block| vec![InstClass::Graph; block.body.len()])
            .collect(),
        cfg,
        values: BTreeMap::new(),
        origins: BTreeMap::new(),
        trace_members: selector::members(function).into_iter().collect(),
        pinned: BTreeMap::new(),
        graph_instructions: 0,
        see_through_copies: 0,
        skeleton_instructions: 0,
        frontier_instructions: 0,
        cost_before: 0,
    };

    // Dominator-tree preorder with scope enter/exit events.
    enum Event {
        Enter(usize),
        Exit,
    }
    let mut stack = vec![Event::Enter(reader.cfg.entry)];
    while let Some(event) = stack.pop() {
        match event {
            Event::Enter(block) => {
                reader.engine.graph.push_scope();
                reader.block(block)?;
                stack.push(Event::Exit);
                let kids = reader.cfg.children.get(block).cloned().unwrap_or_default();
                for child in kids.into_iter().rev() {
                    stack.push(Event::Enter(child));
                }
            }
            Event::Exit => reader.engine.graph.pop_scope(),
        }
    }

    let fresh_base = fresh_base(function)?;
    Ok(Reading {
        cfg: reader.cfg,
        values: reader.values,
        classes: reader.classes,
        pinned: reader.pinned,
        origins: reader.origins,
        graph_instructions: reader.graph_instructions,
        see_through_copies: reader.see_through_copies,
        skeleton_instructions: reader.skeleton_instructions,
        frontier_instructions: reader.frontier_instructions,
        cost_before: reader.cost_before,
        fresh_base,
    })
}

/// The values trust-ir's `Resume` rule (c) refuses as a `Resume` operand
/// (trust-ir-build `validate_unwind_structure`, a flow-insensitive
/// definition lookup): results of `Const`, `NullPtr`, `Undef` and
/// `GlobalAddr`, and every `LandingPad` result but the first (the type
/// selector). The second value is whether the body has a `LandingPad`.
pub(crate) fn resume_refused_values(function: &Function) -> (BTreeSet<ValueId>, bool) {
    let mut refused = BTreeSet::new();
    let mut pad = false;
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        match node.inst {
            Inst::Const { .. } | Inst::NullPtr | Inst::Undef { .. } | Inst::GlobalAddr { .. } => {
                refused.extend(node.results.iter().copied());
            }
            Inst::LandingPad { .. } => {
                pad = true;
                refused.extend(node.results.iter().skip(1).copied());
            }
            _ => {}
        }
    }
    (refused, pad)
}

/// A body that breaks trust-ir's `Resume` rule (c) (a `Resume` in a function
/// with no `LandingPad`, or of a value [`resume_refused_values`] names) is
/// invalid IR and is declined.
fn resume_operands(function: &Function) -> Result<(), Decline> {
    let (refused, pad) = resume_refused_values(function);
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        if let Inst::Resume { exn } = &node.inst
            && (!pad || refused.contains(exn))
        {
            return Err(unsupported(
                "a Resume of a value no landing pad produced (trust-ir Resume rule (c))",
            ));
        }
    }
    Ok(())
}

fn fresh_base(function: &Function) -> Result<u32, Decline> {
    let mut max: Option<u32> = None;
    let mut see = |value: ValueId| max = Some(max.map_or(value.0, |m| m.max(value.0)));
    for block in &function.blocks {
        for (value, _) in &block.params {
            see(*value);
        }
        for node in &block.body {
            for value in &node.results {
                see(*value);
            }
            node.inst.visit_value_operands(&mut see);
        }
    }
    for (value, _) in function.value_names.iter().flatten() {
        see(*value);
    }
    match max {
        None => Ok(0),
        Some(max) => max
            .checked_add(1)
            .ok_or_else(|| unsupported("the ValueId space is exhausted")),
    }
}

impl Reader<'_, '_> {
    fn engine_error(error: EngineError) -> Decline {
        Decline::Unsupported(error.to_string())
    }

    fn define(&mut self, value: ValueId, def: ValueDef) -> Result<(), Decline> {
        if self.values.insert(value, def).is_some() {
            return Err(unsupported(format!("value {} is defined twice", value.0)));
        }
        Ok(())
    }

    fn block(&mut self, block: usize) -> Result<(), Decline> {
        let function = self.function;
        let Some(body) = function.blocks.get(block) else {
            return Err(unsupported("a block index outside the function"));
        };
        let block_id = body.id.0;
        for (index, (value, ty)) in body.params.iter().enumerate() {
            let scalar = self.widths.scalar(ty);
            let index = u32::try_from(index).map_err(|_| unsupported("too many parameters"))?;
            let term = scalar.map(|_| self.engine.prover.param(block_id, index));
            self.define(
                *value,
                ValueDef {
                    block,
                    slot: -1,
                    avail: Avail::Dominance,
                    ty: ty.clone(),
                    id: None,
                    term,
                    entry: None,
                    root: *value,
                },
            )?;
        }
        let mut ordinal: u32 = 0;
        for (position, node) in body.body.iter().enumerate() {
            let slot = i64::try_from(position).map_err(|_| unsupported("block too long"))?;
            if matches!(node.inst, Inst::LandingPad { .. }) && position != 0 {
                return Err(unsupported(
                    "a LandingPad that is not the first instruction of its block (section 4)",
                ));
            }
            // A terminator's own results may appear only in its normal-edge
            // arguments; every other operand must be available here.
            let own: &[ValueId] = if node.inst.is_terminator() {
                &node.results
            } else {
                &[]
            };
            let normal_edge = match Self::check_own_results(&node.inst, own)? {
                None => None,
                Some(target) => Some(self.cfg.block_index(target).ok_or_else(|| {
                    unsupported(format!("an edge to undeclared block {}", target.0))
                })?),
            };
            for operand in remap::operands(&node.inst) {
                if own.contains(&operand) {
                    continue;
                }
                let Some(def) = self.values.get(&operand) else {
                    return Err(unsupported(format!(
                        "value {} is used before it is defined",
                        operand.0
                    )));
                };
                let available = def.avail == Avail::Dominance
                    && if def.block == block {
                        def.slot < slot
                    } else {
                        self.cfg.dominates(def.block, block)
                    };
                if !available {
                    return Err(unsupported(format!(
                        "a use of value {} that its definition does not make available \
                         (section 4: a definition must dominate its use, and a terminator \
                         result is available only in its own normal-edge arguments and in \
                         blocks its normal successor dominates when the normal edge \
                         dominates that successor)",
                        operand.0
                    )));
                }
            }
            let result_tys = node.result_tys(self.module);
            if result_tys.len() != node.results.len() {
                return Err(unsupported(format!(
                    "an instruction with {} results but {} result types",
                    node.results.len(),
                    result_tys.len()
                )));
            }

            // See-through copy.
            if let Inst::Copy { ty, operand } = &node.inst
                && self.widths.scalar(ty).is_some()
            {
                let (Some(result), [_]) = (node.results.first(), node.results.as_slice()) else {
                    return Err(unsupported("a copy without exactly one result"));
                };
                let source = self.values.get(operand).cloned().ok_or_else(|| {
                    unsupported(format!("value {} is used before it is defined", operand.0))
                })?;
                if source.ty != *ty || result_tys.first() != Some(ty) {
                    return Err(unsupported(
                        "a copy whose operand type differs from its type",
                    ));
                }
                self.define(
                    *result,
                    ValueDef {
                        block,
                        slot,
                        avail: Avail::Dominance,
                        ty: ty.clone(),
                        ..source
                    },
                )?;
                self.set_class(block, position, InstClass::Copy);
                self.see_through_copies += 1;
                self.cost_before = self.cost_before.saturating_add(COPY_COST);
                continue;
            }

            let form = self.form(&node.inst)?;
            let all_defined = match &form {
                Some(Form::Op(_, args)) => args
                    .iter()
                    .all(|arg| self.values.get(arg).is_some_and(|def| def.id.is_some())),
                Some(Form::Const(..)) => true,
                None => false,
            };
            if let (Some(form), true) = (&form, all_defined) {
                let (Some(result), [_]) = (node.results.first(), node.results.as_slice()) else {
                    return Err(unsupported(
                        "a graph instruction without exactly one result",
                    ));
                };
                let (result_ty, cost) = match form {
                    Form::Op(desc, _) => (desc.result_ty(), desc.cost()),
                    Form::Const(ty, _) => (*ty, CONST_COST),
                };
                if result_tys.first() != Some(&result_ty.to_ty()) {
                    return Err(unsupported(
                        "a graph instruction whose result type disagrees",
                    ));
                }
                let def = self
                    .graph_value(form, block, slot, result_ty)
                    .map_err(Self::engine_error)?;
                if let Some(fresh) = def.1 {
                    self.origins.insert(fresh, (block, position));
                }
                self.define(
                    *result,
                    ValueDef {
                        root: *result,
                        ..def.0
                    },
                )?;
                if self.trace_members.contains(result) {
                    let pinned = match form {
                        Form::Op(desc, args) => PinnedForm::Op(*desc, args.clone()),
                        Form::Const(..) => PinnedForm::Const,
                    };
                    self.pinned.insert(*result, pinned);
                    self.set_class(block, position, InstClass::Pinned);
                } else {
                    self.set_class(block, position, InstClass::Graph);
                }
                self.graph_instructions += 1;
                self.cost_before = self.cost_before.saturating_add(cost);
                continue;
            }

            // Skeleton.
            if matches!(form, Some(Form::Op(..))) {
                self.frontier_instructions += 1;
            }
            self.skeleton_instructions += 1;
            self.set_class(block, position, InstClass::Skeleton { ordinal });
            let defined = defines_results(&node.inst);
            // A terminator's results are defined on its normal edge (section
            // 4): at the entry of its normal successor when that edge
            // dominates the successor, else nowhere but its own normal-edge
            // arguments.
            let (def_block, def_slot, avail) = match normal_edge {
                None => (block, slot, Avail::Dominance),
                Some(target) if self.cfg.normal_edge_dominates(block, target) => {
                    (target, -1, Avail::Dominance)
                }
                Some(_) => (block, slot, Avail::OwnNormalEdge),
            };
            for (index, (value, ty)) in node.results.iter().zip(&result_tys).enumerate() {
                let index = u32::try_from(index).map_err(|_| unsupported("too many results"))?;
                let scalar = self.widths.scalar(ty);
                let pos = LeafPos::Result {
                    block: block_id,
                    ordinal,
                    index,
                };
                let (id, term, entry) = match scalar {
                    Some(scalar) => {
                        let term = self.engine.prover.result(block_id, ordinal, index);
                        if defined {
                            let id = self
                                .engine
                                .leaf(pos, scalar, *value)
                                .map_err(Self::engine_error)?;
                            let entry =
                                self.engine.prover.refl(term).map_err(Self::engine_error)?;
                            (Some(id), Some(term), Some(entry))
                        } else {
                            (None, Some(term), None)
                        }
                    }
                    None => (None, None, None),
                };
                self.define(
                    *value,
                    ValueDef {
                        block: def_block,
                        slot: def_slot,
                        avail,
                        ty: ty.clone(),
                        id,
                        term,
                        entry,
                        root: *value,
                    },
                )?;
            }
            ordinal = ordinal
                .checked_add(1)
                .ok_or_else(|| unsupported("too many skeleton instructions"))?;
        }
        Ok(())
    }

    /// For a terminator with results (`own`): the index of its normal
    /// successor, after checking that it has exactly one normal edge and
    /// that each own result occurs among its operands no more often than in
    /// that edge's arguments (section 4: a terminator result is defined on
    /// its normal edge only). `None` for every other instruction.
    fn check_own_results(inst: &Inst, own: &[ValueId]) -> Result<Option<BlockId>, Decline> {
        if own.is_empty() {
            return Ok(None);
        }
        let edges = inst.successor_edges();
        let mut normal = edges.iter().filter(|edge| edge.kind == EdgeKind::Normal);
        let (Some(edge), None) = (normal.next(), normal.next()) else {
            return Err(unsupported(
                "a terminator with results and not exactly one normal edge",
            ));
        };
        let operands = remap::operands(inst);
        for value in own {
            let uses = operands.iter().filter(|operand| *operand == value).count();
            let on_edge = edge.args.iter().filter(|arg| *arg == value).count();
            if uses > on_edge {
                return Err(unsupported(format!(
                    "value {} is used by its own terminator outside its normal-edge \
                     arguments (section 4)",
                    value.0
                )));
            }
        }
        Ok(Some(edge.target))
    }

    fn set_class(&mut self, block: usize, position: usize, class: InstClass) {
        if let Some(slot) = self
            .classes
            .get_mut(block)
            .and_then(|list| list.get_mut(position))
        {
            *slot = class;
        }
    }

    fn operand_ty(&self, value: ValueId) -> Result<&Ty, Decline> {
        self.values
            .get(&value)
            .map(|def| &def.ty)
            .ok_or_else(|| unsupported(format!("value {} is used before it is defined", value.0)))
    }

    fn expect_ty(&self, value: ValueId, ty: &Ty) -> Result<(), Decline> {
        if self.operand_ty(value)? == ty {
            Ok(())
        } else {
            Err(unsupported(format!(
                "operand {} of a graph-form instruction has type {}, expected {ty}",
                value.0,
                self.operand_ty(value)?
            )))
        }
    }

    /// The graph form of `inst` (section 2.2), if it has one.
    fn form(&self, inst: &Inst) -> Result<Option<Form>, Decline> {
        let widths = self.widths;
        Ok(match inst {
            Inst::BinOp { op, ty, lhs, rhs } => {
                let (Some(code), Some(scalar)) = (BinOpCode::from_ir(*op), widths.scalar(ty))
                else {
                    return Ok(None);
                };
                let desc = OpDesc::Bin(code, scalar);
                if !desc.admitted() {
                    return Ok(None);
                }
                self.expect_ty(*lhs, ty)?;
                self.expect_ty(*rhs, ty)?;
                Some(Form::Op(desc, vec![*lhs, *rhs]))
            }
            Inst::UnOp { op, ty, operand } => {
                let (Some(code), Some(scalar)) = (UnOpCode::from_ir(*op), widths.scalar(ty)) else {
                    return Ok(None);
                };
                let desc = OpDesc::Un(code, scalar);
                if !desc.admitted() {
                    return Ok(None);
                }
                self.expect_ty(*operand, ty)?;
                Some(Form::Op(desc, vec![*operand]))
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let Some(scalar) = widths.scalar(ty) else {
                    return Ok(None);
                };
                let desc = OpDesc::Cmp(CmpPred::from_ir(*op), scalar);
                if !desc.admitted() {
                    return Ok(None);
                }
                self.expect_ty(*lhs, ty)?;
                self.expect_ty(*rhs, ty)?;
                Some(Form::Op(desc, vec![*lhs, *rhs]))
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let (Some(code), Some(src), Some(dst)) = (
                    CastOpCode::from_ir(*op),
                    widths.scalar(src_ty),
                    widths.scalar(dst_ty),
                ) else {
                    return Ok(None);
                };
                let desc = OpDesc::Cast(code, src, dst);
                if !desc.admitted() {
                    return Ok(None);
                }
                self.expect_ty(*operand, src_ty)?;
                Some(Form::Op(desc, vec![*operand]))
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                let Some(scalar) = widths.scalar(ty) else {
                    return Ok(None);
                };
                if *self.operand_ty(*cond)? != Ty::Bool {
                    return Ok(None);
                }
                self.expect_ty(*then_val, ty)?;
                self.expect_ty(*else_val, ty)?;
                Some(Form::Op(
                    OpDesc::Select(scalar),
                    vec![*cond, *then_val, *else_val],
                ))
            }
            Inst::Const { ty, value } => {
                let Some(scalar) = widths.scalar(ty) else {
                    return Ok(None);
                };
                let Some(width) = widths.width(scalar) else {
                    return Ok(None);
                };
                // Section 2.2 `Const` row: `Int(v)` with v in T's range at
                // the module's pointer width, `U128(v)` only at u128 above
                // i128::MAX (trust-ir's canonical spelling), `Bool` at Bool.
                // Any other constant instruction is skeleton, and its result
                // is a maybe-poison leaf (section 2.3 does not list it).
                match (scalar, value) {
                    (ScalarTy::Bool, Constant::Bool(b)) => {
                        Some(Form::Const(ScalarTy::Bool, u128::from(*b)))
                    }
                    (ScalarTy::Bool, _) => None,
                    (_, Constant::Int(v))
                        if value.value_matches_ty(ty, self.module.pointer_bits()) =>
                    {
                        Some(Form::Const(scalar, eval::i128_residue(*v, width)))
                    }
                    (ScalarTy::U128, Constant::U128(v)) if i128::try_from(*v).is_err() => {
                        Some(Form::Const(scalar, *v))
                    }
                    _ => None,
                }
            }
            _ => None,
        })
    }

    /// Create the graph value of a graph instruction: its def and the node
    /// created fresh for it, if any.
    fn graph_value(
        &mut self,
        form: &Form,
        block: usize,
        slot: i64,
        result_ty: ScalarTy,
    ) -> Result<(ValueDef, Option<Id>), EngineError> {
        match form {
            Form::Const(ty, residue) => {
                let made = self.engine.constant(*ty, *residue)?;
                let term = self.engine.graph.canon(made.id)?;
                Ok((
                    ValueDef {
                        block,
                        slot,
                        avail: Avail::Dominance,
                        ty: ty.to_ty(),
                        id: Some(made.id),
                        term: Some(term),
                        entry: Some(made.proof),
                        root: ValueId(0),
                    },
                    made.fresh,
                ))
            }
            Form::Op(desc, args) => {
                let mut ids = Vec::with_capacity(args.len());
                let mut terms = Vec::with_capacity(args.len());
                let mut entries = Vec::with_capacity(args.len());
                for arg in args {
                    let def = self
                        .values
                        .get(arg)
                        .ok_or_else(|| EngineError(format!("operand {} unread", arg.0)))?;
                    match (def.id, def.term, def.entry) {
                        (Some(id), Some(term), Some(entry)) => {
                            ids.push(id);
                            terms.push(term);
                            entries.push(entry);
                        }
                        _ => return Err(EngineError("a graph operand without an Id".to_owned())),
                    }
                }
                let term = self.engine.prover.op(*desc, &terms);
                let to_canon_args = self.engine.prover.congr(*desc, &entries)?;
                let made = self.engine.operator(*desc, &ids, 0)?;
                let entry = self.engine.prover.trans(to_canon_args, made.proof)?;
                Ok((
                    ValueDef {
                        block,
                        slot,
                        avail: Avail::Dominance,
                        ty: result_ty.to_ty(),
                        id: Some(made.id),
                        term: Some(term),
                        entry: Some(entry),
                        root: ValueId(0),
                    },
                    made.fresh,
                ))
            }
        }
    }
}
