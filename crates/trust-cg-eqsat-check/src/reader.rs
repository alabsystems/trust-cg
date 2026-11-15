// trust-cg-eqsat-check/src/reader.rs - eligibility, structure, dominance and the graph/skeleton reading of a body
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker's own reading of one function body (docs/eqsat-tier-e.md
//! sections 2 and 4, and section 8 items 1 and 2 for one body):
//!
//! * [`analyze`] refuses an ineligible function (section 2.5, the irmid
//!   classes), a structurally unreadable body (including a `LandingPad`
//!   that is not the first instruction of its block, and a `Resume` of a
//!   value no landing pad can have produced), a value defined twice and a use
//!   its definition does not make available (section 4); it then classifies
//!   every instruction as a graph instruction, a see-through `Copy` or a
//!   skeleton instruction, decides which values are defined (never poison),
//!   and builds the positional leaf table.
//! * [`terms`] gives every value its term in the shared interner.
//!
//! Fail-closed readings: an instruction is a graph instruction only when its
//! shape, types (exactly the operator's operand and result types, read with
//! `InstrNode::result_tys`), result count (one) and operand definedness are
//! all positively established; anything else, including every instruction
//! kind this reader does not name, is skeleton. A `Const` is a graph
//! constant only when its value lies in trust-ir's range for its type.
//!
//! Availability of a terminator's results (section 4): they are defined on
//! the terminator's normal edge only, and the terminator must have exactly
//! one normal edge, to a successor S. They are available in that
//! terminator's own normal-edge arguments, and in a block B when S dominates
//! B and the normal edge dominates S: S is not the entry block and every
//! other incoming edge of S (counted as edges, so the unwind edge to S or a
//! second edge from the invoking block counts) comes from a block S
//! dominates. trust-ir's `DominatorTree::definition_available_at` states the
//! same rule; this reader computes it with its own dominator tree.
//!
//! Positional rules that this reader enforces in both bodies because a graph
//! instruction's placement or a changed operand could break them while every
//! skeleton comparison holds: a `LandingPad` is the first instruction of its
//! block (the interpreter enters an unwind destination at its first
//! instruction; trust-ir-build `MisplacedLandingPad`), and a `Resume` operand
//! is not a landing pad's selector result or a literal (`Const`, `NullPtr`,
//! `Undef`, `GlobalAddr`) and occurs only in a function with a `LandingPad`
//! (trust-ir-build `validate_unwind_structure` rule (c), which looks at the
//! operand's defining instruction, so removing a `Copy` in front of a
//! literal would otherwise turn a valid input into an invalid output). The
//! validity rules of section 2.5's last paragraph (value names, instruction
//! scopes, span files, cast width directions, the default block of an
//! exhaustive `Switch`) are read by [`crate::validity`], also on both bodies.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{CastOp, Constant, EdgeKind, Function, ICmpOp, Inst, Module, Ty, ValueId};

use crate::dom::DomTree;
use crate::rejection::{Body, Rejection, TermSite};
use crate::semantics::{int_fits, int_residue};
use crate::terms::{Interner, Leaf, LeafInfo, TermError, TermId};
use crate::types::{BinK, CastK, Ctx, OpDesc, Pred, Sty, UnK};
use crate::validity;

/// The term operator of a graph instruction, or a graph constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum GraphForm {
    Op(OpDesc, Vec<ValueId>),
    Const(Sty, u128),
}

/// How the reader classifies one instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Class {
    Graph(GraphForm),
    SeeThrough(ValueId),
    /// The ordinal among the block's skeleton instructions.
    Skeleton(u32),
}

/// A value's term: an interned term, or a leaf whose type is not a graph
/// type (such a leaf can only ever equal itself).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValTerm {
    Term(TermId),
    Opaque(Leaf),
}

#[derive(Clone, Copy, Debug)]
enum DefSite {
    Param {
        block: usize,
    },
    Inst {
        block: usize,
        pos: usize,
    },
    /// A terminator's results, defined on its normal edge only. They are
    /// usable in the terminator's own normal-edge arguments (`block`, `pos`
    /// locate it), and in blocks the normal successor dominates when the
    /// normal edge dominates that successor (`succ`; `None` when it does
    /// not, or when the terminator has no unique normal edge).
    Edge {
        block: usize,
        pos: usize,
        succ: Option<usize>,
    },
}

pub(crate) struct Analysis<'f> {
    pub(crate) func: &'f Function,
    pub(crate) dom: DomTree,
    /// `classes[block index][instruction index]`.
    pub(crate) classes: Vec<Vec<Class>>,
    /// `skeleton[block index]` = instruction indices of the skeleton, in order.
    pub(crate) skeleton: Vec<Vec<usize>>,
    pub(crate) leaves: BTreeMap<Leaf, LeafInfo>,
}

fn ineligible(body: Body, class: &'static str, detail: impl Into<String>) -> Rejection {
    Rejection::Ineligible {
        body,
        class,
        detail: detail.into(),
    }
}

fn malformed(
    body: Body,
    block: Option<u32>,
    inst: Option<usize>,
    detail: impl Into<String>,
) -> Rejection {
    Rejection::MalformedBody {
        body,
        block,
        inst,
        detail: detail.into(),
    }
}

/// Section 2.5, read as the irmid ineligibility classes
/// (`crates/trust-cg-irmid/src/manager.rs`), all of them.
fn eligibility(module: &Module, func: &Function, body: Body) -> Result<(), Rejection> {
    if func.blocks.is_empty() {
        return Err(ineligible(body, "no_body", "the function has no body"));
    }
    if !module.spec_modules.is_empty() {
        return Err(ineligible(
            body,
            "spec_modules",
            "the module carries spec modules",
        ));
    }
    for (i, obligation) in module.proof_obligations.iter().enumerate() {
        let site_fn = obligation.site.as_ref().map(|s| s.function);
        match (obligation.function, site_fn) {
            (None, None) => {
                return Err(ineligible(
                    body,
                    "unscoped_obligation",
                    format!("module obligation {i} names no function"),
                ));
            }
            (f, s) if f == Some(func.id) || s == Some(func.id) => {
                return Err(ineligible(
                    body,
                    "module_obligation",
                    format!("module obligation {i} names this function"),
                ));
            }
            _ => {}
        }
    }
    if !func.proofs.is_empty() {
        return Err(ineligible(
            body,
            "function_proofs",
            "Function::proofs is not empty",
        ));
    }
    for block in &func.blocks {
        for (i, node) in block.body.iter().enumerate() {
            if !node.proofs.is_empty() || node.proof_context.is_some() {
                return Err(ineligible(
                    body,
                    "instruction_proofs",
                    format!(
                        "bb{} instruction {i} carries proofs or a proof_context",
                        block.id.0
                    ),
                ));
            }
        }
    }
    if func.summary.is_some() {
        return Err(ineligible(body, "summary", "the function has a summary"));
    }
    if func.source_provenance.is_some() {
        return Err(ineligible(
            body,
            "source_provenance",
            "the function has source_provenance",
        ));
    }
    if func.body_gate.is_some() {
        return Err(ineligible(
            body,
            "body_gate",
            "the function has a body_gate",
        ));
    }
    Ok(())
}

/// Reads one body: eligibility, structure, dominance, classification.
pub(crate) fn analyze<'f>(
    module: &Module,
    func: &'f Function,
    body: Body,
    ctx: Ctx,
) -> Result<Analysis<'f>, Rejection> {
    eligibility(module, func, body)?;

    // ---- structure
    let mut index: BTreeMap<u32, usize> = BTreeMap::new();
    for (i, block) in func.blocks.iter().enumerate() {
        if index.insert(block.id.0, i).is_some() {
            return Err(malformed(
                body,
                Some(block.id.0),
                None,
                "duplicate block id",
            ));
        }
    }
    let Some(&entry) = index.get(&func.entry.0) else {
        return Err(malformed(
            body,
            Some(func.entry.0),
            None,
            "the entry block does not exist",
        ));
    };
    let mut succs: Vec<Vec<usize>> = vec![Vec::new(); func.blocks.len()];
    let mut normal_succs: Vec<Vec<usize>> = vec![Vec::new(); func.blocks.len()];
    for (bi, block) in func.blocks.iter().enumerate() {
        let n = block.body.len();
        if n == 0 {
            return Err(malformed(body, Some(block.id.0), None, "empty block"));
        }
        for (pos, node) in block.body.iter().enumerate() {
            if pos != 0 && matches!(node.inst, Inst::LandingPad { .. }) {
                return Err(malformed(
                    body,
                    Some(block.id.0),
                    Some(pos),
                    "a landingpad that is not the first instruction of its block",
                ));
            }
            let is_term = node.inst.is_terminator();
            if is_term != (pos + 1 == n) {
                return Err(malformed(
                    body,
                    Some(block.id.0),
                    Some(pos),
                    if is_term {
                        "terminator before the end of the block"
                    } else {
                        "the block does not end with a terminator"
                    },
                ));
            }
            let tys = node.result_tys(module);
            if tys.len() != node.results.len() {
                return Err(malformed(
                    body,
                    Some(block.id.0),
                    Some(pos),
                    format!(
                        "{} result(s) but result_tys gives {}",
                        node.results.len(),
                        tys.len()
                    ),
                ));
            }
            for edge in node.inst.successor_edges() {
                let Some(&t) = index.get(&edge.target.0) else {
                    return Err(malformed(
                        body,
                        Some(block.id.0),
                        Some(pos),
                        format!("edge to missing block bb{}", edge.target.0),
                    ));
                };
                succs[bi].push(t);
                if edge.kind == EdgeKind::Normal {
                    normal_succs[bi].push(t);
                }
            }
        }
    }
    let dom = DomTree::compute(&succs, entry);
    for (bi, block) in func.blocks.iter().enumerate() {
        if !dom.is_reachable(bi) {
            return Err(ineligible(
                body,
                "unreachable_block",
                format!("bb{} is not reachable from the entry block", block.id.0),
            ));
        }
    }
    // One entry per incoming edge (not per predecessor block): the source
    // block index. Every block is reachable here.
    let mut incoming: Vec<Vec<usize>> = vec![Vec::new(); func.blocks.len()];
    for (bi, ss) in succs.iter().enumerate() {
        for &s in ss {
            incoming[s].push(bi);
        }
    }
    // Whether the normal edge from `src` to `s` dominates `s`: `s` is not
    // the entry block and every other incoming edge of `s` comes from a
    // block `s` dominates (one edge from `src` is the normal edge itself).
    let normal_edge_dominates = |src: usize, s: usize| -> bool {
        if s == entry {
            return false;
        }
        let mut skipped = false;
        incoming[s].iter().all(|&p| {
            if p == src && !skipped {
                skipped = true;
                return true;
            }
            dom.dominates(s, p)
        }) && skipped
    };

    // ---- definitions
    let mut defs: BTreeMap<ValueId, DefSite> = BTreeMap::new();
    let mut tys: BTreeMap<ValueId, Ty> = BTreeMap::new();
    let mut define = |v: ValueId, site: DefSite, ty: Ty| -> Result<(), Rejection> {
        if defs.insert(v, site).is_some() {
            return Err(Rejection::DuplicateDefinition { body, value: v.0 });
        }
        tys.insert(v, ty);
        Ok(())
    };
    for (bi, block) in func.blocks.iter().enumerate() {
        for (v, ty) in &block.params {
            define(*v, DefSite::Param { block: bi }, ty.clone())?;
        }
        for (pos, node) in block.body.iter().enumerate() {
            let site = if node.inst.is_terminator() && !node.results.is_empty() {
                let succ = match normal_succs[bi].as_slice() {
                    [s] if normal_edge_dominates(bi, *s) => Some(*s),
                    _ => None,
                };
                DefSite::Edge {
                    block: bi,
                    pos,
                    succ,
                }
            } else {
                DefSite::Inst { block: bi, pos }
            };
            for (v, ty) in node.results.iter().zip(node.result_tys(module)) {
                define(*v, site, ty)?;
            }
        }
    }

    // ---- availability of every use (section 4)
    for (bi, block) in func.blocks.iter().enumerate() {
        for (pos, node) in block.body.iter().enumerate() {
            let mut failure: Option<Rejection> = None;
            // Uses of this terminator's own results, counted here and
            // compared below with their occurrences in its normal-edge
            // arguments.
            let mut own_uses = 0usize;
            node.inst.visit_value_operands(|v| {
                if failure.is_some() {
                    return;
                }
                let not_dom = |detail: &str| Rejection::NotDominated {
                    body,
                    block: block.id.0,
                    inst: pos,
                    value: v.0,
                    detail: detail.to_owned(),
                };
                match defs.get(&v) {
                    None => failure = Some(not_dom("no definition")),
                    Some(DefSite::Param { block: d }) => {
                        if !dom.dominates(*d, bi) {
                            failure = Some(not_dom("parameter of a non-dominating block"));
                        }
                    }
                    Some(DefSite::Inst { block: d, pos: j }) => {
                        let ok = if *d == bi {
                            *j < pos
                        } else {
                            dom.dominates(*d, bi)
                        };
                        if !ok {
                            failure = Some(not_dom("defined later or in a non-dominating block"));
                        }
                    }
                    Some(DefSite::Edge {
                        block: d, pos: j, ..
                    }) if *d == bi && *j == pos => own_uses += 1,
                    Some(DefSite::Edge { succ: Some(s), .. }) => {
                        if !dom.dominates(*s, bi) {
                            failure = Some(not_dom(
                                "terminator result in a block its normal successor does not dominate",
                            ));
                        }
                    }
                    Some(DefSite::Edge { succ: None, .. }) => {
                        failure = Some(not_dom(
                            "terminator result whose normal edge does not dominate its successor",
                        ));
                    }
                }
            });
            if let Some(f) = failure {
                return Err(f);
            }
            if own_uses > 0 {
                let edges = node.inst.successor_edges();
                let normal: Vec<_> = edges
                    .iter()
                    .filter(|e| e.kind == EdgeKind::Normal)
                    .collect();
                let in_normal_args = match normal.as_slice() {
                    [e] => e.args.iter().filter(|a| node.results.contains(a)).count(),
                    _ => 0,
                };
                if in_normal_args != own_uses {
                    let value = node.results.first().map_or(0, |v| v.0);
                    return Err(Rejection::NotDominated {
                        body,
                        block: block.id.0,
                        inst: pos,
                        value,
                        detail: "terminator result used by its own terminator outside its \
                                 normal-edge arguments"
                            .to_owned(),
                    });
                }
            }
        }
    }

    // ---- Resume operands (trust-ir-build `validate_unwind_structure` rule
    // (c), read on each body's own definitions)
    check_resume_operands(func, body)?;

    // ---- the validity rules a graph rewrite can break (section 2.5, last
    // paragraph): value names, instruction scopes, span files, cast width
    // directions, exhaustive-switch default blocks
    let defined_values: BTreeSet<ValueId> = defs.keys().copied().collect();
    validity::check(module, func, body, &defined_values)?;

    // ---- classification, in reverse postorder (definitions before uses)
    let mut classes: Vec<Vec<Class>> = func
        .blocks
        .iter()
        .map(|b| vec![Class::Skeleton(u32::MAX); b.body.len()])
        .collect();
    let mut skeleton: Vec<Vec<usize>> = vec![Vec::new(); func.blocks.len()];
    let mut defined: BTreeMap<ValueId, bool> = BTreeMap::new();
    let mut leaves: BTreeMap<Leaf, LeafInfo> = BTreeMap::new();
    for &bi in &dom.rpo {
        let block = &func.blocks[bi];
        let bid = block.id.0;
        for (i, (v, ty)) in block.params.iter().enumerate() {
            defined.insert(*v, false);
            leaves.insert(
                Leaf::Param {
                    block: bid,
                    index: u32::try_from(i).unwrap_or(u32::MAX),
                },
                LeafInfo {
                    ty: ty.clone(),
                    sty: Sty::from_ir(ty, ctx),
                    defined: false,
                },
            );
        }
        let mut ordinal: u32 = 0;
        for (pos, node) in block.body.iter().enumerate() {
            let is_defined = |v: &ValueId| defined.get(v).copied().unwrap_or(false);
            if let Some(src) = see_through(node, &tys, ctx) {
                let d = is_defined(&src);
                for r in &node.results {
                    defined.insert(*r, d);
                }
                classes[bi][pos] = Class::SeeThrough(src);
                continue;
            }
            if let Some(form) = graph_form(node, module, &tys, ctx) {
                let all_defined = match &form {
                    GraphForm::Op(_, ops) => ops.iter().all(is_defined),
                    GraphForm::Const(..) => true,
                };
                if all_defined {
                    for r in &node.results {
                        defined.insert(*r, true);
                    }
                    classes[bi][pos] = Class::Graph(form);
                    continue;
                }
            }
            let results_defined = matches!(
                node.inst,
                Inst::BinOp { .. }
                    | Inst::UnOp { .. }
                    | Inst::ICmp { .. }
                    | Inst::FCmp { .. }
                    | Inst::Cast { .. }
                    | Inst::Overflow { .. }
            );
            for (j, (r, ty)) in node.results.iter().zip(node.result_tys(module)).enumerate() {
                defined.insert(*r, results_defined);
                leaves.insert(
                    Leaf::Result {
                        block: bid,
                        ordinal,
                        index: u32::try_from(j).unwrap_or(u32::MAX),
                    },
                    LeafInfo {
                        sty: Sty::from_ir(&ty, ctx),
                        ty,
                        defined: results_defined,
                    },
                );
            }
            classes[bi][pos] = Class::Skeleton(ordinal);
            skeleton[bi].push(pos);
            ordinal = ordinal.saturating_add(1);
        }
    }

    Ok(Analysis {
        func,
        dom,
        classes,
        skeleton,
        leaves,
    })
}

/// A `Resume` re-raises only what a landing pad produced: refuse one in a
/// function with no `LandingPad`, and one whose operand is defined by a
/// landing pad's second (selector) result or by a literal (`Const`,
/// `NullPtr`, `Undef`, `GlobalAddr`). This is trust-ir-build's
/// flow-insensitive rule (c); it inspects the operand's defining
/// instruction, not its value, so it is checked on each body.
fn check_resume_operands(func: &Function, body: Body) -> Result<(), Rejection> {
    let mut defining: BTreeMap<ValueId, (&Inst, usize)> = BTreeMap::new();
    let mut has_pad = false;
    for block in &func.blocks {
        for node in &block.body {
            has_pad |= matches!(node.inst, Inst::LandingPad { .. });
            for (j, r) in node.results.iter().enumerate() {
                defining.insert(*r, (&node.inst, j));
            }
        }
    }
    for block in &func.blocks {
        for (pos, node) in block.body.iter().enumerate() {
            let Inst::Resume { exn } = &node.inst else {
                continue;
            };
            let detail = match defining.get(exn) {
                _ if !has_pad => Some("resume in a function with no landingpad"),
                Some((Inst::LandingPad { .. }, j)) if *j != 0 => {
                    Some("resume of a landingpad's selector result")
                }
                Some((
                    Inst::Const { .. }
                    | Inst::NullPtr
                    | Inst::Undef { .. }
                    | Inst::GlobalAddr { .. },
                    _,
                )) => Some("resume of a literal"),
                _ => None,
            };
            if let Some(detail) = detail {
                return Err(malformed(body, Some(block.id.0), Some(pos), detail));
            }
        }
    }
    Ok(())
}

/// A see-through `Copy`: graph-typed, one result, operand of exactly that
/// type.
fn see_through(
    node: &trust_ir::InstrNode,
    tys: &BTreeMap<ValueId, Ty>,
    ctx: Ctx,
) -> Option<ValueId> {
    let Inst::Copy { ty, operand } = &node.inst else {
        return None;
    };
    Sty::from_ir(ty, ctx)?;
    if node.results.len() != 1 || tys.get(operand) != Some(ty) {
        return None;
    }
    Some(*operand)
}

fn bin_kind(op: &trust_ir::BinOp) -> Option<BinK> {
    use trust_ir::BinOp as B;
    Some(match op {
        B::Add => BinK::Add,
        B::Sub => BinK::Sub,
        B::Mul => BinK::Mul,
        B::And => BinK::And,
        B::Or => BinK::Or,
        B::Xor => BinK::Xor,
        B::RotL => BinK::RotL,
        B::RotR => BinK::RotR,
        B::BAnd => BinK::BAnd,
        B::BOr => BinK::BOr,
        B::BXor => BinK::BXor,
        _ => return None,
    })
}

fn un_kind(op: &trust_ir::UnOp) -> Option<UnK> {
    use trust_ir::UnOp as U;
    Some(match op {
        U::Neg => UnK::Neg,
        U::Not => UnK::Not,
        U::CtPop => UnK::CtPop,
        U::CtLz => UnK::CtLz,
        U::CtTz => UnK::CtTz,
        U::BSwap => UnK::BSwap,
        U::BitReverse => UnK::BitReverse,
        _ => return None,
    })
}

fn pred(op: &ICmpOp) -> Pred {
    match op {
        ICmpOp::Eq => Pred::Eq,
        ICmpOp::Ne => Pred::Ne,
        ICmpOp::Ult => Pred::Ult,
        ICmpOp::Ule => Pred::Ule,
        ICmpOp::Ugt => Pred::Ugt,
        ICmpOp::Uge => Pred::Uge,
        ICmpOp::Slt => Pred::Slt,
        ICmpOp::Sle => Pred::Sle,
        ICmpOp::Sgt => Pred::Sgt,
        ICmpOp::Sge => Pred::Sge,
    }
}

fn cast_kind(op: &CastOp) -> Option<CastK> {
    Some(match op {
        CastOp::Trunc => CastK::Trunc,
        CastOp::ZExt => CastK::ZExt,
        CastOp::SExt => CastK::SExt,
        _ => return None,
    })
}

/// The graph form of an instruction whose shape, types and result count are
/// those of a section 2.2 operator; operand definedness is decided by the
/// caller.
fn graph_form(
    node: &trust_ir::InstrNode,
    module: &Module,
    tys: &BTreeMap<ValueId, Ty>,
    ctx: Ctx,
) -> Option<GraphForm> {
    if node.results.len() != 1 {
        return None;
    }
    let result_ty = node.result_tys(module).into_iter().next()?;
    let (desc, ops) = match &node.inst {
        Inst::BinOp { op, ty, lhs, rhs } => (
            OpDesc::Bin(bin_kind(op)?, Sty::from_ir(ty, ctx)?),
            vec![*lhs, *rhs],
        ),
        Inst::UnOp { op, ty, operand } => (
            OpDesc::Un(un_kind(op)?, Sty::from_ir(ty, ctx)?),
            vec![*operand],
        ),
        Inst::ICmp { op, ty, lhs, rhs } => (
            OpDesc::Cmp(pred(op), Sty::from_ir(ty, ctx)?),
            vec![*lhs, *rhs],
        ),
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => (
            OpDesc::Cast(
                cast_kind(op)?,
                Sty::from_ir(src_ty, ctx)?,
                Sty::from_ir(dst_ty, ctx)?,
            ),
            vec![*operand],
        ),
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => (
            OpDesc::Select(Sty::from_ir(ty, ctx)?),
            vec![*cond, *then_val, *else_val],
        ),
        Inst::Const { ty, value } => {
            let t = Sty::from_ir(ty, ctx)?;
            let w = ctx.width(t)?;
            if result_ty != t.to_ir() {
                return None;
            }
            let r = match (value, t) {
                (Constant::Bool(b), Sty::Bool) => u128::from(*b),
                (Constant::Int(v), t) if int_fits(*v, t, w) => int_residue(*v, w),
                (Constant::U128(v), Sty::U128) if *v > i128::MAX as u128 => *v,
                _ => return None,
            };
            return Some(GraphForm::Const(t, r));
        }
        _ => return None,
    };
    if !desc.admitted(ctx) || result_ty != desc.result_ty().to_ir() {
        return None;
    }
    for (v, want) in ops.iter().zip(desc.operand_tys()) {
        if tys.get(v) != Some(&want.to_ir()) {
            return None;
        }
    }
    Some(GraphForm::Op(desc, ops))
}

/// The rejection for a term that cannot be formed at `site`.
pub(crate) fn term_rejection(e: TermError, site: TermSite) -> Rejection {
    match e {
        TermError::IllTyped(detail) => Rejection::IllTypedTerm { site, detail },
        TermError::UnknownLeaf(leaf) => Rejection::UnknownLeaf {
            site,
            leaf: leaf.to_string(),
        },
        TermError::MaybePoison(leaf) => Rejection::MaybePoisonLeaf {
            site,
            leaf: leaf.to_string(),
        },
    }
}

/// The term of every value of a body, interned against the input body's
/// leaf table (the caller has established that both bodies have the same
/// leaves).
pub(crate) fn terms(
    a: &Analysis<'_>,
    interner: &mut Interner,
    body: Body,
) -> Result<BTreeMap<ValueId, ValTerm>, Rejection> {
    let mut out: BTreeMap<ValueId, ValTerm> = BTreeMap::new();
    let leaf_term =
        |interner: &mut Interner, leaf: Leaf, site: TermSite| -> Result<ValTerm, Rejection> {
            match interner.leaf_info(leaf) {
                None => Err(term_rejection(TermError::UnknownLeaf(leaf), site)),
                Some(info) if info.sty.is_none() => Ok(ValTerm::Opaque(leaf)),
                Some(_) => interner
                    .leaf(leaf)
                    .map(ValTerm::Term)
                    .map_err(|e| term_rejection(e, site)),
            }
        };
    for &bi in &a.dom.rpo {
        let block = &a.func.blocks[bi];
        let bid = block.id.0;
        for (i, (v, _)) in block.params.iter().enumerate() {
            let leaf = Leaf::Param {
                block: bid,
                index: u32::try_from(i).unwrap_or(u32::MAX),
            };
            let t = leaf_term(
                interner,
                leaf,
                TermSite::Body {
                    body,
                    block: bid,
                    inst: 0,
                },
            )?;
            out.insert(*v, t);
        }
        for (pos, node) in block.body.iter().enumerate() {
            let site = TermSite::Body {
                body,
                block: bid,
                inst: pos,
            };
            match &a.classes[bi][pos] {
                Class::SeeThrough(src) => {
                    let Some(t) = out.get(src).copied() else {
                        return Err(term_rejection(
                            TermError::IllTyped(format!("copy operand %{} has no term", src.0)),
                            site,
                        ));
                    };
                    for r in &node.results {
                        out.insert(*r, t);
                    }
                }
                Class::Graph(GraphForm::Const(t, r)) => {
                    let id = interner
                        .constant(*t, *r)
                        .map_err(|e| term_rejection(e, site))?;
                    for res in &node.results {
                        out.insert(*res, ValTerm::Term(id));
                    }
                }
                Class::Graph(GraphForm::Op(desc, ops)) => {
                    let mut args = Vec::with_capacity(ops.len());
                    for v in ops {
                        match out.get(v) {
                            Some(ValTerm::Term(id)) => args.push(*id),
                            _ => {
                                return Err(term_rejection(
                                    TermError::IllTyped(format!(
                                        "operand %{} has no graph term",
                                        v.0
                                    )),
                                    site,
                                ));
                            }
                        }
                    }
                    let id = interner
                        .op(*desc, &args)
                        .map_err(|e| term_rejection(e, site))?;
                    for res in &node.results {
                        out.insert(*res, ValTerm::Term(id));
                    }
                }
                Class::Skeleton(k) => {
                    for (j, r) in node.results.iter().enumerate() {
                        let leaf = Leaf::Result {
                            block: bid,
                            ordinal: *k,
                            index: u32::try_from(j).unwrap_or(u32::MAX),
                        };
                        let t = leaf_term(interner, leaf, site.clone())?;
                        out.insert(*r, t);
                    }
                }
            }
        }
    }
    Ok(out)
}
