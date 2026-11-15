// trust-cg-verify/trust_ir_mid_tv_selbr.rs - branches on selects, and selects under their branch
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the select-branch rules ([`SelectBranchWitness`]),
//! deriving every premise from the SOURCE function and the module with this
//! module's own code. The rustc bridge spells an early-exit loop's test and
//! an `Option<&T>`'s niche as `select`s that a `switch` then reads back
//! (`switch zext(select c, 1, 0)`, `switch select(p == 0, trunc p, 1)` on a
//! pointer `select c, q, null`); LLVM branches on `c`. Two rules, applied in
//! the witness's order (every terminator rule, then every forward):
//!
//! **The terminator rule** ([`SelectTerminator`]): block `B` ends in `switch
//! s` or `condbr s`, and the witness names a `bool` value `c`. The scrutinee
//! `s` is evaluated twice by the abstract evaluator below, once assuming `c`
//! is `true` and once `false`; each evaluation must decide the edge `B`
//! takes (a case, the default, or a `condbr` arm). `B`'s terminator becomes
//! `condbr c` to the two edges, their arguments unchanged, or `br` when both
//! are the same edge. A `condbr c` requires the block defining `c` to
//! dominate `B` in the source (the rewrites only drop edges, so it still
//! does): the evaluator may decide the scrutinee through the value an
//! equality `c` pins without reading `c`. A refinement: where an arm of a `select` is poison the
//! source may branch on poison where the target branches on `c`.
//!
//! **The evaluator.** A value is KNOWN as integer bits at its width (a
//! pointer as its address at the pointer width) or as NONNULL (an address
//! that is not zero), else unknown. `c` itself is the assumed bit; when `c`
//! is `icmp eq x, k` assumed `true` (or `icmp ne x, k` assumed `false`)
//! with `k` a constant, `x` is `k`. Constants, `null`, `select` on a known
//! condition, `copy`, integer `zext`/`sext`/`trunc`/`bitcast`, `ptrtoptr`,
//! `inttoptr` from and `ptrtoint` to the pointer width (the identity on the
//! address, in the reference interpreter and on wasm), `ptrtoint` to a wider
//! integer (zero extension), `icmp` and the integer arithmetic of known
//! operands are evaluated. NONNULL is an address read as an `alloca` of a
//! known size plus a constant offset at most that size, through `copy`,
//! `ptrtoptr`, pointer-width `ptrtoint`/`inttoptr`/`bitcast`, `add` of a
//! constant and `gep u8` by a constant: no allocation contains address 0
//! and an address at most one past an allocation's end does not wrap (the
//! reference interpreter places its first allocation at 1024; the wasm32
//! lane carves frame slots below the stack pointer, above static data). It
//! survives `ptrtoptr`, `inttoptr`, `ptrtoint` to the pointer width or
//! wider, and `copy`; `icmp eq`/`ne` of NONNULL and a known zero is decided.
//!
//! **The forward rule** ([`SelectForward`]): instruction `i` of block `U`
//! reads a value `w` that is `select c, a, b` behind a chain of at most
//! [`MAX_FORWARD_CHAIN`] `copy` and cast instructions (each with one
//! operand: integer `zext`, `sext`, `trunc`, `bitcast`, and `ptrtoint`,
//! `inttoptr`, `ptrtoptr`). `U` is dominated by a block `G`, not the
//! function's entry (the call enters it too), that exactly one edge enters
//! (counting every edge of every terminator), the `then` (or
//! `else`) edge of a `condbr g` whose two targets differ, and that edge
//! fixes `c`: `g` is `c` itself, so `c` is `true` (or `false`) in `U`; or
//! assuming `c` is `x` the evaluator decides `g` to be the value that does
//! not take the edge, so `c` is not `x` in `U` (`Zip::next`'s niche test
//! `select(c, q, null) == 0` leaves its loop when `c` is false, so `c` holds
//! in the loop's body). The chain is copied, innermost first, onto `a` (or
//! `b`) under the witness's fresh names, just before `i`, and `i` reads the
//! last copy (or the arm itself, for an empty chain) wherever it read `w`.
//! The arm dominates the select, which dominates `w`'s uses. Exact: in `U`
//! the select is its arm, and the copied chain applies the same operations.
//! Indices are those of the function as the rules before it left it.
//!
//! **Unreachable blocks.** Between the two rules the witness names the
//! blocks the terminator rewrites leave unreachable from the entry; each
//! must be unreachable (and not the entry), and none of its values may be
//! used by a block that stays. They go, as constant-branch folding removes
//! them.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, Ty, ValueId,
};

use crate::fsym_layout::FsymLayout;

use super::{
    Defs, MidTvError, WitnessVerdict, block_positions, dominator_tree, drop_names, incoming_edges,
    int_shape, reachable, used_values,
};

/// The longest cast chain a forward copies.
pub const MAX_FORWARD_CHAIN: usize = 4;

/// The terminator of `block` rewritten as a branch on `cond`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SelectTerminator {
    pub block: BlockId,
    pub cond: ValueId,
}

/// The operand `operand` of instruction `index` of `block` replaced by the
/// arm of the select on `cond` its chain reaches, the chain copied under
/// `values` (innermost first) before the instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SelectForward {
    pub block: BlockId,
    pub index: usize,
    pub operand: ValueId,
    pub cond: ValueId,
    pub values: Vec<ValueId>,
}

/// The select-branch rules' claim: the terminator rewrites in order, the
/// blocks they leave unreachable, then the forwards in order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SelectBranchWitness {
    pub terminators: Vec<SelectTerminator>,
    pub removed_blocks: Vec<BlockId>,
    pub forwards: Vec<SelectForward>,
}

impl SelectBranchWitness {
    /// Rewrites claimed.
    pub fn rewrite_count(&self) -> usize {
        self.terminators.len() + self.forwards.len()
    }
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// A value the evaluator knows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Known {
    Int { raw: u128, width: u32 },
    NonNull,
}

fn int(raw: u128, width: u32) -> Known {
    Known::Int {
        raw: raw & mask(width),
        width,
    }
}

fn signed(raw: u128, width: u32) -> i128 {
    if width == 0 || width >= 128 {
        return raw as i128;
    }
    let s = 128 - width;
    ((raw << s) as i128) >> s
}

/// The single-result definitions and types of the current function.
struct View<'f> {
    func: &'f Function,
    defs: HashMap<ValueId, (usize, usize)>,
    pointer_bits: u32,
    layout: FsymLayout<'f>,
}

impl<'f> View<'f> {
    fn new(module: &'f Module, func: &'f Function, pointer_bits: u32) -> Self {
        let mut defs = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                if let [r] = node.results.as_slice() {
                    defs.entry(*r).or_insert((bi, ni));
                }
            }
        }
        Self {
            func,
            defs,
            pointer_bits,
            layout: FsymLayout::new(module),
        }
    }

    fn inst(&self, v: ValueId) -> Option<&'f Inst> {
        let &(b, n) = self.defs.get(&v)?;
        Some(&self.func.blocks[b].body[n].inst)
    }

    /// The width of an integer, `bool` or pointer-like type.
    fn width(&self, ty: &Ty) -> Option<u32> {
        if *ty == Ty::Bool {
            return Some(1);
        }
        if let Some((w, _)) = int_shape(ty, self.pointer_bits) {
            return Some(w);
        }
        matches!(
            ty,
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
        .then_some(self.pointer_bits)
    }

    /// `v` read as an `alloca` plus a constant offset (module docs).
    fn slot_offset(&self, v: ValueId, depth: usize) -> Option<(ValueId, u128)> {
        if depth > 32 {
            return None;
        }
        let pb = self.pointer_bits;
        let int_w = |ty: &Ty| int_shape(ty, pb).map(|(w, _)| w);
        let constant = |x: ValueId| match self.inst(x)? {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if int_w(ty) == Some(pb) => Some((*k as u128) & mask(pb)),
            _ => None,
        };
        match self.inst(v)? {
            Inst::Alloca { .. } => Some((v, 0)),
            Inst::Copy { operand, .. } => self.slot_offset(*operand, depth + 1),
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let through = match op {
                    CastOp::PtrToPtr => true,
                    CastOp::PtrToInt => int_w(dst_ty) == Some(pb),
                    CastOp::IntToPtr => int_w(src_ty) == Some(pb),
                    CastOp::Bitcast => int_w(src_ty) == Some(pb) && int_w(dst_ty) == Some(pb),
                    _ => false,
                };
                through.then(|| self.slot_offset(*operand, depth + 1))?
            }
            Inst::BinOp {
                op: BinOp::Add,
                ty,
                lhs,
                rhs,
            } if int_w(ty) == Some(pb) => {
                if let Some(k) = constant(*rhs) {
                    let (s, o) = self.slot_offset(*lhs, depth + 1)?;
                    Some((s, o.checked_add(k)?))
                } else {
                    let k = constant(*lhs)?;
                    let (s, o) = self.slot_offset(*rhs, depth + 1)?;
                    Some((s, o.checked_add(k)?))
                }
            }
            Inst::GEP {
                pointee_ty: Ty::U8 | Ty::I8,
                base,
                indices,
                ..
            } => {
                let [index] = indices.as_slice() else {
                    return None;
                };
                let k = constant(*index)?;
                let (s, o) = self.slot_offset(*base, depth + 1)?;
                Some((s, o.checked_add(k)?))
            }
            _ => None,
        }
    }

    /// Whether `v` is an address inside (or one past) an `alloca` of a
    /// known size.
    fn nonnull(&self, v: ValueId) -> bool {
        let Some((slot, off)) = self.slot_offset(v, 0) else {
            return false;
        };
        let Some(Inst::Alloca { ty, count, .. }) = self.inst(slot) else {
            return false;
        };
        let Ok(size) = self.layout.size(ty) else {
            return false;
        };
        let count = match count {
            None => 1u128,
            Some(c) => match self.inst(*c) {
                Some(Inst::Const {
                    value: Constant::Int(k),
                    ..
                }) if *k >= 1 => *k as u128,
                _ => return false,
            },
        };
        size > 0
            && u128::from(size)
                .checked_mul(count)
                .is_some_and(|total| off <= total)
    }

    /// `v` under the assumption, or `None` when unknown.
    fn eval(&self, v: ValueId, assume: &Assume, depth: usize) -> Option<Known> {
        if depth > 64 {
            return None;
        }
        if v == assume.cond {
            return Some(int(u128::from(assume.value), 1));
        }
        if let Some((x, k)) = assume.equal
            && v == x
        {
            return Some(k);
        }
        if let Some(known) = assume.memo.borrow().get(&v) {
            return *known;
        }
        let known = self
            .eval_def(v, assume, depth)
            .or_else(|| self.nonnull(v).then_some(Known::NonNull));
        assume.memo.borrow_mut().insert(v, known);
        known
    }

    /// `v`'s definition evaluated under the assumption.
    fn eval_def(&self, v: ValueId, assume: &Assume, depth: usize) -> Option<Known> {
        match self.inst(v) {
            Some(Inst::Const { ty, value }) => {
                let w = self.width(ty)?;
                match value {
                    Constant::Int(k) => Some(int(*k as u128, w)),
                    Constant::Bool(b) if w == 1 => Some(int(u128::from(*b), 1)),
                    _ => None,
                }
            }
            Some(Inst::NullPtr) => Some(int(0, self.pointer_bits)),
            Some(Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            }) => match self.eval(*cond, assume, depth + 1)? {
                Known::Int { raw, width: 1 } => self.eval(
                    if raw == 1 { *then_val } else { *else_val },
                    assume,
                    depth + 1,
                ),
                _ => None,
            },
            Some(Inst::Copy { operand, .. }) => self.eval(*operand, assume, depth + 1),
            Some(Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            }) => self.cast(*op, src_ty, dst_ty, *operand, assume, depth),
            Some(Inst::ICmp { op, ty, lhs, rhs }) => {
                let w = self.width(ty)?;
                let (a, b) = (
                    self.eval(*lhs, assume, depth + 1),
                    self.eval(*rhs, assume, depth + 1),
                );
                match (a, b) {
                    (
                        Some(Known::Int { raw: x, width: wa }),
                        Some(Known::Int { raw: y, width: wb }),
                    ) if wa == w && wb == w => {
                        let (sx, sy) = (signed(x, w), signed(y, w));
                        Some(int(
                            u128::from(match op {
                                ICmpOp::Eq => x == y,
                                ICmpOp::Ne => x != y,
                                ICmpOp::Ult => x < y,
                                ICmpOp::Ule => x <= y,
                                ICmpOp::Ugt => x > y,
                                ICmpOp::Uge => x >= y,
                                ICmpOp::Slt => sx < sy,
                                ICmpOp::Sle => sx <= sy,
                                ICmpOp::Sgt => sx > sy,
                                ICmpOp::Sge => sx >= sy,
                            }),
                            1,
                        ))
                    }
                    (Some(Known::NonNull), Some(Known::Int { raw: 0, .. }))
                    | (Some(Known::Int { raw: 0, .. }), Some(Known::NonNull))
                        if matches!(op, ICmpOp::Eq | ICmpOp::Ne) =>
                    {
                        Some(int(u128::from(*op == ICmpOp::Ne), 1))
                    }
                    _ => None,
                }
            }
            Some(Inst::BinOp { op, ty, lhs, rhs }) => {
                let w = int_shape(ty, self.pointer_bits)?.0;
                let (Known::Int { raw: a, width: wa }, Known::Int { raw: b, width: wb }) = (
                    self.eval(*lhs, assume, depth + 1)?,
                    self.eval(*rhs, assume, depth + 1)?,
                ) else {
                    return None;
                };
                if wa != w || wb != w {
                    return None;
                }
                let amount = || u32::try_from(b).ok().filter(|k| *k < w);
                Some(int(
                    match op {
                        BinOp::Add => a.wrapping_add(b),
                        BinOp::Sub => a.wrapping_sub(b),
                        BinOp::Mul => a.wrapping_mul(b),
                        BinOp::And => a & b,
                        BinOp::Or => a | b,
                        BinOp::Xor => a ^ b,
                        BinOp::Shl => a << amount()?,
                        BinOp::LShr => a >> amount()?,
                        _ => return None,
                    },
                    w,
                ))
            }
            _ => None,
        }
    }

    fn cast(
        &self,
        op: CastOp,
        src_ty: &Ty,
        dst_ty: &Ty,
        operand: ValueId,
        assume: &Assume,
        depth: usize,
    ) -> Option<Known> {
        let pb = self.pointer_bits;
        let (sw, dw) = (self.width(src_ty)?, self.width(dst_ty)?);
        let inner = self.eval(operand, assume, depth + 1)?;
        match (op, inner) {
            (_, Known::Int { width, .. }) if width != sw => None,
            (CastOp::ZExt, Known::Int { raw, .. }) if dw >= sw => Some(int(raw, dw)),
            (CastOp::SExt, Known::Int { raw, .. }) if dw >= sw => {
                Some(int(signed(raw, sw) as u128, dw))
            }
            (CastOp::Trunc, Known::Int { raw, .. }) if dw <= sw => Some(int(raw, dw)),
            (CastOp::Bitcast, k) if dw == sw && int_shape(src_ty, pb).is_some() => Some(k),
            (CastOp::PtrToPtr, k) => Some(k),
            (CastOp::IntToPtr, k) if sw == pb => Some(k),
            (CastOp::PtrToInt, k) if dw == pb => Some(k),
            (CastOp::PtrToInt, Known::Int { raw, .. }) if dw > pb => Some(int(raw, dw)),
            (CastOp::PtrToInt, Known::NonNull) if dw > pb => Some(Known::NonNull),
            _ => None,
        }
    }
}

/// One assumption about the named condition.
struct Assume {
    cond: ValueId,
    value: bool,
    /// The value an equality condition pins under the assumption.
    equal: Option<(ValueId, Known)>,
    /// Each value's reading under the assumption, once computed.
    memo: RefCell<HashMap<ValueId, Option<Known>>>,
}

fn assume(view: &View<'_>, cond: ValueId, value: bool) -> Assume {
    let constant = |x: ValueId| -> Option<Known> {
        match view.inst(x)? {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } => Some(int(*k as u128, view.width(ty)?)),
            _ => None,
        }
    };
    let equal = match view.inst(cond) {
        Some(Inst::ICmp { op, lhs, rhs, .. })
            if (*op == ICmpOp::Eq && value) || (*op == ICmpOp::Ne && !value) =>
        {
            constant(*rhs)
                .map(|k| (*lhs, k))
                .or_else(|| constant(*lhs).map(|k| (*rhs, k)))
        }
        _ => None,
    };
    Assume {
        cond,
        value,
        equal,
        memo: RefCell::new(HashMap::new()),
    }
}

/// The edge a terminator takes on a known scrutinee.
fn taken_edge(inst: &Inst, known: Known) -> Option<(BlockId, Vec<ValueId>)> {
    let Known::Int { raw, width } = known else {
        return None;
    };
    match inst {
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } if width == 1 => Some(if raw == 1 {
            (*then_target, then_args.clone())
        } else {
            (*else_target, else_args.clone())
        }),
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            for case in cases {
                let Constant::Int(k) = case.value else {
                    return None;
                };
                if (k as u128) & mask(width) == raw {
                    return Some((case.target, case.args.clone()));
                }
            }
            Some((*default, default_args.clone()))
        }
        _ => None,
    }
}

fn refuse(block: BlockId, why: impl Into<String>) -> MidTvError {
    MidTvError::NotSelectBranch {
        block,
        why: why.into(),
    }
}

/// The cast chain from `w` back to a `select` on `cond`: the chain's
/// instructions outermost first, and the select's arms.
fn chain_to_select(
    view: &View<'_>,
    w: ValueId,
    cond: ValueId,
) -> Option<(Vec<Inst>, ValueId, ValueId)> {
    let mut chain = Vec::new();
    let mut v = w;
    loop {
        match view.inst(v)? {
            Inst::Select {
                cond: c,
                then_val,
                else_val,
                ..
            } if *c == cond => return Some((chain, *then_val, *else_val)),
            inst @ (Inst::Copy { operand, .. }
            | Inst::Cast {
                op:
                    CastOp::ZExt
                    | CastOp::SExt
                    | CastOp::Trunc
                    | CastOp::Bitcast
                    | CastOp::PtrToInt
                    | CastOp::IntToPtr
                    | CastOp::PtrToPtr,
                operand,
                ..
            }) => {
                if chain.len() >= MAX_FORWARD_CHAIN {
                    return None;
                }
                chain.push(inst.clone());
                v = *operand;
            }
            _ => return None,
        }
    }
}

/// The value `cond` is known to hold in block `u` by a guarding edge, or
/// `None`: an edge of `condbr g` taken when `g` is `v`, into a block other
/// than the entry (which the call also enters) entered by no other edge and
/// dominating `u`, guards `cond` when `g` is `cond` (it holds `v`), or when
/// assuming `cond` is `x` makes the evaluator decide `g` to be the other
/// value than `v` (so in `u`, `cond` is not `x`).
fn guard(view: &View<'_>, cfg: &Cfg, cond: ValueId, u: usize) -> Result<Option<bool>, String> {
    let cur = view.func;
    let (positions, preds, entry) = (&cfg.positions, &cfg.preds, cfg.entry);
    let dominates = |a: usize, b: usize| cfg.dominates(a, b);
    let mut found: Option<bool> = None;
    for block in &cur.blocks {
        let Some(Inst::CondBr {
            cond: c,
            then_target,
            else_target,
            ..
        }) = block.body.last().map(|n| &n.inst)
        else {
            continue;
        };
        if then_target == else_target {
            continue;
        }
        // The value of `cond` each edge implies.
        let implied = |edge: bool| -> Option<bool> {
            if *c == cond {
                return Some(edge);
            }
            for x in [true, false] {
                if let Some(Known::Int { raw, width: 1 }) = view.eval(*c, &assume(view, cond, x), 0)
                    && (raw == 1) != edge
                {
                    return Some(!x);
                }
            }
            None
        };
        for (target, edge) in [(*then_target, true), (*else_target, false)] {
            let Some(&g) = positions.get(&target) else {
                continue;
            };
            // The call also enters the entry block, without the edge.
            if g != entry && preds[g].len() == 1 && dominates(g, u) {
                let Some(value) = implied(edge) else {
                    continue;
                };
                if found.is_some_and(|f| f != value) {
                    return Err("two guards disagree".to_string());
                }
                found = Some(value);
            }
        }
    }
    Ok(found)
}

/// The control-flow facts the forwards read: the forwards insert no
/// terminator, so they hold for every forward of one witness.
struct Cfg {
    positions: HashMap<BlockId, usize>,
    preds: Vec<Vec<usize>>,
    idom: Vec<usize>,
    entry: usize,
}

impl Cfg {
    fn of(func: &Function) -> Option<Self> {
        let positions = block_positions(func);
        let preds = incoming_edges(func, &positions);
        let (_, idom) = dominator_tree(func, &positions, &preds)?;
        let entry = *positions.get(&func.entry)?;
        Some(Self {
            positions,
            preds,
            idom,
            entry,
        })
    }

    /// Whether block `a` dominates block `b` (positions); an unreachable
    /// `b` is dominated by nothing.
    fn dominates(&self, a: usize, mut b: usize) -> bool {
        loop {
            if b == a {
                return true;
            }
            if b == self.entry || self.idom[b] == usize::MAX {
                return false;
            }
            b = self.idom[b];
        }
    }

    /// The position of the block defining `v` (as a parameter or a
    /// result).
    fn def_block(func: &Function, v: ValueId) -> Option<usize> {
        func.blocks.iter().position(|block| {
            block.params.iter().any(|(p, _)| *p == v)
                || block.body.iter().any(|n| n.results.contains(&v))
        })
    }
}

pub(super) fn rebuild_select_branch(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &SelectBranchWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut cur = source.clone();
    let mut taken: HashSet<ValueId> = used_values(source);
    for block in &source.blocks {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    let mut verdict = WitnessVerdict::default();
    // The terminator rewrites only drop edges, so a block that dominates
    // another in the source still does after any of them.
    let source_cfg = if witness.terminators.is_empty() {
        None
    } else {
        Some(Cfg::of(source).ok_or_else(|| MidTvError::TargetDiffers {
            detail: "the function has no entry block".to_string(),
        })?)
    };
    for rewrite in &witness.terminators {
        let positions = block_positions(&cur);
        let b = *positions
            .get(&rewrite.block)
            .ok_or_else(|| refuse(rewrite.block, "no such block"))?;
        let next = {
            let view = View::new(module, &cur, pointer_bits);
            if Defs::of(&cur).value_type(rewrite.cond) != Some(Ty::Bool) {
                return Err(refuse(rewrite.block, "the condition is not a bool"));
            }
            let term = &cur.blocks[b]
                .body
                .last()
                .ok_or_else(|| refuse(rewrite.block, "the block is empty"))?
                .inst;
            let scrutinee = match term {
                Inst::Switch { value, .. } => *value,
                Inst::CondBr { cond, .. } => {
                    if *cond == rewrite.cond {
                        return Err(refuse(rewrite.block, "the block already branches on it"));
                    }
                    *cond
                }
                _ => {
                    return Err(refuse(
                        rewrite.block,
                        "the block does not end in a switch or condbr",
                    ));
                }
            };
            let mut edges = Vec::new();
            for value in [true, false] {
                let a = assume(&view, rewrite.cond, value);
                let known = view.eval(scrutinee, &a, 0).ok_or_else(|| {
                    refuse(
                        rewrite.block,
                        format!("the scrutinee is not decided when the condition is {value}"),
                    )
                })?;
                edges.push(taken_edge(term, known).ok_or_else(|| {
                    refuse(
                        rewrite.block,
                        format!("no edge is decided when the condition is {value}"),
                    )
                })?);
            }
            let (t, f) = (edges[0].clone(), edges[1].clone());
            // A `condbr` on the condition reads it: its definition must
            // dominate `B` (the evaluator may have decided the scrutinee
            // through the value an equality pins, without reading `c`).
            let defined_above = source_cfg.as_ref().is_some_and(|cfg| {
                Cfg::def_block(source, rewrite.cond).is_some_and(|d| cfg.dominates(d, b))
            });
            if t != f && !defined_above {
                return Err(refuse(
                    rewrite.block,
                    "the condition's definition does not dominate the block",
                ));
            }
            if t == f {
                Inst::Br {
                    target: t.0,
                    args: t.1,
                }
            } else {
                Inst::CondBr {
                    cond: rewrite.cond,
                    then_target: t.0,
                    then_args: t.1,
                    else_target: f.0,
                    else_args: f.1,
                }
            }
        };
        if let Some(last) = cur.blocks[b].body.last_mut() {
            last.inst = next;
        }
        verdict.refinements += 1;
    }
    // ---- The blocks the terminator rewrites leave unreachable.
    {
        let live = reachable(&cur);
        let doomed: HashSet<BlockId> = witness.removed_blocks.iter().copied().collect();
        if doomed.len() != witness.removed_blocks.len() {
            return Err(MidTvError::TargetDiffers {
                detail: "a block is removed twice".to_string(),
            });
        }
        let positions = block_positions(&cur);
        let mut removed = HashSet::new();
        for id in &doomed {
            if live.contains(id) || *id == cur.entry {
                return Err(MidTvError::ReachableBlockRemoved { block: *id });
            }
            let &bi = positions
                .get(id)
                .ok_or(MidTvError::ReachableBlockRemoved { block: *id })?;
            let block = &cur.blocks[bi];
            removed.extend(block.params.iter().map(|(v, _)| *v));
            for node in &block.body {
                removed.extend(node.results.iter().copied());
            }
        }
        cur.blocks.retain(|b| !doomed.contains(&b.id));
        if let Some(value) = used_values(&cur).intersection(&removed).next() {
            return Err(MidTvError::RemovedValueUsed { value: *value });
        }
        drop_names(&mut cur, &removed);
        verdict.exact += doomed.len();
    }
    let cfg = if witness.forwards.is_empty() {
        None
    } else {
        Some(Cfg::of(&cur).ok_or_else(|| MidTvError::TargetDiffers {
            detail: "the function has no entry block".to_string(),
        })?)
    };
    for fwd in &witness.forwards {
        let positions = block_positions(&cur);
        let u = *positions
            .get(&fwd.block)
            .ok_or_else(|| refuse(fwd.block, "no such block"))?;
        if fwd.index >= cur.blocks[u].body.len() {
            return Err(refuse(fwd.block, "no such instruction"));
        }
        let mut reads = false;
        cur.blocks[u].body[fwd.index]
            .inst
            .visit_value_operands(|v| reads |= v == fwd.operand);
        if !reads {
            return Err(refuse(
                fwd.block,
                "the instruction does not read the operand",
            ));
        }
        let cfg = cfg
            .as_ref()
            .ok_or_else(|| refuse(fwd.block, "no control-flow facts"))?;
        let value = guard(&View::new(module, &cur, pointer_bits), cfg, fwd.cond, u)
            .map_err(|why| refuse(fwd.block, why))?
            .ok_or_else(|| refuse(fwd.block, "no edge on the condition guards the block"))?;
        let (chain, then_val, else_val) = {
            let view = View::new(module, &cur, pointer_bits);
            chain_to_select(&view, fwd.operand, fwd.cond).ok_or_else(|| {
                refuse(
                    fwd.block,
                    "the operand is not a select on the condition behind a cast chain",
                )
            })?
        };
        if fwd.values.len() != chain.len() {
            return Err(refuse(
                fwd.block,
                format!(
                    "the chain has {} instructions, the witness names {}",
                    chain.len(),
                    fwd.values.len()
                ),
            ));
        }
        for v in &fwd.values {
            if !taken.insert(*v) {
                return Err(refuse(fwd.block, format!("%{v} is not fresh")));
            }
        }
        let mut current = if value { then_val } else { else_val };
        let mut inserted: Vec<InstrNode> = Vec::new();
        for (inst, fresh) in chain.iter().rev().zip(&fwd.values) {
            let mut copy = inst.clone();
            match &mut copy {
                Inst::Copy { operand, .. } | Inst::Cast { operand, .. } => *operand = current,
                _ => return Err(refuse(fwd.block, "a chain instruction is not a cast")),
            }
            inserted.push(InstrNode::new(copy).with_results([*fresh]));
            current = *fresh;
        }
        let at = fwd.index;
        let map: HashMap<ValueId, ValueId> = [(fwd.operand, current)].into_iter().collect();
        trust_ir::mem2reg::rewrite_node(&mut cur.blocks[u].body[at], &map);
        let block = &mut cur.blocks[u];
        for (k, node) in inserted.into_iter().enumerate() {
            block.body.insert(at + k, node);
        }
        verdict.exact += 1;
    }
    Ok((cur, verdict))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_selbr_tests.rs"]
mod tests;
