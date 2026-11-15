// trust-cg-irmid/passes/unroll.rs - full unrolling of constant-trip loops
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Full unrolling: the native lanes' constant-trip unroll
//! (`trust_cg_opt::loop_unroll`) lifted to trust-ir. A loop whose header
//! leaves it on a compare that is decided on every visit, from induction
//! variables `init + k * step` read through the bridge's address casts and
//! constant offsets, is replaced by its iterations: LLVM does the same for
//! the small loops over local arrays and the constant ranges of the corpus
//! (`c12_fold__horner`, `result_loop`, `k10_matrix`'s inner products), after
//! which the induction variables are constants per copy, the array accesses
//! are at constant offsets, and constant folding, store forwarding and
//! scalar replacement remove the arrays.
//!
//! **Which loops** (each re-derived by the checker, `trust_ir_mid_tv_unroll.rs`):
//! a natural loop with a dedicated preheader and one back edge, whose other
//! blocks form no cycle (inner loops go first: the pass repeats until
//! nothing changes), whose header ends in `condbr` on an `icmp` it computes
//! with one edge leaving the loop, and whose blocks end in `br`, `condbr`,
//! `switch`, `ret` or `unreachable`. Other edges leaving the loop (side
//! exits) are allowed. A block entered by one side exit alone that reads a
//! value of the loop, leaves without re-entering it and whose values nothing
//! else reads is an exit block, copied with each iteration; elsewhere only
//! the header's values may be used after the loop, and with a side exit only
//! in blocks the header's exit target dominates when the header's exit edge
//! is its only entry. The
//! trip count `N` is the first visit on which the compare exits, at most
//! `MAX_UNROLL_TRIPS`, and every earlier visit must be decided to continue:
//! each operand is read as a root (a constant, a value from before the loop,
//! or a header parameter) plus a constant offset, through `copy`, same-width
//! `bitcast`, `ptrtoint`/`inttoptr`/`ptrtoptr` at pointer width, `add` and
//! `sub` of a constant, `mul` of constants and `gep u8` by a constant; a
//! header parameter whose back-edge argument reads as itself plus `s` holds
//! `init + k * s` on visit `k`. Equality compares are decided on a shared
//! root, ordered ones on constants. `N` times the loop's instructions is at
//! most `MAX_UNROLLED_INSTS`.
//!
//! **Policy** (not the checker's): at most `POLICY_TRIPS` (16) trips, at
//! most `MAX_UNROLLED_INSTS` (1,024, the checker's own bound) instructions
//! copied, of which at most `POLICY_INSTS` (256) are estimated to remain
//! after constant folding ([`copy_cost`]); the cost model: no copy may keep a
//! [`heavy`] instruction (a call, or a 128-bit operation other than a slot
//! access at a constant offset), whose cost unrolling does not reduce while
//! each copy repeats it (measured on the wasm32 harness: every such unroll
//! saved at most 1% of its program's executed instructions, one of them
//! for 931 code bytes); the loop allocates nothing (the wasm32
//! lane gives an `alloca` the loop executes one frame slot, which each copy
//! would multiply), and every instruction copied must be one
//! trust-ir's validator reads without a finding (operands of the types the
//! instruction declares, no field access through a pointer, no aggregate
//! or pointer constant), because the wasm32 lane emits a mid-end output only
//! when it adds no finding, and a finding copied into a new block is a new
//! one. The header's exit compare is not copied when its branch is its only
//! use.
//!
//! **The rewrite** is the checker's construction: copy `k` of the header
//! (without parameters: they are substituted by the preheader's arguments in
//! copy 0 and by the back edge's arguments of copy `k - 1` after it) and of
//! each other block, in layout order, before the header; the copies' back
//! edges go to the next header copy, the last one's to the original header,
//! which runs once on the last visit's values and branches to the exit. The
//! witness names the trip count and the fresh blocks and values in the
//! checker's order.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{
    MAX_UNROLL_TRIPS, MAX_UNROLLED_INSTS, PassWitness, UnrollLoop, UnrollWitness,
};
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, Ty, ValueId,
};

use super::loops::{Loop, clean, def_blocks, first_free_value, rewritable_loops};
use super::{MidPass, PassContext, drop_names, int_shape, value_types_with_overflow};
use crate::cfg::TrustIrCfg;

pub(crate) struct Unroll;

/// The largest trip count the pass unrolls (the checker accepts up to
/// `MAX_UNROLL_TRIPS`).
const POLICY_TRIPS: u32 = 16;

/// The most instructions the copies of a loop may keep once the induction
/// variables are constants: the trip count times
/// [`CopyCost::unfolded_insts`]. The copied
/// instructions themselves are bounded only by the checker's
/// `MAX_UNROLLED_INSTS`.
const POLICY_INSTS: usize = 256;

/// Whether `node` is heavy for the cost model: a call, which executes a
/// body the copy does not see, or a 128-bit operation (arithmetic, a
/// compare, a select, a load or a store; an extension or truncation moves
/// one word), which the wasm32 lane emits as a sequence of `i64`
/// operations on a pair or a helper call.
/// Either costs a copy far more than the loop control unrolling removes,
/// and each copy repeats its whole sequence in the code.
fn heavy(node: &InstrNode) -> bool {
    let wide = |ty: &Ty| matches!(ty, Ty::I128 | Ty::U128);
    match &node.inst {
        Inst::Call { .. } | Inst::CallIndirect { .. } => true,
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Select { ty, .. } => wide(ty),
        _ => false,
    }
}

/// What one copy of a loop is estimated to keep once every induction
/// variable with a constant start is a constant per copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct CopyCost {
    /// The instructions of a copy that do not become constants (slot traffic
    /// included), the bound [`POLICY_INSTS`] reads.
    pub(super) unfolded_insts: usize,
    /// The [`heavy`] instructions of a copy that remain: neither constants
    /// nor a load or store through a frame slot at a constant offset (store
    /// forwarding and scalar replacement turn those into values once the
    /// offset is a constant).
    pub(super) heavy: usize,
}

/// The cost model's estimate for `lp` ([`CopyCost`]): constants propagate
/// through the pure instructions, and an address that is an `alloca` plus
/// a constant (through `copy`, pointer casts, `ptrtoint`/`inttoptr`, `add`
/// or `sub` of a constant and `gep` by constants, from a value before the
/// loop or an induction variable starting at one) is a slot address, as is
/// every load and store through it.
pub(super) fn copy_cost(
    func: &Function,
    lp: &Loop,
    ivs: &[Option<(Lin, u128)>],
    params: &[(ValueId, Ty)],
) -> CopyCost {
    let mut constant: HashSet<ValueId> = HashSet::new();
    let mut slot: HashSet<ValueId> = HashSet::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        match (&node.inst, node.results.as_slice()) {
            (Inst::Const { .. }, [r]) => {
                constant.insert(*r);
            }
            (Inst::Alloca { .. }, [r]) => {
                slot.insert(*r);
            }
            _ => {}
        }
    }
    let all: Vec<&InstrNode> = func.blocks.iter().flat_map(|b| &b.body).collect();
    // The function's constants and slot addresses first (an induction
    // variable may start at one), then the header's induction variables and
    // what they reach.
    propagate(&all, &mut constant, &mut slot);
    for (j, (p, _)) in params.iter().enumerate() {
        match ivs.get(j) {
            Some(Some((start, _))) if start.root == LinRoot::Const => {
                constant.insert(*p);
            }
            Some(Some((start, _))) if matches!(start.root, LinRoot::Before(v) if slot.contains(&v)) =>
            {
                slot.insert(*p);
            }
            _ => {}
        }
    }
    propagate(&all, &mut constant, &mut slot);
    let mut cost = CopyCost {
        unfolded_insts: 0,
        heavy: 0,
    };
    let body = func
        .blocks
        .iter()
        .filter(|b| lp.body.contains(&b.id))
        .flat_map(|b| &b.body);
    for node in body {
        let folded = node.results.first().is_some_and(|r| constant.contains(r));
        if !folded {
            cost.unfolded_insts += 1;
        }
        let slot_traffic = node.results.first().is_some_and(|r| slot.contains(r))
            || match &node.inst {
                Inst::Load {
                    ptr,
                    volatile: false,
                    ..
                }
                | Inst::Store {
                    ptr,
                    volatile: false,
                    ..
                } => slot.contains(ptr),
                _ => false,
            };
        if !folded && !slot_traffic && heavy(node) {
            cost.heavy += 1;
        }
    }
    cost
}

/// Grow `constant` and `slot` ([`copy_cost`]) over `nodes` to a fixpoint.
fn propagate(nodes: &[&InstrNode], constant: &mut HashSet<ValueId>, slot: &mut HashSet<ValueId>) {
    loop {
        let mut grew = false;
        for node in nodes {
            let [r] = node.results.as_slice() else {
                continue;
            };
            if constant.contains(r) || slot.contains(r) {
                continue;
            }
            let is_slot = |v: ValueId| slot.contains(&v);
            let is_const = |v: ValueId| constant.contains(&v);
            let slot_address = match &node.inst {
                Inst::Copy { operand, .. } => is_slot(*operand),
                Inst::Cast {
                    op: CastOp::PtrToPtr | CastOp::PtrToInt | CastOp::IntToPtr | CastOp::Bitcast,
                    operand,
                    ..
                } => is_slot(*operand),
                Inst::BinOp {
                    op: BinOp::Add,
                    lhs,
                    rhs,
                    ..
                } => (is_slot(*lhs) && is_const(*rhs)) || (is_const(*lhs) && is_slot(*rhs)),
                Inst::BinOp {
                    op: BinOp::Sub,
                    lhs,
                    rhs,
                    ..
                } => is_slot(*lhs) && is_const(*rhs),
                Inst::GEP { base, indices, .. } => {
                    is_slot(*base) && indices.iter().all(|i| is_const(*i))
                }
                _ => false,
            };
            if slot_address {
                slot.insert(*r);
                grew = true;
                continue;
            }
            if !matches!(
                node.inst,
                Inst::BinOp { .. }
                    | Inst::UnOp { .. }
                    | Inst::ICmp { .. }
                    | Inst::Cast { .. }
                    | Inst::Copy { .. }
                    | Inst::Select { .. }
            ) {
                continue;
            }
            let mut all = true;
            node.inst
                .visit_value_operands(|v| all &= constant.contains(&v));
            if all {
                constant.insert(*r);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
}

/// The evidence name of full unrolling.
pub(crate) const UNROLL_NAME: &str = "unroll";

impl MidPass for Unroll {
    fn name(&self) -> &'static str {
        UNROLL_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut cur = func.clone();
        let mut next_value = first_free_value(func);
        let mut next_block = func.blocks.iter().map(|b| b.id.index() + 1).max()?;
        let mut loops = Vec::new();
        // An unrolled inner loop may leave its enclosing loop unrollable:
        // look again until nothing changes (bounded).
        for _ in 0..64 {
            let mut done = None;
            for lp in rewritable_loops(&cur) {
                if let Some(out) = unroll(
                    &cur,
                    cx.module,
                    cx.pointer_bits,
                    &lp,
                    next_value,
                    next_block,
                ) {
                    done = Some(out);
                    break;
                }
            }
            let Some((out, claim)) = done else {
                break;
            };
            next_value += u32::try_from(claim.values.len()).ok()?;
            next_block += u32::try_from(claim.blocks.len()).ok()?;
            cur = out;
            loops.push(claim);
        }
        if loops.is_empty() {
            return None;
        }
        Some((cur, PassWitness::Unroll(UnrollWitness { loops })))
    }
}

/// A value as `root + off` modulo `2^bits`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Lin {
    pub(super) root: LinRoot,
    pub(super) off: u128,
    pub(super) bits: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LinRoot {
    Const,
    Before(ValueId),
    Param(usize),
}

pub(super) fn low(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// The pass's affine reading of the values around one loop.
pub(super) struct Lins<'f> {
    pub(super) func: &'f Function,
    pub(super) pointer_bits: u32,
    pub(super) nodes: HashMap<ValueId, &'f Inst>,
    pub(super) def_at: HashMap<ValueId, BlockId>,
    pub(super) body: &'f HashSet<BlockId>,
    pub(super) params: Vec<ValueId>,
    pub(super) types: HashMap<ValueId, Ty>,
}

impl Lins<'_> {
    pub(super) fn bits(&self, ty: &Ty) -> Option<u32> {
        int_shape(ty, self.pointer_bits)
            .map(|(b, _)| b)
            .or(matches!(
                ty,
                Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
            )
            .then_some(self.pointer_bits))
    }

    pub(super) fn lin(&self, v: ValueId, depth: u32) -> Option<Lin> {
        if depth > 64 {
            return None;
        }
        if let Some(j) = self.params.iter().position(|p| *p == v) {
            return Some(Lin {
                root: LinRoot::Param(j),
                off: 0,
                bits: self.bits(self.types.get(&v)?)?,
            });
        }
        let inside = self.body.contains(self.def_at.get(&v)?);
        let before = || -> Option<Lin> {
            if inside {
                return None;
            }
            Some(Lin {
                root: LinRoot::Before(v),
                off: 0,
                bits: self.bits(self.types.get(&v)?)?,
            })
        };
        let Some(inst) = self.nodes.get(&v) else {
            return before();
        };
        let ibits = |ty: &Ty| int_shape(ty, self.pointer_bits).map(|(b, _)| b);
        let sub = |x: ValueId| self.lin(x, depth + 1);
        let found = match inst {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } => ibits(ty).map(|bits| Lin {
                root: LinRoot::Const,
                off: (*k as u128) & low(bits),
                bits,
            }),
            Inst::Copy { ty, operand } => match (self.bits(ty), sub(*operand)) {
                (Some(bits), Some(l)) if l.bits == bits => Some(l),
                _ => None,
            },
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let through = match op {
                    CastOp::Bitcast => ibits(src_ty).is_some() && ibits(src_ty) == ibits(dst_ty),
                    CastOp::PtrToInt => ibits(dst_ty) == Some(self.pointer_bits),
                    CastOp::IntToPtr => ibits(src_ty) == Some(self.pointer_bits),
                    CastOp::PtrToPtr => true,
                    _ => false,
                };
                match (through, self.bits(dst_ty), sub(*operand)) {
                    (true, Some(bits), Some(l)) if l.bits == bits => Some(l),
                    _ => None,
                }
            }
            Inst::BinOp { op, ty, lhs, rhs } => match (ibits(ty), sub(*lhs), sub(*rhs)) {
                (Some(bits), Some(a), Some(b)) if a.bits == bits && b.bits == bits => {
                    let m = low(bits);
                    match op {
                        BinOp::Add if b.root == LinRoot::Const => Some(Lin {
                            off: a.off.wrapping_add(b.off) & m,
                            ..a
                        }),
                        BinOp::Add if a.root == LinRoot::Const => Some(Lin {
                            off: a.off.wrapping_add(b.off) & m,
                            ..b
                        }),
                        BinOp::Sub if b.root == LinRoot::Const => Some(Lin {
                            off: a.off.wrapping_sub(b.off) & m,
                            ..a
                        }),
                        BinOp::Mul if a.root == LinRoot::Const && b.root == LinRoot::Const => {
                            Some(Lin {
                                off: a.off.wrapping_mul(b.off) & m,
                                ..a
                            })
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
            Inst::GEP {
                pointee_ty: Ty::U8 | Ty::I8,
                base,
                indices,
                ..
            } => match (indices.as_slice(), sub(*base)) {
                ([index], Some(a)) if a.bits == self.pointer_bits => match sub(*index) {
                    Some(k) if k.root == LinRoot::Const && k.bits == self.pointer_bits => {
                        Some(Lin {
                            off: a.off.wrapping_add(k.off) & low(self.pointer_bits),
                            ..a
                        })
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        found.or_else(before)
    }
}

/// `pred` on two constants at `bits`.
fn holds(pred: ICmpOp, a: u128, b: u128, bits: u32) -> bool {
    let shift = 128 - bits;
    let (x, y) = (
        ((a << shift) as i128) >> shift,
        ((b << shift) as i128) >> shift,
    );
    match pred {
        ICmpOp::Eq => a == b,
        ICmpOp::Ne => a != b,
        ICmpOp::Ult => a < b,
        ICmpOp::Ule => a <= b,
        ICmpOp::Ugt => a > b,
        ICmpOp::Uge => a >= b,
        ICmpOp::Slt => x < y,
        ICmpOp::Sle => x <= y,
        ICmpOp::Sgt => x > y,
        ICmpOp::Sge => x >= y,
    }
}

/// The edges of a copied terminator moved through `map`, the arguments of
/// its edge into `clear` dropped.
pub(super) fn redirect(inst: &mut Inst, map: &dyn Fn(BlockId) -> BlockId, clear: Option<BlockId>) {
    let one = |target: &mut BlockId, args: &mut Vec<ValueId>| {
        if clear == Some(*target) {
            args.clear();
        }
        *target = map(*target);
    };
    match inst {
        Inst::Br { target, args } => one(target, args),
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => {
            one(then_target, then_args);
            one(else_target, else_args);
        }
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            one(default, default_args);
            for case in cases {
                one(&mut case.target, &mut case.args);
            }
        }
        _ => {}
    }
}

/// Whether the loop's blocks other than its header contain a cycle.
pub(super) fn inner_cycle(func: &Function, lp: &Loop) -> bool {
    let index: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    let succs = |id: BlockId| -> Vec<BlockId> {
        index
            .get(&id)
            .and_then(|&i| func.blocks[i].body.last())
            .map(|t| {
                t.inst
                    .successor_edges()
                    .iter()
                    .map(|e| e.target)
                    .filter(|t| *t != lp.header && lp.body.contains(t))
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut colour: HashMap<BlockId, bool> = HashMap::new();
    fn visit(
        b: BlockId,
        succs: &dyn Fn(BlockId) -> Vec<BlockId>,
        colour: &mut HashMap<BlockId, bool>,
    ) -> bool {
        colour.insert(b, false);
        for s in succs(b) {
            match colour.get(&s) {
                Some(false) => return true,
                Some(true) => {}
                None => {
                    if visit(s, succs, colour) {
                        return true;
                    }
                }
            }
        }
        colour.insert(b, true);
        false
    }
    lp.body
        .iter()
        .filter(|b| **b != lp.header)
        .any(|b| !colour.contains_key(b) && visit(*b, &succs, &mut colour))
}

/// `lp` unrolled in `func` with fresh names from `next_value` and
/// `next_block`, or `None`.
fn unroll(
    func: &Function,
    module: &Module,
    pointer_bits: u32,
    lp: &Loop,
    next_value: u32,
    next_block: u32,
) -> Option<(Function, UnrollLoop)> {
    if lp.back_edges != 1 || inner_cycle(func, lp) {
        return None;
    }
    let pos = |id: BlockId| func.blocks.iter().position(|b| b.id == id);
    let h = pos(lp.header)?;
    let def_at = def_blocks(func);
    let types = value_types_with_overflow(func);
    // The policy's typing also reads a direct call's results.
    let mut typed = types.clone();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let Inst::Call { callee, .. } = &node.inst
            && let Some(sig) = module
                .function_by_id(*callee)
                .and_then(|f| module.func_type(f.ty))
            && sig.returns.len() == node.results.len()
        {
            for (value, ty) in node.results.iter().zip(&sig.returns) {
                typed.insert(*value, ty.clone());
            }
        }
    }
    // ---- Terminators, the latch and the side exits.
    let mut latch = None;
    let mut side_exit = false;
    for block in func.blocks.iter().filter(|b| lp.body.contains(&b.id)) {
        let last = &block.body.last()?.inst;
        if !matches!(
            last,
            Inst::Br { .. }
                | Inst::CondBr { .. }
                | Inst::Switch { .. }
                | Inst::Return { .. }
                | Inst::Unreachable
        ) {
            return None;
        }
        // Policy: an `alloca` the loop executes keeps one frame slot in the
        // wasm32 lane; its copies would each take one.
        if block
            .body
            .iter()
            .any(|n| matches!(n.inst, Inst::Alloca { .. }))
        {
            return None;
        }
        for edge in last.successor_edges() {
            if edge.target == lp.header {
                latch = Some(block.id);
            } else if block.id != lp.header && !lp.body.contains(&edge.target) {
                side_exit = true;
            }
        }
    }
    let latch = latch?;
    // ---- The exit compare.
    let hb = &func.blocks[h];
    let Inst::CondBr {
        cond,
        then_target,
        then_args,
        else_target,
        else_args,
    } = &hb.body.last()?.inst
    else {
        return None;
    };
    let stays = lp.body.contains(then_target);
    if stays == lp.body.contains(else_target) {
        return None;
    }
    let (cont, cont_args, exit, exit_args) = if stays {
        (*then_target, then_args, *else_target, else_args)
    } else {
        (*else_target, else_args, *then_target, then_args)
    };
    // Exit blocks: entered by one side exit alone, reading a value of the
    // loop, their values read nowhere else; each copy takes its own.
    let mut entries: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &func.blocks {
        if let Some(last) = block.body.last() {
            for e in last.inst.successor_edges() {
                entries.entry(e.target).or_default().push(block.id);
            }
        }
    }
    let mut exit_blocks: HashSet<BlockId> = HashSet::new();
    for block in func
        .blocks
        .iter()
        .filter(|b| !lp.body.contains(&b.id) && b.id != func.entry)
    {
        let Some([from]) = entries.get(&block.id).map(Vec::as_slice) else {
            continue;
        };
        if !lp.body.contains(from) || *from == lp.header {
            continue;
        }
        let Some(last) = block.body.last() else {
            continue;
        };
        let leaves = matches!(
            last.inst,
            Inst::Br { .. }
                | Inst::CondBr { .. }
                | Inst::Switch { .. }
                | Inst::Return { .. }
                | Inst::Unreachable
        ) && last
            .inst
            .successor_edges()
            .iter()
            .all(|e| !lp.body.contains(&e.target));
        let mut reads = false;
        for node in &block.body {
            node.inst.visit_value_operands(|v| {
                reads |= def_at.get(&v).is_some_and(|d| lp.body.contains(d));
            });
        }
        let own: HashSet<ValueId> = block
            .params
            .iter()
            .map(|(v, _)| *v)
            .chain(block.body.iter().flat_map(|n| n.results.iter().copied()))
            .collect();
        let read_elsewhere = func.blocks.iter().filter(|b| b.id != block.id).any(|b| {
            b.body.iter().any(|n| {
                let mut hit = false;
                n.inst.visit_value_operands(|v| hit |= own.contains(&v));
                hit
            })
        });
        if leaves && reads && !read_elsewhere {
            exit_blocks.insert(block.id);
        }
    }
    // Uses after the loop: of the header's values only, and with a side exit
    // only where the exit target dominates and the header alone enters it.
    {
        let view = TrustIrCfg::new(func);
        let cfg = view.analysis();
        let entries_of_exit = entries.get(&exit).map_or(0, Vec::len);
        for block in func
            .blocks
            .iter()
            .filter(|b| !lp.body.contains(&b.id) && !exit_blocks.contains(&b.id))
        {
            let behind_exit = entries_of_exit == 1
                && cfg.idom.contains_key(&block.id)
                && cfg.dominates(exit, block.id);
            for node in &block.body {
                let mut leaks = false;
                node.inst.visit_value_operands(|v| {
                    if let Some(d) = def_at.get(&v)
                        && lp.body.contains(d)
                    {
                        leaks |= *d != lp.header || (side_exit && !behind_exit);
                    }
                });
                if leaks {
                    return None;
                }
            }
        }
    }
    let cond_at = hb
        .body
        .iter()
        .position(|n| n.results.as_slice() == [*cond])?;
    let Inst::ICmp {
        op,
        ty: cmp_ty,
        lhs,
        rhs,
    } = &hb.body[cond_at].inst
    else {
        return None;
    };
    let pre = pos(lp.preheader)?;
    let Inst::Br { args: init, .. } = &func.blocks[pre].body.last()?.inst else {
        return None;
    };
    let back: Vec<ValueId> = func.blocks[pos(latch)?]
        .body
        .last()?
        .inst
        .successor_edges()
        .into_iter()
        .find(|e| e.target == lp.header)?
        .args
        .to_vec();
    let params: Vec<(ValueId, Ty)> = hb.params.clone();
    if init.len() != params.len() || back.len() != params.len() {
        return None;
    }
    // ---- The trip count.
    let mut nodes: HashMap<ValueId, &Inst> = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let [r] = node.results.as_slice() {
            nodes.insert(*r, &node.inst);
        }
    }
    let lins = Lins {
        func,
        pointer_bits,
        nodes,
        def_at: def_at.clone(),
        body: &lp.body,
        params: params.iter().map(|(v, _)| *v).collect(),
        types: types.clone(),
    };
    let _ = lins.func;
    let mut ivs: Vec<Option<(Lin, u128)>> = Vec::new();
    for j in 0..params.len() {
        let iv = lins.lin(back[j], 0).and_then(|step| {
            let start = lins.lin(init[j], 0)?;
            (step.root == LinRoot::Param(j)
                && start.bits == step.bits
                && !matches!(start.root, LinRoot::Param(_)))
            .then_some((start, step.off))
        });
        ivs.push(iv);
    }
    let w = lins.bits(cmp_ty)?;
    let (a, b) = (lins.lin(*lhs, 0)?, lins.lin(*rhs, 0)?);
    if a.bits != w || b.bits != w {
        return None;
    }
    let visit = |l: Lin, k: u128| -> Option<Lin> {
        let LinRoot::Param(j) = l.root else {
            return Some(l);
        };
        let (start, step) = (*ivs.get(j)?)?;
        (start.bits == l.bits).then(|| Lin {
            root: start.root,
            off: start
                .off
                .wrapping_add(k.wrapping_mul(step))
                .wrapping_add(l.off)
                & low(l.bits),
            bits: l.bits,
        })
    };
    let mut trips = None;
    for k in 0..=MAX_UNROLL_TRIPS {
        let (x, y) = (visit(a, u128::from(k))?, visit(b, u128::from(k))?);
        let decided = match op {
            ICmpOp::Eq | ICmpOp::Ne if x.root == y.root => (x.off == y.off) == (*op == ICmpOp::Eq),
            _ if x.root == LinRoot::Const && y.root == LinRoot::Const => {
                holds(*op, x.off, y.off, w)
            }
            _ => return None,
        };
        if decided != stays {
            trips = Some(k);
            break;
        }
    }
    let trips = trips?;
    let n = trips as usize;
    let size: usize = func
        .blocks
        .iter()
        .filter(|b| lp.body.contains(&b.id) || exit_blocks.contains(&b.id))
        .map(|b| b.body.len())
        .sum();
    let cost = copy_cost(func, lp, &ivs, &params);
    if trips > POLICY_TRIPS
        || n * size > MAX_UNROLLED_INSTS
        || n * cost.unfolded_insts > POLICY_INSTS
        || (n > 0 && cost.heavy > 0)
    {
        return None;
    }
    if n > 0
        && params
            .iter()
            .enumerate()
            .any(|(j, (_, ty))| types.get(&init[j]) != Some(ty) || types.get(&back[j]) != Some(ty))
    {
        return None;
    }
    // ---- What is copied, and the policy on it.
    let mut uses = 0usize;
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        node.inst
            .visit_value_operands(|v| uses += usize::from(v == *cond));
    }
    let drop_cond = uses == 1;
    let others: Vec<usize> = func
        .blocks
        .iter()
        .enumerate()
        .filter(|(i, b)| lp.body.contains(&b.id) && *i != h)
        .map(|(i, _)| i)
        .chain(
            func.blocks
                .iter()
                .enumerate()
                .filter(|(_, b)| exit_blocks.contains(&b.id))
                .map(|(i, _)| i),
        )
        .collect();
    if n > 0 {
        // The copies' `br` along the continue edge passes its arguments.
        let cont_params = func
            .blocks
            .iter()
            .find(|b| b.id == cont)
            .map(|b| &b.params)?;
        if cont_params.len() != cont_args.len()
            || cont_args
                .iter()
                .zip(cont_params)
                .any(|(a, (_, t))| typed.get(a) != Some(t))
        {
            return None;
        }
        for (i, node) in hb.body.iter().enumerate() {
            if node.inst.is_terminator() || (drop_cond && i == cond_at) {
                continue;
            }
            if !clean(module, func, pointer_bits, &node.inst, &typed) {
                return None;
            }
        }
        for &bi in &others {
            if !func.blocks[bi]
                .body
                .iter()
                .all(|n| clean(module, func, pointer_bits, &n.inst, &typed))
            {
                return None;
            }
        }
    }
    // ---- The copies.
    let per_copy = 1 + others.len();
    let blocks: Vec<BlockId> = (0..n * per_copy)
        .map(|i| BlockId::new(next_block + u32::try_from(i).unwrap_or(u32::MAX)))
        .collect();
    let mut fresh = next_value;
    let mut values: Vec<ValueId> = Vec::new();
    let mut take = |values: &mut Vec<ValueId>| {
        let v = ValueId::new(fresh);
        fresh += 1;
        values.push(v);
        v
    };
    let mut out_blocks: Vec<Block> = Vec::new();
    let mut last_map: HashMap<ValueId, ValueId> = HashMap::new();
    for k in 0..n {
        let name = |m: &HashMap<ValueId, ValueId>, v: ValueId| m.get(&v).copied().unwrap_or(v);
        let mut map: HashMap<ValueId, ValueId> = HashMap::new();
        for (j, (p, _)) in params.iter().enumerate() {
            let v = if k == 0 {
                init[j]
            } else {
                name(&last_map, back[j])
            };
            map.insert(*p, v);
        }
        for (i, node) in hb.body.iter().enumerate() {
            if node.inst.is_terminator() || (drop_cond && i == cond_at) {
                continue;
            }
            for r in &node.results {
                let v = take(&mut values);
                map.insert(*r, v);
            }
        }
        for &bi in &others {
            let block = &func.blocks[bi];
            for (p, _) in &block.params {
                let v = take(&mut values);
                map.insert(*p, v);
            }
            for node in &block.body {
                for r in &node.results {
                    let v = take(&mut values);
                    map.insert(*r, v);
                }
            }
        }
        let here = |id: BlockId| -> BlockId {
            match others.iter().position(|&bi| func.blocks[bi].id == id) {
                Some(j) => blocks[k * per_copy + 1 + j],
                None => id,
            }
        };
        let next_head = if k + 1 < n {
            blocks[(k + 1) * per_copy]
        } else {
            lp.header
        };
        let mut body = Vec::new();
        for (i, node) in hb.body.iter().enumerate() {
            if node.inst.is_terminator() {
                let args: Vec<ValueId> = cont_args.iter().map(|v| name(&map, *v)).collect();
                let mut t = node.clone();
                t.inst = if cont == lp.header {
                    Inst::Br {
                        target: next_head,
                        args: if k + 1 < n { Vec::new() } else { args },
                    }
                } else {
                    Inst::Br {
                        target: here(cont),
                        args,
                    }
                };
                body.push(t);
            } else if !(drop_cond && i == cond_at) {
                let mut c = node.clone();
                trust_ir::mem2reg::rewrite_node(&mut c, &map);
                body.push(c);
            }
        }
        out_blocks.push(Block {
            id: blocks[k * per_copy],
            params: Vec::new(),
            body,
        });
        for &bi in &others {
            let block = &func.blocks[bi];
            let mut body: Vec<InstrNode> = Vec::new();
            for node in &block.body {
                let mut c = node.clone();
                trust_ir::mem2reg::rewrite_node(&mut c, &map);
                if c.inst.is_terminator() {
                    let more = k + 1 < n;
                    let to = |id: BlockId| {
                        if id == lp.header { next_head } else { here(id) }
                    };
                    redirect(&mut c.inst, &to, more.then_some(lp.header));
                }
                body.push(c);
            }
            out_blocks.push(Block {
                id: here(block.id),
                params: block
                    .params
                    .iter()
                    .map(|(p, t)| (name(&map, *p), t.clone()))
                    .collect(),
                body,
            });
        }
        last_map = map;
    }
    // ---- The preheader, the header, the removed blocks.
    let mut out = func.clone();
    if n > 0
        && let Some(t) = out.blocks[pre].body.last_mut()
    {
        t.inst = Inst::Br {
            target: blocks[0],
            args: Vec::new(),
        };
    }
    if let Some(t) = out.blocks[h].body.last_mut() {
        t.inst = Inst::Br {
            target: exit,
            args: exit_args.clone(),
        };
    }
    let mut removed: HashSet<ValueId> = HashSet::new();
    let removed_blocks: HashSet<BlockId> = others.iter().map(|&bi| func.blocks[bi].id).collect();
    for &bi in &others {
        let block = &func.blocks[bi];
        removed.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            removed.extend(node.results.iter().copied());
        }
    }
    out.blocks.retain(|b| !removed_blocks.contains(&b.id));
    let at = out.blocks.iter().position(|b| b.id == lp.header)?;
    out.blocks.splice(at..at, out_blocks);
    drop_names(&mut out, &removed);
    Some((
        out,
        UnrollLoop {
            header: lp.header,
            trips,
            blocks,
            values,
        },
    ))
}
