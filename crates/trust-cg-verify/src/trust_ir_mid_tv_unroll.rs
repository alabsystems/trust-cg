// trust-cg-verify/trust_ir_mid_tv_unroll.rs - the full unrolling checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the mid-end's full unrolling ([`UnrollWitness`]), the
//! trust-ir form of the native machine pass `trust-cg-opt/src/loop_unroll.rs`
//! (constant trip count, single latch, the loop replaced by its iterations)
//! restated over trust-ir's semantics. Everything below is derived here from
//! the SOURCE function with this module's own code; the witness names only
//! the header, the trip count and the fresh blocks and values of the copies.
//!
//! **The loop** is the natural loop of the named header `H`
//! ([`super::loops`]: every block dominated by `H`, one edge entering it from
//! outside, from a preheader `P` ending in `br H(init)`), with exactly one
//! back edge, from the LATCH. The body's blocks other than `H` form no cycle
//! (an inner loop is unrolled first or the outer loop is left). `H` ends in
//! `condbr c, ...` with one edge into the body (the CONTINUE edge) and one
//! leaving it (the EXIT edge, to `X`), and `c` is an `icmp` defined in `H`.
//! Every other block of the body ends in `br`, `condbr`, `switch`, `ret` or
//! `unreachable`; an edge of one of them to a block outside the body is a
//! SIDE EXIT. An EXIT BLOCK is a block outside the body, not the entry,
//! entered by exactly one edge, a side exit, that uses a value defined in the
//! loop, ends in one of those terminators with no edge back into the body,
//! and whose own values no other block uses: it is copied with each
//! iteration, so its uses of the loop's values read that iteration's.
//! Elsewhere outside the body only values defined in `H` may be used (the
//! original `H` still defines them on the last visit; the other blocks'
//! values reach outside only as arguments of exit edges, which each copy
//! renames), and when the loop has a side exit only in blocks dominated by
//! the exit target `X`, which `H`'s exit edge alone enters: in the target `X`
//! is still entered only from the original `H`.
//!
//! **The trip count.** Each operand of `c` is read as an AFFINE value `r + o`
//! at a width `w`: `r` is a constant (zero), an invariant base (a value
//! defined outside the loop that none of the steps below peels further), or
//! a parameter of `H`; `o` is a constant modulo `2^w`. The steps, through the
//! loop and the code before it: an integer constant; a `copy`, a same-width
//! integer `bitcast`, and `ptrtoint`, `inttoptr` and `ptrtoptr` between
//! pointer-width integers and pointers (each is the identity on an address,
//! in the reference interpreter and on wasm); `add` of a constant; `sub` of a
//! constant; a `mul` of two constants; and `gep u8|i8, p, k` by one constant
//! of pointer width. A parameter `i` of `H` whose back-edge argument reads,
//! by these steps, as `i + s` is an INDUCTION VARIABLE: on visit `k` of `H`
//! it holds `init + k * s` (modulo `2^w`), where `init` is `P`'s argument read
//! as affine; one passed back unchanged holds `init` on every visit. On visit
//! `k` each operand of `c` is then `r + o` with `r` a constant or an
//! invariant base: `==` and `!=` are decided when both operands have the
//! same root (equal offsets modulo `2^w` are equal values), the ordered
//! compares only when both are constants (at the compare's width, unsigned
//! or as two's complement). The TRIP COUNT `N` is the first visit on which
//! `H` takes its exit edge; every visit before it must be decided to
//! continue, and `N` must be at most [`MAX_UNROLL_TRIPS`]. The witness's count
//! must equal it.
//!
//! **The bound.** `N` times the instructions of the loop's blocks and exit
//! blocks (terminators included) is at most [`MAX_UNROLLED_INSTS`].
//!
//! **The rewrite.** With `B1..Bm` the body's blocks other than `H` in layout
//! order followed by the exit blocks in layout order, copy `k` (for `k < N`)
//! is a block `H_k` and blocks `B1_k..Bm_k`.
//! `H`'s parameters are substituted, not bound, in the copies: in copy 0 by
//! `P`'s arguments, in copy `k + 1` by the latch's back-edge arguments as
//! copy `k` names them (each of the parameter's own type, by this module's
//! typing: the binding the substitution drops would fault on any other).
//! `H_k` holds `H`'s instructions, renamed, without `c` when `H`'s
//! terminator is `c`'s only use, and ends in `br` along the continue edge
//! (into copy `k` of its target, or along the back edge itself when `H` is
//! the latch). A copied block keeps its parameters under fresh names, and
//! its edges go to the same copy of a body block, to `H_(k+1)` without
//! arguments on the back edge (to `H` itself with the renamed arguments from
//! the last copy), to the same copy of an exit block, and to the same block
//! outside the body on any other side exit.
//! `P` branches to `H_0` (to `H` unchanged when `N = 0`), `H` keeps its
//! parameters, its instructions and their names, runs once on the values of
//! the last visit and ends in `br X` with the exit edge's arguments, and the
//! original `B1..Bm` (the exit blocks among them) go. The copies are placed before `H`, in order; their
//! blocks and values take the witness's fresh names in that order (per copy:
//! `H_k`, then each `Bj_k`; per copy the values of `H_k`'s instructions,
//! then each `Bj_k`'s parameters and instruction results).
//!
//! Every visit of the source's loop is a copy in the target executing the
//! same instructions on the same values, and every branch of the source
//! that the rewrite removed went the way the trip count says. The rewrite
//! is exact, but for the copies of `c` it drops, a refinement (an `icmp`
//! faults on poison operands, where its copy no longer runs).

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, Ty, ValueId,
};

use super::loops::{LoopShape, def_blocks, loop_shape, refuse, value_types};
use super::{
    MidTvError, WitnessVerdict, block_positions, dominator_tree, drop_names, incoming_edges,
    int_shape, used_values,
};

/// The largest trip count this checker accepts for a full unroll.
pub const MAX_UNROLL_TRIPS: u32 = 32;

/// The most instructions the copies of one unrolled loop may hold: its trip
/// count times the instructions of its blocks, terminators included (a hard
/// cap; the pass's policy unrolls less).
pub const MAX_UNROLLED_INSTS: usize = 1024;

/// One loop at `header` replaced by its `trips` iterations; the copies'
/// blocks and values take `blocks` and `values` in the order the module
/// docs fix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnrollLoop {
    pub header: BlockId,
    pub trips: u32,
    pub blocks: Vec<BlockId>,
    pub values: Vec<ValueId>,
}

/// Full unrolling's claim, applied loop by loop.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UnrollWitness {
    pub loops: Vec<UnrollLoop>,
}

impl UnrollWitness {
    /// Loops unrolled.
    pub fn rewrite_count(&self) -> usize {
        self.loops.len()
    }
}

// ---------------------------------------------------------------------------
// Affine values
// ---------------------------------------------------------------------------

/// What an affine value is relative to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Root {
    /// Zero: the value is its offset.
    Zero,
    /// A value defined outside the loop.
    Base(ValueId),
    /// A parameter of the header, by position.
    Param(usize),
}

/// `root + off` modulo `2^bits`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Affine {
    pub(super) root: Root,
    pub(super) off: u128,
    pub(super) bits: u32,
}

pub(super) fn mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// The affine reading of a function's values around one loop.
pub(super) struct Reader<'f> {
    func: &'f Function,
    pointer_bits: u32,
    defs: HashMap<ValueId, (usize, usize)>,
    blocks: HashMap<ValueId, usize>,
    body: &'f HashSet<usize>,
    header_params: Vec<ValueId>,
    types: HashMap<ValueId, Ty>,
}

impl<'f> Reader<'f> {
    pub(super) fn new(func: &'f Function, pointer_bits: u32, shape: &'f LoopShape) -> Self {
        let mut defs = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                if let [result] = node.results.as_slice() {
                    defs.insert(*result, (bi, ni));
                }
            }
        }
        Self {
            func,
            pointer_bits,
            defs,
            blocks: def_blocks(func),
            body: &shape.body,
            header_params: func.blocks[shape.header]
                .params
                .iter()
                .map(|(v, _)| *v)
                .collect(),
            types: value_types(func),
        }
    }

    /// The width of an integer or pointer-like type.
    pub(super) fn width(&self, ty: &Ty) -> Option<u32> {
        if let Some((bits, _)) = int_shape(ty, self.pointer_bits) {
            return Some(bits);
        }
        matches!(
            ty,
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
        .then_some(self.pointer_bits)
    }

    /// `v` read as affine (module docs), or `None`.
    pub(super) fn read(&self, v: ValueId, depth: usize) -> Option<Affine> {
        if depth > 64 {
            return None;
        }
        if let Some(j) = self.header_params.iter().position(|p| *p == v) {
            let bits = self.width(self.types.get(&v)?)?;
            return Some(Affine {
                root: Root::Param(j),
                off: 0,
                bits,
            });
        }
        let outside = |v: ValueId| -> Option<Affine> {
            let bits = self.width(self.types.get(&v)?)?;
            Some(Affine {
                root: Root::Base(v),
                off: 0,
                bits,
            })
        };
        let Some(&(bi, ni)) = self.defs.get(&v) else {
            // A parameter of another block or a result of a multi-result
            // instruction: a base when defined outside the loop.
            let block = *self.blocks.get(&v)?;
            return if self.body.contains(&block) {
                None
            } else {
                outside(v)
            };
        };
        let in_loop = self.body.contains(&bi);
        let stop = || if in_loop { None } else { outside(v) };
        let inst = &self.func.blocks[bi].body[ni].inst;
        let int_bits = |ty: &Ty| int_shape(ty, self.pointer_bits).map(|(b, _)| b);
        let same = |a: Affine, bits: u32| (a.bits == bits).then_some(a);
        let read = |x: ValueId| self.read(x, depth + 1);
        let result = match inst {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } => int_bits(ty).map(|bits| Affine {
                root: Root::Zero,
                off: (*k as u128) & mask(bits),
                bits,
            }),
            Inst::Copy { ty, operand } => {
                let bits = self.width(ty);
                bits.and_then(|bits| read(*operand).and_then(|a| same(a, bits)))
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let identity = match op {
                    CastOp::Bitcast => {
                        int_bits(src_ty).is_some() && int_bits(src_ty) == int_bits(dst_ty)
                    }
                    CastOp::PtrToInt => int_bits(dst_ty) == Some(self.pointer_bits),
                    CastOp::IntToPtr => int_bits(src_ty) == Some(self.pointer_bits),
                    CastOp::PtrToPtr => true,
                    _ => false,
                };
                match (identity, self.width(dst_ty)) {
                    (true, Some(bits)) => read(*operand).and_then(|a| same(a, bits)),
                    _ => None,
                }
            }
            Inst::BinOp { op, ty, lhs, rhs } => int_bits(ty).and_then(|bits| {
                let (a, b) = (read(*lhs)?, read(*rhs)?);
                if a.bits != bits || b.bits != bits {
                    return None;
                }
                let m = mask(bits);
                match op {
                    BinOp::Add if b.root == Root::Zero => Some(Affine {
                        off: a.off.wrapping_add(b.off) & m,
                        ..a
                    }),
                    BinOp::Add if a.root == Root::Zero => Some(Affine {
                        off: b.off.wrapping_add(a.off) & m,
                        ..b
                    }),
                    BinOp::Sub if b.root == Root::Zero => Some(Affine {
                        off: a.off.wrapping_sub(b.off) & m,
                        ..a
                    }),
                    BinOp::Mul if a.root == Root::Zero && b.root == Root::Zero => Some(Affine {
                        off: a.off.wrapping_mul(b.off) & m,
                        ..a
                    }),
                    _ => None,
                }
            }),
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                ..
            } if matches!(pointee_ty, Ty::U8 | Ty::I8) && indices.len() == 1 => {
                let (a, k) = (read(*base)?, read(indices[0])?);
                (a.bits == self.pointer_bits && k.bits == self.pointer_bits && k.root == Root::Zero)
                    .then(|| Affine {
                        off: a.off.wrapping_add(k.off) & mask(self.pointer_bits),
                        ..a
                    })
            }
            _ => None,
        };
        result.or_else(stop)
    }
}

/// How the header's parameters evolve: `Some((init, step))` for an induction
/// variable (`step` 0 for one passed back unchanged), `None` otherwise.
type Evolution = Vec<Option<(Affine, u128)>>;

/// The decision of `c` on visit `k`: `Some(true)` when the compare holds.
fn decide(
    reader: &Reader<'_>,
    evolution: &Evolution,
    op: ICmpOp,
    lhs: Affine,
    rhs: Affine,
    k: u128,
) -> Option<bool> {
    let at = |a: Affine| -> Option<Affine> {
        match a.root {
            Root::Param(j) => {
                let (init, step) = (*evolution.get(j)?)?;
                if init.bits != a.bits {
                    return None;
                }
                Some(Affine {
                    root: init.root,
                    off: init
                        .off
                        .wrapping_add(k.wrapping_mul(step))
                        .wrapping_add(a.off)
                        & mask(a.bits),
                    bits: a.bits,
                })
            }
            _ => Some(a),
        }
    };
    let (a, b) = (at(lhs)?, at(rhs)?);
    if a.bits != b.bits || matches!(a.root, Root::Param(_)) || matches!(b.root, Root::Param(_)) {
        return None;
    }
    let _ = reader;
    match op {
        ICmpOp::Eq | ICmpOp::Ne if a.root == b.root => Some((a.off == b.off) == (op == ICmpOp::Eq)),
        _ if a.root == Root::Zero && b.root == Root::Zero => {
            let bits = a.bits;
            let sx = |raw: u128| -> i128 {
                if bits >= 128 {
                    raw as i128
                } else if raw & (1u128 << (bits - 1)) != 0 {
                    (raw | !mask(bits)) as i128
                } else {
                    raw as i128
                }
            };
            let (x, y) = (a.off, b.off);
            Some(match op {
                ICmpOp::Eq => x == y,
                ICmpOp::Ne => x != y,
                ICmpOp::Ult => x < y,
                ICmpOp::Ule => x <= y,
                ICmpOp::Ugt => x > y,
                ICmpOp::Uge => x >= y,
                ICmpOp::Slt => sx(x) < sx(y),
                ICmpOp::Sle => sx(x) <= sx(y),
                ICmpOp::Sgt => sx(x) > sx(y),
                ICmpOp::Sge => sx(x) >= sx(y),
            })
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The check and the rebuild
// ---------------------------------------------------------------------------

pub(super) fn rebuild_unroll(
    pointer_bits: u32,
    module: &Module,
    source: &Function,
    witness: &UnrollWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let _ = module;
    // Every claimed value and block is fresh and claimed once.
    let mut taken: HashSet<ValueId> = used_values(source);
    let mut blocks: HashSet<BlockId> = HashSet::new();
    for block in &source.blocks {
        blocks.insert(block.id);
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    for lp in &witness.loops {
        for value in &lp.values {
            if !taken.insert(*value) {
                return Err(refuse(lp.header, format!("%{value} is not fresh")));
            }
        }
        for block in &lp.blocks {
            if !blocks.insert(*block) {
                return Err(refuse(lp.header, format!("block {block} is not fresh")));
            }
        }
    }
    let mut cur = source.clone();
    let mut verdict = WitnessVerdict::default();
    for lp in &witness.loops {
        if unroll_loop(&mut cur, pointer_bits, lp)? {
            verdict.exact += 1;
        } else {
            verdict.refinements += 1;
        }
    }
    Ok((cur, verdict))
}

/// Whether a copied block may end in `inst`.
pub(super) fn admitted_terminator(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::Unreachable
    )
}

/// Move `inst`'s edges through `map` and drop the arguments of its one edge
/// into `drop_args_of` when given.
pub(super) fn retarget(
    inst: &mut Inst,
    map: &dyn Fn(BlockId) -> BlockId,
    drop_args_of: Option<BlockId>,
) {
    let edge = |target: &mut BlockId, args: &mut Vec<ValueId>| {
        if Some(*target) == drop_args_of {
            args.clear();
        }
        *target = map(*target);
    };
    match inst {
        Inst::Br { target, args } => edge(target, args),
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => {
            edge(then_target, then_args);
            edge(else_target, else_args);
        }
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            edge(default, default_args);
            for case in cases {
                edge(&mut case.target, &mut case.args);
            }
        }
        _ => {}
    }
}

/// Unroll the loop at `lp.header` in place; `true` when exact.
fn unroll_loop(cur: &mut Function, pointer_bits: u32, lp: &UnrollLoop) -> Result<bool, MidTvError> {
    let header = lp.header;
    let shape = loop_shape(cur, header)?;
    if shape.back_edges != 1 {
        return Err(refuse(header, "the loop has more than one back edge"));
    }
    let positions = block_positions(cur);
    let h = shape.header;
    let in_body = |id: BlockId| positions.get(&id).is_some_and(|p| shape.body.contains(p));
    // ---- The body's other blocks form no cycle.
    {
        let mut state: HashMap<usize, u8> = HashMap::new();
        for &start in &shape.body {
            if start == h || state.contains_key(&start) {
                continue;
            }
            let mut stack = vec![(start, 0usize)];
            state.insert(start, 1);
            while let Some((b, k)) = stack.pop() {
                let succs: Vec<usize> = cur.blocks[b]
                    .body
                    .last()
                    .map(|t| t.inst.successor_edges())
                    .unwrap_or_default()
                    .iter()
                    .filter_map(|e| positions.get(&e.target).copied())
                    .filter(|t| *t != h && shape.body.contains(t))
                    .collect();
                if k < succs.len() {
                    stack.push((b, k + 1));
                    let s = succs[k];
                    match state.get(&s) {
                        Some(1) => return Err(refuse(header, "the loop body has an inner cycle")),
                        Some(_) => {}
                        None => {
                            state.insert(s, 1);
                            stack.push((s, 0));
                        }
                    }
                } else {
                    state.insert(b, 2);
                }
            }
        }
    }
    // ---- Terminators and side exits.
    let mut side_exit = false;
    let mut latch: Option<usize> = None;
    for &b in &shape.body {
        let Some(last) = cur.blocks[b].body.last() else {
            return Err(refuse(header, "a loop block has no terminator"));
        };
        if !admitted_terminator(&last.inst) {
            return Err(refuse(
                header,
                format!(
                    "block {} ends in a terminator the copies cannot take",
                    cur.blocks[b].id
                ),
            ));
        }
        for edge in last.inst.successor_edges() {
            if edge.target == header {
                latch = Some(b);
            } else if b != h && !in_body(edge.target) {
                side_exit = true;
            }
        }
    }
    let latch = latch.ok_or_else(|| refuse(header, "no back edge"))?;
    // ---- The exit.
    let hb = &cur.blocks[h];
    let Some(Inst::CondBr {
        cond,
        then_target,
        then_args,
        else_target,
        else_args,
    }) = hb.body.last().map(|n| &n.inst)
    else {
        return Err(refuse(header, "the header does not end in a condbr"));
    };
    let then_in = in_body(*then_target);
    if then_in == in_body(*else_target) {
        return Err(refuse(
            header,
            "the header's condbr does not leave the loop exactly once",
        ));
    }
    let (cont_target, cont_args, exit_target, exit_args) = if then_in {
        (
            *then_target,
            then_args.clone(),
            *else_target,
            else_args.clone(),
        )
    } else {
        (
            *else_target,
            else_args.clone(),
            *then_target,
            then_args.clone(),
        )
    };
    let cond = *cond;
    let mut exits: Vec<usize> = Vec::new();
    // ---- Uses after the loop: only of the header's values, which the
    // original header (the last visit) still defines; with a side exit only
    // in blocks the exit target dominates, which the header's exit edge
    // alone enters (the copies' side exits then reach no such block).
    {
        let preds = incoming_edges(cur, &positions);
        let (_, idom) = dominator_tree(cur, &positions, &preds)
            .ok_or_else(|| refuse(header, "the function has no entry block"))?;
        let entry = positions[&cur.entry];
        let dominates = |a: usize, mut b: usize| loop {
            if b == a {
                return true;
            }
            if b == entry || idom[b] == usize::MAX {
                return false;
            }
            b = idom[b];
        };
        let x = positions
            .get(&exit_target)
            .copied()
            .ok_or_else(|| refuse(header, "the exit target does not exist"))?;
        let x_alone = preds[x].len() == 1;
        let defs_at = def_blocks(cur);
        // Exit blocks (module docs): entered by one side exit alone, using a
        // value of the loop, their own values used nowhere else.
        for (e, block) in cur.blocks.iter().enumerate() {
            if shape.body.contains(&e) || e == entry {
                continue;
            }
            let [from] = preds[e].as_slice() else {
                continue;
            };
            if !shape.body.contains(from) || *from == h {
                continue;
            }
            let Some(last) = block.body.last() else {
                continue;
            };
            if !admitted_terminator(&last.inst)
                || last
                    .inst
                    .successor_edges()
                    .iter()
                    .any(|t| in_body(t.target))
            {
                continue;
            }
            let mut reads_loop = false;
            for node in &block.body {
                node.inst.visit_value_operands(|v| {
                    reads_loop |= defs_at.get(&v).is_some_and(|d| shape.body.contains(d));
                });
            }
            let own: HashSet<ValueId> = block
                .params
                .iter()
                .map(|(v, _)| *v)
                .chain(block.body.iter().flat_map(|n| n.results.iter().copied()))
                .collect();
            let escapes = cur.blocks.iter().enumerate().any(|(o, other)| {
                o != e
                    && other.body.iter().any(|n| {
                        let mut hit = false;
                        n.inst.visit_value_operands(|v| hit |= own.contains(&v));
                        hit
                    })
            });
            if reads_loop && !escapes {
                exits.push(e);
            }
        }
        for (bi, block) in cur.blocks.iter().enumerate() {
            if shape.body.contains(&bi) || exits.contains(&bi) {
                continue;
            }
            for node in &block.body {
                let mut leak = false;
                node.inst.visit_value_operands(|v| {
                    if let Some(d) = defs_at.get(&v)
                        && shape.body.contains(d)
                    {
                        leak |= *d != h || (side_exit && !(x_alone && dominates(x, bi)));
                    }
                });
                if leak {
                    return Err(refuse(
                        header,
                        "a value of the loop is used outside it where the copies would not \
                         dominate the use",
                    ));
                }
            }
        }
    }
    let Some(cond_at) = hb.body.iter().position(|n| n.results.as_slice() == [cond]) else {
        return Err(refuse(
            header,
            "the exit condition is not computed in the header",
        ));
    };
    let Inst::ICmp {
        op,
        ty: cmp_ty,
        lhs,
        rhs,
    } = &hb.body[cond_at].inst
    else {
        return Err(refuse(header, "the exit condition is not an icmp"));
    };
    let (op, cmp_ty, lhs, rhs) = (*op, cmp_ty.clone(), *lhs, *rhs);
    // ---- The arguments.
    let Some(Inst::Br { args: init, .. }) =
        cur.blocks[shape.preheader].body.last().map(|n| &n.inst)
    else {
        return Err(refuse(header, "the preheader lost its branch"));
    };
    let init = init.clone();
    let back: Vec<ValueId> = cur.blocks[latch]
        .body
        .last()
        .map(|t| t.inst.successor_edges())
        .unwrap_or_default()
        .into_iter()
        .find(|e| e.target == header)
        .map(|e| e.args.to_vec())
        .unwrap_or_default();
    let params: Vec<(ValueId, Ty)> = cur.blocks[h].params.clone();
    if init.len() != params.len() || back.len() != params.len() {
        return Err(refuse(
            header,
            "an edge into the header passes the wrong arity",
        ));
    }
    // ---- The trip count.
    let trips = {
        let reader = Reader::new(cur, pointer_bits, &shape);
        let evolution: Evolution = (0..params.len())
            .map(|j| {
                let step = reader.read(back[j], 0)?;
                if step.root != Root::Param(j) {
                    return None;
                }
                let start = reader.read(init[j], 0)?;
                if matches!(start.root, Root::Param(_)) || start.bits != step.bits {
                    return None;
                }
                Some((start, step.off))
            })
            .collect();
        let width = reader.width(&cmp_ty);
        let (a, b) = match (reader.read(lhs, 0), reader.read(rhs, 0), width) {
            (Some(a), Some(b), Some(w)) if a.bits == w && b.bits == w => (a, b),
            _ => {
                return Err(refuse(
                    header,
                    "an operand of the exit compare is not affine at the compare's width",
                ));
            }
        };
        let mut trips = None;
        for k in 0..=MAX_UNROLL_TRIPS {
            let holds = decide(&reader, &evolution, op, a, b, u128::from(k)).ok_or_else(|| {
                refuse(
                    header,
                    format!("the exit compare is not decided on visit {k}"),
                )
            })?;
            if holds != then_in {
                trips = Some(k);
                break;
            }
        }
        trips.ok_or_else(|| {
            refuse(
                header,
                format!("the loop runs more than {MAX_UNROLL_TRIPS} iterations"),
            )
        })?
    };
    if trips != lp.trips {
        return Err(refuse(
            header,
            format!("the trip count is {trips}, not {}", lp.trips),
        ));
    }
    let n = trips as usize;
    let size: usize = shape
        .body
        .iter()
        .chain(&exits)
        .map(|&b| cur.blocks[b].body.len())
        .sum();
    if n.saturating_mul(size) > MAX_UNROLLED_INSTS {
        return Err(refuse(
            header,
            format!("{n} copies of {size} instructions are over the bound of {MAX_UNROLLED_INSTS}"),
        ));
    }
    // ---- Substitution types.
    if n > 0 {
        let types = value_types(cur);
        for (j, (param, ty)) in params.iter().enumerate() {
            if types.get(&init[j]) != Some(ty) || types.get(&back[j]) != Some(ty) {
                return Err(refuse(
                    header,
                    format!("an argument of %{param} does not have its type"),
                ));
            }
        }
    }
    // ---- The compare dropped from the copies.
    let mut uses = 0usize;
    for node in cur.blocks.iter().flat_map(|b| &b.body) {
        node.inst
            .visit_value_operands(|v| uses += usize::from(v == cond));
    }
    let drop_cond = uses == 1;
    // ---- The fresh names.
    let others: Vec<usize> = (0..cur.blocks.len())
        .filter(|b| shape.body.contains(b) && *b != h)
        .chain(exits.iter().copied())
        .collect();
    let per_copy_values: usize = cur.blocks[h]
        .body
        .iter()
        .enumerate()
        .filter(|(i, n)| !n.inst.is_terminator() && !(drop_cond && *i == cond_at))
        .map(|(_, n)| n.results.len())
        .sum::<usize>()
        + others
            .iter()
            .map(|&b| {
                let block = &cur.blocks[b];
                block.params.len() + block.body.iter().map(|n| n.results.len()).sum::<usize>()
            })
            .sum::<usize>();
    if lp.blocks.len() != n * (1 + others.len()) {
        return Err(refuse(
            header,
            format!(
                "the witness names {} blocks, the copies need {}",
                lp.blocks.len(),
                n * (1 + others.len())
            ),
        ));
    }
    if lp.values.len() != n * per_copy_values {
        return Err(refuse(
            header,
            format!(
                "the witness names {} values, the copies define {}",
                lp.values.len(),
                n * per_copy_values
            ),
        ));
    }
    // ---- The copies.
    let mut fresh_values = lp.values.iter().copied();
    let mut copies: Vec<Block> = Vec::new();
    let mut prev: HashMap<ValueId, ValueId> = HashMap::new();
    for k in 0..n {
        let rename = |m: &HashMap<ValueId, ValueId>, v: ValueId| *m.get(&v).unwrap_or(&v);
        let mut sigma: HashMap<ValueId, ValueId> = HashMap::new();
        for (j, (param, _)) in params.iter().enumerate() {
            let v = if k == 0 {
                init[j]
            } else {
                rename(&prev, back[j])
            };
            sigma.insert(*param, v);
        }
        let block_of = |id: BlockId| -> BlockId {
            if id == header {
                return id;
            }
            match others.iter().position(|&b| cur.blocks[b].id == id) {
                Some(j) => lp.blocks[k * (1 + others.len()) + 1 + j],
                None => id,
            }
        };
        let h_k = lp.blocks[k * (1 + others.len())];
        let next_header = if k + 1 < n {
            lp.blocks[(k + 1) * (1 + others.len())]
        } else {
            header
        };
        // Fresh names, in the module docs' order.
        for (i, node) in cur.blocks[h].body.iter().enumerate() {
            if node.inst.is_terminator() || (drop_cond && i == cond_at) {
                continue;
            }
            for r in &node.results {
                sigma.insert(*r, fresh_values.next().unwrap_or(*r));
            }
        }
        for &b in &others {
            let block = &cur.blocks[b];
            for (p, _) in &block.params {
                sigma.insert(*p, fresh_values.next().unwrap_or(*p));
            }
            for node in &block.body {
                for r in &node.results {
                    sigma.insert(*r, fresh_values.next().unwrap_or(*r));
                }
            }
        }
        // H_k.
        let mut body: Vec<InstrNode> = Vec::new();
        for (i, node) in cur.blocks[h].body.iter().enumerate() {
            if node.inst.is_terminator() {
                let mut term = node.clone();
                let args: Vec<ValueId> = cont_args.iter().map(|v| rename(&sigma, *v)).collect();
                term.inst = if cont_target == header {
                    if k + 1 < n {
                        Inst::Br {
                            target: next_header,
                            args: Vec::new(),
                        }
                    } else {
                        Inst::Br {
                            target: header,
                            args,
                        }
                    }
                } else {
                    Inst::Br {
                        target: block_of(cont_target),
                        args,
                    }
                };
                body.push(term);
                continue;
            }
            if drop_cond && i == cond_at {
                continue;
            }
            let mut copy = node.clone();
            trust_ir::mem2reg::rewrite_node(&mut copy, &sigma);
            body.push(copy);
        }
        copies.push(Block {
            id: h_k,
            params: Vec::new(),
            body,
        });
        // The other blocks.
        for &b in &others {
            let block = &cur.blocks[b];
            let mut body: Vec<InstrNode> = Vec::new();
            for node in &block.body {
                let mut copy = node.clone();
                trust_ir::mem2reg::rewrite_node(&mut copy, &sigma);
                if copy.inst.is_terminator() {
                    let last = k + 1 == n;
                    let map = |id: BlockId| {
                        if id == header {
                            if last { header } else { next_header }
                        } else {
                            block_of(id)
                        }
                    };
                    let drop = (!last).then_some(header);
                    retarget(&mut copy.inst, &map, drop);
                }
                body.push(copy);
            }
            copies.push(Block {
                id: block_of(block.id),
                params: block
                    .params
                    .iter()
                    .map(|(p, t)| (rename(&sigma, *p), t.clone()))
                    .collect(),
                body,
            });
        }
        prev = sigma;
    }
    // ---- The preheader, the header and the removed blocks.
    if n > 0 {
        let first = lp.blocks[0];
        if let Some(last) = cur.blocks[shape.preheader].body.last_mut() {
            last.inst = Inst::Br {
                target: first,
                args: Vec::new(),
            };
        }
    }
    if let Some(last) = cur.blocks[h].body.last_mut() {
        last.inst = Inst::Br {
            target: exit_target,
            args: exit_args,
        };
    }
    let mut removed: HashSet<ValueId> = HashSet::new();
    for &b in &others {
        let block = &cur.blocks[b];
        removed.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            removed.extend(node.results.iter().copied());
        }
    }
    let header_block = cur.blocks[h].id;
    let removed_ids: HashSet<BlockId> = others.iter().map(|&b| cur.blocks[b].id).collect();
    cur.blocks.retain(|b| !removed_ids.contains(&b.id));
    let at = cur
        .blocks
        .iter()
        .position(|b| b.id == header_block)
        .unwrap_or(cur.blocks.len());
    cur.blocks.splice(at..at, copies);
    drop_names(cur, &removed);
    Ok(!(drop_cond && n > 0))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_unroll_tests.rs"]
mod tests;
