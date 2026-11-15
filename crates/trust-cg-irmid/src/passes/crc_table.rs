// trust-cg-irmid/passes/crc_table.rs - a bit-serial byte loop as a table lookup
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The CRC-table rewrite: the bit-serial CRC step over one byte (`for _ in
//! 0..8 { c = if c & 1 != 0 { P ^ (c >> 1) } else { c >> 1 } }`, which full
//! unrolling leaves as eight shift-xor diamonds) becomes one load from a
//! 256-entry read-only table, as LLVM builds for `dyn_hash`'s CRC hasher.
//! Eight branches per byte become a multiply, an address and a load.
//!
//! **Which regions** (each re-derived by the checker,
//! `trust_ir_mid_tv_crctable.rs`): a block `E` ending in `condbr` or
//! `switch`, the blocks reachable from it before a join `X`
//! with one parameter (acyclic, entered only from `E` or each other, as `X`
//! is), and `E`'s pure tail from an index `s`; every instruction a pure
//! integer operation (`const`, `copy`, `add`, `sub`, `mul`, `and`, `or`,
//! `xor`, shifts, `icmp`, `select`, integer casts), its values used only
//! inside the region, its only non-constant input a value `x` whose
//! definition bounds it below 256 (an `and` with a constant, a `zext` of a
//! byte, a `urem` or `lshr` by a constant). The region is evaluated for
//! every byte; the table holds the 256 results.
//!
//! **Policy** (not the checker's): the region xors one constant, the
//! polynomial, at least four times, and holds at least sixteen
//! instructions, so the lookup replaces a bit loop and not a short
//! computation; the result is an integer of one, two, four or eight bytes.
//! Like constant-table promotion, it appends a read-only global, so
//! [`crate::MidConfig::promote_constant_tables`] withholds it.
//!
//! **The rewrite** is the checker's construction: `E` keeps its
//! instructions before `s` and ends in the lookup (`global_addr`, the input
//! as `i32`, the entry size, the byte offset, an in-bounds `gep`, the load)
//! and `br X` with the entry; the region's blocks go.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{CrcTable, CrcTableWitness, PassWitness};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, Global, ICmpOp, Inst, InstrNode, Linkage, Ty, TyId,
    ValueId, Visibility,
};

use super::loops::first_free_value;
use super::{MidPass, PassContext, drop_names, int_shape, sole_defs, value_types};

pub(crate) struct CrcTablePass;

/// The evidence name of the CRC-table rewrite.
pub(crate) const CRC_TABLE_NAME: &str = "crc_table";

/// The fewest xors of the polynomial a region must hold.
const MIN_ROUNDS: usize = 4;

/// The fewest instructions a region must hold.
const MIN_REGION_INSTS: usize = 16;

/// The most blocks a region may span (eight rounds of a diamond are 24).
const MAX_REGION_BLOCKS: usize = 64;

/// Each value's uses, by block position and instruction index.
type Uses = HashMap<ValueId, Vec<(usize, usize)>>;

/// The pass's own integer reading: bits at a width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Word {
    bits: u128,
    width: u32,
}

fn low(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn word(bits: u128, width: u32) -> Word {
    Word {
        bits: bits & low(width),
        width,
    }
}

fn as_signed(w: Word) -> i128 {
    if w.width == 0 || w.width >= 128 {
        return w.bits as i128;
    }
    let s = 128 - w.width;
    ((w.bits << s) as i128) >> s
}

fn width_of(ty: &Ty, pointer_bits: u32) -> Option<u32> {
    if *ty == Ty::Bool {
        return Some(1);
    }
    int_shape(ty, pointer_bits).map(|(b, _)| b)
}

fn const_word(inst: &Inst, pointer_bits: u32) -> Option<Word> {
    match inst {
        Inst::Const {
            ty,
            value: Constant::Int(k),
        } => Some(word(*k as u128, width_of(ty, pointer_bits)?)),
        Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(b),
        } => Some(word(u128::from(*b), 1)),
        _ => None,
    }
}

fn pure(inst: &Inst) -> bool {
    match inst {
        Inst::Const { .. } | Inst::Copy { .. } | Inst::ICmp { .. } | Inst::Select { .. } => true,
        Inst::BinOp { op, .. } => matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::And
                | BinOp::Or
                | BinOp::Xor
                | BinOp::Shl
                | BinOp::LShr
                | BinOp::AShr
        ),
        Inst::Cast { op, .. } => matches!(
            op,
            CastOp::ZExt | CastOp::SExt | CastOp::Trunc | CastOp::Bitcast
        ),
        _ => false,
    }
}

/// One instruction on known operands, by the pass's own semantics; `None`
/// where the checker would refuse.
fn step(inst: &Inst, pointer_bits: u32, val: &dyn Fn(ValueId) -> Option<Word>) -> Option<Word> {
    if let Some(w) = const_word(inst, pointer_bits) {
        return Some(w);
    }
    let w = |ty: &Ty| width_of(ty, pointer_bits);
    match inst {
        Inst::Copy { ty, operand } => val(*operand).filter(|v| Some(v.width) == w(ty)),
        Inst::BinOp { op, ty, lhs, rhs } => {
            let n = w(ty)?;
            let (a, b) = (val(*lhs)?, val(*rhs)?);
            if a.width != n || b.width != n {
                return None;
            }
            let amount = || u32::try_from(b.bits).ok().filter(|k| *k < n);
            Some(word(
                match op {
                    BinOp::Add => a.bits.wrapping_add(b.bits),
                    BinOp::Sub => a.bits.wrapping_sub(b.bits),
                    BinOp::Mul => a.bits.wrapping_mul(b.bits),
                    BinOp::And => a.bits & b.bits,
                    BinOp::Or => a.bits | b.bits,
                    BinOp::Xor => a.bits ^ b.bits,
                    BinOp::Shl => a.bits << amount()?,
                    BinOp::LShr => a.bits >> amount()?,
                    BinOp::AShr => (as_signed(a) >> amount()?) as u128,
                    _ => return None,
                },
                n,
            ))
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let n = w(ty)?;
            let (a, b) = (val(*lhs)?, val(*rhs)?);
            if a.width != n || b.width != n {
                return None;
            }
            let (x, y) = (as_signed(a), as_signed(b));
            Some(word(
                u128::from(match op {
                    ICmpOp::Eq => a.bits == b.bits,
                    ICmpOp::Ne => a.bits != b.bits,
                    ICmpOp::Ult => a.bits < b.bits,
                    ICmpOp::Ule => a.bits <= b.bits,
                    ICmpOp::Ugt => a.bits > b.bits,
                    ICmpOp::Uge => a.bits >= b.bits,
                    ICmpOp::Slt => x < y,
                    ICmpOp::Sle => x <= y,
                    ICmpOp::Sgt => x > y,
                    ICmpOp::Sge => x >= y,
                }),
                1,
            ))
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            let c = val(*cond).filter(|c| c.width == 1)?;
            val(if c.bits == 1 { *then_val } else { *else_val }).filter(|v| Some(v.width) == w(ty))
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let (s, d) = (w(src_ty)?, w(dst_ty)?);
            let v = val(*operand).filter(|v| v.width == s)?;
            match op {
                CastOp::ZExt if d >= s => Some(word(v.bits, d)),
                CastOp::SExt if d >= s => Some(word(as_signed(v) as u128, d)),
                CastOp::Trunc if d <= s => Some(word(v.bits, d)),
                CastOp::Bitcast if d == s => Some(v),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The largest value `x`'s definition admits, by the pass's own reading.
fn byte_bound(defs: &HashMap<ValueId, &Inst>, pointer_bits: u32, x: ValueId) -> Option<u128> {
    let k = |v: ValueId| const_word(defs.get(&v)?, pointer_bits).map(|w| w.bits);
    match defs.get(&x)? {
        Inst::BinOp {
            op: BinOp::And,
            lhs,
            rhs,
            ..
        } => match (k(*lhs), k(*rhs)) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (Some(c), None) | (None, Some(c)) => Some(c),
            _ => None,
        },
        Inst::BinOp {
            op: BinOp::URem,
            rhs,
            ..
        } => k(*rhs).filter(|c| *c > 0).map(|c| c - 1),
        Inst::BinOp {
            op: BinOp::LShr,
            ty,
            rhs,
            ..
        } => {
            let n = width_of(ty, pointer_bits)?;
            let s = u32::try_from(k(*rhs)?).ok().filter(|s| *s < n)?;
            Some(low(n - s))
        }
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty,
            ..
        } => width_of(src_ty, pointer_bits).filter(|w| *w <= 8).map(low),
        inst @ Inst::Const { .. } => const_word(inst, pointer_bits).map(|w| w.bits),
        _ => None,
    }
}

/// A region the pass found: `E` at position `e`, its tail from `start`, the
/// join at position `x`, the inner blocks by position, the input.
struct Found {
    e: usize,
    start: usize,
    x: usize,
    inner: Vec<usize>,
    input: ValueId,
}

fn successors(func: &Function, at: &HashMap<BlockId, usize>, b: usize) -> Vec<usize> {
    func.blocks[b]
        .body
        .last()
        .map(|t| t.inst.successor_edges())
        .unwrap_or_default()
        .iter()
        .filter_map(|e| at.get(&e.target).copied())
        .collect()
}

/// The largest region from `e` (module docs), or `None`.
fn find_region(
    func: &Function,
    at: &HashMap<BlockId, usize>,
    preds: &[Vec<usize>],
    defs: &HashMap<ValueId, &Inst>,
    uses: &Uses,
    pointer_bits: u32,
    e: usize,
) -> Option<Found> {
    let entry = *at.get(&func.entry)?;
    if !matches!(
        func.blocks[e].body.last()?.inst,
        Inst::CondBr { .. } | Inst::Switch { .. }
    ) {
        return None;
    }
    let pure_block = |b: usize| {
        let body = &func.blocks[b].body;
        let Some((term, rest)) = body.split_last() else {
            return false;
        };
        matches!(
            term.inst,
            Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
        ) && rest.iter().all(|n| pure(&n.inst) && n.results.len() == 1)
    };
    // The closure of pure blocks entered only from `E` and each other, by
    // a worklist over the edges out of it (a block joins once every edge
    // into it comes from `E` or the closure).
    let mut closure: HashSet<usize> = HashSet::new();
    let mut entered: HashMap<usize, usize> = HashMap::new();
    let mut work = successors(func, at, e);
    while let Some(b) = work.pop() {
        if b == e || b == entry || closure.contains(&b) {
            continue;
        }
        let count = entered.entry(b).or_default();
        *count += 1;
        if *count < preds[b].len() || !pure_block(b) {
            continue;
        }
        closure.insert(b);
        if closure.len() > MAX_REGION_BLOCKS {
            return None;
        }
        work.extend(successors(func, at, b));
    }
    // Candidate joins, the farthest first: one parameter, entered only
    // from the closure.
    let mut joins: Vec<usize> = closure
        .iter()
        .copied()
        .chain(
            closure
                .iter()
                .flat_map(|b| successors(func, at, *b))
                .filter(|b| !closure.contains(b)),
        )
        .filter(|b| func.blocks[*b].params.len() == 1)
        .collect();
    joins.sort_unstable();
    joins.dedup();
    joins.reverse();
    'join: for x in joins {
        if x == e || !preds[x].iter().all(|p| *p == e || closure.contains(p)) {
            continue;
        }
        let mut inner: HashSet<usize> = HashSet::new();
        let mut work = successors(func, at, e);
        while let Some(b) = work.pop() {
            if b == x || inner.contains(&b) {
                continue;
            }
            if !closure.contains(&b) {
                continue 'join;
            }
            inner.insert(b);
            work.extend(successors(func, at, b));
        }
        if inner.contains(&x) || inner.is_empty() {
            continue;
        }
        let mut inner: Vec<usize> = inner.into_iter().collect();
        inner.sort_unstable();
        if let Some((start, input)) = tail(func, defs, uses, pointer_bits, e, &inner) {
            return Some(Found {
                e,
                start,
                x,
                inner,
                input,
            });
        }
    }
    None
}

/// The tail of `E` the region starts with and its one input, extending the
/// tail backwards over pure instructions until the region reads a single
/// non-constant value bounded below 256.
fn tail(
    func: &Function,
    defs: &HashMap<ValueId, &Inst>,
    uses: &Uses,
    pointer_bits: u32,
    e: usize,
    inner: &[usize],
) -> Option<(usize, ValueId)> {
    let body = &func.blocks[e].body;
    let mut start = body.len() - 1;
    loop {
        let mut defined: HashSet<ValueId> = HashSet::new();
        let mut nodes: Vec<&InstrNode> = body[start..].iter().collect();
        for &b in inner {
            defined.extend(func.blocks[b].params.iter().map(|(v, _)| *v));
            nodes.extend(&func.blocks[b].body);
        }
        for n in &nodes {
            defined.extend(n.results.iter().copied());
        }
        let mut inputs: Vec<ValueId> = Vec::new();
        for n in &nodes {
            n.inst.visit_value_operands(|v| {
                let constant = defs
                    .get(&v)
                    .is_some_and(|i| const_word(i, pointer_bits).is_some());
                if !defined.contains(&v) && !constant && !inputs.contains(&v) {
                    inputs.push(v);
                }
            });
        }
        if let [x] = inputs.as_slice()
            && byte_bound(defs, pointer_bits, *x).is_some_and(|b| b < 256)
        {
            return Some((start, *x));
        }
        // Take in the instruction before the tail when it is pure and only
        // the region reads it.
        let prev = start.checked_sub(1)?;
        let node = &body[prev];
        let [r] = node.results.as_slice() else {
            return None;
        };
        let read_outside = uses.get(r).is_some_and(|at| {
            at.iter()
                .any(|&(bi, ni)| !(inner.contains(&bi) || bi == e && ni > prev))
        });
        if !pure(&node.inst) || read_outside {
            return None;
        }
        start = prev;
    }
}

/// The region run on `v` by the pass's own semantics: the join's argument.
fn run(
    func: &Function,
    at: &HashMap<BlockId, usize>,
    defs: &HashMap<ValueId, &Inst>,
    pointer_bits: u32,
    found: &Found,
    v: Word,
) -> Option<Word> {
    let mut env: HashMap<ValueId, Word> = HashMap::new();
    env.insert(found.input, v);
    let (mut b, mut from) = (found.e, found.start);
    for _ in 0..=found.inner.len() + 1 {
        for node in &func.blocks[b].body[from..] {
            let val = |id: ValueId| {
                env.get(&id)
                    .copied()
                    .or_else(|| const_word(defs.get(&id)?, pointer_bits))
            };
            let (target, args) = match &node.inst {
                Inst::Br { target, args } => (*target, args),
                Inst::CondBr {
                    cond,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => {
                    if val(*cond)?.bits == 1 {
                        (*then_target, then_args)
                    } else {
                        (*else_target, else_args)
                    }
                }
                Inst::Switch {
                    value,
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    let s = val(*value)?;
                    let mut taken = (*default, default_args);
                    for case in cases {
                        let Constant::Int(k) = case.value else {
                            return None;
                        };
                        if word(k as u128, s.width) == s {
                            taken = (case.target, &case.args);
                            break;
                        }
                    }
                    taken
                }
                inst => {
                    let w = step(inst, pointer_bits, &val)?;
                    env.insert(*node.results.first()?, w);
                    continue;
                }
            };
            let t = *at.get(&target)?;
            let values: Vec<Word> = args.iter().map(|a| val(*a)).collect::<Option<_>>()?;
            if t == found.x {
                return values.first().copied();
            }
            for ((p, _), w) in func.blocks[t].params.iter().zip(values) {
                env.insert(*p, w);
            }
            b = t;
            from = 0;
            break;
        }
    }
    None
}

impl MidPass for CrcTablePass {
    fn name(&self) -> &'static str {
        CRC_TABLE_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        if cx.pointer_bits != 32 {
            return None;
        }
        let at: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); func.blocks.len()];
        for b in 0..func.blocks.len() {
            for s in successors(func, &at, b) {
                preds[s].push(b);
            }
        }
        let defs = sole_defs(func);
        // Policy: a function without `MIN_ROUNDS` xors of one constant holds
        // no region; most functions stop here.
        let mut xors: HashMap<u128, usize> = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let Inst::BinOp {
                op: BinOp::Xor,
                lhs,
                rhs,
                ..
            } = &node.inst
            {
                for side in [lhs, rhs] {
                    if let Some(c) = defs.get(side).and_then(|i| const_word(i, cx.pointer_bits)) {
                        *xors.entry(c.bits).or_default() += 1;
                    }
                }
            }
        }
        if xors.values().all(|n| *n < MIN_ROUNDS) {
            return None;
        }
        let mut uses: Uses = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                node.inst
                    .visit_value_operands(|v| uses.entry(v).or_default().push((bi, ni)));
            }
        }
        let types = value_types(func);
        let mut used: HashSet<usize> = HashSet::new();
        let mut regions: Vec<(Found, u128, Vec<u8>, u32)> = Vec::new();
        for e in 0..func.blocks.len() {
            if used.contains(&e) {
                continue;
            }
            let Some(found) = find_region(func, &at, &preds, &defs, &uses, cx.pointer_bits, e)
            else {
                continue;
            };
            if found.inner.iter().any(|b| used.contains(b)) {
                continue;
            }
            // Policy: one polynomial, xored at least `MIN_ROUNDS` times, in a
            // region of at least `MIN_REGION_INSTS` instructions whose values
            // nothing outside it reads.
            let mut nodes: Vec<&InstrNode> = func.blocks[e].body[found.start..].iter().collect();
            let mut defined: HashSet<ValueId> = HashSet::new();
            for &b in &found.inner {
                defined.extend(func.blocks[b].params.iter().map(|(v, _)| *v));
                nodes.extend(&func.blocks[b].body);
            }
            for n in &nodes {
                defined.extend(n.results.iter().copied());
            }
            let mut polys: Vec<u128> = Vec::new();
            for n in &nodes {
                if let Inst::BinOp {
                    op: BinOp::Xor,
                    lhs,
                    rhs,
                    ..
                } = &n.inst
                {
                    for side in [lhs, rhs] {
                        if let Some(c) = defs.get(side).and_then(|i| const_word(i, cx.pointer_bits))
                        {
                            polys.push(c.bits);
                        }
                    }
                }
            }
            let Some(&poly) = polys.first() else {
                continue;
            };
            if polys.len() < MIN_ROUNDS
                || polys.iter().any(|p| *p != poly)
                || nodes.len() < MIN_REGION_INSTS
            {
                continue;
            }
            let region_blocks: HashSet<usize> = found.inner.iter().copied().collect();
            let leaks = func.blocks.iter().enumerate().any(|(bi, block)| {
                if region_blocks.contains(&bi) {
                    return false;
                }
                let upto = if bi == e {
                    found.start
                } else {
                    block.body.len()
                };
                block.body[..upto].iter().any(|n| {
                    let mut hit = false;
                    n.inst.visit_value_operands(|v| hit |= defined.contains(&v));
                    hit
                })
            });
            if leaks {
                continue;
            }
            let Some((_, out_ty)) = func.blocks[found.x].params.first() else {
                continue;
            };
            let Some((out_bits, _)) = int_shape(out_ty, cx.pointer_bits) else {
                continue;
            };
            if !matches!(out_bits, 8 | 16 | 32 | 64) {
                continue;
            }
            let Some(in_ty) = types.get(&found.input) else {
                continue;
            };
            let Some((in_bits, _)) = int_shape(in_ty, cx.pointer_bits) else {
                continue;
            };
            let n = out_bits / 8;
            let mut data = Vec::with_capacity(256 * n as usize);
            let mut ok = true;
            for v in 0..256u128 {
                match run(func, &at, &defs, cx.pointer_bits, &found, word(v, in_bits)) {
                    Some(w) if w.width == out_bits => {
                        data.extend_from_slice(&w.bits.to_le_bytes()[..n as usize]);
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            used.insert(e);
            used.extend(found.inner.iter().copied());
            regions.push((found, poly, data, n));
        }
        if regions.is_empty() {
            return None;
        }
        // The module entries: a `u8` type when the module has none, and one
        // fresh internal read-only global per table.
        let mut new_types = Vec::new();
        let u8_id = match cx.module.types.iter().position(|t| *t == Ty::U8) {
            Some(i) => TyId::new(u32::try_from(i).ok()?),
            None => {
                new_types.push(Ty::U8);
                TyId::new(u32::try_from(cx.module.types.len()).ok()?)
            }
        };
        let mut taken: HashSet<String> = cx
            .module
            .globals
            .iter()
            .map(|g| g.name.clone())
            .chain(cx.module.functions.iter().map(|f| f.name.clone()))
            .collect();
        let mut next = first_free_value(func);
        let mut out = func.clone();
        let mut witness = CrcTableWitness {
            new_types,
            ..CrcTableWitness::default()
        };
        let mut removed_blocks: HashSet<BlockId> = HashSet::new();
        let mut removed: HashSet<ValueId> = HashSet::new();
        // Equal tables share one global.
        let mut tables: HashMap<(Vec<u8>, u32), GlobalId> = HashMap::new();
        for (found, poly, data, n) in regions {
            let id = match tables.get(&(data.clone(), n)) {
                Some(id) => *id,
                None => {
                    let id = GlobalId::new(
                        u32::try_from(cx.module.globals.len() + witness.new_globals.len()).ok()?,
                    );
                    let mut name = format!("{}.irmid.crc.{}", func.name, func.blocks[found.e].id);
                    while taken.contains(&name) {
                        name.push('_');
                    }
                    taken.insert(name.clone());
                    tables.insert((data.clone(), n), id);
                    witness.new_globals.push(Global {
                        name,
                        ty: Ty::Array(u8_id, data.len() as u64),
                        mutable: false,
                        initializer: Some(Constant::Bytes { data, utf8: false }),
                        linkage: Linkage::Internal,
                        tls: None,
                        align: Some(n),
                        section: None,
                        visibility: Visibility::Default,
                        retained: false,
                    });
                    id
                }
            };
            let values: Vec<ValueId> = (0..6).map(|i| ValueId::new(next + i)).collect();
            next += 6;
            let in_ty = types.get(&found.input)?.clone();
            let in_bits = int_shape(&in_ty, cx.pointer_bits)?.0;
            let index = if in_ty == Ty::I32 {
                Inst::Copy {
                    ty: Ty::I32,
                    operand: found.input,
                }
            } else {
                Inst::Cast {
                    op: match in_bits.cmp(&32) {
                        std::cmp::Ordering::Equal => CastOp::Bitcast,
                        std::cmp::Ordering::Less => CastOp::ZExt,
                        std::cmp::Ordering::Greater => CastOp::Trunc,
                    },
                    src_ty: in_ty,
                    dst_ty: Ty::I32,
                    operand: found.input,
                }
            };
            let out_ty = func.blocks[found.x].params[0].1.clone();
            let exit = func.blocks[found.x].id;
            let lookup = [
                InstrNode::new(Inst::GlobalAddr { global: id }).with_results([values[0]]),
                InstrNode::new(index).with_results([values[1]]),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(i128::from(n)),
                })
                .with_results([values[2]]),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I32,
                    lhs: values[1],
                    rhs: values[2],
                })
                .with_results([values[3]]),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: values[0],
                    indices: vec![values[3]],
                    inbounds: true,
                })
                .with_results([values[4]]),
                InstrNode::new(Inst::Load {
                    ty: out_ty,
                    ptr: values[4],
                    volatile: false,
                    align: Some(u64::from(n)),
                })
                .with_results([values[5]]),
                InstrNode::new(Inst::Br {
                    target: exit,
                    args: vec![values[5]],
                }),
            ];
            for n in &func.blocks[found.e].body[found.start..] {
                removed.extend(n.results.iter().copied());
            }
            for &b in &found.inner {
                removed_blocks.insert(func.blocks[b].id);
                removed.extend(func.blocks[b].params.iter().map(|(v, _)| *v));
                for n in &func.blocks[b].body {
                    removed.extend(n.results.iter().copied());
                }
            }
            let body = &mut out.blocks[found.e].body;
            body.truncate(found.start);
            body.extend(lookup);
            witness.tables.push(CrcTable {
                block: func.blocks[found.e].id,
                start: found.start,
                exit,
                input: found.input,
                polynomial: poly,
                global: id,
                values,
            });
        }
        out.blocks.retain(|b| !removed_blocks.contains(&b.id));
        drop_names(&mut out, &removed);
        Some((out, PassWitness::CrcTable(witness)))
    }
}
