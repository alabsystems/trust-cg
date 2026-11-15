// trust-cg-irmid/passes/byte_copy.rs - byte copies as `memcopy`, stores forwarded through it
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The byte-copy rewrite. The rustc bridge copies a value of a byte-array
//! type (a `#[repr(packed)]` struct, whose fields are unaligned) one byte at
//! a time: a `load i8` of each source byte and a `store i8` of it (or a
//! write-through `insertfield`, which field-access lowering, earlier in the
//! pipeline, has made a store). Building a packed struct returned through
//! its out-pointer was four typed stores into a temporary, then fifteen byte
//! loads and stores; scalar replacement then carried the temporary as
//! integers and rebuilt each byte by shifts. Two rewrites, run in order:
//!
//! * **runs**: a run of at least two such byte copies in one block, whose
//!   source bytes are consecutive bytes of one allocation and whose
//!   destination bytes are the same offsets from another (or a disjoint
//!   range of the same one), with only instructions between them that
//!   neither touch memory nor call nor assert, becomes one `memcopy` of
//!   the run's length at its last store. The wasm32 lane expands a
//!   `memcopy` of at most 32 constant bytes into word loads and stores.
//! * **forwards**: a `memcopy` of a constant length out of a frame slot
//!   that does not escape, whose copied bytes are exactly covered by
//!   earlier stores of the same block with no other write to the slot
//!   since, becomes those stores, made into the destination at the same
//!   offsets. The slot is then only written, and dead-slot removal drops
//!   it: the packed struct's four fields are stored into the out-pointer,
//!   as LLVM stores them.
//!
//! The allocations are resolved by the pass's own walk (an `alloca`, an
//! entry parameter or a global's address, then copies, `ptrtoptr`s and
//! `gep`s by non-negative constants); two ranges are disjoint when they are
//! in different `alloca`s, in an `alloca` and a parameter or global (an
//! allocation this activation made is not one its caller could name), in
//! two different globals, or are disjoint bytes of one base. The checker
//! (`trust_cg_verify::trust_ir_mid_tv`, `trust_ir_mid_tv_bytecopy.rs`)
//! derives every premise again with its own code.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{
    ByteCopyForward, ByteCopyRun, ByteCopyWitness, ForwardedStore, PassWitness,
};
use trust_ir::value::GlobalId;
use trust_ir::{BinOp, CastOp, Constant, Function, Inst, InstrNode, Module, Ty, ValueId};

use super::loops::first_free_value;
use super::{MidPass, PassContext, drop_names, sole_defs, value_types};

pub(crate) struct ByteCopyPass;

/// The evidence name of the byte-copy rewrite.
pub(crate) const BYTE_COPY_NAME: &str = "byte_copy";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Base {
    Alloca(ValueId),
    Param(ValueId),
    Global(GlobalId),
}

struct Addresses<'f> {
    module: &'f Module,
    defs: HashMap<ValueId, &'f Inst>,
    params: HashSet<ValueId>,
}

impl<'f> Addresses<'f> {
    fn new(module: &'f Module, func: &'f Function) -> Self {
        Self {
            module,
            defs: sole_defs(func),
            params: func
                .blocks
                .iter()
                .find(|b| b.id == func.entry)
                .map(|b| b.params.iter().map(|(v, _)| *v).collect())
                .unwrap_or_default(),
        }
    }

    fn size(&self, ty: &Ty) -> Option<u64> {
        self.module.ty_layout_shape(ty).ok()?.size_bytes()
    }

    /// `(base, displacement)` of the address `v`.
    fn resolve(&self, mut v: ValueId) -> Option<(Base, u64)> {
        let mut disp: u64 = 0;
        for _ in 0..64 {
            if self.params.contains(&v) {
                return Some((Base::Param(v), disp));
            }
            match self.defs.get(&v)? {
                Inst::Alloca { .. } => return Some((Base::Alloca(v), disp)),
                Inst::GlobalAddr { global } => return Some((Base::Global(*global), disp)),
                Inst::Copy { operand, .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                } => v = *operand,
                Inst::GEP {
                    pointee_ty,
                    base,
                    indices,
                    ..
                } => {
                    let elem = self.size(pointee_ty)?;
                    for k in indices {
                        let Inst::Const {
                            ty,
                            value: Constant::Int(k),
                        } = self.defs.get(k)?
                        else {
                            return None;
                        };
                        if !ty.is_integer() {
                            return None;
                        }
                        disp = disp.checked_add(elem.checked_mul(u64::try_from(*k).ok()?)?)?;
                    }
                    v = *base;
                }
                _ => return None,
            }
        }
        None
    }
}

fn disjoint(a: Base, x: u64, b: Base, y: u64, n: u64) -> bool {
    match (a, b) {
        (Base::Alloca(p), Base::Alloca(q)) if p == q => x + n <= y || y + n <= x,
        (Base::Global(p), Base::Global(q)) if p == q => x + n <= y || y + n <= x,
        (Base::Alloca(_), _) | (_, Base::Alloca(_)) => true,
        (Base::Global(_), Base::Global(_)) => true,
        _ => false,
    }
}

fn one_byte(ty: &Ty) -> bool {
    matches!(ty, Ty::I8 | Ty::U8)
}

fn inert(inst: &Inst) -> bool {
    match inst {
        Inst::Const { .. } | Inst::Copy { .. } | Inst::Cast { .. } | Inst::GEP { .. } => true,
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
        _ => false,
    }
}

/// Every value's number of using instructions.
fn use_counts(func: &Function) -> HashMap<ValueId, usize> {
    let mut counts: HashMap<ValueId, usize> = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        let mut seen = HashSet::new();
        node.inst.visit_value_operands(|v| {
            if seen.insert(v) {
                *counts.entry(v).or_default() += 1;
            }
        });
    }
    counts
}

/// One run found in a block: `(first, last, k, src, dst)`.
type Found = (usize, usize, u64, ValueId, ValueId);

/// A byte's address: `(base, displacement)`.
type Resolved = (Base, u64);

/// The runs of `body` (module docs).
fn runs_of(
    addr: &Addresses<'_>,
    body: &[InstrNode],
    uses: &HashMap<ValueId, usize>,
    types: &HashMap<ValueId, Ty>,
) -> Vec<Found> {
    let mut out = Vec::new();
    let mut ni = 0;
    while ni < body.len() {
        let starts =
            matches!(&body[ni].inst, Inst::Load { ty, volatile: false, .. } if one_byte(ty));
        if !starts {
            ni += 1;
            continue;
        }
        // Scan forward: pending loads, completed pairs, the last position
        // where no load is pending after a store.
        let mut pending: HashMap<ValueId, ValueId> = HashMap::new();
        let mut pairs: Vec<(ValueId, ValueId)> = Vec::new();
        let mut end: Option<(usize, usize)> = None;
        let mut j = ni;
        while j < body.len() {
            let node = &body[j];
            match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    ..
                } if one_byte(ty) => match node.results.as_slice() {
                    [r] if uses.get(r) == Some(&1) => {
                        pending.insert(*r, *ptr);
                    }
                    _ => break,
                },
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    ..
                } if one_byte(ty) && types.get(value) == Some(ty) => {
                    let Some(src) = pending.remove(value) else {
                        break;
                    };
                    pairs.push((src, *ptr));
                    if pending.is_empty() {
                        end = Some((j, pairs.len()));
                    }
                }
                inst if inert(inst) => {}
                _ => break,
            }
            j += 1;
        }
        let Some((last, n)) = end else {
            ni += 1;
            continue;
        };
        let pairs = &pairs[..n];
        let resolved: Option<Vec<(Resolved, Resolved)>> = pairs
            .iter()
            .map(|(s, d)| Some((addr.resolve(*s)?, addr.resolve(*d)?)))
            .collect();
        let accepted = resolved.and_then(|resolved| {
            let k = u64::try_from(resolved.len()).ok()?;
            if k < 2 {
                return None;
            }
            let (lo, &((sb, s0), (db, d0))) = resolved
                .iter()
                .enumerate()
                .min_by_key(|(_, ((_, s), _))| *s)?;
            let mut seen = HashSet::new();
            for &((b1, s), (b2, d)) in &resolved {
                if b1 != sb
                    || b2 != db
                    || s < s0
                    || d < d0
                    || s - s0 != d - d0
                    || s - s0 >= k
                    || !seen.insert(s - s0)
                {
                    return None;
                }
            }
            disjoint(sb, s0, db, d0, k).then_some((k, pairs[lo].0, pairs[lo].1))
        });
        if let Some((k, src, dst)) = accepted {
            out.push((ni, last, k, src, dst));
            ni = last + 1;
        } else {
            ni += 1;
        }
    }
    out
}

/// Whether the `alloca` `slot`'s address stays inside the function's own
/// accesses; its derived pointers.
fn family_of(func: &Function, slot: ValueId) -> Option<HashSet<ValueId>> {
    let mut family: HashSet<ValueId> = HashSet::from([slot]);
    loop {
        let mut grew = false;
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let derived = match &node.inst {
                Inst::Copy { operand, .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                } => family.contains(operand),
                Inst::GEP { base, .. } => family.contains(base),
                _ => false,
            };
            if derived && let [r] = node.results.as_slice() {
                grew |= family.insert(*r);
            }
        }
        if !grew {
            break;
        }
    }
    let escapes = func.blocks.iter().flat_map(|b| &b.body).any(|node| {
        let mut touches = false;
        node.inst
            .visit_value_operands(|v| touches |= family.contains(&v));
        touches
            && !match &node.inst {
                Inst::Load { .. }
                | Inst::MemCopy { .. }
                | Inst::MemSet { .. }
                | Inst::Copy { .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr,
                    ..
                } => true,
                Inst::Store { value, .. } => !family.contains(value),
                Inst::GEP { indices, .. } => !indices.iter().any(|i| family.contains(i)),
                _ => false,
            }
    });
    (!escapes).then_some(family)
}

impl MidPass for ByteCopyPass {
    fn name(&self) -> &'static str {
        BYTE_COPY_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut next = first_free_value(func);
        let mut fresh = || {
            let v = ValueId::new(next);
            next += 1;
            v
        };
        // Runs, on the source.
        let uses = use_counts(func);
        let types = value_types(func);
        let mut witness = ByteCopyWitness::default();
        let mut after = func.clone();
        {
            let addr = Addresses::new(cx.module, func);
            let mut dead: HashSet<ValueId> = HashSet::new();
            for (bi, block) in func.blocks.iter().enumerate() {
                let found = runs_of(&addr, &block.body, &uses, &types);
                if found.is_empty() {
                    continue;
                }
                let mut removed: HashSet<usize> = HashSet::new();
                let mut inserted: HashMap<usize, Vec<InstrNode>> = HashMap::new();
                for (first, last, k, src, dst) in found {
                    let count = fresh();
                    witness.runs.push(ByteCopyRun {
                        block: block.id,
                        first,
                        last,
                        count,
                    });
                    for (offset, node) in block.body[first..=last].iter().enumerate() {
                        let ni = first + offset;
                        if matches!(node.inst, Inst::Load { .. } | Inst::Store { .. }) {
                            removed.insert(ni);
                            dead.extend(node.results.iter().copied());
                        }
                    }
                    let template = &block.body[last];
                    let mut constant = template.clone();
                    constant.inst = Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(i128::from(k)),
                    };
                    constant.results = vec![count];
                    let mut copy = template.clone();
                    copy.inst = Inst::MemCopy {
                        dst,
                        src,
                        bytes: count,
                        overlap: false,
                    };
                    copy.results = Vec::new();
                    inserted.insert(last, vec![constant, copy]);
                }
                let body = std::mem::take(&mut after.blocks[bi].body);
                for (ni, node) in body.into_iter().enumerate() {
                    if let Some(nodes) = inserted.remove(&ni) {
                        after.blocks[bi].body.extend(nodes);
                    } else if !removed.contains(&ni) {
                        after.blocks[bi].body.push(node);
                    }
                }
            }
            drop_names(&mut after, &dead);
        }
        // Forwards, on the function after the runs.
        let mut out = after.clone();
        {
            let addr = Addresses::new(cx.module, &after);
            let mut families: HashMap<ValueId, Option<HashSet<ValueId>>> = HashMap::new();
            for (bi, block) in after.blocks.iter().enumerate() {
                let mut replaced: HashMap<usize, Vec<InstrNode>> = HashMap::new();
                for (ci, node) in block.body.iter().enumerate() {
                    let Inst::MemCopy {
                        dst, src, bytes, ..
                    } = &node.inst
                    else {
                        continue;
                    };
                    let Some(Inst::Const {
                        ty,
                        value: Constant::Int(k),
                    }) = addr.defs.get(bytes).copied()
                    else {
                        continue;
                    };
                    let Ok(k) = u64::try_from(*k) else { continue };
                    if !ty.is_integer() || k == 0 {
                        continue;
                    }
                    let (Some((Base::Alloca(slot), t)), Some((db, d))) =
                        (addr.resolve(*src), addr.resolve(*dst))
                    else {
                        continue;
                    };
                    if !disjoint(Base::Alloca(slot), t, db, d, k) {
                        continue;
                    }
                    let family = families
                        .entry(slot)
                        .or_insert_with(|| family_of(&after, slot));
                    let Some(family) = family.as_ref() else {
                        continue;
                    };
                    // Walk back, collecting the stores that cover [t, t + k).
                    let mut pieces: Vec<(u64, u64, usize)> = Vec::new();
                    let mut covered = 0u64;
                    let mut ok = false;
                    for si in (0..ci).rev() {
                        let inst = &block.body[si].inst;
                        let (ptr, size) = match inst {
                            Inst::Store {
                                ty,
                                ptr,
                                volatile: false,
                                ..
                            } if family.contains(ptr) => match addr.size(ty) {
                                Some(s) if s > 0 => (*ptr, s),
                                _ => break,
                            },
                            Inst::Store { ptr, .. } if family.contains(ptr) => break,
                            Inst::MemCopy { dst, .. } | Inst::MemSet { dst, .. }
                                if family.contains(dst) =>
                            {
                                break;
                            }
                            _ => continue,
                        };
                        let Some((Base::Alloca(s), o)) = addr.resolve(ptr) else {
                            break;
                        };
                        if s != slot
                            || o < t
                            || o + size > t + k
                            || pieces
                                .iter()
                                .any(|&(po, ps, _)| o < po + ps && po < o + size)
                        {
                            break;
                        }
                        pieces.push((o, size, si));
                        covered += size;
                        if covered == k {
                            ok = true;
                            break;
                        }
                    }
                    if !ok {
                        continue;
                    }
                    pieces.sort_by_key(|p| p.0);
                    let mut stores = Vec::new();
                    let mut nodes = Vec::new();
                    for (o, _, si) in pieces {
                        let Inst::Store { ty, value, .. } = &block.body[si].inst else {
                            continue;
                        };
                        let (offset, address) = (fresh(), fresh());
                        stores.push(ForwardedStore {
                            store: si,
                            offset,
                            address,
                        });
                        let mut c = node.clone();
                        c.inst = Inst::Const {
                            ty: Ty::Usize,
                            value: Constant::Int(i128::from(o - t)),
                        };
                        c.results = vec![offset];
                        let mut g = node.clone();
                        g.inst = Inst::GEP {
                            pointee_ty: Ty::U8,
                            base: *dst,
                            indices: vec![offset],
                            inbounds: false,
                        };
                        g.results = vec![address];
                        let mut st = node.clone();
                        st.inst = Inst::Store {
                            ty: ty.clone(),
                            ptr: address,
                            value: *value,
                            volatile: false,
                            align: Some(1),
                        };
                        st.results = Vec::new();
                        nodes.extend([c, g, st]);
                    }
                    witness.forwards.push(ByteCopyForward {
                        block: block.id,
                        copy: ci,
                        stores,
                    });
                    replaced.insert(ci, nodes);
                }
                if replaced.is_empty() {
                    continue;
                }
                let body = std::mem::take(&mut out.blocks[bi].body);
                out.blocks[bi].body = body
                    .into_iter()
                    .enumerate()
                    .flat_map(|(ni, node)| replaced.remove(&ni).unwrap_or_else(|| vec![node]))
                    .collect();
            }
        }
        if witness.rewrite_count() == 0 {
            return None;
        }
        Some((out, PassWitness::ByteCopy(witness)))
    }
}
