// trust-cg-irmid/passes/ctp.rs - constant-table promotion
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A count-free `alloca` that is only ever written with constants and read,
//! whose address is never observed and never leaves the function, becomes
//! the address of a new read-only global holding the bytes those stores
//! write (bytes no store writes are 0), and the stores go. The rustc
//! bridge builds a local constant array (`let t = [3, 1, 4]; t[i]`) as such
//! an `alloca`, rebuilt on every call; promoted, it is data.
//!
//! The facts come from the capture analysis (`escape.rs`, shared with the
//! wasm32 lane): the values derived from the address, each an offset value
//! (the address plus a displacement) of the allocation's provenance, with
//! `inttoptr` of an offset integer resolving to the allocation only where its
//! displacement provably lies inside it. On top of them this pass requires
//! that
//!
//! * no derived value carries the address's bits, crosses a block edge, or
//!   is used other than by a `copy`, a `gep` (by indices that are not
//!   derived), `ptrtoint`/`inttoptr`/`bitcast` between the address and an
//!   address-width integer, an `add` of an independent amount or a `sub` of a
//!   constant, a plain load, or a plain store THROUGH it;
//! * every store through it writes an integer or `bool` constant (not a
//!   derived value) at a known displacement inside the allocation, two
//!   stores never write different bytes, and some load reads it.
//!
//! Then every access the source makes reaches only this allocation's bytes,
//! each of which holds the image's byte or is still undefined, so reading the
//! image instead is a refinement: equal where the source is defined. The
//! address differs, but nothing observes it. A uniform image (one byte
//! value) is left alone: its canonical spelling is a splat.

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{CtpPromotion, CtpWitness, PassWitness};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, Global, Inst, Linkage, Ty, TyId, ValueId,
    Visibility,
};

use super::{MidPass, PassContext, int_shape, value_types};
use crate::escape::{self, Disp, Extent, FuncFacts, ParamCaptures};

pub(crate) struct Ctp;

/// Whether `ty` is a wasm32 address-width integer.
fn address_int(ty: &Ty) -> bool {
    matches!(ty, Ty::I32 | Ty::U32 | Ty::Isize | Ty::Usize)
}

/// The little-endian bytes a plain store of the constant writes: an integer
/// in two's complement at its type's width, a `bool` as 0 or 1.
fn constant_bytes(ty: &Ty, value: &Constant, pointer_bits: u32) -> Option<Vec<u8>> {
    let (raw, bytes) = match (ty, value) {
        (Ty::Bool, Constant::Bool(b)) => (u128::from(*b), 1usize),
        (_, Constant::Int(c)) => {
            let (bits, signed) = int_shape(ty, pointer_bits)?;
            let in_range = if bits >= 128 {
                signed || *c >= 0
            } else if signed {
                let half = 1i128 << (bits - 1);
                (-half..half).contains(c)
            } else {
                *c >= 0 && *c < (1i128 << bits)
            };
            if !in_range {
                return None;
            }
            (*c as u128, (bits / 8) as usize)
        }
        (Ty::U128, Constant::U128(u)) => (*u, 16),
        _ => return None,
    };
    Some(raw.to_le_bytes()[..bytes].to_vec())
}

/// One promotable table.
struct Table {
    at: (usize, usize),
    alloca: ValueId,
    stores: BTreeSet<(usize, usize)>,
    image: Vec<u8>,
    align: u64,
}

impl MidPass for Ctp {
    fn name(&self) -> &'static str {
        super::CTP_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        if cx.pointer_bits != 32 {
            return None;
        }
        let has_alloca = func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Alloca { count: None, .. }));
        if !has_alloca {
            return None;
        }
        let block_index: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let facts = FuncFacts::new(func, block_index, value_types(func));
        let no_callees = ParamCaptures::default();
        let mut tables = Vec::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                if let (
                    Inst::Alloca {
                        ty,
                        count: None,
                        align,
                    },
                    [alloca],
                ) = (&node.inst, node.results.as_slice())
                    && let Some(table) =
                        promotable(cx, func, &facts, &no_callees, (bi, ni), *alloca, ty, *align)
                {
                    tables.push(table);
                }
            }
        }
        if tables.is_empty() {
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
        let mut out = func.clone();
        let mut witness = CtpWitness {
            new_types,
            ..CtpWitness::default()
        };
        let mut doomed: HashSet<(usize, usize)> = HashSet::new();
        for (j, table) in tables.into_iter().enumerate() {
            let id = GlobalId::new(u32::try_from(cx.module.globals.len() + j).ok()?);
            let mut name = format!("{}.irmid.ctp.{}", func.name, table.alloca.index());
            while taken.contains(&name) {
                name.push('_');
            }
            taken.insert(name.clone());
            witness.new_globals.push(Global {
                name,
                ty: Ty::Array(u8_id, table.image.len() as u64),
                mutable: false,
                initializer: Some(Constant::Bytes {
                    data: table.image,
                    utf8: false,
                }),
                linkage: Linkage::Internal,
                tls: None,
                align: Some(u32::try_from(table.align).ok()?),
                section: None,
                visibility: Visibility::Default,
                retained: false,
            });
            witness.promotions.push(CtpPromotion {
                block: func.blocks[table.at.0].id,
                index: table.at.1,
                alloca: table.alloca,
                global: id,
                stores: table
                    .stores
                    .iter()
                    .map(|&(bi, ni)| (func.blocks[bi].id, ni))
                    .collect(),
            });
            out.blocks[table.at.0].body[table.at.1].inst = Inst::GlobalAddr { global: id };
            doomed.extend(table.stores);
        }
        for (bi, block) in out.blocks.iter_mut().enumerate() {
            let mut ni = 0usize;
            block.body.retain(|_| {
                let keep = !doomed.contains(&(bi, ni));
                ni += 1;
                keep
            });
        }
        Some((out, PassWitness::Ctp(witness)))
    }
}

/// The table `alloca` makes, when it is one (module docs).
#[allow(clippy::too_many_arguments)]
fn promotable(
    cx: &PassContext<'_>,
    func: &Function,
    facts: &FuncFacts<'_>,
    no_callees: &ParamCaptures,
    at: (usize, usize),
    alloca: ValueId,
    ty: &Ty,
    align: Option<u64>,
) -> Option<Table> {
    let shape = cx.module.ty_layout_shape(ty).ok()?;
    let size = shape.size_bytes().filter(|&s| s > 0)?;
    let align = align.or_else(|| {
        shape
            .align_bits
            .filter(|b| b.is_multiple_of(8))
            .map(|b| b / 8)
    })?;
    let derived = escape::derive(facts, no_callees, Extent::Bytes(size), &[alloca]);
    if derived.captured || derived.returned || !derived.param_blocks.is_empty() {
        return None;
    }
    let is_derived = |v: &ValueId| derived.facts.contains_key(v);
    let mut image: Vec<Option<u8>> = vec![None; usize::try_from(size).ok()?];
    let mut stores = BTreeSet::new();
    let mut loads = 0usize;
    // The known displacement of a pointer a store writes through: the
    // walk's constant, or a byte `gep` by a constant of a known one.
    let mut store_disp: HashMap<ValueId, i128> = HashMap::new();
    let mut order: Vec<ValueId> = derived.values.clone();
    order.sort_by_key(|v| v.index());
    for &v in &derived.values {
        let fact = derived.facts.get(&v)?;
        if fact.bits {
            return None;
        }
        if let Disp::Const(c) = fact.disp {
            store_disp.insert(v, c);
        }
    }
    // Byte `gep`s by a constant, to a fixpoint (a chain is at most as long
    // as the derived values).
    for _ in 0..derived.values.len() {
        let mut grew = false;
        for &v in &derived.values {
            if store_disp.contains_key(&v) {
                continue;
            }
            let Some(Inst::GEP {
                pointee_ty: Ty::U8 | Ty::I8,
                base,
                indices,
                ..
            }) = facts.def(v)
            else {
                continue;
            };
            let ([k], Some(&b)) = (indices.as_slice(), store_disp.get(base)) else {
                continue;
            };
            let Some(Inst::Const {
                ty,
                value: Constant::Int(k),
            }) = facts.def(*k)
            else {
                continue;
            };
            if address_int(ty)
                && let Some(d) = b.checked_add(*k)
            {
                store_disp.insert(v, d);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    for &v in &order {
        let fact = derived.facts[&v];
        for &(bi, ni) in facts.uses_of(v) {
            let node = &func.blocks[bi].body[ni];
            match &node.inst {
                Inst::Copy { .. } => {}
                Inst::GEP { base, indices, .. }
                    if *base == v && !indices.iter().any(is_derived) =>
                {
                    if fact.stray {
                        return None;
                    }
                }
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty,
                    ..
                } if address_int(dst_ty) => {}
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty,
                    dst_ty: Ty::Ptr,
                    ..
                } if address_int(src_ty) => {
                    let [r] = node.results.as_slice() else {
                        return None;
                    };
                    if derived.facts.get(r).is_none_or(|f| f.stray) {
                        return None;
                    }
                }
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty,
                    dst_ty,
                    ..
                } if address_int(src_ty) && address_int(dst_ty) => {}
                Inst::BinOp {
                    op: BinOp::Add,
                    ty,
                    lhs,
                    rhs,
                } if address_int(ty) && (*lhs == v) != (*rhs == v) => {
                    let other = if *lhs == v { rhs } else { lhs };
                    if is_derived(other) {
                        return None;
                    }
                }
                Inst::BinOp {
                    op: BinOp::Sub,
                    ty,
                    lhs,
                    rhs,
                } if address_int(ty) && *lhs == v && *rhs != v => {
                    if !matches!(facts.def(*rhs), Some(Inst::Const { .. })) {
                        return None;
                    }
                }
                Inst::Load {
                    ptr,
                    volatile: false,
                    ..
                } if *ptr == v => {
                    if fact.stray {
                        return None;
                    }
                    loads += 1;
                }
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    ..
                } if *ptr == v && !is_derived(value) => {
                    if fact.stray {
                        return None;
                    }
                    let start = u64::try_from(*store_disp.get(&v)?).ok()?;
                    let Some(Inst::Const { ty: c_ty, value: c }) = facts.def(*value) else {
                        return None;
                    };
                    if c_ty != ty {
                        return None;
                    }
                    let bytes = constant_bytes(ty, c, cx.pointer_bits)?;
                    let end = start.checked_add(bytes.len() as u64)?;
                    if end > size {
                        return None;
                    }
                    for (k, byte) in bytes.into_iter().enumerate() {
                        let slot = &mut image[usize::try_from(start).ok()? + k];
                        if slot.is_some_and(|b| b != byte) {
                            return None;
                        }
                        *slot = Some(byte);
                    }
                    stores.insert((bi, ni));
                }
                _ => return None,
            }
        }
    }
    if loads == 0 {
        return None;
    }
    let image: Vec<u8> = image.into_iter().map(|b| b.unwrap_or(0)).collect();
    if image.len() >= 2 && image.iter().all(|b| *b == image[0]) {
        return None;
    }
    Some(Table {
        at,
        alloca,
        stores,
        image,
        align,
    })
}
