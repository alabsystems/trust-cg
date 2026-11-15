// trust-cg-irmid/passes/slots.rs - unobservable frame slots
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The frame slots the memory passes may reason about exactly: a count-free
//! `alloca` of a known size whose address is used only by plain loads and
//! stores through it, and by `gep u8|i8` of it by one non-negative constant
//! (the byte-offset form `ptr_gep` produces) used only by plain loads and
//! stores through it. No other value derives from such an address — no
//! `ptrtoint`, call, block argument or store of it — so only those accesses
//! reach its bytes (an address whose bits are never observed cannot be
//! rebuilt: the capture analysis's premise, `escape.rs`). Every access lies
//! inside the allocation. This is the passes' own analysis;
//! `trust_cg_verify::trust_ir_mid_tv` derives the same facts independently.

use std::collections::HashMap;

use trust_ir::{Constant, Function, Inst, Module, Ty, ValueId};

/// One plain load or store through a slot's pointers.
#[derive(Debug, Clone)]
pub(crate) struct Access {
    /// `(block position, node index)`.
    pub at: (usize, usize),
    pub store: bool,
    pub offset: u64,
    pub size: u64,
}

/// An unobservable slot (module docs).
#[derive(Debug, Clone)]
pub(crate) struct Slot {
    pub alloca: ValueId,
    /// `(block position, node index)` of the `alloca`.
    pub at: (usize, usize),
    pub accesses: Vec<Access>,
}

/// Every unobservable slot of `func`, in definition order.
pub(crate) fn unobservable_slots(module: &Module, func: &Function) -> Vec<Slot> {
    let mut uses: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
    let mut defs: HashMap<ValueId, (usize, usize)> = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            node.inst.visit_value_operands(|v| {
                let list = uses.entry(v).or_default();
                if list.last() != Some(&(bi, ni)) {
                    list.push((bi, ni));
                }
            });
            if let [r] = node.results.as_slice() {
                defs.insert(*r, (bi, ni));
            }
        }
    }
    let size_of = |ty: &Ty| {
        module
            .ty_layout_shape(ty)
            .ok()
            .and_then(|shape| shape.size_bytes())
    };
    let mut slots = Vec::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            let (
                Inst::Alloca {
                    ty, count: None, ..
                },
                [alloca],
            ) = (&node.inst, node.results.as_slice())
            else {
                continue;
            };
            let Some(size) = size_of(ty).filter(|&s| s > 0) else {
                continue;
            };
            if let Some(accesses) = accesses_of(func, &uses, &defs, *alloca, size, &size_of) {
                slots.push(Slot {
                    alloca: *alloca,
                    at: (bi, ni),
                    accesses,
                });
            }
        }
    }
    slots
}

/// The accesses of the slot `alloca` of `size` bytes, or `None` when its
/// address is observable or an access leaves it.
fn accesses_of(
    func: &Function,
    uses: &HashMap<ValueId, Vec<(usize, usize)>>,
    defs: &HashMap<ValueId, (usize, usize)>,
    alloca: ValueId,
    size: u64,
    size_of: &impl Fn(&Ty) -> Option<u64>,
) -> Option<Vec<Access>> {
    let inst_of = |v: ValueId| defs.get(&v).map(|&(bi, ni)| &func.blocks[bi].body[ni].inst);
    let mut pointers: Vec<(ValueId, u64)> = vec![(alloca, 0)];
    let mut accesses = Vec::new();
    let mut next = 0;
    while next < pointers.len() {
        let (pointer, offset) = pointers[next];
        next += 1;
        for &(bi, ni) in uses.get(&pointer).map_or(&[][..], Vec::as_slice) {
            let node = &func.blocks[bi].body[ni];
            let (store, ty) = match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    ..
                } if *ptr == pointer => (false, ty),
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    ..
                } if *ptr == pointer && !pointers.iter().any(|(p, _)| p == value) => (true, ty),
                Inst::GEP {
                    pointee_ty: Ty::U8 | Ty::I8,
                    base,
                    indices,
                    ..
                } if pointer == alloca && *base == alloca => {
                    let [k] = indices.as_slice() else {
                        return None;
                    };
                    let Some(Inst::Const {
                        ty: k_ty,
                        value: Constant::Int(k),
                    }) = inst_of(*k)
                    else {
                        return None;
                    };
                    if !(k_ty.is_integer() || matches!(k_ty, Ty::Isize | Ty::Usize)) {
                        return None;
                    }
                    let k = u64::try_from(*k).ok().filter(|&k| k < size)?;
                    let [g] = node.results.as_slice() else {
                        return None;
                    };
                    pointers.push((*g, k));
                    continue;
                }
                _ => return None,
            };
            let width = size_of(ty).filter(|&w| w > 0)?;
            if offset.checked_add(width)? > size {
                return None;
            }
            accesses.push(Access {
                at: (bi, ni),
                store,
                offset,
                size: width,
            });
        }
    }
    Some(accesses)
}

/// The scalar types a reload returns exactly as stored in the reference
/// interpreter: integers, `bool`, `char` and floats are their bytes. A
/// pointer is not one (a reload resolves the address to whichever live
/// allocation contains it).
pub(crate) fn round_trips(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Bool
            | Ty::Char
            | Ty::F16
            | Ty::F32
            | Ty::F64
    )
}
