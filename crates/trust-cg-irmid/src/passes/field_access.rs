// trust-cg-irmid/passes/field_access.rs - field access through a pointer
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Field-access lowering: the rustc bridge's read and write of a record's
//! field through a pointer (`extractfield T %p, i` / `insertfield T %p, i,
//! %v` with `%p` a pointer, which the wasm32 lane loads or stores as lane
//! `i` of `T`) becomes that load or store, at a `gep u8` of the lane's byte
//! offset. trust-ir's validator reports the pointer forms
//! (`FieldAccessInvalid`), and the inliner copies no callee carrying one, so
//! an iterator method such as `size_hint` stayed a call that kept its
//! caller's iterator in memory; spelled as the access it is, the callee is
//! clean and the memory passes read the access like any other.
//!
//! A write's result must be unused and its value of the lane's type, and a
//! read's every use must read its result as the lane's type (or, for a
//! pointer lane, as the pointer of a load or `gep`, or by a `copy` of
//! another thin pointer type, which the copy respelling after this pass
//! makes a `ptrtoptr`): the validator leaves
//! the pointer form's result untyped, so a use expecting another type (the
//! bridge's sign-reinterpreting `copy`) would become a new finding once the
//! result is a typed load (policy). The lane's offset and type come from the
//! module's layout (`record_lane`).
//! The witness names each rewritten instruction by its result with the
//! fresh offset and address values; the checker (`trust_ir_mid_tv_addr.rs`)
//! derives the lane again with the interpreter's layout and rebuilds the
//! access.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{FieldAccess, FieldAccessWitness, PassWitness};
use trust_ir::{Constant, Function, Inst, InstrNode, Ty, ValueId};

use super::loops::first_free_value;
use super::sroa::reads_as;
use super::{MidPass, PassContext, drop_names, record_lane, value_types};

pub(crate) struct FieldAccessPass;

/// The evidence name of field-access lowering.
pub(crate) const FIELD_ACCESS_NAME: &str = "field_access";

impl MidPass for FieldAccessPass {
    fn name(&self) -> &'static str {
        FIELD_ACCESS_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let types = value_types(func);
        let mut used: HashSet<ValueId> = HashSet::new();
        let mut uses: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                node.inst.visit_value_operands(|v| {
                    used.insert(v);
                    let list = uses.entry(v).or_default();
                    if list.last() != Some(&(bi, ni)) {
                        list.push((bi, ni));
                    }
                });
            }
        }
        let thin = |ty: &Ty| {
            matches!(
                ty,
                Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
            )
        };
        // Every use reads the result as the lane's type (`sroa::reads_as`),
        // or, for a pointer lane, as the pointer a load or `gep` goes through
        // or as a `copy` of another thin pointer type (the copy respelling
        // that runs after this pass makes it a `ptrtoptr`).
        let reads_lane = |result: ValueId, lane: &Ty| {
            let at = uses.get(&result).map(Vec::as_slice).unwrap_or(&[]);
            at.iter().all(|&(bi, ni)| {
                let inst = &func.blocks[bi].body[ni].inst;
                let pointer_use = thin(lane)
                    && match inst {
                        Inst::Load { ptr, .. } => *ptr == result,
                        Inst::GEP { base, indices, .. } => {
                            *base == result && !indices.contains(&result)
                        }
                        Inst::Copy { ty, .. } => thin(ty),
                        _ => false,
                    };
                pointer_use || reads_as(func, &[(bi, ni)], result, lane)
            })
        };
        let pointer = |ty: Option<&Ty>| {
            matches!(
                ty,
                Some(Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_))
            )
        };
        let mut next = first_free_value(func);
        let mut rewrites = Vec::new();
        let mut replaced: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
        let mut removed: HashSet<ValueId> = HashSet::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                let [result] = node.results.as_slice() else {
                    continue;
                };
                let (ty, aggregate, field, value) = match &node.inst {
                    Inst::ExtractField {
                        ty,
                        aggregate,
                        field,
                    } => (ty, *aggregate, *field, None),
                    Inst::InsertField {
                        ty,
                        aggregate,
                        field,
                        value,
                    } => (ty, *aggregate, *field, Some(*value)),
                    _ => continue,
                };
                if !pointer(types.get(&aggregate)) {
                    continue;
                }
                let Some((offset, lane_ty)) = record_lane(cx.module, ty, field) else {
                    continue;
                };
                if let Some(v) = value
                    && (used.contains(result) || types.get(&v) != Some(&lane_ty))
                {
                    continue;
                }
                if value.is_none() && !reads_lane(*result, &lane_ty) {
                    continue;
                }
                let (index, address) = (ValueId::new(next), ValueId::new(next + 1));
                next += 2;
                let mut constant = node.clone();
                constant.inst = Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(i128::from(offset)),
                };
                constant.results = vec![index];
                let mut gep = node.clone();
                gep.inst = Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: aggregate,
                    indices: vec![index],
                    inbounds: false,
                };
                gep.results = vec![address];
                let mut access = node.clone();
                if let Some(v) = value {
                    access.inst = Inst::Store {
                        ty: lane_ty,
                        ptr: address,
                        value: v,
                        volatile: false,
                        align: None,
                    };
                    access.results = Vec::new();
                    removed.insert(*result);
                } else {
                    access.inst = Inst::Load {
                        ty: lane_ty,
                        ptr: address,
                        volatile: false,
                        align: None,
                    };
                }
                replaced.insert((bi, ni), vec![constant, gep, access]);
                rewrites.push(FieldAccess {
                    value: *result,
                    index,
                    address,
                });
            }
        }
        if rewrites.is_empty() {
            return None;
        }
        let mut out = func.clone();
        for (bi, block) in out.blocks.iter_mut().enumerate() {
            let body = std::mem::take(&mut block.body);
            block.body = body
                .into_iter()
                .enumerate()
                .flat_map(|(ni, n)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![n]))
                .collect();
        }
        drop_names(&mut out, &removed);
        Some((
            out,
            PassWitness::FieldAccess(FieldAccessWitness { rewrites }),
        ))
    }
}
