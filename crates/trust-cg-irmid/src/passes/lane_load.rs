// trust-cg-irmid/passes/lane_load.rs - an array load read lane by lane
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Lane-load scalarization: a `load [T x n], ptr %a` of an array of scalars
//! whose result is read lane by lane (`extractfield [T x n] %v, i`, the
//! rustc bridge's declared-aggregate spelling of an array value's lane)
//! gains, right after it, a scalar load of each lane read, `load T` at a
//! fresh `gep u8, %a, i * size(T)`, and each read becomes a `copy` of its
//! lane's load.
//! Current typed arrays use `extractelement T` with an in-range constant
//! `usize` index; that form is checked and scalarized at the same load.
//!
//! The inliner binds an array the bridge passes or returns by the address
//! of its bytes to such a `load` (the differential's view reads that
//! argument or returned value as the load of the pointee's bytes), so a
//! spliced closure's environment or `Option<Ordering>` result is read here
//! as scalars the memory passes forward from the stores that wrote them; the
//! array load is left unused for dead-code elimination, and trust-ir's
//! validator no longer sees the array-value field reads
//! (`FieldAccessInvalid`) the splice copied.
//!
//! Which loads: not volatile, of an array whose element is an integer,
//! float, `bool`, `char` or thin pointer, and with a known element size;
//! every read rewritten is an `extractfield` of the load's result whose
//! declared type is the array type and whose lane is below its length (any
//! other use of the result stays). The lane loads take alignment 1 (never
//! stricter than the array load's). The witness names each array load with
//! its lanes' fresh values and the reads; the checker
//! (`trust_ir_mid_tv_lanes.rs`) derives the lanes again from the
//! interpreter's layout and rebuilds the function.

use std::collections::HashMap;

use trust_cg_verify::trust_ir_mid_tv::{LaneLoad, LaneLoadWitness, LaneRead, PassWitness};
use trust_ir::{Constant, Function, Inst, InstrNode, Ty, ValueId};

use super::loops::first_free_value;
use super::{MidPass, PassContext, record_lane, sole_defs};

pub(crate) struct LaneLoadPass;

/// The evidence name of lane-load scalarization.
pub(crate) const LANE_LOAD_NAME: &str = "lane_load";

/// Whether `ty` is a scalar a lane may be loaded as.
fn scalar(ty: &Ty) -> bool {
    ty.is_integer()
        || ty.is_float()
        || matches!(
            ty,
            Ty::Bool
                | Ty::Char
                | Ty::Ptr
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
        )
}

impl MidPass for LaneLoadPass {
    fn name(&self) -> &'static str {
        LANE_LOAD_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        // The array loads of scalars, by result: (array type, address).
        let mut arrays: HashMap<ValueId, (Ty, ValueId)> = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let (
                Inst::Load {
                    ty: ty @ Ty::Array(elem, _),
                    ptr,
                    volatile: false,
                    ..
                },
                [result],
            ) = (&node.inst, node.results.as_slice())
                && cx.module.ty(*elem).is_some_and(scalar)
            {
                arrays.insert(*result, (ty.clone(), *ptr));
            }
        }
        if arrays.is_empty() {
            return None;
        }
        // The lane reads of each, in body order: (read result, lane).
        let mut reads: HashMap<ValueId, Vec<(ValueId, u32)>> = HashMap::new();
        let defs = sole_defs(func);
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let [result] = node.results.as_slice() else {
                continue;
            };
            let (aggregate, field) = match &node.inst {
                Inst::ExtractField {
                    ty,
                    aggregate,
                    field,
                } if arrays.get(aggregate).is_some_and(|(array, _)| array == ty) => {
                    (*aggregate, *field)
                }
                Inst::ExtractElement { ty, array, index } => {
                    let Some((array_ty, _)) = arrays.get(array) else {
                        continue;
                    };
                    let Some(Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(index),
                    }) = defs.get(index).copied()
                    else {
                        continue;
                    };
                    let Ok(field) = u32::try_from(*index) else {
                        continue;
                    };
                    if !record_lane(cx.module, array_ty, field).is_some_and(|(_, elem)| elem == *ty)
                    {
                        continue;
                    }
                    (*array, field)
                }
                _ => continue,
            };
            if arrays
                .get(&aggregate)
                .is_some_and(|(array, _)| record_lane(cx.module, array, field).is_some())
            {
                reads.entry(aggregate).or_default().push((*result, field));
            }
        }
        if reads.is_empty() {
            return None;
        }
        let mut next = first_free_value(func);
        let mut fresh = || {
            let v = ValueId::new(next);
            next += 1;
            v
        };
        let mut loads: Vec<LaneLoad> = Vec::new();
        // Per array load: the nodes following it; per read: its lane value.
        let mut after: HashMap<ValueId, Vec<InstrNode>> = HashMap::new();
        let mut copies: HashMap<ValueId, (Ty, ValueId)> = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let [result] = node.results.as_slice() else {
                continue;
            };
            let (Some(list), Some((array, address))) = (reads.get(result), arrays.get(result))
            else {
                continue;
            };
            let mut lanes: Vec<LaneRead> = Vec::new();
            let mut nodes: Vec<InstrNode> = Vec::new();
            let mut lane_value: HashMap<u32, (Ty, ValueId)> = HashMap::new();
            for &(read, field) in list {
                if let std::collections::hash_map::Entry::Vacant(slot) = lane_value.entry(field) {
                    let (offset, lane_ty) =
                        record_lane(cx.module, array, field).expect("checked above");
                    let (index, at, value) = (fresh(), fresh(), fresh());
                    let mut constant = node.clone();
                    constant.inst = Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(i128::from(offset)),
                    };
                    constant.results = vec![index];
                    let mut gep = node.clone();
                    gep.inst = Inst::GEP {
                        pointee_ty: Ty::U8,
                        base: *address,
                        indices: vec![index],
                        inbounds: false,
                    };
                    gep.results = vec![at];
                    let mut load = node.clone();
                    load.inst = Inst::Load {
                        ty: lane_ty.clone(),
                        ptr: at,
                        volatile: false,
                        align: Some(1),
                    };
                    load.results = vec![value];
                    nodes.extend([constant, gep, load]);
                    lanes.push(LaneRead {
                        field,
                        index,
                        address: at,
                        value,
                    });
                    slot.insert((lane_ty, value));
                }
                copies.insert(read, lane_value[&field].clone());
            }
            after.insert(*result, nodes);
            loads.push(LaneLoad {
                array: *result,
                lanes,
                reads: list.iter().map(|(r, _)| *r).collect(),
            });
        }
        let mut out = func.clone();
        for block in &mut out.blocks {
            let body = std::mem::take(&mut block.body);
            let mut rebuilt = Vec::with_capacity(body.len());
            for mut node in body {
                let result = node.results.first().copied();
                if let Some(r) = result
                    && let Some((ty, value)) = copies.get(&r)
                {
                    node.inst = Inst::Copy {
                        ty: ty.clone(),
                        operand: *value,
                    };
                }
                rebuilt.push(node);
                if let Some(r) = result
                    && let Some(nodes) = after.remove(&r)
                {
                    rebuilt.extend(nodes);
                }
            }
            block.body = rebuilt;
        }
        Some((out, PassWitness::LaneLoad(LaneLoadWitness { loads })))
    }
}
