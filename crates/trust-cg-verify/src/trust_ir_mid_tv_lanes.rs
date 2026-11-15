// trust-cg-verify/trust_ir_mid_tv_lanes.rs - an array load read lane by lane
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of lane-load scalarization ([`LaneLoadWitness`]), deriving
//! its premises from the SOURCE function and the module with this module's
//! own code.
//!
//! The rustc bridge passes and returns a small aggregate as an array value
//! (`[T x n]`) that the wasm32 lane carries by the address of its bytes, and
//! reads its lane `i` as `extractfield [T x n] %v, i` (the declared type the
//! array itself; the differential's view reads it as the interpreter's
//! element read). The inliner binds such an argument or returned value to
//! the `load [T x n], ptr %a` of its bytes. Each claimed rewrite names one
//! such load (`array`), the lanes it reads and the reads:
//!
//! * the instruction defining `array` is a `load` of an array type, not
//!   volatile, whose element (by the module's type table) is an integer, a
//!   float, `bool`, `char` or a thin pointer, of known size `s` (the
//!   interpreter's layout); each claimed lane `i` is below the length, named
//!   once, and gets three fresh values: `index = const usize i * s`,
//!   `address = gep u8, %a, [index]` (not `inbounds`) and `value = load T,
//!   ptr address` (align 1, not volatile), inserted in that order right after
//!   the array load, lane by lane in the claimed order;
//! * each claimed read is the single result of an `extractfield` of `array`
//!   whose declared type is the array type and whose lane is a claimed lane;
//!   it becomes `copy T` of that lane's `value`, in place.
//!
//! Exact: an array's lane `i` is the `T` its element bytes `[i * s, i * s +
//! s)` decode to, in the interpreter's array load as in a scalar load of
//! those bytes; the lane loads read only bytes the array load read just
//! before them, with nothing between, so each succeeds exactly when it does
//! and gives lane `i`, and alignment 1 asks no more than any load. The
//! array load stays (its result may still be used; dead-code elimination
//! removes it otherwise, as a refinement).

use std::collections::{HashMap, HashSet};

use trust_ir::{Constant, Function, Inst, InstrNode, Module, Ty, ValueId};

use super::{MidTvError, WitnessVerdict, used_values};
use crate::fsym_layout::FsymLayout;

/// One lane of an array load: its field, and the fresh offset, address
/// and loaded value (module documentation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaneRead {
    pub field: u32,
    pub index: ValueId,
    pub address: ValueId,
    pub value: ValueId,
}

/// One array load read lane by lane: the load's result, the lanes loaded
/// after it (in order) and the lane reads that become copies.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaneLoad {
    pub array: ValueId,
    pub lanes: Vec<LaneRead>,
    pub reads: Vec<ValueId>,
}

/// Lane-load scalarization's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LaneLoadWitness {
    pub loads: Vec<LaneLoad>,
}

impl LaneLoadWitness {
    /// Number of claimed rewrites (lane reads made copies).
    pub fn rewrite_count(&self) -> usize {
        self.loads.iter().map(|l| l.reads.len()).sum()
    }
}

/// A scalar lane type: an integer, a float, `bool`, `char` or a thin
/// pointer.
fn scalar_lane(ty: &Ty) -> bool {
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

pub(super) fn rebuild_lane_load(
    module: &Module,
    source: &Function,
    witness: &LaneLoadWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let layout = FsymLayout::new(module);
    let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
    let mut taken: HashSet<ValueId> = used_values(source);
    for (bi, block) in source.blocks.iter().enumerate() {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for (ni, node) in block.body.iter().enumerate() {
            taken.extend(node.results.iter().copied());
            if let [r] = node.results.as_slice() {
                at.insert(*r, (bi, ni));
            }
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    if witness.loads.is_empty() {
        return Err(MidTvError::NotLaneLoad {
            value: ValueId::new(0),
            why: "the witness claims no load".to_string(),
        });
    }
    let mut after: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
    let mut copies: HashMap<(usize, usize), Inst> = HashMap::new();
    for claim in &witness.loads {
        let bad = |why: &str| MidTvError::NotLaneLoad {
            value: claim.array,
            why: why.to_string(),
        };
        let &(bi, ni) = at
            .get(&claim.array)
            .ok_or_else(|| bad("not the single result of an instruction"))?;
        if after.contains_key(&(bi, ni)) {
            return Err(bad("claimed twice"));
        }
        let node = &source.blocks[bi].body[ni];
        let Inst::Load {
            ty: array_ty,
            ptr,
            volatile: false,
            ..
        } = &node.inst
        else {
            return Err(bad("not a load that is not volatile"));
        };
        let Ty::Array(elem, length) = array_ty else {
            return Err(bad("not a load of an array"));
        };
        let elem = module
            .ty(*elem)
            .ok_or_else(|| bad("the element type is not in the module's table"))?
            .clone();
        if !scalar_lane(&elem) {
            return Err(bad("the element is not a scalar"));
        }
        let size = layout
            .size(&elem)
            .map_err(|_| bad("the element's size is unknown"))?;
        if claim.lanes.is_empty() || claim.reads.is_empty() {
            return Err(bad("no lane or no read is claimed"));
        }
        let mut nodes: Vec<InstrNode> = Vec::new();
        let mut lane_values: HashMap<u32, ValueId> = HashMap::new();
        for lane in &claim.lanes {
            if u64::from(lane.field) >= *length {
                return Err(bad("a lane past the array's length"));
            }
            if lane_values.insert(lane.field, lane.value).is_some() {
                return Err(bad("a lane is claimed twice"));
            }
            for v in [lane.index, lane.address, lane.value] {
                if !taken.insert(v) {
                    return Err(bad("a named value is not fresh"));
                }
            }
            let offset = u64::from(lane.field)
                .checked_mul(size)
                .ok_or_else(|| bad("the lane's offset overflows"))?;
            let mut constant = node.clone();
            constant.inst = Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(i128::from(offset)),
            };
            constant.results = vec![lane.index];
            let mut gep = node.clone();
            gep.inst = Inst::GEP {
                pointee_ty: Ty::U8,
                base: *ptr,
                indices: vec![lane.index],
                inbounds: false,
            };
            gep.results = vec![lane.address];
            let mut load = node.clone();
            load.inst = Inst::Load {
                ty: elem.clone(),
                ptr: lane.address,
                volatile: false,
                align: Some(1),
            };
            load.results = vec![lane.value];
            nodes.extend([constant, gep, load]);
        }
        for read in &claim.reads {
            let &(rb, rn) = at
                .get(read)
                .ok_or_else(|| bad("a read is not the single result of an instruction"))?;
            let field = match &source.blocks[rb].body[rn].inst {
                Inst::ExtractField {
                    ty,
                    aggregate,
                    field,
                } if *aggregate == claim.array && ty == array_ty => *field,
                Inst::ExtractElement { ty, array, index }
                    if *array == claim.array && *ty == elem =>
                {
                    let &(ib, ins) = at
                        .get(index)
                        .ok_or_else(|| bad("a lane index has no definition"))?;
                    let Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(i),
                    } = source.blocks[ib].body[ins].inst
                    else {
                        return Err(bad("a lane index is not a usize constant"));
                    };
                    u32::try_from(i).map_err(|_| bad("a lane index is out of range"))?
                }
                _ => return Err(bad("a read is not a typed constant lane of the array load")),
            };
            let value = *lane_values
                .get(&field)
                .ok_or_else(|| bad("a read's lane is not claimed"))?;
            if copies
                .insert(
                    (rb, rn),
                    Inst::Copy {
                        ty: elem.clone(),
                        operand: value,
                    },
                )
                .is_some()
            {
                return Err(bad("a read is claimed twice"));
            }
        }
        after.insert((bi, ni), nodes);
    }
    let mut expected = source.clone();
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        let mut rebuilt = Vec::with_capacity(body.len());
        for (ni, mut node) in body.into_iter().enumerate() {
            if let Some(inst) = copies.remove(&(bi, ni)) {
                node.inst = inst;
            }
            rebuilt.push(node);
            if let Some(nodes) = after.remove(&(bi, ni)) {
                rebuilt.extend(nodes);
            }
        }
        block.body = rebuilt;
    }
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.rewrite_count(),
            refinements: 0,
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_lanes_tests.rs"]
mod tests;
