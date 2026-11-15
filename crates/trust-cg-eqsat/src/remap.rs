// crates/trust-cg-eqsat/src/remap.rs - mutable walk over every SSA operand of a trust-ir instruction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir has an exhaustive *read-only* operand walk
//! (`Inst::visit_value_operands`) and no mutable one. Elaboration must change
//! exactly the value operands of a skeleton instruction and nothing else, so
//! this module is the mutable twin: one `match` with an arm per `Inst`
//! variant and no wildcard (a new trust-ir variant is a compile error here,
//! not a silently skipped operand), visiting the same positions in the same
//! order as `visit_value_operands` at the pinned revision. A unit test checks
//! the two walks agree on every variant.

use trust_ir::{Inst, ValueId};

/// Call `visit` on every SSA value operand of `inst`, in
/// `Inst::visit_value_operands` order, by mutable reference.
#[allow(clippy::too_many_lines)]
pub(crate) fn for_each_operand_mut(inst: &mut Inst, visit: &mut dyn FnMut(&mut ValueId)) {
    match inst {
        Inst::Drop { ptr, .. } => visit(ptr),
        Inst::DropInvoke {
            ptr, normal_args, ..
        } => {
            visit(ptr);
            normal_args.iter_mut().for_each(&mut *visit);
        }
        Inst::BinOp { lhs, rhs, .. }
        | Inst::TensorContract { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. } => {
            visit(lhs);
            visit(rhs);
        }
        Inst::SeqMapAddK { seq, .. } | Inst::SeqMapNot { seq, .. } | Inst::SeqMap { seq, .. } => {
            visit(seq);
        }
        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } | Inst::Copy { operand, .. } => {
            visit(operand);
        }
        Inst::Load { ptr, .. }
        | Inst::PtrData { ptr, .. }
        | Inst::PtrMetadata { ptr, .. }
        | Inst::AtomicLoad { ptr, .. }
        | Inst::Borrow { ptr }
        | Inst::BorrowMut { ptr }
        | Inst::Retain { ptr }
        | Inst::Release { ptr }
        | Inst::IsUnique { ptr }
        | Inst::Dealloc { ptr } => visit(ptr),
        Inst::Store { ptr, value, .. }
        | Inst::AtomicStore { ptr, value, .. }
        | Inst::AtomicRMW { ptr, value, .. } => {
            visit(ptr);
            visit(value);
        }
        Inst::MemCopy {
            dst, src, bytes, ..
        } => {
            visit(dst);
            visit(src);
            visit(bytes);
        }
        Inst::MemSet { dst, byte, bytes } => {
            visit(dst);
            visit(byte);
            visit(bytes);
        }
        Inst::Alloca { count, .. } | Inst::HeapAlloc { count, .. } => {
            if let Some(count) = count {
                visit(count);
            }
        }
        Inst::GEP { base, indices, .. } => {
            visit(base);
            indices.iter_mut().for_each(&mut *visit);
        }
        Inst::PtrFromParts { data, metadata, .. } => {
            visit(data);
            visit(metadata);
        }
        Inst::CmpXchg {
            ptr,
            expected,
            desired,
            ..
        } => {
            visit(ptr);
            visit(expected);
            visit(desired);
        }
        Inst::Br { args, .. } | Inst::Call { args, .. } | Inst::CallCannotUnwind { args, .. } => {
            args.iter_mut().for_each(&mut *visit);
        }
        Inst::CondBr {
            cond,
            then_args,
            else_args,
            ..
        } => {
            visit(cond);
            then_args.iter_mut().for_each(&mut *visit);
            else_args.iter_mut().for_each(&mut *visit);
        }
        Inst::Switch {
            value,
            default_args,
            cases,
            ..
        } => {
            visit(value);
            default_args.iter_mut().for_each(&mut *visit);
            for case in cases {
                case.args.iter_mut().for_each(&mut *visit);
            }
        }
        Inst::CallIndirect { callee, args, .. }
        | Inst::CallIndirectCannotUnwind { callee, args, .. } => {
            visit(callee);
            args.iter_mut().for_each(&mut *visit);
        }
        Inst::Return { values } => values.iter_mut().for_each(&mut *visit),
        Inst::MakeAggregate { fields, .. }
        | Inst::MakeClosure {
            captures: fields, ..
        } => fields.iter_mut().for_each(&mut *visit),
        Inst::ArraySplat { value, .. } => visit(value),
        // trust-ir v68/v69 tensor instructions, in `visit_value_operands`
        // order; the map body's lanes, the view's index nodes and the axis
        // lists are not values.
        Inst::TensorMap { args, .. } => args.iter_mut().for_each(&mut *visit),
        Inst::TensorReduce { src, .. } => visit(src),
        Inst::TensorView {
            src, params, fill, ..
        } => {
            visit(src);
            params.iter_mut().for_each(&mut *visit);
            if let Some(fill) = fill {
                visit(fill);
            }
        }
        Inst::TensorGather { data, coords, .. } => {
            visit(data);
            coords.iter_mut().for_each(&mut *visit);
        }
        Inst::TensorScatter {
            init, src, coords, ..
        } => {
            visit(init);
            visit(src);
            coords.iter_mut().for_each(&mut *visit);
        }
        Inst::ExtractField { aggregate, .. } => visit(aggregate),
        Inst::InsertField {
            aggregate, value, ..
        } => {
            visit(aggregate);
            visit(value);
        }
        Inst::ExtractElement { array, index, .. } => {
            visit(array);
            visit(index);
        }
        Inst::InsertElement {
            array,
            index,
            value,
            ..
        } => {
            visit(array);
            visit(index);
            visit(value);
        }
        Inst::Assume { cond } => visit(cond),
        Inst::Assert { cond, kind, site } => {
            visit(cond);
            if let Some(operands) = kind.operands_mut() {
                for operand in operands {
                    visit(operand);
                }
            }
            if let Some(location) = site.as_mut().and_then(|site| site.location_value_mut()) {
                visit(location);
            }
        }
        Inst::AssertInvoke {
            cond,
            kind,
            site,
            normal_args,
            ..
        } => {
            visit(cond);
            if let Some(operands) = kind.operands_mut() {
                for operand in operands {
                    visit(operand);
                }
            }
            if let Some(location) = site.location_value_mut() {
                visit(location);
            }
            normal_args.iter_mut().for_each(&mut *visit);
        }
        Inst::Select {
            cond,
            then_val,
            else_val,
            ..
        } => {
            visit(cond);
            visit(then_val);
            visit(else_val);
        }
        Inst::EndBorrow { borrow_ptr } => visit(borrow_ptr),
        Inst::BindSlot { frame, value, .. } | Inst::CoroSuspend { frame, value, .. } => {
            visit(frame);
            visit(value);
        }
        Inst::LoadSlot { frame, .. } | Inst::CloseFrame { frame } => visit(frame),
        Inst::Invoke {
            args, normal_args, ..
        } => {
            args.iter_mut().for_each(&mut *visit);
            normal_args.iter_mut().for_each(&mut *visit);
        }
        Inst::InvokeIndirect {
            callee,
            args,
            normal_args,
            ..
        } => {
            visit(callee);
            args.iter_mut().for_each(&mut *visit);
            normal_args.iter_mut().for_each(&mut *visit);
        }
        Inst::Resume { exn } => visit(exn),
        Inst::DialectOp(operation) => operation.operands.iter_mut().for_each(&mut *visit),
        Inst::Fence { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Unreachable
        | Inst::OpenFrame { .. }
        | Inst::LandingPad { .. } => {}
    }
}

/// Replace the operands of `inst`, in visit order, with `values`. Returns
/// `false` (leaving `inst` partly rewritten) when the count differs.
pub(crate) fn replace_operands(inst: &mut Inst, values: &[ValueId]) -> bool {
    let mut next = values.iter();
    let mut ok = true;
    for_each_operand_mut(inst, &mut |slot| match next.next() {
        Some(value) => *slot = *value,
        None => ok = false,
    });
    ok && next.next().is_none()
}

/// The operands of `inst` in `visit_value_operands` order.
pub(crate) fn operands(inst: &Inst) -> Vec<ValueId> {
    let mut out = Vec::new();
    inst.visit_value_operands(|value| out.push(value));
    out
}

#[cfg(test)]
mod tests;
