// trust-cg-eqsat-check/src/operands.rs - positional value-operand walk and overwrite
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The value operands of an instruction, in `Inst::visit_value_operands`
//! order (the order docs/eqsat-tier-e.md section 8 item 4 names), and the
//! positional overwrite the skeleton comparison uses.
//!
//! trust-ir has no mutable operand visitor, so [`set_operands`] is a
//! hand-written match over every `Inst` variant, with no wildcard arm: a new
//! variant at a future pin is a compile error here, not a silent gap. Its
//! output is re-walked with trust-ir's own visitor and refused unless the walk
//! yields exactly the requested operands, so an order drift between this
//! match and `visit_value_operands` is a refusal, never a wrong comparison.

use trust_ir::{Inst, ValueId};

/// The value operands of `inst`, in trust-ir's visit order.
pub(crate) fn operands(inst: &Inst) -> Vec<ValueId> {
    let mut out = Vec::new();
    inst.visit_value_operands(|v| out.push(v));
    out
}

struct Feed<'a> {
    it: std::slice::Iter<'a, ValueId>,
}

impl Feed<'_> {
    fn put(&mut self, slot: &mut ValueId) -> Option<()> {
        *slot = *self.it.next()?;
        Some(())
    }

    fn put_all(&mut self, slots: &mut [ValueId]) -> Option<()> {
        for slot in slots {
            self.put(slot)?;
        }
        Some(())
    }
}

/// Overwrites the value operands of `inst` positionally with `new`. Returns
/// `None` when the counts differ or the overwrite does not reproduce `new`
/// under trust-ir's own walk.
pub(crate) fn set_operands(inst: &mut Inst, new: &[ValueId]) -> Option<()> {
    let mut f = Feed { it: new.iter() };
    match inst {
        Inst::Drop { ptr, .. } => f.put(ptr)?,
        Inst::DropInvoke {
            ptr, normal_args, ..
        } => {
            f.put(ptr)?;
            f.put_all(normal_args)?;
        }
        Inst::BinOp { lhs, rhs, .. }
        | Inst::TensorContract { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. } => {
            f.put(lhs)?;
            f.put(rhs)?;
        }
        Inst::SeqMapAddK { seq, .. } | Inst::SeqMapNot { seq, .. } | Inst::SeqMap { seq, .. } => {
            f.put(seq)?
        }
        Inst::UnOp { operand, .. }
        | Inst::Cast { operand, .. }
        | Inst::Copy { operand, .. }
        | Inst::BoxDeref { operand, .. } => f.put(operand)?,
        Inst::Load { ptr, .. }
        | Inst::PtrData { ptr, .. }
        | Inst::PtrMetadata { ptr, .. }
        | Inst::AtomicLoad { ptr, .. }
        | Inst::Borrow { ptr }
        | Inst::BorrowMut { ptr }
        | Inst::Retain { ptr }
        | Inst::Release { ptr }
        | Inst::IsUnique { ptr }
        | Inst::Dealloc { ptr } => f.put(ptr)?,
        Inst::Store { ptr, value, .. }
        | Inst::AtomicStore { ptr, value, .. }
        | Inst::AtomicRMW { ptr, value, .. } => {
            f.put(ptr)?;
            f.put(value)?;
        }
        Inst::MemCopy {
            dst, src, bytes, ..
        } => {
            f.put(dst)?;
            f.put(src)?;
            f.put(bytes)?;
        }
        Inst::MemSet { dst, byte, bytes } => {
            f.put(dst)?;
            f.put(byte)?;
            f.put(bytes)?;
        }
        Inst::Alloca { count, .. } | Inst::HeapAlloc { count, .. } => {
            if let Some(count) = count {
                f.put(count)?;
            }
        }
        Inst::GEP { base, indices, .. } => {
            f.put(base)?;
            f.put_all(indices)?;
        }
        Inst::PtrFromParts { data, metadata, .. } => {
            f.put(data)?;
            f.put(metadata)?;
        }
        Inst::CmpXchg {
            ptr,
            expected,
            desired,
            ..
        } => {
            f.put(ptr)?;
            f.put(expected)?;
            f.put(desired)?;
        }
        Inst::Br { args, .. } | Inst::Call { args, .. } | Inst::CallCannotUnwind { args, .. } => {
            f.put_all(args)?
        }
        Inst::CondBr {
            cond,
            then_args,
            else_args,
            ..
        } => {
            f.put(cond)?;
            f.put_all(then_args)?;
            f.put_all(else_args)?;
        }
        Inst::Switch {
            value,
            default_args,
            cases,
            ..
        } => {
            f.put(value)?;
            f.put_all(default_args)?;
            for case in cases {
                f.put_all(&mut case.args)?;
            }
        }
        Inst::CallIndirect { callee, args, .. }
        | Inst::CallIndirectCannotUnwind { callee, args, .. } => {
            f.put(callee)?;
            f.put_all(args)?;
        }
        Inst::Return { values } => f.put_all(values)?,
        Inst::MakeAggregate { fields, .. } => f.put_all(fields)?,
        Inst::MakeClosure { captures, .. } => f.put_all(captures)?,
        Inst::ArraySplat { value, .. } => f.put(value)?,
        // trust-ir v68/v69 tensor instructions, in `visit_value_operands`
        // order; the map body's lanes, the view's index nodes and the axis
        // lists are not values.
        Inst::TensorMap { args, .. } => f.put_all(args)?,
        Inst::TensorReduce { src, .. } => f.put(src)?,
        Inst::TensorView {
            src, params, fill, ..
        } => {
            f.put(src)?;
            f.put_all(params)?;
            if let Some(fill) = fill {
                f.put(fill)?;
            }
        }
        Inst::TensorGather { data, coords, .. } => {
            f.put(data)?;
            f.put_all(coords)?;
        }
        Inst::TensorScatter {
            init, src, coords, ..
        } => {
            f.put(init)?;
            f.put(src)?;
            f.put_all(coords)?;
        }
        Inst::ExtractField { aggregate, .. } => f.put(aggregate)?,
        Inst::InsertField {
            aggregate, value, ..
        } => {
            f.put(aggregate)?;
            f.put(value)?;
        }
        Inst::ExtractElement { array, index, .. } => {
            f.put(array)?;
            f.put(index)?;
        }
        Inst::InsertElement {
            array,
            index,
            value,
            ..
        } => {
            f.put(array)?;
            f.put(index)?;
            f.put(value)?;
        }
        Inst::Assume { cond } => f.put(cond)?,
        Inst::Assert { cond, kind, site } => {
            f.put(cond)?;
            if let Some(slots) = kind.operands_mut() {
                for slot in slots {
                    f.put(slot)?;
                }
            }
            if let Some(location) = site.as_mut().and_then(|s| s.location_value_mut()) {
                f.put(location)?;
            }
        }
        Inst::AssertInvoke {
            cond,
            kind,
            site,
            normal_args,
            ..
        } => {
            f.put(cond)?;
            if let Some(slots) = kind.operands_mut() {
                for slot in slots {
                    f.put(slot)?;
                }
            }
            if let Some(location) = site.location_value_mut() {
                f.put(location)?;
            }
            f.put_all(normal_args)?;
        }
        Inst::Select {
            cond,
            then_val,
            else_val,
            ..
        } => {
            f.put(cond)?;
            f.put(then_val)?;
            f.put(else_val)?;
        }
        Inst::EndBorrow { borrow_ptr } => f.put(borrow_ptr)?,
        Inst::BindSlot { frame, value, .. } | Inst::CoroSuspend { frame, value, .. } => {
            f.put(frame)?;
            f.put(value)?;
        }
        Inst::LoadSlot { frame, .. } | Inst::CloseFrame { frame } => f.put(frame)?,
        Inst::Invoke {
            args, normal_args, ..
        } => {
            f.put_all(args)?;
            f.put_all(normal_args)?;
        }
        Inst::InvokeIndirect {
            callee,
            args,
            normal_args,
            ..
        } => {
            f.put(callee)?;
            f.put_all(args)?;
            f.put_all(normal_args)?;
        }
        Inst::Resume { exn } => f.put(exn)?,
        Inst::DialectOp(operation) => f.put_all(&mut operation.operands)?,
        Inst::Fence { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Unreachable
        | Inst::OpenFrame { .. }
        | Inst::LandingPad { .. } => {}
    }
    if f.it.next().is_some() {
        return None;
    }
    if operands(inst) != new {
        return None;
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{BlockId, SwitchCase, Ty};

    #[test]
    fn switch_case_args_round_trip() {
        let v = ValueId::new;
        let mut inst = Inst::Switch {
            value: v(0),
            default: BlockId::new(1),
            default_args: vec![v(1)],
            cases: vec![SwitchCase {
                value: trust_ir::Constant::Int(3),
                target: BlockId::new(2),
                args: vec![v(2), v(3)],
            }],
            exhaustive_enum_unreachable: false,
        };
        let new = [v(10), v(11), v(12), v(13)];
        assert_eq!(set_operands(&mut inst, &new), Some(()));
        assert_eq!(operands(&inst), new.to_vec());
        assert_eq!(set_operands(&mut inst, &new[..3]), None);
    }

    #[test]
    fn binop_overwrite_and_count_mismatch() {
        let v = ValueId::new;
        let mut inst = Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::U32,
            lhs: v(0),
            rhs: v(1),
        };
        assert_eq!(set_operands(&mut inst, &[v(5), v(6)]), Some(()));
        assert_eq!(operands(&inst), vec![v(5), v(6)]);
        assert_eq!(set_operands(&mut inst, &[v(5), v(6), v(7)]), None);
    }
}
