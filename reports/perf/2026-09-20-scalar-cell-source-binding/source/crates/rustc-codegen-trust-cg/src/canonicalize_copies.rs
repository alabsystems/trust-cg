// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Make representation-preserving reinterpretation explicit before SSA checks.
//!
//! Copy requires exact operand/result type agreement. A pointer address extracted
//! from a typed reference must instead use PtrToPtr with its original source
//! type. This pass grants no lifetime, allocation, aliasing or access authority.
//! Fat-pointer metadata and function/Rc/handle carriers are outside this repair.

use std::collections::HashMap;
use trust_ir::{CastOp, Function, Inst, Ty};

use crate::pointer_casts::can_transport_address;

pub(crate) fn canonicalize_reinterpret_copies(func: &mut Function) {
    let mut val_ty: HashMap<u32, Ty> = HashMap::new();
    for block in &func.blocks {
        for (vid, ty) in &block.params {
            val_ty.insert(vid.index(), ty.clone());
        }
        for node in &block.body {
            let ty = match &node.inst {
                Inst::Copy { ty, .. }
                | Inst::Const { ty, .. }
                | Inst::BinOp { ty, .. }
                | Inst::UnOp { ty, .. }
                | Inst::Load { ty, .. } => Some(ty.clone()),
                // Alloca's result is the opaque address carrier, regardless
                // of the stored element type. A subsequent typed raw-pointer
                // Copy therefore needs the same explicit PtrToPtr repair as
                // a pointer parameter does.
                Inst::Alloca { .. } => Some(Ty::Ptr),
                Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
                _ => None,
            };
            if let Some(ty) = ty {
                if let Some(result) = node.results.first() {
                    val_ty.insert(result.index(), ty);
                }
            }
        }
    }
    for block in &mut func.blocks {
        for node in &mut block.body {
            if let Inst::Copy { ty, operand } = &node.inst {
                let declared = ty.clone();
                let operand = *operand;
                if let Some(op_ty) = val_ty.get(&operand.index()) {
                    if op_ty != &declared
                        && declared.is_integer()
                        && op_ty.is_integer()
                        && declared.bit_width().is_some()
                        && declared.bit_width() == op_ty.bit_width()
                    {
                        node.inst = Inst::Cast {
                            op: CastOp::Bitcast,
                            src_ty: op_ty.clone(),
                            dst_ty: declared,
                            operand,
                        };
                    } else if op_ty != &declared && can_transport_address(op_ty, &declared) {
                        node.inst = Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: op_ty.clone(),
                            dst_ty: declared,
                            operand,
                        };
                    }
                }
            }
        }
    }
}
