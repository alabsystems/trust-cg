// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Address transport for thin pointers. These operations supply no allocation,
//! lifetime, aliasing, pointee-layout or dereference authority.

use trust_ir::{Block, CastOp, Inst, InstrNode, Ty, ValueId};

pub(crate) fn is_thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    ) && ty.default_pointer_layout_shape() == Ty::Ptr.default_pointer_layout_shape()
}

/// Whether an address of thin-pointer type `source` may be re-typed as the thin
/// pointer type `destination` by `PtrToPtr`: both are one pointer-width address
/// (a raw pointer, a reference or the bare `Ptr` carrier). The re-type states no
/// pointee layout, validity or dereference authority of its own; it only lets a
/// value that already is an address have the type its consumer declares.
pub(crate) fn can_retype_thin_address(source: &Ty, destination: &Ty) -> bool {
    is_thin_pointer(source) && is_thin_pointer(destination)
}

pub(crate) fn can_transport_address(source: &Ty, destination: &Ty) -> bool {
    is_thin_pointer(source)
        && is_thin_pointer(destination)
        && matches!(destination, Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_))
}

/// TrustIR's pointer/integer casts use the bare `Ptr` carrier. Retain typed
/// endpoints with separate PtrToPtr instructions instead of changing the cast's
/// declared operand type. Check the whole request before allocating or emitting.
/// The integer is exactly pointer-width for the session's target (64 bits, or
/// 32 on wasm32); other integer widths require their own explicit conversion.
pub(crate) fn emit_pointer_integer_cast(
    block: &mut Block,
    op: CastOp,
    source: Ty,
    destination: Ty,
    operand: ValueId,
    result: ValueId,
    mut fresh: impl FnMut() -> ValueId,
) -> Result<(), String> {
    let valid = match op {
        CastOp::PtrToInt => {
            is_thin_pointer(&source)
                && destination.is_integer()
                && destination.bit_width() == Some(crate::session_pointer_bits())
        }
        CastOp::IntToPtr => {
            source.is_integer()
                && source.bit_width() == Some(crate::session_pointer_bits())
                && can_transport_address(&Ty::Ptr, &destination)
        }
        _ => false,
    };
    if !valid {
        return Err(format!(
            "pointer/integer address transport {op:?}: {source:?} -> {destination:?}"
        ));
    }
    let mut emit = |op, src_ty, dst_ty, operand, result| {
        block.body.push(
            InstrNode::new(Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            })
            .with_result(result),
        );
    };
    if op == CastOp::PtrToInt && source != Ty::Ptr {
        let address = fresh();
        emit(CastOp::PtrToPtr, source, Ty::Ptr, operand, address);
        emit(op, Ty::Ptr, destination, address, result);
    } else if op == CastOp::IntToPtr && destination != Ty::Ptr {
        let address = fresh();
        emit(op, source, Ty::Ptr, operand, address);
        emit(CastOp::PtrToPtr, Ty::Ptr, destination, address, result);
    } else {
        emit(op, source, destination, operand, result);
    }
    Ok(())
}
