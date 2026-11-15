//! Runtime layout queries for sized values and bare slices/strings.
//! Data is never dereferenced: a sized layout is constant, and a slice's
//! dynamic size is its element stride multiplied by its length metadata.

use super::*;

pub(super) fn intrinsic<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    call: &DirectCallTerminator<'_, 'tcx>,
    callee: Instance<'tcx>,
    name: &str,
) -> Result<bool, String> {
    if !matches!(name, "size_of_val" | "align_of_val") {
        return Ok(false);
    }
    let pointee = ctx.monomorphize_ty(callee.args.type_at(0));
    let layout = ctx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(pointee))
        .map_err(|e| format!("value layout intrinsic layout_of({pointee:?}): {e:?}"))?;
    if !layout.is_sized() && !matches!(pointee.kind(), ty::Slice(_) | ty::Str) {
        return Ok(false);
    }
    let result_ty = place_trust_ir_ty(ctx, body, call.destination)?;
    if call.args.len() != 1
        || ctx.tcx.data_layout.pointer_size().bytes() != 8
        || !result_ty.is_integer()
        || result_ty.bit_width() != Some(64)
    {
        return Err(
            "value layout intrinsic requires one pointer and a pointer-sized result".into(),
        );
    }
    let value = if name == "align_of_val" {
        emit_i64_const(ctx, block, i128::from(layout.align.bytes()))
    } else if layout.is_sized() {
        emit_i64_const(ctx, block, i128::from(layout.size.bytes()))
    } else {
        let element = match pointee.kind() {
            ty::Slice(element) => *element,
            ty::Str => ctx.tcx.types.u8,
            _ => return Err("value layout intrinsic requires a bare slice or string".into()),
        };
        let (stride, _) = element_layout_size_align(ctx.tcx, element)?;
        if stride == 0 {
            // ZST slices may carry any usize length; no multiplication or
            // truncation of that metadata is needed to establish their size.
            emit_i64_const(ctx, block, 0)
        } else {
            let operand = &call.args[0].node;
            let len = match operand {
                Operand::Copy(place) | Operand::Move(place) if !place.projection.is_empty() => {
                    // A fat-pointer field's runtime metadata lives at its actual
                    // field address. Never substitute the containing local's len.
                    let (_, len) = fat_ptr_source_data_meta(ctx, body, block, operand)?
                        .ok_or("value layout intrinsic has no projected slice metadata")?;
                    len
                }
                _ => match ptr_metadata_len(ctx, body, block, operand)? {
                    PtrMetadataLen::Runtime(len) => len,
                    PtrMetadataLen::Const(len) => emit_i64_const(ctx, block, i128::from(len)),
                },
            };
            let stride = emit_i64_const(ctx, block, i128::from(stride));
            // The intrinsic's valid-input contract requires the dynamic size
            // to fit isize. This is the same ordinary product as LLVM emits.
            emit_i64_binop(ctx, block, TrustIrBinOp::Mul, len, stride)
        }
    };
    lower_elided_scalar_return_call(ctx, body, block, call.destination, call.target, value)?;
    Ok(true)
}
