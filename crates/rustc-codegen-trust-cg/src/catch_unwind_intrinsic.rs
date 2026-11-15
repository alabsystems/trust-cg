// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! GNU catch-unwind intrinsic on the native Linux AArch64 lane.
//!
//! The intrinsic calls the typed try callback with its original data pointer.
//! A catch-all handler passes the runtime's exception pointer to the typed catch
//! callback, which owns the runtime-specific cleanup. The helper returns false
//! on normal return and true after the catch callback. No exception is resumed,
//! freed, or interpreted by the bridge. The intrinsic's unsafe contract forbids
//! its catch callback from unwinding.

use super::*;

fn refusal(why: &str) -> String {
    format!("[TCG-CATCH-UNWIND] {why}; failing closed")
}

fn callback_signature<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    callback: Ty<'tcx>,
    inputs: &[Ty<'tcx>],
) -> Result<trust_ir::FuncTyId, String> {
    let ty::FnPtr(types, header) = callback.kind() else {
        return Err(refusal("callback is not a Rust function pointer"));
    };
    let poly = types.with(*header);
    let signature = ctx.tcx.instantiate_bound_regions_with_erased(poly);
    if signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.safety() != rustc_hir::Safety::Unsafe
        || signature.c_variadic()
        || signature.inputs() != inputs
        || !signature.output().is_unit()
    {
        return Err(refusal(&format!(
            "unsupported callback signature {signature:?}"
        )));
    }
    let (id, plan) = ctx.fn_pointer_call_signature(poly)?;
    let declared = &ctx.module.func_types[id.index() as usize];
    let expected = inputs
        .iter()
        .map(|input| rust_ty_to_trust_ir_ty(ctx.tcx, *input))
        .collect::<Result<Vec<_>, _>>()?;
    if plan.is_some()
        || !inputs
            .iter()
            .all(|input| is_thin_pointer_ref_ty(ctx.tcx, *input))
        || !expected.iter().all(is_pointer_like_trust_ir_ty)
        || declared.params != expected
        || !declared.returns.is_empty()
        || declared.is_vararg
    {
        return Err(refusal(
            "callback FnAbi does not lower to thin pointer inputs and unit",
        ));
    }
    Ok(id)
}

pub(super) fn lower<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    call: &DirectCallTerminator<'_, 'tcx>,
    callee: Instance<'tcx>,
) -> Result<(), String> {
    if ctx.tcx.sess.target.arch.desc() != "aarch64"
        || ctx.tcx.sess.target.os != rustc_target::spec::Os::Linux
        || ctx.tcx.sess.target.env != rustc_target::spec::Env::Gnu
        || ctx.tcx.data_layout.pointer_size().bytes() != 8
    {
        return Err(refusal(
            "native qualification requires Linux AArch64 GNU with 64-bit pointers",
        ));
    }
    if !panic_is_abort(ctx.tcx) && crate::knobs::is_enabled(crate::knobs::DISABLE_UNWIND) {
        return Err(refusal("unwinding is disabled"));
    }
    if !matches!(callee.def, ty::InstanceKind::Intrinsic(_))
        || Some(callee.def_id().krate) != real_core_crate(ctx.tcx)
        || ctx.tcx.def_kind(callee.def_id()) != rustc_hir::def::DefKind::Fn
        || ctx.tcx.is_foreign_item(callee.def_id())
    {
        return Err(refusal("callee is not core's intrinsic function"));
    }
    let instance_ty = callee.ty(ctx.tcx, ty::TypingEnv::fully_monomorphized());
    let signature = ctx
        .tcx
        .instantiate_bound_regions_with_erased(instance_ty.fn_sig(ctx.tcx));
    let inputs = signature.inputs();
    if inputs.len() != 3
        || call.args.len() != 3
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.safety() != rustc_hir::Safety::Unsafe
        || signature.c_variadic()
        || signature.output() != ctx.tcx.types.bool
        || ctx.monomorphize_ty(place_rust_ty(ctx, body, call.destination)) != ctx.tcx.types.bool
        || !matches!(inputs[1].kind(), ty::RawPtr(_, rustc_hir::Mutability::Mut))
        || !is_thin_pointer_ref_ty(ctx.tcx, inputs[1])
    {
        return Err(refusal(&format!(
            "unsupported intrinsic signature {signature:?}"
        )));
    }
    for (arg, expected) in call.args.iter().zip(inputs) {
        if ctx.monomorphize_ty(operand_rust_ty(ctx, body, &arg.node)?) != *expected {
            return Err(refusal(
                "operand type differs from the intrinsic's actual signature",
            ));
        }
    }
    let exception_ty = Ty::new_mut_ptr(ctx.tcx, ctx.tcx.types.u8);
    let try_sig = callback_signature(ctx, inputs[0], &[inputs[1]])?;
    let catch_sig = callback_signature(ctx, inputs[2], &[inputs[1], exception_ty])?;
    // The helper uses the intrinsic's actual FnAbi, including its bool return.
    let helper_sig = ctx.func_ty_for_instance(callee)?;
    let declared = &ctx.module.func_types[helper_sig.index() as usize];
    let data_ty = rust_ty_to_trust_ir_ty(ctx.tcx, inputs[1])?;
    if declared.params != [TrustIrTy::Ptr, data_ty, TrustIrTy::Ptr]
        || declared.returns != [TrustIrTy::Bool]
        || declared.is_vararg
        || RustcFnAbiSource::Instance(callee)
            .query(ctx.tcx)?
            .can_unwind
    {
        return Err(refusal(
            "intrinsic FnAbi differs from three thin pointers returning bool",
        ));
    }
    let helper = define_helper(ctx, helper_sig, try_sig, catch_sig)?;
    let mut args = Vec::with_capacity(3);
    for arg in call.args {
        args.push(lower_operand_to_value(ctx, body, block, &arg.node)?);
    }
    ctx.bridge_map_images.clear();
    let result = ctx.fresh_value();
    block.body.push(
        InstrNode::new(Inst::Call {
            callee: helper,
            args,
        })
        .with_result(result),
    );
    lower_elided_scalar_return_call(ctx, body, block, call.destination, call.target, result)
}

fn define_helper(
    ctx: &mut MirLoweringCtx<'_>,
    signature: trust_ir::FuncTyId,
    try_sig: trust_ir::FuncTyId,
    catch_sig: trust_ir::FuncTyId,
) -> Result<FuncId, String> {
    let key = (signature, try_sig, catch_sig);
    if let Some(id) = ctx.catch_unwind_helpers.get(&key) {
        return Ok(*id);
    }
    let stem = format!(
        "trustcg.catch_unwind.{}.{}",
        ctx.tcx.symbol_name(ctx.instance).name,
        signature.index()
    );
    let abort = panic_is_abort(ctx.tcx);
    let thunk = if abort {
        None
    } else {
        Some(ctx.indirect_unwind_thunk(try_sig)?)
    };
    if !abort {
        // The same non-callable marker used by ordinary MIR cleanup lowering.
        // It selects the Rust personality for every EH function in this module.
        ctx.extern_callee_by_name(
            "rust_eh_personality",
            FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                abi: None,
                is_vararg: false,
            },
        );
    }
    let name = ctx.fresh_private_helper_name(&stem)?;
    let id = FuncId::new((ctx.extern_callees.len() + 1) as u32);
    let mut function = TrustIrFunction::new(id, name.clone(), signature, BlockId::new(0));
    function.linkage = Linkage::Internal;
    let mut entry = Block::new(BlockId::new(0));
    entry.params = ctx.module.func_types[signature.index() as usize]
        .params
        .iter()
        .enumerate()
        .map(|(i, ty)| (ValueId::new(i as u32), ty.clone()))
        .collect();
    let data = ValueId::new(1);
    let try_fn = ValueId::new(3);
    entry.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ReifyFnPointer,
            src_ty: TrustIrTy::Ptr,
            dst_ty: TrustIrTy::Func(try_sig),
            operand: ValueId::new(0),
        })
        .with_result(try_fn),
    );
    let normal_id = BlockId::new(1);
    let catch_id = BlockId::new(2);
    if let Some(thunk) = thunk {
        entry.body.push(InstrNode::new(Inst::Invoke {
            callee: thunk,
            args: vec![try_fn, data],
            normal_dest: normal_id,
            normal_args: Vec::new(),
            unwind_dest: catch_id,
        }));
    } else {
        entry.body.push(InstrNode::new(Inst::CallIndirect {
            callee: try_fn,
            sig: try_sig,
            args: vec![data],
            calling_conv: trust_ir::CallingConv::default(),
        }));
        entry.body.push(InstrNode::new(Inst::Br {
            target: normal_id,
            args: Vec::new(),
        }));
    }
    function.blocks.push(entry);
    let mut normal = Block::new(normal_id);
    let returned = ValueId::new(4);
    normal.body.push(
        InstrNode::new(Inst::Const {
            ty: TrustIrTy::Bool,
            value: Constant::Bool(false),
        })
        .with_result(returned),
    );
    normal.body.push(InstrNode::new(Inst::Return {
        values: vec![returned],
    }));
    function.blocks.push(normal);
    if !abort {
        let mut catch = Block::new(catch_id);
        let exception = ValueId::new(5);
        let selector = ValueId::new(6);
        catch.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: false,
                catch_type_indices: vec![0],
            })
            .with_results(vec![exception, selector]),
        );
        let catch_fn = ValueId::new(7);
        catch.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: TrustIrTy::Ptr,
                dst_ty: TrustIrTy::Func(catch_sig),
                operand: ValueId::new(2),
            })
            .with_result(catch_fn),
        );
        let typed_exception = ValueId::new(9);
        catch.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: TrustIrTy::Ptr,
                dst_ty: ctx.module.func_types[catch_sig.index() as usize].params[1].clone(),
                operand: exception,
            })
            .with_result(typed_exception),
        );
        catch.body.push(InstrNode::new(Inst::CallIndirect {
            callee: catch_fn,
            sig: catch_sig,
            args: vec![data, typed_exception],
            calling_conv: trust_ir::CallingConv::default(),
        }));
        let returned = ValueId::new(8);
        catch.body.push(
            InstrNode::new(Inst::Const {
                ty: TrustIrTy::Bool,
                value: Constant::Bool(true),
            })
            .with_result(returned),
        );
        catch.body.push(InstrNode::new(Inst::Return {
            values: vec![returned],
        }));
        function.blocks.push(catch);
    }
    ctx.module
        .try_add_function(function)
        .map_err(|e| e.to_string())?;
    ctx.extern_callees.insert(name, id);
    ctx.catch_unwind_helpers.insert(key, id);
    // Core declares this intrinsic nounwind. In abort-frame LSDA policy its
    // helper has the same boundary as the source intrinsic it replaces.
    ctx.note_synthesized_call_nounwind(id);
    Ok(id)
}
