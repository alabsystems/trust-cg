// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure argument transport from the ordinary compiler-owned ABI plans.
//! Select and validate the complete list before emitting any argument bytes.

use super::*;

mod argument_emit;
mod argument_plan;
mod copy_layout;

pub(super) use argument_emit::emit_lane_copy;
pub(super) use copy_layout::{byte_copy_shape, lane_copy_shape, plan_field_copy};

pub(super) fn argument_values<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    block: &mut Block,
    source: RustcFnAbiSource<'tcx>,
    args: Vec<ClosureArg<'tcx>>,
) -> Result<Vec<ClosureArgValues>, String> {
    let plans = args
        .into_iter()
        .map(|arg| argument_plan::plan(ctx, source, arg))
        .collect::<Result<Vec<_>, _>>()?;
    plans
        .into_iter()
        .map(|plan| argument_emit::emit(ctx, block, plan))
        .collect()
}

pub(super) fn call_args<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    block: &mut Block,
    instance: Instance<'tcx>,
    env: Option<ValueId>,
    mut args: Vec<ClosureArg<'tcx>>,
) -> Result<Vec<ValueId>, String> {
    let source = RustcFnAbiSource::Instance(instance);
    let instance_ty = instance.ty(ctx.tcx, ty::TypingEnv::fully_monomorphized());
    let mut borrowed_env = None;
    if matches!(instance_ty.kind(), ty::Closure(..)) && closure_body_takes_env(ctx.tcx, instance) {
        let env = env.ok_or_else(|| {
            format!(
                "[TCG-ARG-ABI] the closure body `{}` takes an environment but its call site \
                 has none; failing closed",
                ctx.tcx.symbol_name(instance).name
            )
        })?;
        if closure_body_env_by_value(ctx.tcx, instance) {
            args.insert(
                0,
                ClosureArg {
                    ty: instance_ty,
                    abi_arg_index: 0,
                    src: ClosureArgSrc::Slot(env),
                },
            );
        } else {
            borrowed_env = Some(env);
        }
    }
    // Plans retain original FnAbi ordinals, including skipped ZST positions.
    // No loads, copies, fresh IDs or fresh_arg_copies mutations occur here.
    let abi = source.query(ctx.tcx)?;
    let mut supplied = vec![false; abi.args.len()];
    if borrowed_env.is_some() {
        let Some(receiver) = supplied.first_mut() else {
            return Err("[TCG-ARG-ABI] closure environment has no original FnAbi receiver".into());
        };
        *receiver = true;
    }
    for arg in &args {
        let Some(present) = supplied.get_mut(arg.abi_arg_index) else {
            return Err(format!(
                "[TCG-ARG-ABI] closure argument {} has no original FnAbi ordinal",
                arg.abi_arg_index
            ));
        };
        if std::mem::replace(present, true) {
            return Err(format!(
                "[TCG-ARG-ABI] closure argument {} repeats its original FnAbi ordinal",
                arg.abi_arg_index
            ));
        }
    }
    for (index, arg) in abi.args.iter().enumerate() {
        // The existing outer call binder owns the hidden trailing Location;
        // it is not a semantic argument of this transport builder.
        let caller_location =
            instance_abi_has_caller_location(ctx.tcx, instance) && index + 1 == abi.args.len();
        if !supplied[index] && !caller_location && !is_zero_sized_call_ty(ctx.tcx, arg.layout.ty) {
            return Err(format!(
                "[TCG-ARG-ABI] closure argument {index} is missing its original FnAbi input"
            ));
        }
    }
    let built = argument_values(ctx, block, source, args)?;
    let mut values = Vec::with_capacity(built.len() + usize::from(borrowed_env.is_some()));
    values.extend(borrowed_env);
    for arg in built {
        values.extend(arg.values);
    }
    Ok(values)
}

/// A generic intercepted call binds one result, not a Pair or hidden buffer.
/// MIR and dedicated try_fold calls keep their own checked result binders.
pub(super) fn refuse_single_result_call<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    instance: Instance<'tcx>,
) -> Result<(), String> {
    if ctx.scalar_pair_returns.contains_key(&instance) {
        return Err(format!(
            "[TCG-RET-ABI] hand-built closure `{}` needs its two-result Pair binder",
            ctx.tcx.def_path_str(instance.def_id())
        ));
    }
    if ctx.sret_returns.contains_key(&instance) {
        return Err(format!(
            "[TCG-SRET-ABI] hand-built closure `{}` needs its indirect-result buffer binder",
            ctx.tcx.def_path_str(instance.def_id())
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
