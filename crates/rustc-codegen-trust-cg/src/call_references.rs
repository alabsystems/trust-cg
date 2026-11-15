//! Stable referent storage for Linux AArch64 call arguments.
use super::*;

fn enabled(ctx: &MirLoweringCtx<'_>) -> bool {
    ctx.tcx.sess.target.arch.desc() == "aarch64"
        && ctx.tcx.sess.target.os == rustc_target::spec::Os::Linux
        && ctx.tcx.data_layout.pointer_size().bytes() == 8
}

/// A register-held borrow is a value model, not a reference address. A fresh
/// argument temporary changes identity even when no mutation or escape occurs.
pub(super) fn check_stable_address<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    operand: &Operand<'tcx>,
    expected_ty: Ty<'tcx>,
    index: usize,
) -> Result<(), String> {
    if enabled(ctx) && matches!(expected_ty.kind(), ty::Ref(..)) {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            if ctx.borrowed_scalars.contains_key(&place.local)
                || ctx.borrowed_aggregates.contains_key(&place.local)
            {
                return Err(format!(
                    "[TCG-REF-ARG-STORAGE] call reference argument {index} has no stable referent address; a temporary would change pointer identity"
                ));
            }
        }
    }
    Ok(())
}

/// A reference passed to a call exposes the identity of its referent. Give
/// that local the same stable storage needed by raw address-taking. Returning
/// no reference does not make a snapshot safe: a callee can compare arguments
/// or return a raw address. Follow whole copies and reborrows to a fixed point;
/// unresolved bindings retain the call-side stable-address refusal.
pub(super) fn address_taken_locals<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
) -> HashSet<Local> {
    let mut refs = HashSet::new();
    let mut locals = HashSet::new();
    if !enabled(ctx) {
        return locals;
    }
    for data in body.basic_blocks.iter() {
        let TerminatorKind::Call { args, .. } = &data.terminator().kind else {
            continue;
        };
        for arg in args {
            let ty = ctx.monomorphize_ty(arg.node.ty(&body.local_decls, ctx.tcx));
            if matches!(ty.kind(), ty::Ref(..)) && is_thin_pointer_ref_ty(ctx.tcx, ty) {
                if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                    if place.projection.is_empty() {
                        refs.insert(place.local);
                    }
                }
            }
        }
    }
    if refs.is_empty() {
        return locals;
    }
    loop {
        let mut changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(boxed) = &statement.kind else {
                    continue;
                };
                let (dst, value) = &**boxed;
                if !dst.projection.is_empty() || !refs.contains(&dst.local) {
                    continue;
                }
                match value {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _)
                        if src.projection.is_empty() =>
                    {
                        changed |= refs.insert(src.local);
                    }
                    Rvalue::Ref(_, _, src) => {
                        if matches!(src.projection.first(), Some(ProjectionElem::Deref)) {
                            changed |= refs.insert(src.local);
                        } else if !src
                            .projection
                            .iter()
                            .any(|p| matches!(p, ProjectionElem::Deref))
                        {
                            locals.insert(src.local);
                            // Taking the address of a reference value needs its
                            // pointee address available when that value is stored.
                            let ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, src.local));
                            if matches!(ty.kind(), ty::Ref(..)) {
                                changed |= refs.insert(src.local);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }
    locals
}
