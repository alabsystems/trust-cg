//! A stronger, condition-free threading proof for a bounded set of paths.
//!
//! Each source path to one latch must produce the same expressions over header
//! scalars alone. Branch predicates and reads may be unknown: they restrict
//! reachability, while this check proves the result for every enumerated path
//! and every input, including infeasible paths. Unknowns never become shared
//! source/implementation inputs. The independent IR walk must agree on all its
//! paths too. This proves scalar threading, not memory or branch correctness.

use super::*;

const MAX_VISITS: usize = 4096;
const MAX_PATHS: usize = 256;
const MAX_DEPTH: usize = 128;

fn paths(
    body: &Body<'_>,
    header: mir::BasicBlock,
    latch: mir::BasicBlock,
) -> Result<Vec<Vec<mir::BasicBlock>>, String> {
    let region = vc_mir_loop_blocks(body, header, latch);
    let mut work = vec![vec![header]];
    let mut result = Vec::new();
    let mut visits = 0;
    while let Some(path) = work.pop() {
        visits += 1;
        if visits > MAX_VISITS || path.len() > MAX_DEPTH || result.len() >= MAX_PATHS {
            return Err("source path-consensus traversal budget exceeded".to_owned());
        }
        let current = *path.last().unwrap();
        let term = &body.basic_blocks[current].terminator().kind;
        if current == latch {
            if !crate::mir_goto::view(term).is_some_and(|goto| goto.target() == header) {
                return Err("source path-consensus latch is not a direct back-edge".to_owned());
            }
            result.push(path);
            continue;
        }
        for next in terminator_successors(term) {
            if next == header || !region.contains(&next) {
                continue;
            }
            if path.contains(&next) {
                return Err("source path-consensus contains a nested cycle".to_owned());
            }
            let mut branch = path.clone();
            branch.push(next);
            work.push(branch);
        }
    }
    if result.is_empty() {
        return Err("source path-consensus has no path to the latch".to_owned());
    }
    Ok(result)
}

/// Only the inherent core slice lookup with a usize index is abstracted here.
/// It reads no scalar local by address and cannot mutate one through its args.
fn readonly_get<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    callee: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
) -> bool {
    let Some((id, name)) = call_callee_item_name(ctx, body, callee) else {
        return false;
    };
    name == "get"
        && matches!(ctx.tcx.crate_name(id.krate).as_str(), "core" | "std")
        && ctx.tcx.impl_of_assoc(id).is_some()
        && ctx.tcx.trait_of_assoc(id).is_none()
        && args.len() == 2
        && matches!(ctx.monomorphize_ty(args[0].node.ty(&body.local_decls, ctx.tcx)).kind(),
            ty::Ref(_, inner, rustc_hir::Mutability::Not) if matches!(inner.kind(), ty::Slice(_)))
        && matches!(
            ctx.monomorphize_ty(args[1].node.ty(&body.local_decls, ctx.tcx))
                .kind(),
            ty::Uint(ty::UintTy::Usize)
        )
}

pub(super) fn source<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    header: mir::BasicBlock,
    latch: mir::BasicBlock,
    slots: &[(Local, refine::MirScalarTy)],
) -> Result<Vec<refine::MirStmt>, String> {
    // No address of any MIR local may escape, including before the loop. A
    // memory operation therefore cannot secretly reassign a modeled scalar.
    // This conservative boundary also excludes closure captures and inline asm.
    for data in body.basic_blocks.iter() {
        if matches!(data.terminator().kind, TerminatorKind::InlineAsm { .. }) {
            return Err("source path-consensus excludes inline assembly".to_owned());
        }
        for statement in &data.statements {
            if let StatementKind::Assign(assignment) = &statement.kind {
                if matches!(assignment.1, Rvalue::Ref(..) | Rvalue::RawPtr(..)) {
                    return Err("source path-consensus excludes address-taken locals".to_owned());
                }
            }
        }
    }
    let allowed: HashSet<String> = slots.iter().map(|(l, _)| vc_local_name(*l)).collect();
    let mut consensus: Option<Vec<SmtExpr>> = None;
    let mut representative = Vec::new();
    for (path_id, path) in paths(body, header, latch)?.into_iter().enumerate() {
        let mut statements = Vec::new();
        let mut overflow = HashMap::new();
        for block in path {
            let data = &body.basic_blocks[block];
            for (index, statement) in data.statements.iter().enumerate() {
                match &statement.kind {
                    StatementKind::Assign(assignment) => {
                        let (place, value) = &**assignment;
                        if !place.projection.is_empty() {
                            return Err(
                                "source path-consensus excludes projected writes".to_owned()
                            );
                        }
                        let modeled = vc_try_overflow_stmt(ctx, body, place, value, &mut overflow)
                            .ok()
                            .flatten()
                            .or_else(|| {
                                vc_rvalue(ctx, body, value)
                                    .ok()
                                    .map(|rvalue| refine::MirStmt {
                                        dst: vc_local_name(place.local),
                                        rvalue,
                                    })
                            });
                        if let Some(stmt) = modeled {
                            statements.push(stmt);
                        } else {
                            overflow.remove(&place.local);
                            // Havoc an unsupported scalar read. Non-scalar reads
                            // cannot enter the scalar encoder; their subsequent
                            // projections are independently havoced as well.
                            if let Ok(ty) = vc_scalar_ty(local_rust_ty(ctx, body, place.local)) {
                                statements.push(refine::MirStmt {
                                    dst: vc_local_name(place.local),
                                    rvalue: refine::MirRvalue::Use {
                                        src: refine::MirOperand::Var {
                                            name: format!(
                                                "__source_unknown_{path_id}_{}_{index}",
                                                block.index()
                                            ),
                                            ty,
                                        },
                                    },
                                });
                            }
                        }
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::FakeRead(_)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType(_, _)
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Nop => {}
                    _ => return Err("source path-consensus has an unmodeled statement".to_owned()),
                }
            }
            match &data.terminator().kind {
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::Assert { .. } => {}
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target: Some(ret),
                    // Continue leaves this function on unwind, so only the
                    // normal return can reach the latch. The call must still
                    // match one of the independent models below; cleanup and
                    // terminate edges remain outside this path abstraction.
                    unwind: mir::UnwindAction::Unreachable | mir::UnwindAction::Continue,
                    ..
                } => {
                    if !destination.projection.is_empty() {
                        return Err(
                            "source path-consensus excludes projected call results".to_owned()
                        );
                    }
                    if let Some(stmt) = vc_model_overflowing_call(
                        ctx,
                        body,
                        func,
                        args,
                        destination,
                        &mut overflow,
                    )? {
                        statements.push(stmt);
                    } else if let Some((local, rvalue, _)) =
                        vc_model_wrapping_call(ctx, body, func, args, destination, *ret)?
                    {
                        statements.push(refine::MirStmt {
                            dst: vc_local_name(local),
                            rvalue,
                        });
                    } else if readonly_get(ctx, body, func, args) {
                        // Its Option<&T> result is deliberately NOT modeled as
                        // a scalar or an overflow pair. No borrowed byte may
                        // become a header expression through this abstraction.
                        overflow.remove(&destination.local);
                    } else {
                        return Err("source path-consensus has an unmodeled call".to_owned());
                    }
                }
                _ => return Err("source path-consensus has an unmodeled terminator".to_owned()),
            }
        }
        let mut store =
            refine::encode_block_store(&refine::MirBlock::straight_line(statements.clone()))?;
        let values: Vec<_> = slots
            .iter()
            .map(|(local, ty)| {
                store.resolve(&refine::MirOperand::Var {
                    name: vc_local_name(*local),
                    ty: ty.clone(),
                })
            })
            .collect();
        if values
            .iter()
            .any(|value| value.free_vars().iter().any(|name| !allowed.contains(name)))
        {
            return Err(
                "source path-consensus result depends on an unmodeled or non-header value"
                    .to_owned(),
            );
        }
        if let Some(expected) = &consensus {
            if expected != &values {
                return Err("source paths to the latch disagree on threaded values".to_owned());
            }
        } else {
            consensus = Some(values);
            representative = statements;
        }
    }
    Ok(representative)
}
