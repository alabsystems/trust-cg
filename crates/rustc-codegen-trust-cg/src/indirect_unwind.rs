//! Indirect calls that keep a live unwind edge on AArch64 Darwin (ledger
//! L06-P8).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! trust-ir's `Invoke` names a function, so an indirect call (a function
//! pointer, a vtable method, a `dyn` place's drop slot) with a cleanup or
//! terminate edge is routed through a private typed forwarding thunk
//! (`MirLoweringCtx::indirect_unwind_thunk`): the thunk has no cleanup of its
//! own, and an unwind out of it lands in the caller's pad. AArch64 Linux has
//! done this since `8df247a87`. On AArch64 Darwin each of the three lanes
//! refused a cleanup edge by name, and a terminate edge on a plain indirect
//! call was refused by `[TCG-EH-CALL-EDGE]`, so admitting the thunk there
//! changes only bodies that did not compile: a `thread_local!` access
//! (`LocalKey::try_with` calls its accessor through a function pointer), a
//! `dyn` method call and a `Box<dyn Trait>` drop with a live cleanup edge.
//! The `Box<dyn Fn*>` blanket `call*` lane (`lower_box_dyn_fn_call_terminator`,
//! the -O0/-O1 form of a boxed closure call) refused a cleanup edge on every
//! target; it takes the thunk on Darwin only ([`blanket_call_target`]).
//!
//! On Darwin the edge is kept unconditionally ([`invoke_keeping_edge`]):
//! `push_call_with_normal_continuation`'s Darwin branch keeps a cleanup edge
//! only for the observable pads `lower_direct_call_terminator` admits, and
//! the drop-slot lane does not pass through that check.

use super::*;

/// The targets whose indirect calls keep a live unwind edge through the
/// typed thunk; every other target refuses such a call by name.
pub(super) fn thunk_target(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.target.arch.desc() == "aarch64"
        && (tcx.sess.target.os == rustc_target::spec::Os::Linux || tcx.sess.target.is_like_darwin)
}

/// The targets whose `Box<dyn Fn*>` blanket `call*` lane routes a live unwind
/// edge through the thunk: AArch64 Darwin, measured here. Linux AArch64 keeps
/// that lane's cleanup refusal until it is run there.
pub(super) fn blanket_call_target(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.target.arch.desc() == "aarch64" && tcx.sess.target.is_like_darwin
}

/// `Invoke` the thunk with the call's own unwind edge (its cleanup pad, or the
/// reason's terminate pad), and continue at a fresh normal block.
pub(super) fn invoke_keeping_edge(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    unwind: &mir::UnwindAction,
    thunk: FuncId,
    args: Vec<ValueId>,
    results: Vec<ValueId>,
) -> Result<(), String> {
    let unwind_dest = match unwind {
        mir::UnwindAction::Cleanup(pad) => {
            if !ctx.eh_active {
                return Err(
                    "indirect call with a cleanup edge while EH is inactive (disable-unwind) — \
                     failing closed rather than walking past the cleanup"
                        .into(),
                );
            }
            BlockId::new(pad.index() as u32)
        }
        mir::UnwindAction::Terminate(reason) => terminate_pad_block(ctx, *reason)?,
        mir::UnwindAction::Continue | mir::UnwindAction::Unreachable => {
            return Err("indirect unwind thunk invoked without a live unwind edge".into());
        }
    };
    let continuation = ctx.fresh_block_id();
    block.body.push(
        InstrNode::new(Inst::Invoke {
            callee: thunk,
            args,
            normal_dest: continuation,
            normal_args: Vec::new(),
            unwind_dest,
        })
        .with_results(results),
    );
    let finished = std::mem::replace(block, Block::new(continuation));
    ctx.extra_blocks.push(finished);
    Ok(())
}
