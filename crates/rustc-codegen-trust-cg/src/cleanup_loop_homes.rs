//! [TCG-EH-CLEANUP-LOOP] Frame homes for the loop-carried scalars an unwind
//! edge cannot pass as block arguments (ledger L06-P8).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! This frontend carries a loop's live, reassigned scalars through loop-header
//! block parameters, so inside a loop such a local's SSA value is the header
//! parameter and outside it is the value from before the loop. A landing pad
//! is entered by the unwinder, which supplies no block arguments; when two of
//! the pad's incoming edges disagree about a scalar the pad reads, the pad
//! needs a parameter no unwind edge can feed, and the body is refused
//! (`[TCG-EH-CLEANUP-LOOP]` from `patch_loop_header_edge`, or the SSA gate's
//! "passes 0 arg(s) to a block with 1 param(s)"). Two shapes of ordinary Rust
//! reach it:
//!
//! * rustc's `drop_in_place::<[T]>` glue (every `Vec<T>` whose element has
//!   drop glue): an element drop that unwinds enters a NESTED cleanup loop
//!   that drops the rest of the slice, so the pad is itself a loop header and
//!   its index and length are header parameters;
//! * a value with drop glue live across a loop whose body can unwind (a
//!   `Drop` guard, a `Vec` being filled): the guard's cleanup pad is entered
//!   from inside the loop (where a carried scalar is the header parameter) and
//!   from outside it (where it is the pre-loop value).
//!
//! On Linux AArch64 every scalar live into any landing pad already has a frame
//! home (`cleanup_scalar_homes_enabled`). This module runs on AArch64 Darwin
//! only ([`target`]), the one target whose native runs measure it; every other
//! target keeps its established EH lowering and its refusals. On Darwin it
//! homes exactly the locals of those two shapes: the carried scalars of a
//! landing pad that is a loop header, and a loop's carried scalars that are
//! live into a landing pad with incoming edges both inside and outside that
//! loop. A pad that needs no SSA input (`cleanup_blocks_without_ssa_inputs`:
//! its chain only drops values that need no drop and then resumes) takes no
//! block parameters, so it lowered before and gets no homes. A body with
//! neither shape is unchanged. A carried local without a single-scalar home
//! shape (`cleanup_scalar_home_shape`) is not homed, so its refusal still
//! names it.
//!
//! Liveness here is the access-use model (`compute_live_in_with(.., true)`):
//! a local read only to reach a place (an `Index` local, the base of a deref
//! in a destination) counts as live, as in the loop-completeness gate.
//!
//! A homed local is read and written through its cell everywhere in the body
//! (`compute_scalar_cell_locals`' representation), so every edge into the pad
//! observes the one current value.

use super::*;

/// The targets this module changes: AArch64 Darwin. AArch64 Linux homes every
/// cleanup-live scalar already (`cleanup_scalar_homes_enabled`), and no other
/// target has run these shapes, so each keeps its refusals.
fn target(ctx: &MirLoweringCtx<'_>) -> bool {
    ctx.tcx.sess.target.arch.desc() == "aarch64" && ctx.tcx.sess.target.is_like_darwin
}

/// Whether this module may change the body being lowered: the target is
/// [`target`] and the body lowers EH with at least one landing pad.
fn active_pads(ctx: &MirLoweringCtx<'_>) -> bool {
    target(ctx) && ctx.eh_active && !ctx.eh_landing_pad_blocks.is_empty()
}

/// Each block's live-in locals under the access-use model.
fn access_live_in(body: &Body<'_>) -> Vec<HashSet<Local>> {
    let successors: Vec<Vec<mir::BasicBlock>> = body
        .basic_blocks
        .iter()
        .map(|data| terminator_successors(&data.terminator().kind))
        .collect();
    compute_live_in_with(body, &successors, true)
}

/// The extra scalar cells for `body`'s cleanup-loop shapes on AArch64 Darwin
/// (none elsewhere).
pub(super) fn loop_carried_pad_homes<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    predecessors: &[Vec<mir::BasicBlock>],
    memory_backed_only: &HashSet<Local>,
    scalar_cell_only: &HashSet<Local>,
) -> HashSet<Local> {
    let mut homes = HashSet::new();
    if !active_pads(ctx) {
        return homes;
    }
    let mut excluded = memory_backed_only.clone();
    excluded.extend(scalar_cell_only.iter().copied());
    let params = compute_loop_header_params(ctx, body, predecessors, &excluded);
    let mut headers: Vec<(mir::BasicBlock, &[Local])> = params
        .headers
        .iter()
        .filter(|(_, carried)| !carried.is_empty())
        .map(|(header, carried)| (*header, carried.as_slice()))
        .collect();
    if headers.is_empty() {
        return homes;
    }
    headers.sort_by_key(|(header, _)| header.index());
    let live_in = access_live_in(body);
    let dominators = body.basic_blocks.dominators();
    // A pad whose chain needs no SSA input takes no block parameters, so it
    // already lowers; homing its loop's scalars would only move them to memory.
    let without_ssa_inputs = cleanup_blocks_without_ssa_inputs(ctx, body, scalar_cell_only);
    let mut pads: Vec<mir::BasicBlock> = ctx
        .eh_landing_pad_blocks
        .iter()
        .copied()
        .filter(|pad| !without_ssa_inputs.contains(pad))
        .collect();
    pads.sort_by_key(|pad| pad.index());
    let add = |carried: &mut dyn Iterator<Item = Local>, homes: &mut HashSet<Local>| {
        let carried: Vec<Local> = carried.collect();
        if !carried.is_empty()
            && carried
                .iter()
                .all(|local| cleanup_scalar_home_shape(ctx, body, *local))
        {
            homes.extend(carried);
        }
    };
    for pad in pads {
        // The pad is itself a loop header (the slice glue's nested cleanup).
        add(&mut params.for_block(pad).iter().copied(), &mut homes);
        // The pad is entered both from inside and from outside a loop whose
        // carried scalars it reads.
        let pad_preds: Vec<mir::BasicBlock> = predecessors[pad.index()]
            .iter()
            .copied()
            .filter(|pred| dominators.is_reachable(*pred))
            .collect();
        for (header, carried) in &headers {
            let inside = pad_preds
                .iter()
                .filter(|pred| dominators.dominates(*header, **pred))
                .count();
            if inside == 0 || inside == pad_preds.len() {
                continue;
            }
            add(
                &mut carried
                    .iter()
                    .copied()
                    .filter(|local| live_in[pad.index()].contains(local)),
                &mut homes,
            );
        }
    }
    homes
}

/// The access-use live-in locals of each landing pad of `body` on AArch64
/// Darwin (empty elsewhere, and when `body` lowers no EH).
pub(super) fn landing_pad_live_in<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
) -> HashMap<mir::BasicBlock, HashSet<Local>> {
    if !active_pads(ctx) {
        return HashMap::new();
    }
    let live_in = access_live_in(body);
    ctx.eh_landing_pad_blocks
        .iter()
        .map(|pad| (*pad, live_in[pad.index()].clone()))
        .collect()
}

/// A landing pad's forward-join scalar parameters, kept only for the locals
/// the pad reads (AArch64 Darwin; elsewhere `landing_pad_live_in` is empty
/// and every block keeps its parameters).
///
/// The pad's head is the unwind destination of an `Invoke`, and an unwind edge
/// supplies no block argument, so any parameter left on a landing pad fails the
/// SSA gate ("passes 0 arg(s)"); dropping one can therefore change only a body
/// that is refused today. A join parameter exists because two predecessors
/// bind a local to different values. The parameter is dropped only for a local
/// that is dead into the pad under the access-use model (no path from the pad
/// reads it, or uses it to reach a place, before redefining it), so no read of
/// it on those paths remains. The safety rests on that liveness, not on a
/// later refusal: an unbound read of an entry-argument local would fall back
/// to the incoming parameter (`value_for_scalar_binding`), not fail closed.
/// Every other block keeps its parameters unchanged.
pub(super) fn retain_live_pad_params(
    landing_pad_live_in: &HashMap<mir::BasicBlock, HashSet<Local>>,
    bb: mir::BasicBlock,
    mut params: Vec<ScalarBlockParam>,
) -> Vec<ScalarBlockParam> {
    if let Some(live) = landing_pad_live_in.get(&bb) {
        params.retain(|param| live.contains(&param.local));
    }
    params
}
