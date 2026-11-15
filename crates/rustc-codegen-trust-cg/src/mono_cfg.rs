//! Use the same monomorphized reachability as rustc's item collector.
//!
//! An associated constant or runtime-check switch can make a generic MIR arm
//! dead for one instance. The collector intentionally omits that arm's callees;
//! retaining its calls in an object creates references no crate will define.
use std::borrow::Cow;

use rustc_middle::mir::{self, Body, TerminatorKind};
use rustc_middle::ty::{Instance, TyCtxt};

pub(super) fn for_instance<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &'a Body<'tcx>,
) -> Cow<'a, Body<'tcx>> {
    let live = mir::traversal::mono_reachable_as_bitset(body, tcx, instance);
    let mut changes = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if !live.contains(bb) {
            if !data.is_empty_unreachable() {
                changes.push((bb, None));
            }
            continue;
        }
        if matches!(data.terminator().kind, TerminatorKind::SwitchInt { .. }) {
            // mono_successors evaluates only the exact constant/runtime-check
            // cases rustc recognizes. A dynamic switch retains all its edges.
            let mut successors = data.mono_successors(tcx, instance);
            if let Some(target) = successors.next() {
                if successors.next().is_none() {
                    changes.push((bb, Some(target)));
                }
            }
        }
    }
    if changes.is_empty() {
        return Cow::Borrowed(body);
    }
    let mut normalized = body.clone();
    for (bb, target) in changes {
        let data = &mut normalized.basic_blocks_mut()[bb];
        data.terminator_mut().kind = match target {
            Some(target) => crate::mir_goto::new(target),
            None => {
                data.statements.clear();
                TerminatorKind::Unreachable
            }
        };
    }
    Cow::Owned(normalized)
}
