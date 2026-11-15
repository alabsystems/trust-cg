//! Remove unused forward-join parameters from unwinder-only pad heads.
use std::collections::HashSet;
use trust_cg_verify::ssa_loop_complete::{non_terminator_value_uses, terminator_edges};
use trust_ir::{Function, Inst};

pub(super) fn remove_unused_unwind_params(function: &mut Function) {
    if !function.blocks.iter().any(|block| {
        !block.params.is_empty()
            && block.id != function.entry
            && matches!(
                block.body.first().map(|n| &n.inst),
                Some(Inst::LandingPad { .. })
            )
    }) {
        return;
    }
    // The bridge currently emits no instruction certificates here. Preserve
    // all definitions if a future producer adds proof metadata that could
    // refer to values outside the ordinary operand lists.
    if function
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .any(|n| !n.proofs.is_empty() || n.proof_context.is_some())
    {
        return;
    }
    let mut uses = HashSet::new();
    let mut normal_targets = HashSet::new();
    for block in &function.blocks {
        for node in &block.body {
            uses.extend(non_terminator_value_uses(&node.inst));
        }
        let edges = terminator_edges(block);
        for (_, args) in &edges {
            uses.extend(args.iter().copied());
        }
        if let Some(Inst::Invoke { normal_dest, .. }) = block.body.last().map(|n| &n.inst) {
            normal_targets.insert(*normal_dest);
        } else {
            normal_targets.extend(edges.into_iter().map(|(target, _)| target));
        }
    }
    for block in &mut function.blocks {
        if block.id != function.entry
            && !normal_targets.contains(&block.id)
            && matches!(
                block.body.first().map(|n| &n.inst),
                Some(Inst::LandingPad { .. })
            )
            && block.params.iter().all(|(value, _)| !uses.contains(value))
        {
            block.params.clear();
        }
    }
}
