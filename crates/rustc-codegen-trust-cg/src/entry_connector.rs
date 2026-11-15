// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Move an entry operation intact before inserting a fresh assembly connector.

use rustc_middle::mir::{self, Body, Statement};

/// Move the complete old entry before inserting an assembly-only connector.
/// Existing edges are retargeted in place, preserving every operation payload.
pub(super) fn move_start<'tcx>(body: &mut Body<'tcx>, assemble: Statement<'tcx>) {
    let blocks = body.basic_blocks_mut();
    let entry = blocks[mir::START_BLOCK].clone();
    let moved = blocks.push(entry);
    for data in blocks.iter_mut() {
        if let Some(terminator) = data.terminator.as_mut() {
            terminator.successors_mut(|target| {
                if *target == mir::START_BLOCK {
                    *target = moved;
                }
            });
        }
    }
    let source_info = blocks[mir::START_BLOCK].terminator().source_info;
    let terminator = crate::synthetic_terminator::new(source_info, crate::mir_goto::new(moved));
    // Debug records of the old statements belong to the moved block too.
    // Construct the connector afresh instead of retaining the old block's shell.
    let mut connector = mir::BasicBlockData::new(Some(terminator), false);
    connector.statements.push(assemble);
    blocks[mir::START_BLOCK] = connector;
}
