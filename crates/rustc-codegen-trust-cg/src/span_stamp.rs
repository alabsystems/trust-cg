//! Attach one MIR statement's (or terminator's) source span to the trust-ir
//! instructions it was lowered to (ledger L06-P7, DWARF line tables).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! The bridge lowers a MIR basic block into the open `block` plus finished
//! blocks it files in `ctx.extra_blocks` (a statement that splits control flow
//! moves the open block there and continues in a fresh one: every
//! `std::mem::replace(block, ..)` in the lowering is followed by
//! `ctx.extra_blocks.push(finished)`). A [`Cursor`] taken before the statement
//! and [`Cursor::stamp`] after it therefore reach every instruction the
//! statement appended: the open block's new tail, or, when the block was
//! replaced, the original block's new tail (found by its id among the newly
//! filed blocks) and every other new block whole. Only instructions without a
//! span are stamped, so a span set by an earlier statement is never moved.
//!
//! Pure trust-ir bookkeeping: spans are claim-style metadata with no
//! operational meaning, and the bridge stamps them only when debug lines are
//! requested, so the default lane's trust-ir is unchanged.
#![allow(dead_code)]

use trust_ir::{Block, BlockId, InstrNode, SourceSpan};

/// Where lowering stood before one MIR statement or terminator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Cursor {
    block: BlockId,
    body_len: usize,
    extra_len: usize,
}

impl Cursor {
    /// The position after everything `block` and `extra` hold now.
    pub(crate) fn at(block: &Block, extra: &[Block]) -> Self {
        Self {
            block: block.id,
            body_len: block.body.len(),
            extra_len: extra.len(),
        }
    }

    /// Give `span` to every instruction appended since this cursor was taken
    /// that has none. Returns how many instructions were stamped.
    pub(crate) fn stamp(self, span: SourceSpan, block: &mut Block, extra: &mut [Block]) -> usize {
        let mut stamped = 0;
        let mut fill = |nodes: &mut [InstrNode]| {
            for node in nodes {
                if node.span.is_none() {
                    node.span = Some(span);
                    stamped += 1;
                }
            }
        };
        let new_extra = extra.get_mut(self.extra_len..).unwrap_or_default();
        if block.id == self.block {
            let start = self.body_len.min(block.body.len());
            fill(&mut block.body[start..]);
            for filed in new_extra {
                fill(&mut filed.body);
            }
        } else {
            for filed in new_extra {
                let start = if filed.id == self.block {
                    self.body_len.min(filed.body.len())
                } else {
                    0
                };
                fill(&mut filed.body[start..]);
            }
            fill(&mut block.body);
        }
        stamped
    }
}
