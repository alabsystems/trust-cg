//! Span stamping for DWARF line tables (ledger L06-P7): one MIR statement's
//! span reaches exactly the trust-ir instructions it was lowered to.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
#[path = "../src/span_stamp.rs"]
mod span_stamp;

use span_stamp::Cursor;
use trust_ir::{Block, BlockId, Inst, InstrNode, SourceSpan};

fn span(line: u32) -> SourceSpan {
    SourceSpan {
        file: 0,
        line,
        col: 1,
    }
}

fn nop() -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![] })
}

fn lines(block: &Block) -> Vec<Option<u32>> {
    block
        .body
        .iter()
        .map(|node| node.span.map(|span| span.line))
        .collect()
}

#[test]
fn appended_instructions_of_the_open_block_are_stamped_and_earlier_ones_kept() {
    let mut block = Block::new(BlockId::new(0));
    block.body.push(nop().with_span(span(1)));
    block.body.push(nop());
    let mut extra: Vec<Block> = Vec::new();
    let cursor = Cursor::at(&block, &extra);
    block.body.push(nop());
    block.body.push(nop().with_span(span(9)));
    assert_eq!(cursor.stamp(span(4), &mut block, &mut extra), 1);
    // The unspanned instruction before the cursor stays unspanned, and a span
    // set by the lowering itself is never moved.
    assert_eq!(lines(&block), [Some(1), None, Some(4), Some(9)]);
}

#[test]
fn a_split_statement_stamps_the_finished_tail_new_blocks_and_the_open_block() {
    let mut block = Block::new(BlockId::new(0));
    block.body.push(nop().with_span(span(1)));
    let mut extra = vec![Block::new(BlockId::new(7))];
    extra[0].body.push(nop());
    let cursor = Cursor::at(&block, &extra);
    // The statement appends to block 0, files it, opens block 2 and files a
    // whole block 1 in between, as a control-flow-splitting lowering does.
    block.body.push(nop());
    let mut side = Block::new(BlockId::new(1));
    side.body.push(nop());
    let finished = std::mem::replace(&mut block, Block::new(BlockId::new(2)));
    extra.push(finished);
    extra.push(side);
    block.body.push(nop());
    assert_eq!(cursor.stamp(span(5), &mut block, &mut extra), 3);
    assert_eq!(lines(&extra[0]), [None], "a block filed before the cursor");
    assert_eq!(lines(&extra[1]), [Some(1), Some(5)]);
    assert_eq!(lines(&extra[2]), [Some(5)]);
    assert_eq!(lines(&block), [Some(5)]);
}

#[test]
fn a_statement_that_appends_nothing_stamps_nothing() {
    let mut block = Block::new(BlockId::new(0));
    block.body.push(nop());
    let mut extra = Vec::new();
    let cursor = Cursor::at(&block, &extra);
    assert_eq!(cursor.stamp(span(3), &mut block, &mut extra), 0);
    assert_eq!(lines(&block), [None]);
}
