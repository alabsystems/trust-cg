// trust-cg-codegen/jit_refusal_layer_tests.rs - every retyped JIT block-profile
// splice refusal is raised as JitError::BlockProfileSplice
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Trust-core architecture AD-8 / E0.3, JIT half: the AArch64 block-profile
//! splicers (`splice_block_trampolines_aarch64` and its timing twin) used to
//! raise their refusals as `JitError::Pipeline(PipelineError::Encoding(..))`,
//! which the rustc bridge would file as a machine-code encoding failure. Each
//! is driven here by a real input and asserted as `JitError::BlockProfileSplice`
//! (`TCG-JIT-EXEC`) with the site's own message, for both splicers.

use super::*;
use trust_cg_ir::function::{JumpTableData, MachFunction, Signature};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::X0;

type Splice =
    fn(&MachFunction, &[u8], &HashMap<BlockId, u32>, &mut [Fixup]) -> Result<(), JitError>;

fn plain(
    func: &MachFunction,
    body: &[u8],
    offsets: &HashMap<BlockId, u32>,
    fixups: &mut [Fixup],
) -> Result<(), JitError> {
    splice_block_trampolines_aarch64(func, body, offsets, fixups).map(|_| ())
}

fn timing(
    func: &MachFunction,
    body: &[u8],
    offsets: &HashMap<BlockId, u32>,
    fixups: &mut [Fixup],
) -> Result<(), JitError> {
    splice_block_trampolines_with_timing_aarch64(func, body, offsets, fixups).map(|_| ())
}

const SPLICERS: [(&str, Splice); 2] = [("block-splice", plain), ("timing-block-splice", timing)];

fn splice_refusal(
    splice: Splice,
    func: &MachFunction,
    body: &[u8],
    offsets: &HashMap<BlockId, u32>,
) -> String {
    match splice(func, body, offsets, &mut []) {
        Err(JitError::BlockProfileSplice(message)) => message,
        Err(other) => panic!("expected JitError::BlockProfileSplice, got {other:?}"),
        Ok(()) => panic!("expected a block-profile splice refusal"),
    }
}

/// A function whose block `i` holds `blocks[i]`, laid out in block order.
fn function(blocks: Vec<Vec<MachInst>>) -> MachFunction {
    let mut func = MachFunction::new("spliced".to_string(), Signature::new(vec![], vec![]));
    let mut ids = vec![func.entry];
    for _ in 1..blocks.len() {
        ids.push(func.create_block());
    }
    for (block, insts) in ids.iter().zip(blocks) {
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(*block, id);
        }
    }
    func.block_order = ids;
    func
}

fn ret() -> MachInst {
    MachInst::new(AArch64Opcode::Ret, vec![])
}

fn offsets(pairs: &[(u32, u32)]) -> HashMap<BlockId, u32> {
    pairs
        .iter()
        .map(|&(block, offset)| (BlockId(block), offset))
        .collect()
}

fn words(words: &[(usize, u32)], len: usize) -> Vec<u8> {
    let mut body = vec![0u8; len];
    for &(at, word) in words {
        body[at..at + 4].copy_from_slice(&word.to_le_bytes());
    }
    body
}

fn adr_to_jump_table(index: u32) -> MachInst {
    MachInst::new(
        AArch64Opcode::Adr,
        vec![MachOperand::PReg(X0), MachOperand::JumpTableIndex(index)],
    )
}

#[test]
fn a_missing_block_offset_is_block_profile_splice() {
    let func = function(vec![vec![ret()]]);
    for (prefix, splice) in SPLICERS {
        let message = splice_refusal(splice, &func, &[0; 4], &HashMap::new());
        assert!(
            message.starts_with(&format!("{prefix}: block BlockId(0) missing byte offset")),
            "{message}"
        );
    }
}

#[test]
fn an_empty_block_order_is_block_profile_splice() {
    let mut func = function(vec![vec![ret()]]);
    func.block_order.clear();
    for (prefix, splice) in SPLICERS {
        assert_eq!(
            splice_refusal(splice, &func, &[], &HashMap::new()),
            format!("{prefix}: empty block_order")
        );
    }
}

#[test]
fn a_body_shorter_than_its_instructions_is_block_profile_splice() {
    let func = function(vec![vec![ret(), ret()]]);
    for (prefix, splice) in SPLICERS {
        assert_eq!(
            splice_refusal(splice, &func, &[0; 4], &offsets(&[(0, 0)])),
            format!("{prefix}: computed insts_end_in_body 8 exceeds body_bytes.len() 4")
        );
    }
}

#[test]
fn an_unexplained_tail_is_block_profile_splice() {
    let func = function(vec![vec![ret()]]);
    for (prefix, splice) in SPLICERS {
        let message = splice_refusal(splice, &func, &[0; 8], &offsets(&[(0, 0)]));
        assert!(
            message.starts_with(&format!(
                "{prefix}: body_bytes has 4 bytes of unexpected tail"
            )),
            "{message}"
        );
    }
}

#[test]
fn an_adr_to_a_missing_jump_table_is_block_profile_splice() {
    let func = function(vec![vec![adr_to_jump_table(3), ret()]]);
    for (prefix, splice) in SPLICERS {
        assert_eq!(
            splice_refusal(splice, &func, &[0; 8], &offsets(&[(0, 0)])),
            format!("{prefix}: Adr references jump table index 3 but func has only 0 tables")
        );
    }
}

fn branch_to_entry() -> MachInst {
    MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(0))])
}

#[test]
fn a_branch_before_the_function_is_block_profile_splice() {
    let func = function(vec![vec![branch_to_entry()]]);
    // `B #-4` at byte 0.
    let body = words(&[(0, 0x17FF_FFFF)], 4);
    for (prefix, splice) in SPLICERS {
        assert_eq!(
            splice_refusal(splice, &func, &body, &offsets(&[(0, 0)])),
            format!("{prefix}: negative original branch target -4")
        );
    }
}

#[test]
fn a_branch_into_the_middle_of_a_block_is_block_profile_splice() {
    let func = function(vec![vec![branch_to_entry()]]);
    // `B #+8` at byte 0: byte 8 starts no block.
    let body = words(&[(0, 0x1400_0002)], 4);
    for (prefix, splice) in SPLICERS {
        let message = splice_refusal(splice, &func, &body, &offsets(&[(0, 0)]));
        assert!(
            message.starts_with(&format!(
                "{prefix}: branch at original byte 0 targets 8 which is not a block start"
            )),
            "{message}"
        );
    }
}

#[test]
fn a_branch_pushed_out_of_range_by_trampolines_is_block_profile_splice() {
    // `TBZ` reaches +/-8192 instructions. It targets block 2 with the maximum
    // positive displacement; the trampoline spliced before block 1 pushes it out.
    let tbz = MachInst::new(AArch64Opcode::Tbz, vec![MachOperand::Block(BlockId(2))]);
    let func = function(vec![vec![tbz], vec![ret()], vec![ret()]]);
    let tbz_word = 0x3600_0000u32 | (8191 << 5);
    let body = words(&[(0, tbz_word)], 32_768);
    for (prefix, splice) in SPLICERS {
        let message = splice_refusal(
            splice,
            &func,
            &body,
            &offsets(&[(0, 0), (1, 4), (2, 32_764)]),
        );
        assert!(
            message.starts_with(&format!("{prefix}: branch displacement")),
            "{message}"
        );
        assert!(message.contains("out of 14-bit range after"), "{message}");
    }
}

#[test]
fn an_adr_past_the_spliced_output_is_block_profile_splice() {
    // Block 0 claims 101 instructions but owns only the 8 bytes before block 1,
    // so its trailing ADR lies past everything the splice copies.
    let mut block0: Vec<MachInst> = (0..100)
        .map(|_| {
            MachInst::new(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(X0), MachOperand::Imm(0)],
            )
        })
        .collect();
    block0.push(adr_to_jump_table(0));
    let mut func = function(vec![block0, vec![]]);
    func.jump_tables.push(JumpTableData {
        min_val: 0,
        targets: vec![BlockId(0)],
    });
    for (prefix, splice) in SPLICERS {
        let message = splice_refusal(splice, &func, &[0; 8], &offsets(&[(0, 0), (1, 8)]));
        assert!(
            message.starts_with(&format!("{prefix}: ADR site at post-splice offset")),
            "{message}"
        );
    }
}

#[test]
fn an_adr_too_far_from_its_regenerated_table_is_block_profile_splice() {
    let mut func = function(vec![vec![adr_to_jump_table(0), ret()], vec![ret()]]);
    func.jump_tables.push(JumpTableData {
        min_val: 0,
        targets: vec![BlockId(0)],
    });
    let far = 1_100_000u32;
    let body = vec![0u8; far as usize + 4];
    for (prefix, splice) in SPLICERS {
        let message = splice_refusal(splice, &func, &body, &offsets(&[(0, 0), (1, far)]));
        assert!(
            message.starts_with(&format!("{prefix}: ADR->jump-table offset")),
            "{message}"
        );
        assert!(message.ends_with("does not fit in imm21"), "{message}");
    }
}
