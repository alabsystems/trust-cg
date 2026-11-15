// trust-cg-codegen/relax.rs - Branch relaxation pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 branch relaxation pass.
//!
//! After block layout, computes block offsets (each non-pseudo instruction is
//! 4 bytes) and relaxes branches whose targets are out of range. Uses a
//! fixed-point algorithm: relaxation may insert instructions that push other
//! branches out of range, so we iterate until stable.
//!
//! Relaxation patterns (ARM ARM):
//! - `B.cond far` -> `B.cond_inv +8 ; B far`
//! - `CBZ Rt, far` -> `CBNZ Rt, +8 ; B far`
//! - `CBNZ Rt, far` -> `CBZ Rt, +8 ; B far`
//! - `TBZ Rt, #bit, far` -> `TBNZ Rt, #bit, +8 ; B far`
//! - `TBNZ Rt, #bit, far` -> `TBZ Rt, #bit, +8 ; B far`
//!
//! Reference: LLVM `BranchRelaxation.cpp`.

use thiserror::Error;

use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from branch relaxation.
#[derive(Debug, Error)]
pub enum RelaxError {
    /// The public function boundary received malformed block/instruction/CFG
    /// arenas. This is checked before any indexing or mutation.
    #[error("malformed branch-relaxation input: {0}")]
    MalformedFunction(String),
    /// Unconditional branch target is beyond the +/- 128 MB range.
    ///
    /// This means the function has more than ~32 million instructions. The
    /// fix would be an indirect branch via IP0 (X16), which is not yet
    /// implemented.
    #[error(
        "unconditional B to block {target_block:?} is out of the +/-128 MB range \
         in function '{func_name}'"
    )]
    BranchOutOfRange {
        target_block: BlockId,
        func_name: String,
    },
}

// ---------------------------------------------------------------------------
// Constants: branch ranges in bytes
// ---------------------------------------------------------------------------

/// B (unconditional): 26-bit signed offset * 4 = +/- 128 MB.
const B_MAX_RANGE: i64 = (1 << 27) - 4; // +134,217,724
const B_MIN_RANGE: i64 = -(1 << 27); // -134,217,728

/// B.cond / CBZ / CBNZ: 19-bit signed offset * 4 = +/- 1 MB.
const BCOND_MAX_RANGE: i64 = (1 << 20) - 4; // +1,048,572
const BCOND_MIN_RANGE: i64 = -(1 << 20); // -1,048,576

/// TBZ / TBNZ: 14-bit signed offset * 4 = +/- 32 KB.
const TBZ_MAX_RANGE: i64 = (1 << 15) - 4; // +32,764
const TBZ_MIN_RANGE: i64 = -(1 << 15); // -32,768

// ---------------------------------------------------------------------------
// BlockInfo
// ---------------------------------------------------------------------------

/// Per-block offset and size information for offset computation.
#[derive(Debug, Clone, Copy)]
struct BlockInfo {
    /// Byte offset from the start of the function.
    offset: u32,
    /// Size of the block in bytes (number of non-pseudo instructions * 4).
    /// Only the unit tests read it; relaxation needs only `offset`.
    #[cfg_attr(not(test), allow(dead_code))]
    size: u32,
}

// ---------------------------------------------------------------------------
// Public types and entry point
// ---------------------------------------------------------------------------

/// Result of branch relaxation: the final instruction sequence with resolved
/// block offsets.
#[derive(Debug, Clone)]
pub struct RelaxedCode {
    /// Final instruction sequence in layout order. Branch operands that were
    /// `MachOperand::Block(id)` are replaced with `MachOperand::Imm(offset)`
    /// where offset is the signed displacement in instruction units (bytes / 4).
    pub instructions: Vec<MachInst>,
    /// Byte offset from function start for each BlockId.
    pub block_offsets: Vec<u32>,
}

// ---------------------------------------------------------------------------
// BranchRelaxation pass struct
// ---------------------------------------------------------------------------

/// Branch relaxation pass for the compilation pipeline.
///
/// This pass runs after block layout and frame lowering. It computes byte
/// offsets for each basic block, detects branches whose targets exceed their
/// encoding range, and rewrites them into longer instruction sequences
/// (inverting the condition and inserting an unconditional branch trampoline).
///
/// The pass uses a fixed-point algorithm because relaxation can insert
/// instructions that push other branches out of range.
///
/// # Example
///
/// ```text
/// let pass = BranchRelaxation::new();
/// let relaxed = pass.run(&mut func)?;
/// // relaxed.instructions contains the final instruction sequence
/// // with all branch offsets resolved to immediates
/// ```
pub struct BranchRelaxation;

impl BranchRelaxation {
    /// Create a new branch relaxation pass.
    pub fn new() -> Self {
        Self
    }

    /// Run branch relaxation on a function.
    ///
    /// This is the primary entry point for the pass. It delegates to
    /// [`relax_branches`] which implements the fixed-point algorithm.
    pub fn run(&self, func: &mut MachFunction) -> Result<RelaxedCode, RelaxError> {
        relax_branches(func)
    }

    /// Check if any branches in the function are out of range without
    /// modifying the function. Useful for diagnostics.
    pub fn has_out_of_range_branches(&self, func: &MachFunction) -> Result<bool, RelaxError> {
        validate_relax_input(func)?;
        let infos = compute_block_offsets(func);

        for &block_id in &func.block_order {
            let block_offset = infos[block_id.0 as usize].offset;
            let blk = func.block(block_id);

            let mut inst_byte_offset = block_offset;
            for &inst_id in &blk.insts {
                let inst = func.inst(inst_id);
                if inst.is_pseudo() {
                    continue;
                }

                if is_branch_with_block_target(inst)
                    && let Some(target_bid) = get_branch_target_block(inst)
                {
                    let target_offset = infos[target_bid.0 as usize].offset;
                    let displacement = target_offset as i64 - inst_byte_offset as i64;

                    if !in_range(inst.opcode, displacement) {
                        return Ok(true);
                    }
                }

                inst_byte_offset += 4;
            }
        }

        Ok(false)
    }
}

impl Default for BranchRelaxation {
    fn default() -> Self {
        Self::new()
    }
}

/// Run branch relaxation on a function after block layout.
///
/// This is a fixed-point algorithm:
/// 1. Compute block offsets.
/// 2. Scan all branch instructions for out-of-range targets.
/// 3. Relax any out-of-range branches by splitting them.
/// 4. Repeat until no changes.
/// 5. Build the final instruction sequence with resolved offsets.
pub fn relax_branches(func: &mut MachFunction) -> Result<RelaxedCode, RelaxError> {
    validate_relax_input(func)?;
    // Fixed-point relaxation loop.
    let max_iterations = 32; // safety bound
    for _ in 0..max_iterations {
        let infos = compute_block_offsets(func);
        let mut changed = false;

        // Scan blocks in layout order.
        for layout_idx in 0..func.block_order.len() {
            let block_id = func.block_order[layout_idx];
            let block_offset = infos[block_id.0 as usize].offset;

            let blk = func.block(block_id);
            let inst_ids: Vec<InstId> = blk.insts.clone();

            let mut inst_byte_offset = block_offset;
            for (inst_pos, &inst_id) in inst_ids.iter().enumerate() {
                let inst = func.inst(inst_id);
                if inst.is_pseudo() {
                    continue;
                }

                if is_branch_with_block_target(inst)
                    && let Some(target_bid) = get_branch_target_block(inst)
                {
                    let target_offset = infos[target_bid.0 as usize].offset;
                    let displacement = target_offset as i64 - inst_byte_offset as i64;

                    if !in_range(inst.opcode, displacement) {
                        relax_one_branch(func, block_id, inst_pos)?;
                        changed = true;
                        break; // restart scan for this block
                    }
                }

                inst_byte_offset += 4;
            }
        }

        if !changed {
            break;
        }
    }

    // Build the final instruction sequence with resolved offsets.
    Ok(build_final_code(func))
}

fn validate_relax_input(func: &MachFunction) -> Result<(), RelaxError> {
    crate::pipeline::validate_aarch64_mach_function_totality(func)
        .map_err(|error| RelaxError::MalformedFunction(error.to_string()))
}

// ---------------------------------------------------------------------------
// Offset computation
// ---------------------------------------------------------------------------

/// Compute byte offsets for all blocks based on the current layout order.
/// Each non-pseudo instruction is 4 bytes.
fn compute_block_offsets(func: &MachFunction) -> Vec<BlockInfo> {
    let mut infos = vec![BlockInfo { offset: 0, size: 0 }; func.blocks.len()];

    let mut offset: u32 = 0;
    for &block_id in &func.block_order {
        let blk = func.block(block_id);
        let size = block_code_size(func, blk);
        infos[block_id.0 as usize] = BlockInfo { offset, size };
        offset += size;
    }

    infos
}

/// Compute the code size of a block in bytes (non-pseudo instructions * 4).
fn block_code_size(func: &MachFunction, blk: &trust_cg_ir::MachBlock) -> u32 {
    let mut count = 0u32;
    for &inst_id in &blk.insts {
        let inst = func.inst(inst_id);
        if !inst.is_pseudo() {
            count += 1;
        }
    }
    count * 4
}

// ---------------------------------------------------------------------------
// Range checking
// ---------------------------------------------------------------------------

/// Returns (min_range, max_range) in bytes for the given branch opcode.
pub fn branch_range(opcode: AArch64Opcode) -> (i64, i64) {
    match opcode {
        AArch64Opcode::B | AArch64Opcode::TailCall => (B_MIN_RANGE, B_MAX_RANGE),
        AArch64Opcode::BCond => (BCOND_MIN_RANGE, BCOND_MAX_RANGE),
        AArch64Opcode::Cbz | AArch64Opcode::Cbnz => (BCOND_MIN_RANGE, BCOND_MAX_RANGE),
        AArch64Opcode::Tbz | AArch64Opcode::Tbnz => (TBZ_MIN_RANGE, TBZ_MAX_RANGE),
        _ => (i64::MIN, i64::MAX), // not a branch, always in range
    }
}

/// Check if the signed displacement (in bytes) is within the range for the
/// given branch opcode.
fn in_range(opcode: AArch64Opcode, displacement: i64) -> bool {
    let (min, max) = branch_range(opcode);
    displacement >= min && displacement <= max
}

// ---------------------------------------------------------------------------
// Branch inspection helpers
// ---------------------------------------------------------------------------

/// Returns true if the instruction is a branch with a Block operand target.
fn is_branch_with_block_target(inst: &MachInst) -> bool {
    if !inst.is_branch() {
        return false;
    }
    inst.operands
        .iter()
        .any(|op| matches!(op, MachOperand::Block(_)))
}

/// Extract the Block target from a branch instruction.
fn get_branch_target_block(inst: &MachInst) -> Option<BlockId> {
    for op in &inst.operands {
        if let MachOperand::Block(bid) = op {
            return Some(*bid);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Branch relaxation
// ---------------------------------------------------------------------------

/// Relax a single out-of-range branch at position `inst_pos` in the block.
///
/// The pattern is: invert the short-range conditional branch to skip over an
/// inserted unconditional B to the far target.
///
/// Before: `BCond far_target`
/// After:  `BCond_inv +8 ; B far_target`
///
/// The inverted conditional branches to the next instruction (+8 = skip the B).
fn relax_one_branch(
    func: &mut MachFunction,
    block_id: BlockId,
    inst_pos: usize,
) -> Result<(), RelaxError> {
    let blk = func.block(block_id);
    let inst_id = blk.insts[inst_pos];
    let inst = func.inst(inst_id).clone();

    let far_target = match get_branch_target_block(&inst) {
        Some(target) => target,
        None => return Ok(()),
    };

    match inst.opcode {
        AArch64Opcode::BCond => {
            // BCond has operands: [Imm(condition_code), Block(target)]
            // Invert condition, make short branch skip the next instruction.
            let cc_val = inst
                .operands
                .iter()
                .find_map(|op| {
                    if let MachOperand::Imm(v) = op {
                        Some(*v)
                    } else {
                        None
                    }
                })
                .unwrap_or(0);
            let inverted_cc = invert_cc(cc_val as u8);

            // Create inverted BCond that skips the next instruction.
            // The +8 offset will be resolved in the final code emission;
            // we use a sentinel block for now but actually we just need to
            // branch over 1 instruction. We'll create a new block with just
            // the B instruction, inserted right after this block in layout.
            //
            // Simpler approach: replace the BCond with BCond_inv(+8) and
            // insert a B far_target right after it in the same block.

            // Rewrite the BCond instruction in place: inverted condition, no
            // block target (the +8 is implicit -- it always jumps over the
            // next instruction).
            let inv_bcond = MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Imm(inverted_cc as i64), MachOperand::Imm(2)],
                // Imm(2) = +8 bytes = skip 2 instructions (but we encode as
                // offset in instruction units; the final pass resolves this).
                // Actually: +8 bytes / 4 = 2 instruction units forward.
                // But we just need to skip the *next* instruction (1 inst = 4 bytes).
                // imm19 field = 2 means +8 bytes. We store raw imm here.
            );

            let far_b = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(far_target)]);

            // Replace the original BCond with the inverted one and insert B
            // after it.
            let inv_id = func.push_inst(inv_bcond);
            let far_id = func.push_inst(far_b);

            let blk = func.block_mut(block_id);
            blk.insts[inst_pos] = inv_id;
            blk.insts.insert(inst_pos + 1, far_id);
        }

        AArch64Opcode::Cbz => {
            // CBZ Rt, far -> CBNZ Rt, +8 ; B far
            let mut inv_operands: Vec<MachOperand> = inst
                .operands
                .iter()
                .filter(|op| !matches!(op, MachOperand::Block(_)))
                .cloned()
                .collect();
            inv_operands.push(MachOperand::Imm(2)); // skip next inst

            let inv_inst = MachInst::new(AArch64Opcode::Cbnz, inv_operands);
            let far_b = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(far_target)]);

            let inv_id = func.push_inst(inv_inst);
            let far_id = func.push_inst(far_b);

            let blk = func.block_mut(block_id);
            blk.insts[inst_pos] = inv_id;
            blk.insts.insert(inst_pos + 1, far_id);
        }

        AArch64Opcode::Cbnz => {
            // CBNZ Rt, far -> CBZ Rt, +8 ; B far
            let mut inv_operands: Vec<MachOperand> = inst
                .operands
                .iter()
                .filter(|op| !matches!(op, MachOperand::Block(_)))
                .cloned()
                .collect();
            inv_operands.push(MachOperand::Imm(2));

            let inv_inst = MachInst::new(AArch64Opcode::Cbz, inv_operands);
            let far_b = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(far_target)]);

            let inv_id = func.push_inst(inv_inst);
            let far_id = func.push_inst(far_b);

            let blk = func.block_mut(block_id);
            blk.insts[inst_pos] = inv_id;
            blk.insts.insert(inst_pos + 1, far_id);
        }

        AArch64Opcode::Tbz => {
            // TBZ Rt, #bit, far -> TBNZ Rt, #bit, +8 ; B far
            let mut inv_operands: Vec<MachOperand> = inst
                .operands
                .iter()
                .filter(|op| !matches!(op, MachOperand::Block(_)))
                .cloned()
                .collect();
            inv_operands.push(MachOperand::Imm(2));

            let inv_inst = MachInst::new(AArch64Opcode::Tbnz, inv_operands);
            let far_b = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(far_target)]);

            let inv_id = func.push_inst(inv_inst);
            let far_id = func.push_inst(far_b);

            let blk = func.block_mut(block_id);
            blk.insts[inst_pos] = inv_id;
            blk.insts.insert(inst_pos + 1, far_id);
        }

        AArch64Opcode::Tbnz => {
            // TBNZ Rt, #bit, far -> TBZ Rt, #bit, +8 ; B far
            let mut inv_operands: Vec<MachOperand> = inst
                .operands
                .iter()
                .filter(|op| !matches!(op, MachOperand::Block(_)))
                .cloned()
                .collect();
            inv_operands.push(MachOperand::Imm(2));

            let inv_inst = MachInst::new(AArch64Opcode::Tbz, inv_operands);
            let far_b = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(far_target)]);

            let inv_id = func.push_inst(inv_inst);
            let far_id = func.push_inst(far_b);

            let blk = func.block_mut(block_id);
            blk.insts[inst_pos] = inv_id;
            blk.insts.insert(inst_pos + 1, far_id);
        }

        AArch64Opcode::B | AArch64Opcode::TailCall => {
            // Unconditional B out of range: >128MB of code in a single
            // function. This means ~32 million instructions — practically
            // unreachable, but we return an error instead of panicking.
            //
            // If this ever becomes reachable, the fix is to emit an
            // indirect branch via IP0 (X16): ADRP X16, target ; ADD X16,
            // X16, :lo12:target ; BR X16. This requires absolute address
            // materialization which is not yet implemented.
            return Err(RelaxError::BranchOutOfRange {
                target_block: far_target,
                func_name: func.name.clone(),
            });
        }

        _ => {}
    }

    Ok(())
}

/// Invert an AArch64 condition code (as a u8).
fn invert_cc(cc: u8) -> u8 {
    // AArch64 condition codes: inversion is just flipping bit 0.
    cc ^ 1
}

// ---------------------------------------------------------------------------
// Final code emission
// ---------------------------------------------------------------------------

/// Build the final instruction sequence with branch offsets resolved.
///
/// Walks blocks in layout order, emits instructions, and replaces
/// `MachOperand::Block(id)` operands with `MachOperand::Imm(offset)` where
/// offset is the signed displacement in instruction units (bytes / 4).
fn build_final_code(func: &MachFunction) -> RelaxedCode {
    let infos = compute_block_offsets(func);
    let mut instructions = Vec::new();
    let mut block_offsets = vec![0u32; func.blocks.len()];

    for &bid in &func.block_order {
        block_offsets[bid.0 as usize] = infos[bid.0 as usize].offset;
    }

    let mut current_offset: u32 = 0;
    for &block_id in &func.block_order {
        let blk = func.block(block_id);
        for &inst_id in &blk.insts {
            let inst = func.inst(inst_id);
            if inst.is_pseudo() {
                // Pseudo instructions are not emitted.
                continue;
            }

            // Resolve Block operands to immediate offsets.
            let mut resolved = inst.clone();
            for op in &mut resolved.operands {
                if let MachOperand::Block(target_bid) = op {
                    let target_offset = infos[target_bid.0 as usize].offset;
                    let displacement = (target_offset as i64 - current_offset as i64) / 4;
                    *op = MachOperand::Imm(displacement);
                }
            }

            instructions.push(resolved);
            current_offset += 4;
        }
    }

    RelaxedCode {
        instructions,
        block_offsets,
    }
}

// ---------------------------------------------------------------------------
// Block-structured relaxation: the production pipeline's pass
// ---------------------------------------------------------------------------
//
// `relax_branches` above serves the standalone `lower` path: it rewrites a far
// branch into an intra-block `cond_inv +2 ; B far` pair and returns a flat,
// already-resolved instruction list. The production pipeline cannot take that
// shape. Its final-stream authority reconstructs the CFG from the resolved
// stream and admits exactly one intra-block immediate branch (the
// `B.cond +2 ; BRK` guard skip); the raw JIT's block-profile splice requires
// every resolved intra-function branch to land on a block start; and the
// reaching-definition and frame dataflow nets walk each block linearly. So the
// pipeline relaxes while branch targets are still symbolic, and every branch
// it writes keeps a `Block` target. With `T` the far target, `X` the branch's
// block and `N` the block laid out after `X`:
//
// 1. FALLTHROUGH. `X: … bcc T` with nothing but pseudos and `AlignNop`
//    padding after it (it falls into `N`) becomes `X: … bcc_inv N ; B T`.
//    That encodes as `bcc_inv +8 ; B T`, the standard relaxation, word for
//    word. The edge set of `X` is unchanged ({N, T}).
// 2. SWAP. `X: … bcc T ; B F` with `F` inside the conditional's range becomes
//    `X: … bcc_inv F ; B T`. No instruction is added; the edge set is
//    unchanged ({F, T}).
// 3. SPLIT. Otherwise (the tail after the conditional is direct branches
//    only, e.g. `B F` with `F` out of range too), the tail moves into a new
//    block `Z` laid out immediately after `X`, and `X` ends
//    `bcc_inv Z ; B T`. `Z` sits exactly where the tail was, so the tail's
//    own fallthrough still reaches `N`. Successor/predecessor metadata is
//    rebuilt from the branch operands with the canonical
//    `pipeline::derive_ir_cfg_edges_from_branch_operands`.
// 4. ISLAND. An ordinary tail ending in a non-fallthrough terminator stays
//    in its original block. If the block end is in conditional range, insert
//    `Z: B T` just after it and retarget the UNCHANGED conditional to Z.
//    Neither the not-taken path nor instruction ownership changes; ADR,
//    jump-table and EH custody stays with its original instructions/block.
//    If later growth makes that island unreachable, refuse instead of
//    repeatedly chaining islands or moving an authority-bearing tail.
//
// Termination. A rewrite only INSERTS instructions: none is deleted or
// reordered (a split moves the tail into a block laid out where the tail
// was). So the distance between two existing instructions never shrinks. A
// form-1 or form-3 conditional targets the block that follows its own `B`
// (two instructions away, plus at most the loop-head padding the alignment
// pass may add in between); no later rewrite inserts there, because the only
// branch between them is that unconditional `B`. A form-2 conditional targets
// `F`, which was in range; if later growth pushes `F` out, `T` is still out
// (distances only grow), so its second rewrite is a split, which is final.
// Each conditional is therefore rewritten at most twice, and the fixed point
// is reached within `2 * conditionals + 1` rounds. Exceeding that bound is
// refused, never looped.
// An island is final or refuses if pushed out of range; at most one is
// installed for each conditional in this invocation, so the same bound holds.
//
// A function with no out-of-range branch is left untouched: not an operand,
// not an arena slot, not a CFG list changes, so its emitted bytes are
// identical to a build without this pass.

/// What [`relax_out_of_range_branches`] did to one function.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct BranchRelaxStats {
    /// Fixed-point rounds that found at least one out-of-range branch.
    pub rounds: u32,
    /// Form 1: `bcc T` + fallthrough `N` became `bcc_inv N ; B T`.
    pub fallthrough: u32,
    /// Form 2: `bcc T ; B F` became `bcc_inv F ; B T`.
    pub swapped: u32,
    /// Form 3: the tail after `bcc T` moved to a new layout-next block `Z`,
    /// and the branch became `bcc_inv Z ; B T`.
    pub split: u32,
    /// Form 4: an ordinary, non-fallthrough tail stayed in place and the
    /// unchanged conditional now reaches its far target through a near B.
    pub islands: u32,
}

impl BranchRelaxStats {
    /// Total conditional-branch rewrites.
    pub fn rewrites(&self) -> u32 {
        self.fallthrough + self.swapped + self.split + self.islands
    }
}

/// Errors from [`relax_out_of_range_branches`]. Each one is a refusal: the
/// function is not emitted, exactly as an out-of-range branch was refused by
/// the encoder before this pass existed.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum BranchRelaxError {
    /// An unconditional `B`/`TailCall` to a block is beyond +/-128 MiB.
    #[error(
        "{opcode:?} at {block:?} position {position} targets {target:?} {displacement} bytes away, \
         outside the +/-128 MiB unconditional range (no indirect-branch relaxation)"
    )]
    UnconditionalOutOfRange {
        opcode: AArch64Opcode,
        block: BlockId,
        position: usize,
        target: BlockId,
        displacement: i64,
    },
    /// A conditional branch is out of range but its shape is not one of the
    /// three rewrites.
    #[error("cannot relax {opcode:?} at {block:?} position {position}: {detail}")]
    UnsupportedShape {
        opcode: AArch64Opcode,
        block: BlockId,
        position: usize,
        detail: String,
    },
    /// The block or instruction arena would overflow its u32 ID domain.
    #[error("the {arena} arena is full")]
    ArenaExhausted { arena: &'static str },
    /// The fixed point was not reached within the proven round bound.
    #[error("no fixed point after {rounds} rounds (bound {bound})")]
    NoFixedPoint { rounds: u32, bound: u32 },
}

/// One out-of-range branch found by [`find_out_of_range_branches`].
#[derive(Debug, Clone, Copy)]
struct FarBranch {
    layout_index: usize,
    block: BlockId,
    position: usize,
}

/// True for the direct branches whose `Block` operand branch resolution
/// rewrites to a PC-relative immediate (`pipeline::resolve_branches`).
fn is_resolved_direct_branch(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::B
            | AArch64Opcode::TailCall
            | AArch64Opcode::BCond
            | AArch64Opcode::Cbz
            | AArch64Opcode::Cbnz
            | AArch64Opcode::Tbz
            | AArch64Opcode::Tbnz
    )
}

/// Operand index of the target of a canonical conditional branch:
/// `B.cond [cc, target]`, `CBZ/CBNZ [Rt, target]`, `TBZ/TBNZ [Rt, bit, target]`.
fn conditional_target_index(opcode: AArch64Opcode) -> Option<usize> {
    match opcode {
        AArch64Opcode::BCond | AArch64Opcode::Cbz | AArch64Opcode::Cbnz => Some(1),
        AArch64Opcode::Tbz | AArch64Opcode::Tbnz => Some(2),
        _ => None,
    }
}

/// The `Block` target of a resolvable direct branch, wherever branch
/// resolution would find it.
fn direct_branch_block_target(inst: &MachInst) -> Option<BlockId> {
    if !is_resolved_direct_branch(inst.opcode) {
        return None;
    }
    inst.operands.iter().find_map(|operand| match operand {
        MachOperand::Block(target) => Some(*target),
        _ => None,
    })
}

/// True when `inst` occupies a code slot but is not control flow the relaxer
/// has to look past: layout padding.
fn is_padding(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::AlignNop
}

/// The branch taken exactly when `inst` is not, with every other operand
/// kept: `B.cond` flips the condition (EQ..LE only; AL and NV hold
/// unconditionally and have no complement), `CBZ`<->`CBNZ`, `TBZ`<->`TBNZ`.
fn complemented_conditional(inst: &MachInst) -> Result<MachInst, String> {
    let mut complement = inst.clone();
    match inst.opcode {
        AArch64Opcode::BCond => match inst.operands.first() {
            Some(MachOperand::Imm(cc)) if (0..=13).contains(cc) => {
                complement.operands[0] = MachOperand::Imm(cc ^ 1);
            }
            Some(MachOperand::Imm(cc)) => {
                return Err(format!(
                    "condition code {cc} has no logical complement (AL/NV hold unconditionally)"
                ));
            }
            other => {
                return Err(format!(
                    "condition operand {other:?} is not an immediate condition code"
                ));
            }
        },
        AArch64Opcode::Cbz => complement.opcode = AArch64Opcode::Cbnz,
        AArch64Opcode::Cbnz => complement.opcode = AArch64Opcode::Cbz,
        AArch64Opcode::Tbz => complement.opcode = AArch64Opcode::Tbnz,
        AArch64Opcode::Tbnz => complement.opcode = AArch64Opcode::Tbz,
        other => return Err(format!("{other:?} is not a conditional branch")),
    }
    Ok(complement)
}

/// Byte offset of every laid-out block (`None` for blocks not in
/// `block_order`, which are never emitted). Every non-pseudo instruction,
/// `AlignNop` included, is 4 bytes: the rule branch resolution and the encoder
/// use.
fn laid_out_block_offsets(func: &MachFunction) -> Vec<Option<i64>> {
    let mut offsets = vec![None; func.blocks.len()];
    let mut offset = 0i64;
    for &block_id in &func.block_order {
        offsets[block_id.0 as usize] = Some(offset);
        for &inst_id in &func.block(block_id).insts {
            if !func.inst(inst_id).is_pseudo() {
                offset += 4;
            }
        }
    }
    offsets
}

/// Every laid-out direct branch whose `Block` target is outside its encoding
/// range, in layout order. An unconditional one is refused here: its range is
/// +/-128 MiB and the pass has no indirect-branch form.
fn find_out_of_range_branches(
    func: &MachFunction,
    offsets: &[Option<i64>],
) -> Result<Vec<FarBranch>, BranchRelaxError> {
    let mut far = Vec::new();
    for (layout_index, &block) in func.block_order.iter().enumerate() {
        let Some(mut inst_offset) = offsets[block.0 as usize] else {
            continue;
        };
        for (position, &inst_id) in func.block(block).insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            if inst.is_pseudo() {
                continue;
            }
            if let Some(target) = direct_branch_block_target(inst)
                && let Some(Some(target_offset)) = offsets.get(target.0 as usize)
            {
                let displacement = target_offset - inst_offset;
                if !in_range(inst.opcode, displacement) {
                    if matches!(inst.opcode, AArch64Opcode::B | AArch64Opcode::TailCall) {
                        return Err(BranchRelaxError::UnconditionalOutOfRange {
                            opcode: inst.opcode,
                            block,
                            position,
                            target,
                            displacement,
                        });
                    }
                    far.push(FarBranch {
                        layout_index,
                        block,
                        position,
                    });
                }
            }
            inst_offset += 4;
        }
    }
    Ok(far)
}

/// Number of laid-out conditional branches with a `Block` target: the
/// quantity the round bound is stated in.
fn laid_out_conditional_count(func: &MachFunction) -> u32 {
    func.block_order
        .iter()
        .flat_map(|&block| func.block(block).insts.iter())
        .filter(|&&inst_id| {
            let inst = func.inst(inst_id);
            conditional_target_index(inst.opcode).is_some()
                && direct_branch_block_target(inst).is_some()
        })
        .count()
        .try_into()
        .unwrap_or(u32::MAX)
}

/// Append `B far` to the instruction arena, carrying the relaxed
/// conditional's source location and lowering provenance: it implements the
/// same source branch.
fn push_far_branch(
    func: &mut MachFunction,
    conditional: InstId,
    far: BlockId,
) -> Result<InstId, BranchRelaxError> {
    let mut branch = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(far)]);
    branch.source_loc = func.inst(conditional).source_loc;
    let id = func
        .try_push_inst(branch)
        .ok_or(BranchRelaxError::ArenaExhausted {
            arena: "instruction",
        })?;
    if let Some(provenance) = func.lowering_provenance.get(&conditional).copied() {
        func.lowering_provenance.insert(id, provenance);
    }
    Ok(id)
}

/// Rewrite the out-of-range conditional at `site` into form 1, 2 or 3 (see
/// the section comment).
fn relax_conditional(
    func: &mut MachFunction,
    site: FarBranch,
    offsets: &[Option<i64>],
    stats: &mut BranchRelaxStats,
    islanded: &mut std::collections::BTreeSet<InstId>,
) -> Result<(), BranchRelaxError> {
    let FarBranch {
        layout_index,
        block,
        position,
    } = site;
    let conditional_id = func.block(block).insts[position];
    let conditional = func.inst(conditional_id).clone();
    let unsupported = |detail: String| BranchRelaxError::UnsupportedShape {
        opcode: conditional.opcode,
        block,
        position,
        detail,
    };
    let target_index = conditional_target_index(conditional.opcode)
        .ok_or_else(|| unsupported("not a conditional branch".to_string()))?;
    let far = match conditional.operands.get(target_index) {
        Some(MachOperand::Block(far)) if conditional.operands.len() == target_index + 1 => *far,
        _ => {
            return Err(unsupported(format!(
                "operands {:?} are not the canonical conditional-branch layout",
                conditional.operands
            )));
        }
    };
    let complement = complemented_conditional(&conditional).map_err(unsupported)?;
    let retarget = |mut inst: MachInst, target: BlockId| {
        inst.operands[target_index] = MachOperand::Block(target);
        inst
    };

    let tail: Vec<InstId> = func.block(block).insts[position + 1..].to_vec();
    let real_tail: Vec<InstId> = tail
        .iter()
        .copied()
        .filter(|&id| {
            let inst = func.inst(id);
            !inst.is_pseudo() && !is_padding(inst)
        })
        .collect();

    if islanded.contains(&conditional_id) {
        return Err(unsupported(
            "growth pushed the retained-tail branch island out of conditional range".into(),
        ));
    }

    // Form 1: the conditional ends the block and falls into its layout
    // successor.
    if real_tail.is_empty() {
        let next = *func.block_order.get(layout_index + 1).ok_or_else(|| {
            unsupported("the last laid-out block falls off the end of the function".to_string())
        })?;
        *func.inst_mut(conditional_id) = retarget(complement, next);
        let branch = push_far_branch(func, conditional_id, far)?;
        func.block_mut(block).insts.insert(position + 1, branch);
        stats.fallthrough += 1;
        return Ok(());
    }

    // Form 2: `bcc T ; B F` with F reachable from the conditional.
    if let [tail_branch] = real_tail[..] {
        let inst = func.inst(tail_branch);
        if inst.opcode == AArch64Opcode::B
            && let [MachOperand::Block(near)] = inst.operands[..]
            && let (Some(Some(block_offset)), Some(Some(near_offset))) =
                (offsets.get(block.0 as usize), offsets.get(near.0 as usize))
        {
            let conditional_offset = block_offset
                + 4 * func.block(block).insts[..position]
                    .iter()
                    .filter(|&&id| !func.inst(id).is_pseudo())
                    .count() as i64;
            if in_range(conditional.opcode, near_offset - conditional_offset) {
                *func.inst_mut(conditional_id) = retarget(complement, near);
                func.inst_mut(tail_branch).operands[0] = MachOperand::Block(far);
                stats.swapped += 1;
                return Ok(());
            }
        }
    }

    // Form 3: move the tail into a new block laid out right after this one.
    // The tail may hold only direct branches to blocks: anything else (a
    // call, an indirect or jump-table branch, ordinary code) would carry
    // block-keyed authority — EH call sites, jump-table sources — that a
    // move does not update, so it is refused rather than rewritten.
    if let Some(&other) = real_tail.iter().find(|&&id| {
        let inst = func.inst(id);
        inst.opcode == AArch64Opcode::TailCall || direct_branch_block_target(inst).is_none()
    }) {
        // A nearby out-of-line B preserves the ordinary tail byte-for-byte.
        // Require a hard end: otherwise not-taken execution would fall into
        // the island instead of the original layout successor. An ordinary
        // tail too large for this near target remains explicitly unsupported.
        let tail_ends = real_tail.last().is_some_and(|&id| {
            let last = func.inst(id);
            last.is_unconditional_branch()
                || last.is_return()
                || last.opcode == AArch64Opcode::Brk
                || (last.is_terminator() && !last.is_conditional_branch())
        });
        let to_island = func.block(block).insts[position..]
            .iter()
            .filter(|&&id| !func.inst(id).is_pseudo())
            .count() as i64
            * 4;
        if tail_ends && in_range(conditional.opcode, to_island) {
            let island = func
                .try_create_block()
                .ok_or(BranchRelaxError::ArenaExhausted { arena: "block" })?;
            func.block_order.pop();
            func.block_order.insert(layout_index + 1, island);
            func.block_mut(island).loop_depth = func.block(block).loop_depth;
            let branch = push_far_branch(func, conditional_id, far)?;
            func.block_mut(island).insts.push(branch);
            *func.inst_mut(conditional_id) = retarget(conditional, island);
            islanded.insert(conditional_id);
            stats.islands += 1;
            return Ok(());
        }
        return Err(unsupported(format!(
            "the instructions after it include {:?}; a retained-tail island needs a non-fallthrough end within conditional range",
            func.inst(other).opcode
        )));
    }
    let loop_depth = func.block(block).loop_depth;
    let split = func
        .try_create_block()
        .ok_or(BranchRelaxError::ArenaExhausted { arena: "block" })?;
    // `try_create_block` appends to the layout; lay it out after `block`.
    func.block_order.pop();
    func.block_order.insert(layout_index + 1, split);
    func.block_mut(split).insts = tail;
    func.block_mut(split).loop_depth = loop_depth;
    func.block_mut(block).insts.truncate(position + 1);
    *func.inst_mut(conditional_id) = retarget(complement, split);
    let branch = push_far_branch(func, conditional_id, far)?;
    func.block_mut(block).insts.push(branch);
    stats.split += 1;
    Ok(())
}

/// Relax every out-of-range conditional branch of a laid-out AArch64
/// function in place, iterating to a fixed point, and leave every branch
/// target symbolic for branch resolution (see the section comment for the
/// three rewrites and the termination bound).
///
/// Precondition: the function passed the pipeline's structural validation
/// (every laid-out block and branch target is in the arenas). A function with
/// no out-of-range branch is returned untouched.
pub fn relax_out_of_range_branches(
    func: &mut MachFunction,
) -> Result<BranchRelaxStats, BranchRelaxError> {
    let mut stats = BranchRelaxStats::default();
    let mut islanded = std::collections::BTreeSet::new();
    let mut offsets = laid_out_block_offsets(func);
    let mut far = find_out_of_range_branches(func, &offsets)?;
    if far.is_empty() {
        return Ok(stats);
    }
    let bound = laid_out_conditional_count(func)
        .saturating_mul(2)
        .saturating_add(1);
    while !far.is_empty() {
        if stats.rounds >= bound {
            return Err(BranchRelaxError::NoFixedPoint {
                rounds: stats.rounds,
                bound,
            });
        }
        stats.rounds += 1;
        // Rewrite in reverse layout and position order. A rewrite changes
        // only its own block at or after the branch, and a split inserts its
        // block right after that one in the layout, so every site still to be
        // visited keeps its recorded layout index and position.
        for &site in far.iter().rev() {
            relax_conditional(func, site, &offsets, &mut stats, &mut islanded)?;
        }
        offsets = laid_out_block_offsets(func);
        far = find_out_of_range_branches(func, &offsets)?;
    }
    if stats.split > 0 || stats.islands > 0 {
        let edges = crate::pipeline::derive_ir_cfg_edges_from_branch_operands(func);
        crate::pipeline::install_ir_cfg_edges(func, edges);
    }
    Ok(stats)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{AArch64CC, MachOperand, Signature};

    /// Helper: create a function with given number of blocks.
    fn make_func(name: &str, num_blocks: usize) -> MachFunction {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new(name.to_string(), sig);
        for _ in 1..num_blocks {
            func.create_block();
        }
        func
    }

    fn add_inst(func: &mut MachFunction, block: BlockId, inst: MachInst) -> InstId {
        let id = func.push_inst(inst);
        func.append_inst(block, id);
        id
    }

    // -----------------------------------------------------------------------
    // test_branch_ranges
    // -----------------------------------------------------------------------
    #[test]
    fn test_branch_ranges() {
        // B: +/- 128MB
        let (min, max) = branch_range(AArch64Opcode::B);
        assert_eq!(max, (1 << 27) - 4);
        assert_eq!(min, -(1 << 27));

        // BCond: +/- 1MB
        let (min, max) = branch_range(AArch64Opcode::BCond);
        assert_eq!(max, (1 << 20) - 4);
        assert_eq!(min, -(1 << 20));

        // CBZ/CBNZ: same as BCond
        assert_eq!(
            branch_range(AArch64Opcode::Cbz),
            branch_range(AArch64Opcode::BCond)
        );
        assert_eq!(
            branch_range(AArch64Opcode::Cbnz),
            branch_range(AArch64Opcode::BCond)
        );

        // TBZ/TBNZ: +/- 32KB
        let (min, max) = branch_range(AArch64Opcode::Tbz);
        assert_eq!(max, (1 << 15) - 4);
        assert_eq!(min, -(1 << 15));
        assert_eq!(
            branch_range(AArch64Opcode::Tbnz),
            branch_range(AArch64Opcode::Tbz)
        );
    }

    // -----------------------------------------------------------------------
    // test_in_range
    // -----------------------------------------------------------------------
    #[test]
    fn test_in_range_checks() {
        // BCond: +/- 1MB
        assert!(in_range(AArch64Opcode::BCond, 100));
        assert!(in_range(AArch64Opcode::BCond, -100));
        assert!(in_range(AArch64Opcode::BCond, BCOND_MAX_RANGE));
        assert!(in_range(AArch64Opcode::BCond, BCOND_MIN_RANGE));
        assert!(!in_range(AArch64Opcode::BCond, BCOND_MAX_RANGE + 4));
        assert!(!in_range(AArch64Opcode::BCond, BCOND_MIN_RANGE - 4));

        // TBZ: +/- 32KB
        assert!(in_range(AArch64Opcode::Tbz, 100));
        assert!(!in_range(AArch64Opcode::Tbz, TBZ_MAX_RANGE + 4));
    }

    // -----------------------------------------------------------------------
    // test_no_relaxation_needed
    // -----------------------------------------------------------------------
    #[test]
    fn test_no_relaxation_needed() {
        let mut func = make_func("small", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: BCond bb1 ; B bb2
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(bb1),
                ],
            ),
        );
        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );

        // bb1: AddRI ; Ret
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        // bb2: AddRI ; Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // 6 non-pseudo instructions total.
        assert_eq!(result.instructions.len(), 6);
        // Block offsets: bb0=0, bb1=8, bb2=16
        assert_eq!(result.block_offsets[0], 0);
        assert_eq!(result.block_offsets[1], 8);
        assert_eq!(result.block_offsets[2], 16);
    }

    // -----------------------------------------------------------------------
    // test_offset_computation
    // -----------------------------------------------------------------------
    #[test]
    fn test_offset_computation() {
        let mut func = make_func("offsets", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: 3 instructions (12 bytes)
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        // bb1: 2 instructions (8 bytes)
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        // bb2: 1 instruction (4 bytes)
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let infos = compute_block_offsets(&func);
        assert_eq!(infos[0].offset, 0);
        assert_eq!(infos[0].size, 12);
        assert_eq!(infos[1].offset, 12);
        assert_eq!(infos[1].size, 8);
        assert_eq!(infos[2].offset, 20);
        assert_eq!(infos[2].size, 4);
    }

    // -----------------------------------------------------------------------
    // test_pseudo_instructions_not_counted
    // -----------------------------------------------------------------------
    #[test]
    fn test_pseudo_instructions_not_counted() {
        let mut func = make_func("pseudo", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        // bb0: Nop (pseudo), AddRI, Ret
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::Nop, vec![]));
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        // bb1: Ret
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        let infos = compute_block_offsets(&func);
        // bb0: Nop doesn't count, so 2 real instructions = 8 bytes.
        assert_eq!(infos[0].size, 8);
        assert_eq!(infos[1].offset, 8);
    }

    // -----------------------------------------------------------------------
    // test_bcond_relaxation
    // -----------------------------------------------------------------------
    #[test]
    fn test_bcond_relaxation_via_range_check() {
        // Instead of creating millions of NOPs, directly test the relaxation
        // logic by verifying range checks and the relaxation pattern.

        // Verify out-of-range detection: 2MB displacement > 1MB BCond range.
        assert!(!in_range(AArch64Opcode::BCond, 2 * 1024 * 1024));
        assert!(!in_range(AArch64Opcode::BCond, -(2 * 1024 * 1024)));

        // Verify in-range: 512KB < 1MB
        assert!(in_range(AArch64Opcode::BCond, 512 * 1024));
    }

    // -----------------------------------------------------------------------
    // test_cbz_relaxation_pattern
    // -----------------------------------------------------------------------
    #[test]
    fn test_cbz_relaxation_pattern() {
        // Create a function where we manually trigger relaxation on a CBZ.
        let mut func = make_func("cbz_relax", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        // bb0: CBZ to bb1
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Cbz,
                vec![MachOperand::Imm(0), MachOperand::Block(bb1)],
            ),
        );

        // bb1: Ret
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        // Manually call relax_one_branch to test the pattern.
        relax_one_branch(&mut func, bb0, 0).unwrap();

        let blk = func.block(bb0);
        // Should now have 2 instructions: CBNZ +8, B bb1.
        assert_eq!(blk.insts.len(), 2);

        let inv = func.inst(blk.insts[0]);
        assert_eq!(
            inv.opcode,
            AArch64Opcode::Cbnz,
            "CBZ should be inverted to CBNZ"
        );

        let far = func.inst(blk.insts[1]);
        assert_eq!(
            far.opcode,
            AArch64Opcode::B,
            "far branch should be unconditional B"
        );
        assert_eq!(
            get_branch_target_block(far),
            Some(bb1),
            "B should target bb1"
        );
    }

    // -----------------------------------------------------------------------
    // test_bcond_relaxation_pattern
    // -----------------------------------------------------------------------
    #[test]
    fn test_bcond_relaxation_pattern() {
        let mut func = make_func("bcond_relax", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        // bb0: BCond EQ bb1
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(bb1),
                ],
            ),
        );

        // bb1: Ret
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        relax_one_branch(&mut func, bb0, 0).unwrap();

        let blk = func.block(bb0);
        assert_eq!(blk.insts.len(), 2);

        let inv = func.inst(blk.insts[0]);
        assert_eq!(inv.opcode, AArch64Opcode::BCond);
        // Check inverted condition: EQ (0) -> NE (1)
        let cc = inv.operands[0].as_imm().unwrap();
        assert_eq!(cc, AArch64CC::NE as i64, "EQ should be inverted to NE");

        let far = func.inst(blk.insts[1]);
        assert_eq!(far.opcode, AArch64Opcode::B);
    }

    // -----------------------------------------------------------------------
    // test_tbz_relaxation_pattern
    // -----------------------------------------------------------------------
    #[test]
    fn test_tbz_relaxation_pattern() {
        let mut func = make_func("tbz_relax", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        // bb0: TBZ Rt=X0, bit=5, target=bb1
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Tbz,
                vec![
                    MachOperand::Imm(0), // Rt
                    MachOperand::Imm(5), // bit number
                    MachOperand::Block(bb1),
                ],
            ),
        );

        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        relax_one_branch(&mut func, bb0, 0).unwrap();

        let blk = func.block(bb0);
        assert_eq!(blk.insts.len(), 2);

        let inv = func.inst(blk.insts[0]);
        assert_eq!(
            inv.opcode,
            AArch64Opcode::Tbnz,
            "TBZ should be inverted to TBNZ"
        );

        let far = func.inst(blk.insts[1]);
        assert_eq!(far.opcode, AArch64Opcode::B);
        assert_eq!(get_branch_target_block(far), Some(bb1));
    }

    // -----------------------------------------------------------------------
    // test_invert_cc
    // -----------------------------------------------------------------------
    #[test]
    fn test_invert_cc_values() {
        assert_eq!(invert_cc(AArch64CC::EQ as u8), AArch64CC::NE as u8);
        assert_eq!(invert_cc(AArch64CC::NE as u8), AArch64CC::EQ as u8);
        assert_eq!(invert_cc(AArch64CC::HS as u8), AArch64CC::LO as u8);
        assert_eq!(invert_cc(AArch64CC::LO as u8), AArch64CC::HS as u8);
        assert_eq!(invert_cc(AArch64CC::GE as u8), AArch64CC::LT as u8);
        assert_eq!(invert_cc(AArch64CC::LT as u8), AArch64CC::GE as u8);
        assert_eq!(invert_cc(AArch64CC::GT as u8), AArch64CC::LE as u8);
        assert_eq!(invert_cc(AArch64CC::LE as u8), AArch64CC::GT as u8);
    }

    // -----------------------------------------------------------------------
    // test_resolved_offsets
    // -----------------------------------------------------------------------
    #[test]
    fn test_resolved_offsets() {
        let mut func = make_func("resolved", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: B bb2 (jumps over bb1)
        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );

        // bb1: AddRI ; Ret (2 instructions = 8 bytes)
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // bb0 at offset 0, bb1 at offset 4, bb2 at offset 12.
        // B bb2 at offset 0: displacement = (12 - 0) / 4 = 3.
        assert_eq!(result.instructions.len(), 4);
        let b_inst = &result.instructions[0];
        assert_eq!(b_inst.opcode, AArch64Opcode::B);
        let offset = b_inst.operands.iter().find_map(|op| op.as_imm()).unwrap();
        assert_eq!(
            offset, 3,
            "B bb2 should have displacement of 3 instruction units"
        );
    }

    // -----------------------------------------------------------------------
    // test_fixpoint_convergence
    // -----------------------------------------------------------------------
    #[test]
    fn test_fixpoint_convergence() {
        // A simple function should converge in 1 iteration (no relaxation needed).
        let mut func = make_func("converge", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(bb1),
                ],
            ),
        );
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        // Should not panic or loop infinitely.
        let result = relax_branches(&mut func).unwrap();
        assert_eq!(result.instructions.len(), 3);
    }

    // -----------------------------------------------------------------------
    // Integration tests: full relax_branches() with synthetic large offsets
    // -----------------------------------------------------------------------

    /// TBZ forward over 9000 instructions (36000 bytes > 32KB TBZ range).
    /// Verifies the fixed-point loop detects the out-of-range TBZ, inverts
    /// it to TBNZ, and inserts an unconditional B.
    #[test]
    fn test_tbz_relaxation_large_offset() {
        // bb0: TBZ -> bb2
        // bb1: 9000 x AddRI (filler to push bb2 past 32KB)
        // bb2: Ret
        let mut func = make_func("tbz_large", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: TBZ Rt=0, bit=3, target=bb2
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Tbz,
                vec![
                    MachOperand::Imm(0),
                    MachOperand::Imm(3),
                    MachOperand::Block(bb2),
                ],
            ),
        );

        // bb1: 9000 filler instructions (36000 bytes)
        for _ in 0..9000 {
            add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // After relaxation: TBZ -> TBNZ +8 ; B bb2.
        // Total: 1 (TBNZ) + 1 (B) + 9000 (filler) + 1 (Ret) = 9003.
        // But the original TBZ was 1 inst; after relaxation it becomes 2.
        // So: 2 + 9000 + 1 = 9003.
        assert_eq!(result.instructions.len(), 9003);

        // First instruction should be TBNZ (inverted from TBZ).
        assert_eq!(
            result.instructions[0].opcode,
            AArch64Opcode::Tbnz,
            "TBZ should be relaxed to TBNZ"
        );

        // Second instruction should be unconditional B.
        assert_eq!(
            result.instructions[1].opcode,
            AArch64Opcode::B,
            "inserted far branch should be unconditional B"
        );

        // The B should have a resolved Imm offset pointing to bb2.
        // bb2 offset = (2 + 9000) * 4 = 36008 bytes.
        // B is at offset 4 bytes (instruction index 1).
        // displacement = (36008 - 4) / 4 = 9001.
        let far_offset = result.instructions[1]
            .operands
            .iter()
            .find_map(|op| op.as_imm())
            .unwrap();
        assert_eq!(
            far_offset, 9001,
            "B should jump over 9001 instructions to reach bb2"
        );
    }

    /// TBZ backward over 9000 instructions. bb0 has 9000 filler instructions,
    /// bb1 has a TBZ back to bb0. Verifies backward relaxation.
    #[test]
    fn test_backward_branch_relaxation() {
        let mut func = make_func("tbz_backward", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        // bb0: 9000 filler instructions
        for _ in 0..9000 {
            add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        // bb1: TBZ backward to bb0
        add_inst(
            &mut func,
            bb1,
            MachInst::new(
                AArch64Opcode::Tbz,
                vec![
                    MachOperand::Imm(0),
                    MachOperand::Imm(7),
                    MachOperand::Block(bb0),
                ],
            ),
        );
        // bb1: Ret (so the block has a fallthrough)
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // After relaxation: bb0 (9000) + TBNZ +8 (1) + B bb0 (1) + Ret (1) = 9003.
        // Wait: the original bb1 had [TBZ, Ret]. After relaxation: [TBNZ, B, Ret] = 3.
        // Total: 9000 + 3 = 9003.
        assert_eq!(result.instructions.len(), 9003);

        // Instruction at index 9000 should be TBNZ (inverted from TBZ).
        assert_eq!(
            result.instructions[9000].opcode,
            AArch64Opcode::Tbnz,
            "backward TBZ should be inverted to TBNZ"
        );

        // Instruction at index 9001 should be B (the far branch).
        assert_eq!(
            result.instructions[9001].opcode,
            AArch64Opcode::B,
            "inserted far branch for backward jump"
        );

        // The B targets bb0 at offset 0. B is at byte offset 9001*4 = 36004.
        // displacement = (0 - 36004) / 4 = -9001.
        let far_offset = result.instructions[9001]
            .operands
            .iter()
            .find_map(|op| op.as_imm())
            .unwrap();
        assert_eq!(
            far_offset, -9001,
            "B should jump backward 9001 instructions to bb0"
        );
    }

    /// Unconditional B within 128MB should NOT be relaxed.
    #[test]
    fn test_unconditional_b_in_range() {
        let mut func = make_func("b_in_range", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: B -> bb2 (jumps over bb1)
        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );

        // bb1: 100 filler instructions (400 bytes, well within B range)
        for _ in 0..100 {
            add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // No relaxation needed: 1 (B) + 100 (filler) + 1 (Ret) = 102.
        assert_eq!(result.instructions.len(), 102);

        // The B instruction should still be a B (not relaxed).
        assert_eq!(result.instructions[0].opcode, AArch64Opcode::B);
    }

    /// CBNZ forward over 262145 instructions (>1MB, exceeds CBNZ 19-bit range).
    /// Verifies CBNZ -> CBZ inversion.
    #[test]
    fn test_cbnz_relaxation_large_offset() {
        let count = 262145u32; // just over 1MB / 4 = 262144 instructions
        let mut func = make_func("cbnz_large", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: CBNZ -> bb2
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Cbnz,
                vec![MachOperand::Imm(0), MachOperand::Block(bb2)],
            ),
        );

        // bb1: `count` filler instructions
        for _ in 0..count {
            add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // After relaxation: CBZ +8 (1) + B (1) + count filler + Ret (1) = count + 3.
        assert_eq!(result.instructions.len(), (count + 3) as usize);

        // First instruction should be CBZ (inverted from CBNZ).
        assert_eq!(
            result.instructions[0].opcode,
            AArch64Opcode::Cbz,
            "CBNZ should be relaxed to CBZ"
        );

        // Second should be unconditional B.
        assert_eq!(result.instructions[1].opcode, AArch64Opcode::B);
    }

    // -----------------------------------------------------------------------
    // test_bcond_relaxation_large_offset
    // -----------------------------------------------------------------------
    /// BCond EQ forward over 262145 instructions (>1MB, exceeds 19-bit range).
    /// Verifies BCond EQ becomes BCond NE (inverted) + B through the
    /// fixed-point loop.
    #[test]
    fn test_bcond_relaxation_large_offset() {
        let count = 262145u32; // 262145 * 4 = 1,048,580 bytes > 1MB BCond range
        let mut func = make_func("bcond_large", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: BCond EQ -> bb2
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(bb2),
                ],
            ),
        );

        // bb1: `count` filler instructions
        for _ in 0..count {
            add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // After relaxation: BCond NE (1) + B (1) + count filler + Ret (1) = count + 3.
        assert_eq!(result.instructions.len(), (count + 3) as usize);

        // First instruction: BCond with inverted condition (NE instead of EQ).
        assert_eq!(
            result.instructions[0].opcode,
            AArch64Opcode::BCond,
            "should still be BCond opcode"
        );
        // First operand is the inverted condition code.
        assert_eq!(
            result.instructions[0].operands[0].as_imm().unwrap(),
            AArch64CC::NE as i64,
            "EQ should be inverted to NE"
        );

        // Second instruction: unconditional B to far target.
        assert_eq!(result.instructions[1].opcode, AArch64Opcode::B);
    }

    // -----------------------------------------------------------------------
    // test_tbnz_relaxation_large_offset
    // -----------------------------------------------------------------------
    /// TBNZ forward over 9000 instructions (>32KB, exceeds TBZ/TBNZ 14-bit range).
    /// Verifies TBNZ becomes TBZ (inverted) + B.
    #[test]
    fn test_tbnz_relaxation_large_offset() {
        let mut func = make_func("tbnz_large", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: TBNZ Rt=0, bit=7, target=bb2
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Tbnz,
                vec![
                    MachOperand::Imm(0), // Rt
                    MachOperand::Imm(7), // bit number
                    MachOperand::Block(bb2),
                ],
            ),
        );

        // bb1: 9000 filler instructions (36000 bytes > 32KB)
        for _ in 0..9000 {
            add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // After relaxation: TBZ (1) + B (1) + 9000 (filler) + 1 (Ret) = 9003.
        assert_eq!(result.instructions.len(), 9003);

        // First instruction: TBZ (inverted from TBNZ).
        assert_eq!(
            result.instructions[0].opcode,
            AArch64Opcode::Tbz,
            "TBNZ should be relaxed to TBZ"
        );

        // Second instruction: unconditional B.
        assert_eq!(
            result.instructions[1].opcode,
            AArch64Opcode::B,
            "inserted far branch should be unconditional B"
        );

        // Verify the far B has correct displacement.
        // bb2 offset = (2 + 9000) * 4 = 36008 bytes.
        // B at offset 4 bytes (index 1): displacement = (36008 - 4) / 4 = 9001.
        let far_offset = result.instructions[1]
            .operands
            .iter()
            .find_map(|op| op.as_imm())
            .unwrap();
        assert_eq!(far_offset, 9001, "B should jump 9001 instructions to bb2");
    }

    // -----------------------------------------------------------------------
    // test_empty_function
    // -----------------------------------------------------------------------
    /// A single block with just Ret. No relaxation needed.
    #[test]
    fn test_empty_function_no_relaxation() {
        let mut func = make_func("empty", 1);
        let bb0 = BlockId(0);

        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        assert_eq!(result.instructions.len(), 1);
        assert_eq!(result.instructions[0].opcode, AArch64Opcode::Ret);
        assert_eq!(result.block_offsets[0], 0);
    }

    // -----------------------------------------------------------------------
    // test_single_block_no_branches
    // -----------------------------------------------------------------------
    /// A single block with multiple non-branch instructions.
    #[test]
    fn test_single_block_no_branches() {
        let mut func = make_func("no_branches", 1);
        let bb0 = BlockId(0);

        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        assert_eq!(result.instructions.len(), 4);
        assert_eq!(result.block_offsets[0], 0);
    }

    // -----------------------------------------------------------------------
    // test_bcond_boundary_in_range
    // -----------------------------------------------------------------------
    /// BCond with displacement exactly at BCOND_MAX_RANGE. Should NOT be relaxed.
    #[test]
    fn test_bcond_boundary_in_range() {
        // BCOND_MAX_RANGE = (1 << 20) - 4 = 1,048,572 bytes.
        // Need bb2 at offset = BCOND_MAX_RANGE from the BCond instruction.
        // BCond is the only instruction in bb0 (offset 0), so bb1 starts at 4.
        // bb2 offset = 4 + N*4 = BCOND_MAX_RANGE = 1,048,572.
        // N = (1,048,572 - 4) / 4 = 262,142.
        let filler = 262142u32;
        let mut func = make_func("bcond_boundary_in", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(bb2),
                ],
            ),
        );

        for _ in 0..filler {
            add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // Should NOT be relaxed: 1 (BCond) + filler + 1 (Ret) = filler + 2.
        assert_eq!(result.instructions.len(), (filler + 2) as usize);

        // First instruction should still be BCond (not relaxed, no extra B inserted).
        assert_eq!(result.instructions[0].opcode, AArch64Opcode::BCond);

        // Verify the resolved displacement is correct.
        // BCond at offset 0, bb2 at offset 4 + filler*4 = 1,048,572.
        // displacement in instruction units = 1,048,572 / 4 = 262,143.
        let offset_imm = result.instructions[0]
            .operands
            .iter()
            .filter_map(|op| op.as_imm())
            .next_back()
            .unwrap();
        assert_eq!(offset_imm, 262143, "displacement in instruction units");
    }

    // -----------------------------------------------------------------------
    // test_bcond_boundary_out_of_range
    // -----------------------------------------------------------------------
    /// BCond with displacement at BCOND_MAX_RANGE + 4. Should be relaxed.
    #[test]
    fn test_bcond_boundary_out_of_range() {
        // BCOND_MAX_RANGE + 4 = 1,048,576 bytes.
        // Need bb2 at offset 1,048,576 from the BCond at offset 0.
        // bb2 offset = 4 + N*4 = 1,048,576 => N = (1,048,576 - 4) / 4 = 262,143.
        let filler = 262143u32;
        let mut func = make_func("bcond_boundary_out", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::GE as i64),
                    MachOperand::Block(bb2),
                ],
            ),
        );

        for _ in 0..filler {
            add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // Should be relaxed: BCond LT (1) + B (1) + filler + Ret (1) = filler + 3.
        assert_eq!(result.instructions.len(), (filler + 3) as usize);

        // First instruction: BCond with inverted condition (LT instead of GE).
        assert_eq!(result.instructions[0].opcode, AArch64Opcode::BCond);
        assert_eq!(
            result.instructions[0].operands[0].as_imm().unwrap(),
            AArch64CC::LT as i64,
            "GE should be inverted to LT"
        );

        // Second instruction: unconditional B.
        assert_eq!(result.instructions[1].opcode, AArch64Opcode::B);
    }

    // -----------------------------------------------------------------------
    // test_cbz_backward_relaxation
    // -----------------------------------------------------------------------
    /// CBZ backward over many instructions (>1MB). Verifies backward CBZ
    /// relaxation.
    #[test]
    fn test_cbz_backward_relaxation() {
        let count = 262145u32;
        let mut func = make_func("cbz_backward", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        // bb0: count filler instructions
        for _ in 0..count {
            add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        // bb1: CBZ backward to bb0
        add_inst(
            &mut func,
            bb1,
            MachInst::new(
                AArch64Opcode::Cbz,
                vec![MachOperand::Imm(0), MachOperand::Block(bb0)],
            ),
        );
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // After relaxation: count filler + CBNZ (1) + B (1) + Ret (1) = count + 3.
        assert_eq!(result.instructions.len(), (count + 3) as usize);

        // Instruction at count index should be CBNZ (inverted from CBZ).
        assert_eq!(
            result.instructions[count as usize].opcode,
            AArch64Opcode::Cbnz,
            "backward CBZ should be inverted to CBNZ"
        );

        // Next instruction: unconditional B.
        assert_eq!(
            result.instructions[(count + 1) as usize].opcode,
            AArch64Opcode::B,
        );
    }

    // -----------------------------------------------------------------------
    // test_tbnz_relaxation_pattern
    // -----------------------------------------------------------------------
    /// Manually triggered TBNZ relaxation pattern test.
    #[test]
    fn test_tbnz_relaxation_pattern() {
        let mut func = make_func("tbnz_relax", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        // bb0: TBNZ Rt=0, bit=15, target=bb1
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Tbnz,
                vec![
                    MachOperand::Imm(0),  // Rt
                    MachOperand::Imm(15), // bit number
                    MachOperand::Block(bb1),
                ],
            ),
        );

        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        relax_one_branch(&mut func, bb0, 0).unwrap();

        let blk = func.block(bb0);
        assert_eq!(blk.insts.len(), 2);

        let inv = func.inst(blk.insts[0]);
        assert_eq!(
            inv.opcode,
            AArch64Opcode::Tbz,
            "TBNZ should be inverted to TBZ"
        );
        // Verify the bit number operand is preserved.
        // Operands: [Imm(Rt=0), Imm(bit=15), Imm(skip=2)]
        assert_eq!(
            inv.operands[1].as_imm().unwrap(),
            15,
            "bit number should be preserved"
        );

        let far = func.inst(blk.insts[1]);
        assert_eq!(far.opcode, AArch64Opcode::B);
        assert_eq!(get_branch_target_block(far), Some(bb1));
    }

    // -----------------------------------------------------------------------
    // test_branch_relaxation_pass_struct
    // -----------------------------------------------------------------------
    /// Test the BranchRelaxation pass struct API.
    #[test]
    fn test_branch_relaxation_pass_struct() {
        let mut func = make_func("pass_test", 2);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);

        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        let pass = BranchRelaxation::new();
        let result = pass.run(&mut func).unwrap();

        assert_eq!(result.instructions.len(), 2);
        assert_eq!(result.instructions[0].opcode, AArch64Opcode::B);
        assert_eq!(result.instructions[1].opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn public_relaxation_entrypoints_reject_malformed_arenas_without_panicking() {
        fn assert_rejected(mut func: MachFunction) {
            let pass = BranchRelaxation::new();
            let diagnostic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                pass.has_out_of_range_branches(&func)
            }));
            assert!(matches!(
                diagnostic.expect("diagnostic entrypoint must not panic"),
                Err(RelaxError::MalformedFunction(_))
            ));

            let run =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| pass.run(&mut func)));
            assert!(matches!(
                run.expect("mutating entrypoint must not panic"),
                Err(RelaxError::MalformedFunction(_))
            ));
        }

        let mut bad_layout = make_func("bad_layout", 1);
        bad_layout.block_order = vec![BlockId(99)];
        assert_rejected(bad_layout);

        let mut bad_inst = make_func("bad_inst", 1);
        bad_inst.block_mut(BlockId(0)).insts.push(InstId(99));
        assert_rejected(bad_inst);

        let mut bad_target = make_func("bad_target", 1);
        add_inst(
            &mut bad_target,
            BlockId(0),
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(99))]),
        );
        assert_rejected(bad_target);
    }

    // -----------------------------------------------------------------------
    // test_has_out_of_range_branches
    // -----------------------------------------------------------------------
    /// Test the has_out_of_range_branches diagnostic.
    #[test]
    fn test_has_out_of_range_branches() {
        let pass = BranchRelaxation::new();

        // Small function: no out-of-range branches.
        let mut small_func = make_func("small_diag", 2);
        let s_bb0 = BlockId(0);
        let s_bb1 = BlockId(1);
        add_inst(
            &mut small_func,
            s_bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(s_bb1),
                ],
            ),
        );
        add_inst(
            &mut small_func,
            s_bb1,
            MachInst::new(AArch64Opcode::Ret, vec![]),
        );
        assert!(
            !pass
                .has_out_of_range_branches(&small_func)
                .expect("small fixture must validate")
        );

        // Large function with TBZ: out of range.
        let mut large_func = make_func("large_diag", 3);
        let l_bb0 = BlockId(0);
        let l_bb1 = BlockId(1);
        let l_bb2 = BlockId(2);
        add_inst(
            &mut large_func,
            l_bb0,
            MachInst::new(
                AArch64Opcode::Tbz,
                vec![
                    MachOperand::Imm(0),
                    MachOperand::Imm(3),
                    MachOperand::Block(l_bb2),
                ],
            ),
        );
        for _ in 0..9000 {
            add_inst(
                &mut large_func,
                l_bb1,
                MachInst::new(AArch64Opcode::AddRI, vec![]),
            );
        }
        add_inst(
            &mut large_func,
            l_bb2,
            MachInst::new(AArch64Opcode::Ret, vec![]),
        );
        assert!(
            pass.has_out_of_range_branches(&large_func)
                .expect("large fixture must validate")
        );
    }

    // -----------------------------------------------------------------------
    // test_default_impl
    // -----------------------------------------------------------------------
    #[test]
    fn test_branch_relaxation_default() {
        let pass = BranchRelaxation;
        let mut func = make_func("default_test", 1);
        let bb0 = BlockId(0);
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::Ret, vec![]));
        let result = pass.run(&mut func).unwrap();
        assert_eq!(result.instructions.len(), 1);
    }

    // -----------------------------------------------------------------------
    // test_multiple_branches_in_one_block
    // -----------------------------------------------------------------------
    /// Multiple branch instructions in a single block, all in range.
    #[test]
    fn test_multiple_branches_one_block_all_in_range() {
        let mut func = make_func("multi_branch", 4);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);
        let bb3 = BlockId(3);

        // bb0: BCond -> bb1 ; BCond -> bb2 ; B -> bb3
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(bb1),
                ],
            ),
        );
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::GT as i64),
                    MachOperand::Block(bb2),
                ],
            ),
        );
        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );

        // bb1: Ret
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));
        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));
        // bb3: Ret
        add_inst(&mut func, bb3, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // 3 branches + 3 Rets = 6 instructions, no relaxation.
        assert_eq!(result.instructions.len(), 6);

        // Verify all branches were resolved to Imm offsets.
        for inst in &result.instructions {
            for op in &inst.operands {
                assert!(
                    !matches!(op, MachOperand::Block(_)),
                    "all Block operands should be resolved"
                );
            }
        }
    }

    /// Verify block_offsets array is consistent after TBZ relaxation.
    #[test]
    fn test_relaxation_preserves_block_offsets() {
        let mut func = make_func("offsets_check", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: TBZ -> bb2
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Tbz,
                vec![
                    MachOperand::Imm(0),
                    MachOperand::Imm(0),
                    MachOperand::Block(bb2),
                ],
            ),
        );

        // bb1: 9000 filler
        for _ in 0..9000 {
            add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        }

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        let result = relax_branches(&mut func).unwrap();

        // bb0 offset should be 0.
        assert_eq!(result.block_offsets[0], 0);

        // bb1 offset = bb0 size. After relaxation bb0 has 2 instructions
        // (TBNZ + B), so bb1 offset = 8.
        assert_eq!(result.block_offsets[1], 8);

        // bb2 offset = bb1 offset + bb1 size = 8 + 9000*4 = 36008.
        assert_eq!(result.block_offsets[2], 36008);

        // Total instructions = 2 + 9000 + 1 = 9003.
        assert_eq!(result.instructions.len(), 9003);

        // Verify last block offset + last block size = total code size.
        let total_code_bytes = result.instructions.len() as u32 * 4;
        let last_block_end = result.block_offsets[2] + 4; // bb2 has 1 inst = 4 bytes
        assert_eq!(last_block_end, total_code_bytes);
    }
}

#[cfg(test)]
mod block_structured_tests {
    //! [`relax_out_of_range_branches`]: the three rewrites, the fixed point,
    //! the refusals, and the no-op on in-range code. Every relaxed function is
    //! also run through the pipeline's symbolic CFG authority
    //! (`validate_aarch64_mach_function`), which requires the stored
    //! successor/predecessor lists to equal the edges derived from the branch
    //! operands.

    use super::*;
    use crate::pipeline::{
        derive_ir_cfg_edges_from_branch_operands, install_ir_cfg_edges,
        validate_aarch64_mach_function,
    };
    use trust_cg_ir::regs::{X0, X9, X30};
    use trust_cg_ir::{CondCode, Signature};

    /// B.cond / CBZ / CBNZ reach at most this many instructions forward.
    const BCOND_MAX_INSTS: usize = (BCOND_MAX_RANGE / 4) as usize;
    /// TBZ / TBNZ reach at most this many instructions forward.
    const TBZ_MAX_INSTS: usize = (TBZ_MAX_RANGE / 4) as usize;

    fn function(blocks: usize) -> (MachFunction, Vec<BlockId>) {
        let mut func =
            MachFunction::new("relax_fixture".to_string(), Signature::new(vec![], vec![]));
        let mut ids = vec![func.entry];
        for _ in 1..blocks {
            ids.push(func.create_block());
        }
        (func, ids)
    }

    fn push(func: &mut MachFunction, block: BlockId, inst: MachInst) -> InstId {
        let id = func.push_inst(inst);
        func.append_inst(block, id);
        id
    }

    fn filler(func: &mut MachFunction, block: BlockId, count: usize) {
        for _ in 0..count {
            push(
                func,
                block,
                MachInst::new(
                    AArch64Opcode::AddRI,
                    vec![
                        MachOperand::PReg(X9),
                        MachOperand::PReg(X9),
                        MachOperand::Imm(1),
                    ],
                ),
            );
        }
    }

    fn ret(func: &mut MachFunction, block: BlockId) -> InstId {
        push(
            func,
            block,
            MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
        )
    }

    fn b(func: &mut MachFunction, block: BlockId, target: BlockId) -> InstId {
        push(
            func,
            block,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(target)]),
        )
    }

    /// A conditional branch of `opcode` to `target` in canonical operand form.
    fn conditional(opcode: AArch64Opcode, target: BlockId) -> MachInst {
        let operands = match opcode {
            AArch64Opcode::BCond => vec![
                MachOperand::Imm(CondCode::EQ.encoding() as i64),
                MachOperand::Block(target),
            ],
            AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
                vec![MachOperand::PReg(X0), MachOperand::Block(target)]
            }
            AArch64Opcode::Tbz | AArch64Opcode::Tbnz => vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(3),
                MachOperand::Block(target),
            ],
            other => panic!("{other:?} is not a conditional branch"),
        };
        MachInst::new(opcode, operands)
    }

    /// The maximum forward reach, in instructions, of `opcode`.
    fn reach(opcode: AArch64Opcode) -> usize {
        match opcode {
            AArch64Opcode::Tbz | AArch64Opcode::Tbnz => TBZ_MAX_INSTS,
            _ => BCOND_MAX_INSTS,
        }
    }

    /// Install the CFG the branch operands define, as the pipeline's
    /// authority expects of a function reaching branch resolution.
    fn seal(func: &mut MachFunction) {
        let edges = derive_ir_cfg_edges_from_branch_operands(func);
        install_ir_cfg_edges(func, edges);
        validate_aarch64_mach_function(func).expect("fixture must pass the CFG authority");
    }

    fn assert_in_range_and_valid(func: &MachFunction) {
        let offsets = laid_out_block_offsets(func);
        let far = find_out_of_range_branches(func, &offsets).expect("no unconditional overflow");
        assert!(far.is_empty(), "branches still out of range: {far:?}");
        validate_aarch64_mach_function(func).expect("relaxed function must pass the CFG authority");
    }

    fn succs(func: &MachFunction, block: BlockId) -> std::collections::BTreeSet<BlockId> {
        func.block(block).succs.iter().copied().collect()
    }

    fn opcodes(func: &MachFunction, block: BlockId) -> Vec<AArch64Opcode> {
        func.block(block)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect()
    }

    fn complement_of(opcode: AArch64Opcode) -> AArch64Opcode {
        match opcode {
            AArch64Opcode::BCond => AArch64Opcode::BCond,
            AArch64Opcode::Cbz => AArch64Opcode::Cbnz,
            AArch64Opcode::Cbnz => AArch64Opcode::Cbz,
            AArch64Opcode::Tbz => AArch64Opcode::Tbnz,
            AArch64Opcode::Tbnz => AArch64Opcode::Tbz,
            other => panic!("{other:?}"),
        }
    }

    const CONDITIONALS: [AArch64Opcode; 5] = [
        AArch64Opcode::BCond,
        AArch64Opcode::Cbz,
        AArch64Opcode::Cbnz,
        AArch64Opcode::Tbz,
        AArch64Opcode::Tbnz,
    ];

    /// `b0: bcc b2` falling into `b1: <filler> ; ret`, `b2: ret`. The branch
    /// sits at offset 0 and `b2` starts `filler + 1` instructions later.
    fn forward_over(opcode: AArch64Opcode, fill: usize) -> (MachFunction, Vec<BlockId>) {
        let (mut func, ids) = function(3);
        push(&mut func, ids[0], conditional(opcode, ids[2]));
        filler(&mut func, ids[1], fill);
        ret(&mut func, ids[1]);
        ret(&mut func, ids[2]);
        seal(&mut func);
        (func, ids)
    }

    #[test]
    fn a_function_already_in_range_is_left_byte_for_byte_untouched() {
        for opcode in CONDITIONALS {
            // `b2` is exactly at the maximum reach: in range, not relaxed.
            let (mut func, _) = forward_over(opcode, reach(opcode) - 2);
            let before = format!("{func:?}");
            let stats = relax_out_of_range_branches(&mut func).expect("in-range function");
            assert_eq!(stats, BranchRelaxStats::default(), "{opcode:?}");
            assert_eq!(format!("{func:?}"), before, "{opcode:?} function changed");
        }
    }

    #[test]
    fn fallthrough_form_complements_the_branch_and_jumps_over_a_far_b() {
        for opcode in CONDITIONALS {
            // One instruction past the maximum reach.
            let (mut func, ids) = forward_over(opcode, reach(opcode) - 1);
            let edges_before = succs(&func, ids[0]);
            let stats = relax_out_of_range_branches(&mut func).expect("relaxable");
            assert_eq!(
                stats,
                BranchRelaxStats {
                    rounds: 1,
                    fallthrough: 1,
                    swapped: 0,
                    split: 0,
                    islands: 0,
                },
                "{opcode:?}"
            );
            assert_eq!(
                opcodes(&func, ids[0]),
                vec![complement_of(opcode), AArch64Opcode::B],
                "{opcode:?}"
            );
            let inverted = func.inst(func.block(ids[0]).insts[0]);
            assert_eq!(
                inverted.operands.last(),
                Some(&MachOperand::Block(ids[1])),
                "{opcode:?}: the complemented branch skips the B into the fallthrough block"
            );
            if opcode == AArch64Opcode::BCond {
                assert_eq!(
                    inverted.operands[0],
                    MachOperand::Imm(CondCode::NE.encoding() as i64)
                );
            }
            let far = func.inst(func.block(ids[0]).insts[1]);
            assert_eq!(far.operands, vec![MachOperand::Block(ids[2])]);
            assert_eq!(
                succs(&func, ids[0]),
                edges_before,
                "{opcode:?}: edges unchanged"
            );
            assert_in_range_and_valid(&func);
        }
    }

    #[test]
    fn a_backward_far_branch_is_relaxed_too() {
        // b0 falls into b1 (filler), b2: cbnz x0, b1 (the far back-edge), b3: ret.
        let (mut func, ids) = function(4);
        filler(&mut func, ids[0], 1);
        filler(&mut func, ids[1], BCOND_MAX_INSTS + 2);
        push(&mut func, ids[2], conditional(AArch64Opcode::Cbnz, ids[1]));
        ret(&mut func, ids[3]);
        seal(&mut func);
        let stats = relax_out_of_range_branches(&mut func).expect("relaxable");
        assert_eq!(stats.fallthrough, 1);
        assert_eq!(
            opcodes(&func, ids[2]),
            vec![AArch64Opcode::Cbz, AArch64Opcode::B]
        );
        assert_eq!(
            func.inst(func.block(ids[2]).insts[0]).operands[1],
            MachOperand::Block(ids[3])
        );
        assert_eq!(
            func.inst(func.block(ids[2]).insts[1]).operands[0],
            MachOperand::Block(ids[1])
        );
        assert_in_range_and_valid(&func);
    }

    #[test]
    fn swap_form_exchanges_targets_when_the_other_one_is_near() {
        // b0: b.eq b4 ; b b2   b1: ret   b2: ret   b3: <filler>; ret   b4: ret
        let (mut func, ids) = function(5);
        push(&mut func, ids[0], conditional(AArch64Opcode::BCond, ids[4]));
        b(&mut func, ids[0], ids[2]);
        ret(&mut func, ids[1]);
        ret(&mut func, ids[2]);
        filler(&mut func, ids[3], BCOND_MAX_INSTS);
        ret(&mut func, ids[3]);
        ret(&mut func, ids[4]);
        seal(&mut func);
        let insts_before = func.block(ids[0]).insts.clone();
        let arena_before = func.insts.len();
        let stats = relax_out_of_range_branches(&mut func).expect("relaxable");
        assert_eq!(stats.swapped, 1);
        assert_eq!(stats.rewrites(), 1);
        // No instruction added: the same two instructions, retargeted.
        assert_eq!(func.block(ids[0]).insts, insts_before);
        assert_eq!(func.insts.len(), arena_before);
        let cond = func.inst(insts_before[0]);
        assert_eq!(
            cond.operands,
            vec![
                MachOperand::Imm(CondCode::NE.encoding() as i64),
                MachOperand::Block(ids[2])
            ]
        );
        assert_eq!(
            func.inst(insts_before[1]).operands,
            vec![MachOperand::Block(ids[4])]
        );
        assert_in_range_and_valid(&func);
    }

    #[test]
    fn split_form_when_both_targets_are_far() {
        // b0: b b2   b1: ret   b2: <filler>   b3: tbz x0,#3,b1 ; b b5
        // b4: <filler>; ret   b5: ret
        // The TBZ target b1 is far behind and the B target b5 far ahead.
        let (mut func, ids) = function(6);
        b(&mut func, ids[0], ids[2]);
        ret(&mut func, ids[1]);
        filler(&mut func, ids[2], TBZ_MAX_INSTS + 8);
        let tbz = push(&mut func, ids[3], conditional(AArch64Opcode::Tbz, ids[1]));
        let tail = b(&mut func, ids[3], ids[5]);
        filler(&mut func, ids[4], TBZ_MAX_INSTS + 8);
        ret(&mut func, ids[4]);
        ret(&mut func, ids[5]);
        seal(&mut func);
        let blocks_before = func.blocks.len();
        let stats = relax_out_of_range_branches(&mut func).expect("relaxable");
        assert_eq!(stats.split, 1, "{stats:?}");
        assert_eq!(func.blocks.len(), blocks_before + 1);
        let z = BlockId(blocks_before as u32);
        // Laid out immediately after the split block.
        let at = func.block_order.iter().position(|&b| b == ids[3]).unwrap();
        assert_eq!(func.block_order[at + 1], z);
        assert_eq!(func.block(z).insts, vec![tail]);
        assert_eq!(func.inst(tail).operands, vec![MachOperand::Block(ids[5])]);
        assert_eq!(func.block(ids[3]).insts[0], tbz);
        assert_eq!(
            opcodes(&func, ids[3]),
            vec![AArch64Opcode::Tbnz, AArch64Opcode::B]
        );
        assert_eq!(
            func.inst(tbz).operands,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(3),
                MachOperand::Block(z)
            ]
        );
        let far = func.block(ids[3]).insts[1];
        assert_eq!(func.inst(far).operands, vec![MachOperand::Block(ids[1])]);
        assert_eq!(succs(&func, ids[3]), [ids[1], z].into_iter().collect());
        assert_eq!(succs(&func, z), [ids[5]].into_iter().collect());
        assert_in_range_and_valid(&func);
    }

    #[test]
    fn a_relaxation_that_pushes_another_branch_out_of_range_reaches_a_fixed_point() {
        // b0: b b2          b1: <1 MiB filler>; ret
        // b2: tbz x0,#3,b5  (exactly at its maximum reach)
        // b3: b.eq b1       (far backward; falls into b4)
        // b4: <filler>      b5: ret
        // Relaxing the b.eq inserts one instruction inside the TBZ's span,
        // which pushes the TBZ one instruction past its reach: round two.
        let (mut func, ids) = function(6);
        b(&mut func, ids[0], ids[2]);
        filler(&mut func, ids[1], BCOND_MAX_INSTS + 2);
        ret(&mut func, ids[1]);
        push(&mut func, ids[2], conditional(AArch64Opcode::Tbz, ids[5]));
        push(&mut func, ids[3], conditional(AArch64Opcode::BCond, ids[1]));
        filler(&mut func, ids[4], TBZ_MAX_INSTS - 2);
        ret(&mut func, ids[5]);
        seal(&mut func);
        let offsets = laid_out_block_offsets(&func);
        let first = find_out_of_range_branches(&func, &offsets).unwrap();
        assert_eq!(first.len(), 1, "only the b.eq starts out of range");
        let stats = relax_out_of_range_branches(&mut func).expect("relaxable");
        assert_eq!(
            stats,
            BranchRelaxStats {
                rounds: 2,
                fallthrough: 2,
                swapped: 0,
                split: 0,
                islands: 0,
            }
        );
        assert_eq!(
            opcodes(&func, ids[2]),
            vec![AArch64Opcode::Tbnz, AArch64Opcode::B]
        );
        assert_eq!(
            opcodes(&func, ids[3]),
            vec![AArch64Opcode::BCond, AArch64Opcode::B]
        );
        assert_in_range_and_valid(&func);
    }

    #[test]
    fn a_swapped_branch_that_grows_out_of_range_is_split_next_round() {
        // b0: b.eq b5 ; b b2        (b5 far; b2 exactly at the b.eq's reach)
        // b1: <filler> ; cbz x0, b4 (far; falls into b2)
        // b2: ret   b3: <filler>   b4: ret   b5: ret
        //
        // Round 1 visits the cbz first (reverse layout order): fallthrough
        // form, one instruction inserted between b0 and b2. It then swaps the
        // b.eq onto b2, measured on the round's starting offsets. Round 2
        // finds b2 one instruction past the swapped b.ne's reach, and b5
        // still far: split, which is final.
        let (mut func, ids) = function(6);
        push(&mut func, ids[0], conditional(AArch64Opcode::BCond, ids[5]));
        b(&mut func, ids[0], ids[2]);
        // b0 holds 2 instructions, b1 `max - 2`: b2 starts exactly `max`
        // instructions after the b.eq.
        filler(&mut func, ids[1], BCOND_MAX_INSTS - 3);
        push(&mut func, ids[1], conditional(AArch64Opcode::Cbz, ids[4]));
        ret(&mut func, ids[2]);
        filler(&mut func, ids[3], BCOND_MAX_INSTS + 2);
        ret(&mut func, ids[4]);
        ret(&mut func, ids[5]);
        seal(&mut func);
        let stats = relax_out_of_range_branches(&mut func).expect("relaxable");
        assert_eq!(
            stats,
            BranchRelaxStats {
                rounds: 2,
                fallthrough: 1,
                swapped: 1,
                split: 1,
                islands: 0,
            }
        );
        // b0: b.eq Z ; b b2   Z: b b5 — taken still reaches b5, not taken b2.
        let z = BlockId(6);
        assert_eq!(func.block_order[1], z);
        let b0 = &func.block(ids[0]).insts;
        assert_eq!(
            func.inst(b0[0]).operands,
            vec![
                MachOperand::Imm(CondCode::EQ.encoding() as i64),
                MachOperand::Block(z)
            ]
        );
        assert_eq!(func.inst(b0[1]).operands, vec![MachOperand::Block(ids[2])]);
        let z_insts = &func.block(z).insts;
        assert_eq!(z_insts.len(), 1);
        assert_eq!(
            func.inst(z_insts[0]).operands,
            vec![MachOperand::Block(ids[5])]
        );
        assert_in_range_and_valid(&func);
    }

    #[test]
    fn the_far_b_is_inserted_before_trailing_loop_head_padding() {
        let (mut func, ids) = function(3);
        push(&mut func, ids[0], conditional(AArch64Opcode::Cbz, ids[2]));
        for _ in 0..2 {
            push(
                &mut func,
                ids[0],
                MachInst::new(AArch64Opcode::AlignNop, vec![]),
            );
        }
        filler(&mut func, ids[1], BCOND_MAX_INSTS);
        ret(&mut func, ids[1]);
        ret(&mut func, ids[2]);
        seal(&mut func);
        let stats = relax_out_of_range_branches(&mut func).expect("relaxable");
        assert_eq!(stats.fallthrough, 1);
        assert_eq!(
            opcodes(&func, ids[0]),
            vec![
                AArch64Opcode::Cbnz,
                AArch64Opcode::B,
                AArch64Opcode::AlignNop,
                AArch64Opcode::AlignNop
            ]
        );
        assert_in_range_and_valid(&func);
    }

    #[test]
    fn the_far_b_carries_the_conditionals_source_location_and_provenance() {
        let (mut func, ids) = forward_over(AArch64Opcode::Cbz, BCOND_MAX_INSTS);
        let cond = func.block(ids[0]).insts[0];
        let loc = trust_cg_ir::inst::SourceLoc {
            file: 0,
            line: 42,
            col: 7,
        };
        func.inst_mut(cond).source_loc = Some(loc);
        func.lowering_provenance
            .insert(cond, trust_cg_ir::LoweringProvenance::UNATTRIBUTED);
        relax_out_of_range_branches(&mut func).expect("relaxable");
        let far = func.block(ids[0]).insts[1];
        assert_eq!(func.inst(far).source_loc, Some(loc));
        assert_eq!(
            func.lowering_provenance.get(&far),
            func.lowering_provenance.get(&cond)
        );
    }

    #[test]
    fn b_cond_complement_is_the_irs_logical_complement_and_al_nv_are_refused() {
        const ALL: [CondCode; 16] = [
            CondCode::EQ,
            CondCode::NE,
            CondCode::HS,
            CondCode::LO,
            CondCode::MI,
            CondCode::PL,
            CondCode::VS,
            CondCode::VC,
            CondCode::HI,
            CondCode::LS,
            CondCode::GE,
            CondCode::LT,
            CondCode::GT,
            CondCode::LE,
            CondCode::AL,
            CondCode::NV,
        ];
        for cc in ALL {
            let inst = MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(cc.encoding() as i64),
                    MachOperand::Block(BlockId(0)),
                ],
            );
            match (complemented_conditional(&inst), cc.logical_complement()) {
                (Ok(complement), Some(expected)) => assert_eq!(
                    complement.operands[0],
                    MachOperand::Imm(expected.encoding() as i64),
                    "{cc:?}"
                ),
                (Err(_), None) => {}
                (got, expected) => panic!("{cc:?}: got {got:?}, expected {expected:?}"),
            }
        }
    }

    #[test]
    fn complemented_opcodes_keep_their_flags() {
        for opcode in CONDITIONALS {
            assert_eq!(
                opcode.default_flags(),
                complement_of(opcode).default_flags(),
                "{opcode:?}"
            );
        }
    }

    #[test]
    fn an_always_condition_is_refused_not_inverted() {
        let (mut func, ids) = function(3);
        push(
            &mut func,
            ids[0],
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(CondCode::AL.encoding() as i64),
                    MachOperand::Block(ids[2]),
                ],
            ),
        );
        filler(&mut func, ids[1], BCOND_MAX_INSTS);
        ret(&mut func, ids[1]);
        ret(&mut func, ids[2]);
        seal(&mut func);
        let error = relax_out_of_range_branches(&mut func).unwrap_err();
        assert!(
            matches!(error, BranchRelaxError::UnsupportedShape { .. }),
            "{error}"
        );
    }

    #[test]
    fn an_ordinary_tail_too_far_to_reach_an_island_is_refused() {
        // b0: b b2   b1: ret   b2: <filler>   b3: cbz x0, b1 ; add ; ret
        let (mut func, ids) = function(4);
        b(&mut func, ids[0], ids[2]);
        ret(&mut func, ids[1]);
        filler(&mut func, ids[2], BCOND_MAX_INSTS + 2);
        push(&mut func, ids[3], conditional(AArch64Opcode::Cbz, ids[1]));
        filler(&mut func, ids[3], BCOND_MAX_INSTS + 2);
        ret(&mut func, ids[3]);
        let error = relax_out_of_range_branches(&mut func).unwrap_err();
        assert!(
            matches!(&error, BranchRelaxError::UnsupportedShape { detail, .. } if detail.contains("AddRI")),
            "{error}"
        );
    }

    #[test]
    fn a_far_conditional_with_an_adr_tail_keeps_its_original_instruction_owners() {
        // The conditional crosses >1MiB; its ordinary tail is short and ends
        // in RET. Moving that tail would invalidate block-keyed custody.
        let (mut func, ids) = function(3);
        let cond = push(&mut func, ids[0], conditional(AArch64Opcode::Cbz, ids[2]));
        let adr = push(
            &mut func,
            ids[0],
            MachInst::new(
                AArch64Opcode::Adr,
                vec![MachOperand::PReg(X9), MachOperand::Imm(0)],
            ),
        );
        ret(&mut func, ids[0]);
        filler(&mut func, ids[1], BCOND_MAX_INSTS + 2);
        ret(&mut func, ids[1]);
        ret(&mut func, ids[2]);
        seal(&mut func);
        let original = func.block(ids[0]).insts.clone();
        let adr_before = format!("{:?}", func.inst(adr));
        let stats = relax_out_of_range_branches(&mut func)
            .expect("a nearby branch island preserves the tail");
        assert_eq!(stats.rewrites(), 1);
        assert_eq!(func.block(ids[0]).insts, original);
        assert_eq!(format!("{:?}", func.inst(adr)), adr_before);
        assert_eq!(func.inst(cond).opcode, AArch64Opcode::Cbz);
        assert_in_range_and_valid(&func);
    }

    #[test]
    fn a_far_branch_in_the_last_block_that_falls_off_the_end_is_refused() {
        // b0: b b2   b1: ret   b2: <filler> ; cbz x0, b1   (nothing after b2)
        let (mut func, ids) = function(3);
        b(&mut func, ids[0], ids[2]);
        ret(&mut func, ids[1]);
        filler(&mut func, ids[2], BCOND_MAX_INSTS + 2);
        push(&mut func, ids[2], conditional(AArch64Opcode::Cbz, ids[1]));
        let error = relax_out_of_range_branches(&mut func).unwrap_err();
        assert!(
            matches!(&error, BranchRelaxError::UnsupportedShape { detail, .. } if detail.contains("falls off")),
            "{error}"
        );
    }

    #[test]
    fn an_unconditional_branch_beyond_128_mib_is_refused() {
        let (mut func, ids) = function(2);
        b(&mut func, ids[0], ids[1]);
        ret(&mut func, ids[1]);
        // Offsets as if 128 MiB of code separated the two blocks.
        let offsets = vec![Some(0), Some(1i64 << 27)];
        let error = find_out_of_range_branches(&func, &offsets).unwrap_err();
        assert!(
            matches!(
                error,
                BranchRelaxError::UnconditionalOutOfRange {
                    opcode: AArch64Opcode::B,
                    displacement,
                    ..
                } if displacement == 1 << 27
            ),
            "{error}"
        );
    }
}
