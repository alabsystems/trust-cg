// trust-cg-verify/aarch64_switch_binding.rs - Per-compile switch-dispatch binding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-compile binding of AArch64 switch dispatch to the final bytes.
//!
//! The static `aarch64_jumptable_proofs` discharge the ADR ring identity and
//! the `LDRSW [Xn, Xm, LSL #2]` scaling; the ISel switch emitters run a
//! fail-closed structural gate that the normalized `value -> target` mapping
//! reproduces the source switch. Neither says anything about the words that
//! reach the object. This module reads the final little-endian A64 words of
//! one encoded function independently of the production encoder (bit
//! extraction only; register fields, immediates, widths and displacements come
//! from the words) and binds them to the machine-IR intent and the recorded
//! CFG:
//!
//! * **Jump table** (every `ADR Xd, JumpTableIndex(t)` site): the ADR lands on
//!   the table's recomputed position; every 32-bit table entry equals its
//!   target block's offset from the table base and the target is a recorded
//!   successor of the dispatch block; the block ends in `BR Xt`; the value in
//!   `Xt` was produced by `ADD Xt, Xbase, Xentry` whose operands were produced
//!   (through register copies) by that ADR and by `LDRSW Xentry, [Xbase, Xindex,
//!   LSL #2]` with the same base; the latest conditional branch before the
//!   load is `B.HI` to a recorded successor block start (and, when exactly one
//!   successor lies outside the table, to that block); its flags come from
//!   `CMP Xindex, #(len - 1)` (immediate or a MOVZ/MOVK/MOVN-materialized
//!   register) with no NZCV writer in between; the index value compared and
//!   the index value loaded have one origin; and, for a non-zero `min_val`,
//!   that origin is `SUB Xindex, Xsel, #min_val` (immediate or materialized).
//! * **Compare dispatch** (every `CMP` whose flags reach a `B.cond` in the
//!   same block, which is how the linear-scan and binary-search leaves and
//!   pivots are emitted): the compare word's register, width and immediate or
//!   register operand match the intent, a register operand materialized by a
//!   move-wide chain composes to the intended constant, every conditional
//!   branch consuming those flags matches its intended condition and
//!   displacement with no intervening NZCV writer, and its target is a laid-out
//!   recorded successor or a branch internal to the block.
//! * **Fused compare-and-branch** (`CBZ`/`CBNZ`/`TBZ`/`TBNZ`, which the
//!   cmp-branch fusion pass emits for `case 0` leaves): register, width, bit
//!   and displacement match the intent.
//! * **No unbound `BR`**: every `BR` word or intent must be the terminator of
//!   a jump-table dispatch bound above; the lowering emits `BR` for nothing
//!   else.
//!
//! Register dataflow is followed backwards inside the dispatch block. An
//! intervening word clobbers a register when either the independently decoded
//! word or the machine-IR def model writes it, so both models must agree that
//! the value is untouched. A word outside the modeled encoding classes refuses
//! the binding instead of being assumed harmless. Origins follow 64-bit
//! `MOV Xd, Xm` copies whose intent is the same `MovR`/`MOVXrr` copy, and
//! register-allocation spill reloads: an `LDR`/`LDUR Xt, [Xn, #imm]` whose
//! intent is a `SPILL_SLOT_ACCESS`-flagged `LdrRI` of the same register and
//! address, with a base other than `SP`. A flagged slot is private to the
//! frame. Scanning back from the reload over words that cannot write memory
//! (data processing, single-register immediate loads, non-linking branches)
//! and over immediate stores through the same, unrewritten base register to
//! disjoint bytes, the first possible writer of the slot is either a 64-bit
//! `STR`/`STUR` of exactly that slot (the origin continues at its data
//! register) or anything else (calls, pairs, atomics, other bases): the
//! reload's value is then opaque, and two reloads of the slot are one value
//! only when they see the same writer and the same base value. Move-wide
//! constant chains are evaluated forwards from their MOVZ/MOVN base with each
//! word's own width. A chain word binds to every intent the encoder spells as
//! that word: a MOVZ at `LSL #0` is the canonical `Movz` or one of the
//! shift-free two-operand forms `MovI`, `MOVZWi` and `MOVZXi` (the same
//! intent class the decode check and the constant-materialization proofs
//! use); MOVN and MOVK bind only to `Movn` and `Movk`.
//!
//! Boundaries: this binds bytes to the final machine-IR intent and the
//! recorded CFG. Which block is the source `default` and which case constant
//! routes to which source block is established at ISel by the switch
//! normalization gate and by the static proofs; late passes that retarget or
//! merge blocks keep the intent, not a copy of the source map, so no source
//! map is consulted here. Two exchanged recorded successors are not told apart
//! (the same limit as the layout cross-check), and in a table with holes,
//! whose default block is also a table target, the bounds branch is bound
//! only to some recorded successor. A bounds branch relaxed into an
//! inverted branch over a `B` is refused, not modeled. The loaded entry's
//! value is bound through the table bytes, not through a memory model. The
//! recorded CFG is trusted as given: a conditional branch to an unrecorded
//! block is refused, and one landing on the end of its own block (the next
//! laid-out block start) is accepted as block-internal.
//!
//! Decoder reference: Arm A64 ISA (aarchmrs v2025-03_rel): ADR, ADD/SUB and
//! CMP (immediate and shifted register), ORR (shifted register) MOV alias,
//! MOVN/MOVZ/MOVK, LDRSW (register), LDR/STR (immediate, unsigned offset),
//! LDUR/STUR, B, B.cond, BR/BLR/RET, CBZ/CBNZ, TBZ/TBNZ, and the top-level
//! group classification used for register, NZCV and memory write sets.

use std::collections::HashMap;

use trust_cg_ir::aarch64_regs::{hw_encoding, preg_class};
use trust_cg_ir::function::JumpTableData;
use trust_cg_ir::{
    AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, RegClass, SpecialReg,
};

/// What one function's final bytes bound.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SwitchBindingReport {
    /// Jump-table dispatch sites bound end to end (ADR, table, bounds, BR).
    pub jump_tables: usize,
    /// Table entries bound to their target block offsets.
    pub table_entries: usize,
    /// Compares whose flags reach at least one bound conditional branch.
    pub compare_groups: usize,
    /// Conditional branches bound to a compare in the same block.
    pub compare_consumers: usize,
    /// Move-wide chains bound as the register operand of a compare or a
    /// jump-table bounds/normalization constant.
    pub materialized_constants: usize,
    /// `CBZ`/`CBNZ`/`TBZ`/`TBNZ` words bound to their intent.
    pub fused_branches: usize,
}

/// A refused binding. Every variant fails the encode closed.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SwitchBindingError {
    #[error("invalid local table-address expansion: {0}")]
    AddressExpansion(String),
    #[error("final layout has {layout} body bytes but the image has only {image}")]
    ImageTooShort { layout: usize, image: usize },
    #[error(
        "jump table {table} referenced by the ADR at byte {offset} does not exist ({count} tables)"
    )]
    MissingJumpTable {
        offset: u32,
        table: u32,
        count: usize,
    },
    #[error("jump table {table} needs bytes {start}..{end} but the image has {image}")]
    TableTruncated {
        table: u32,
        start: usize,
        end: usize,
        image: usize,
    },
    #[error(
        "word {word:#010x} at byte {offset} is outside the modeled A64 encoding classes; {what} cannot be bound"
    )]
    UnmodeledWord {
        offset: u32,
        word: u32,
        what: &'static str,
    },
    #[error("byte {offset}: {what} decodes as `{decoded}` but the intent is `{intent}`")]
    IntentMismatch {
        offset: u32,
        what: &'static str,
        decoded: String,
        intent: String,
    },
    #[error(
        "jump table {table}: ADR at byte {offset} addresses byte {encoded} but the table lies at {layout}"
    )]
    TableAddress {
        table: u32,
        offset: u32,
        encoded: i64,
        layout: u32,
    },
    #[error(
        "jump table {table}: entry {entry} encodes {encoded} (byte {lands}) but target {target:?} starts at byte {expected}"
    )]
    TableEntry {
        table: u32,
        entry: usize,
        encoded: i32,
        lands: i64,
        target: BlockId,
        expected: u32,
    },
    #[error("jump table {table}: entry {entry} target {target:?} is not laid out")]
    TableTargetNotLaidOut {
        table: u32,
        entry: usize,
        target: BlockId,
    },
    #[error(
        "jump table {table}: entry {entry} target {target:?} is not a recorded successor of dispatch block {block:?}"
    )]
    TableTargetNotSuccessor {
        table: u32,
        entry: usize,
        target: BlockId,
        block: BlockId,
    },
    #[error("jump table {table}: dispatch block {block:?} does not end in BR")]
    DispatchTerminator { table: u32, block: BlockId },
    #[error("jump table {table}: {what} (byte {offset}): {detail}")]
    Chain {
        table: u32,
        what: &'static str,
        offset: u32,
        detail: String,
    },
    #[error("jump table {table}: bounds check (byte {offset}): {detail}")]
    Bounds {
        table: u32,
        offset: u32,
        detail: String,
    },
    #[error("jump table {table}: index normalization (byte {offset}): {detail}")]
    Normalization {
        table: u32,
        offset: u32,
        detail: String,
    },
    #[error(
        "byte {offset}: {what} constant register x{reg} is not materialized by a move-wide chain: {detail}"
    )]
    Constant {
        offset: u32,
        what: &'static str,
        reg: u8,
        detail: String,
    },
    #[error(
        "byte {offset}: conditional branch lands at byte {target}, which is neither a recorded successor block start of {block:?} nor inside the block"
    )]
    BranchTarget {
        offset: u32,
        target: i64,
        block: BlockId,
    },
    #[error(
        "byte {offset}: indirect branch {word:#010x} (intent {intent}) is not the terminator of a bound jump-table dispatch"
    )]
    UnboundIndirectBranch {
        offset: u32,
        word: u32,
        intent: String,
    },
}

type Result<T> = std::result::Result<T, SwitchBindingError>;

// ===========================================================================
// Independent word decoding
// ===========================================================================

#[inline]
fn bits(word: u32, hi: u32, lo: u32) -> u32 {
    (word >> lo) & ((1u32 << (hi - lo + 1)) - 1)
}

#[inline]
fn sext(value: u32, width: u32) -> i64 {
    let shift = 64 - width;
    ((i64::from(value)) << shift) >> shift
}

/// The A64 condition code `HI` (unsigned higher).
const COND_HI: u32 = 0b1000;

/// Words this module interprets field by field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Word {
    /// ADD/ADDS/SUB/SUBS (immediate).
    AddSubImm {
        sf: u32,
        sub: bool,
        flags: bool,
        sh: u32,
        imm12: u32,
        rn: u8,
        rd: u8,
    },
    /// ADD/ADDS/SUB/SUBS (shifted register).
    AddSubReg {
        sf: u32,
        sub: bool,
        flags: bool,
        shift: u32,
        rm: u8,
        imm6: u32,
        rn: u8,
        rd: u8,
    },
    /// AND/ORR/EOR/ANDS and their inverted forms (shifted register).
    LogicalReg {
        sf: u32,
        opc: u32,
        shift: u32,
        n: u32,
        rm: u8,
        imm6: u32,
        rn: u8,
        rd: u8,
    },
    /// MOVN (opc 00), MOVZ (10), MOVK (11).
    MoveWide {
        sf: u32,
        opc: u32,
        hw: u32,
        imm16: u32,
        rd: u8,
    },
    /// ADR (byte displacement).
    Adr { imm: i64, rd: u8 },
    /// B.cond (word displacement).
    CondBranch { imm19: i64, cond: u32 },
    /// B / BL (word displacement).
    Branch { link: bool, imm26: i64 },
    /// CBZ / CBNZ.
    CmpBranch {
        sf: u32,
        nonzero: bool,
        imm19: i64,
        rt: u8,
    },
    /// TBZ / TBNZ.
    TestBranch {
        bit: u32,
        nonzero: bool,
        imm14: i64,
        rt: u8,
    },
    /// BR (opc 0), BLR (1), RET (2).
    BranchReg { opc: u32, rn: u8 },
    /// LDRSW (register offset).
    LdrswRegOffset {
        rm: u8,
        option: u32,
        s: u32,
        rn: u8,
        rt: u8,
    },
    /// Exception generation (BRK, SVC, ...).
    Exception,
    /// Any other word; classified only by [`effects`].
    Other,
}

fn decode(word: u32) -> Word {
    let rd = bits(word, 4, 0) as u8;
    let rn = bits(word, 9, 5) as u8;
    let rm = bits(word, 20, 16) as u8;
    let sf = bits(word, 31, 31);
    if bits(word, 28, 24) == 0b10000 && sf == 0 {
        let immlo = bits(word, 30, 29);
        let immhi = bits(word, 23, 5);
        return Word::Adr {
            imm: sext((immhi << 2) | immlo, 21),
            rd,
        };
    }
    if bits(word, 28, 23) == 0b100010 {
        return Word::AddSubImm {
            sf,
            sub: bits(word, 30, 30) == 1,
            flags: bits(word, 29, 29) == 1,
            sh: bits(word, 22, 22),
            imm12: bits(word, 21, 10),
            rn,
            rd,
        };
    }
    if bits(word, 28, 23) == 0b100101 {
        return Word::MoveWide {
            sf,
            opc: bits(word, 30, 29),
            hw: bits(word, 22, 21),
            imm16: bits(word, 20, 5),
            rd,
        };
    }
    if bits(word, 28, 24) == 0b01011 && bits(word, 21, 21) == 0 {
        return Word::AddSubReg {
            sf,
            sub: bits(word, 30, 30) == 1,
            flags: bits(word, 29, 29) == 1,
            shift: bits(word, 23, 22),
            rm,
            imm6: bits(word, 15, 10),
            rn,
            rd,
        };
    }
    if bits(word, 28, 24) == 0b01010 {
        return Word::LogicalReg {
            sf,
            opc: bits(word, 30, 29),
            shift: bits(word, 23, 22),
            n: bits(word, 21, 21),
            rm,
            imm6: bits(word, 15, 10),
            rn,
            rd,
        };
    }
    if bits(word, 31, 24) == 0b0101_0100 && bits(word, 4, 4) == 0 {
        return Word::CondBranch {
            imm19: sext(bits(word, 23, 5), 19),
            cond: bits(word, 3, 0),
        };
    }
    if bits(word, 30, 26) == 0b00101 {
        return Word::Branch {
            link: sf == 1,
            imm26: sext(bits(word, 25, 0), 26),
        };
    }
    if bits(word, 30, 25) == 0b011010 {
        return Word::CmpBranch {
            sf,
            nonzero: bits(word, 24, 24) == 1,
            imm19: sext(bits(word, 23, 5), 19),
            rt: rd,
        };
    }
    if bits(word, 30, 25) == 0b011011 {
        return Word::TestBranch {
            bit: (sf << 5) | bits(word, 23, 19),
            nonzero: bits(word, 24, 24) == 1,
            imm14: sext(bits(word, 18, 5), 14),
            rt: rd,
        };
    }
    if bits(word, 31, 25) == 0b1101011 && bits(word, 20, 10) == 0b11111_000000 && rd == 0 {
        return Word::BranchReg {
            opc: bits(word, 24, 21),
            rn,
        };
    }
    if bits(word, 31, 24) == 0b1101_0100 {
        return Word::Exception;
    }
    // LDRSW (register): size 10, 111, V 0, 00, opc 10, 1, Rm, option, S, 10, Rn, Rt.
    if bits(word, 31, 21) == 0b101_1100_0101 && bits(word, 11, 10) == 0b10 {
        return Word::LdrswRegOffset {
            rm,
            option: bits(word, 15, 13),
            s: bits(word, 12, 12),
            rn,
            rt: rd,
        };
    }
    Word::Other
}

/// Register and flag write set of one word, independent of the encoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct Effects {
    /// Bit `n` set when general register `n` (0..=30) is written.
    writes: u32,
    /// The word writes NZCV.
    nzcv: bool,
}

#[inline]
fn reg_mask(reg: u32) -> u32 {
    if reg < 31 { 1 << reg } else { 0 }
}

/// Classify an arbitrary A64 word by its top-level encoding group. `None`
/// means the word is outside the modeled classes (reserved, SVE, SME or
/// unallocated space); a binding that has to cross such a word refuses.
///
/// The write sets over-approximate inside a group (a store's data register is
/// never reported, but for example every atomic memory word reports `Rt`),
/// which can only add refusals.
fn effects(word: u32) -> Option<Effects> {
    let rd = bits(word, 4, 0);
    let rn = bits(word, 9, 5);
    let rt2 = bits(word, 14, 10);
    let rs = bits(word, 20, 16);
    let mut fx = Effects::default();
    match bits(word, 28, 25) {
        // Data processing — immediate.
        0b1000 | 0b1001 => {
            match bits(word, 25, 23) {
                0b010 => fx.nzcv = bits(word, 29, 29) == 1,
                0b100 => fx.nzcv = bits(word, 30, 29) == 0b11,
                _ => {}
            }
            fx.writes = reg_mask(rd);
        }
        // Branches, exception generating and system.
        0b1010 | 0b1011 => {
            if bits(word, 30, 26) == 0b00101 {
                if bits(word, 31, 31) == 1 {
                    fx.writes = reg_mask(30);
                }
            } else if bits(word, 31, 24) == 0b0101_0100
                || bits(word, 30, 25) == 0b011010
                || bits(word, 30, 25) == 0b011011
                || bits(word, 31, 24) == 0b1101_0100
            {
                // B.cond, CBZ/CBNZ, TBZ/TBNZ, exception generation.
            } else if bits(word, 31, 22) == 0b11_0101_0100 {
                if bits(word, 21, 21) == 1 {
                    // MRS / SYSL read a system register into Rt.
                    fx.writes = reg_mask(rd);
                } else if bits(word, 20, 20) == 1 {
                    // MSR (register): NZCV is one of its targets; conservative.
                    fx.nzcv = true;
                }
            } else if bits(word, 31, 25) == 0b1101011 {
                if bits(word, 24, 21) == 0b0001 {
                    fx.writes = reg_mask(30);
                }
            } else {
                return None;
            }
        }
        // Loads and stores.
        0b0100 | 0b0110 | 0b1100 | 0b1110 => {
            let v = bits(word, 26, 26);
            let op2 = bits(word, 24, 23);
            match bits(word, 29, 28) {
                0b00 => {
                    if v == 1 {
                        // Advanced SIMD structure loads/stores: post-index writes Rn.
                        if op2 & 1 == 1 {
                            fx.writes = reg_mask(rn);
                        }
                    } else if bits(word, 31, 28) == 0b1101 && op2 & 0b10 != 0 {
                        // Memory tagging: conservative.
                        fx.writes = reg_mask(rd) | reg_mask(rn);
                    } else {
                        // Exclusive / ordered / compare-and-swap: conservative.
                        fx.writes = reg_mask(rd) | reg_mask(rt2) | reg_mask(rs);
                    }
                }
                0b01 => {
                    if op2 & 0b10 == 0 {
                        if v == 0 {
                            fx.writes = reg_mask(rd);
                        }
                    } else if bits(word, 23, 22) != 0 {
                        fx.writes = reg_mask(rd);
                    }
                }
                0b10 => {
                    if v == 0 && bits(word, 22, 22) == 1 {
                        fx.writes = reg_mask(rd) | reg_mask(rt2);
                    }
                    if op2 == 0b01 || op2 == 0b11 {
                        fx.writes |= reg_mask(rn);
                    }
                }
                _ => {
                    let opc = bits(word, 23, 22);
                    let op4 = bits(word, 11, 10);
                    if op2 & 0b10 != 0 {
                        if v == 0 && opc != 0 {
                            fx.writes = reg_mask(rd);
                        }
                    } else if bits(word, 21, 21) == 0 {
                        if v == 0 && opc != 0 {
                            fx.writes = reg_mask(rd);
                        }
                        if op4 == 0b01 || op4 == 0b11 {
                            fx.writes |= reg_mask(rn);
                        }
                    } else {
                        match op4 {
                            0b00 => {
                                if v == 0 {
                                    fx.writes = reg_mask(rd);
                                }
                            }
                            0b10 => {
                                if v == 0 && opc != 0 {
                                    fx.writes = reg_mask(rd);
                                }
                            }
                            _ => {
                                fx.writes = reg_mask(rd);
                                if bits(word, 11, 11) == 1 {
                                    fx.writes |= reg_mask(rn);
                                }
                            }
                        }
                    }
                }
            }
        }
        // Data processing — register.
        0b0101 | 0b1101 => {
            if bits(word, 28, 28) == 1 {
                match bits(word, 24, 21) {
                    0b0000 => {
                        fx.nzcv = bits(word, 29, 29) == 1;
                        fx.writes = reg_mask(rd);
                    }
                    0b0010 => fx.nzcv = true,
                    0b0100 => fx.writes = reg_mask(rd),
                    0b0110 => {
                        fx.nzcv = bits(word, 29, 29) == 1;
                        fx.writes = reg_mask(rd);
                    }
                    op2 if op2 & 0b1000 != 0 => fx.writes = reg_mask(rd),
                    _ => return None,
                }
            } else if bits(word, 24, 24) == 0 {
                fx.nzcv = bits(word, 30, 29) == 0b11;
                fx.writes = reg_mask(rd);
            } else {
                fx.nzcv = bits(word, 29, 29) == 1;
                fx.writes = reg_mask(rd);
            }
        }
        // Data processing — scalar floating-point and Advanced SIMD.
        0b0111 | 0b1111 => {
            let scalar_fp = bits(word, 31, 24) == 0b0001_1110 && bits(word, 21, 21) == 1;
            if scalar_fp && (bits(word, 13, 10) == 0b1000 || bits(word, 11, 10) == 0b01) {
                fx.nzcv = true;
            }
            if bits(word, 30, 24) == 0b001_1110
                && bits(word, 21, 21) == 1
                && bits(word, 15, 10) == 0
            {
                fx.writes = reg_mask(rd);
            }
            if bits(word, 31, 31) == 0
                && bits(word, 28, 21) == 0b0111_0000
                && bits(word, 15, 15) == 0
                && bits(word, 10, 10) == 1
            {
                fx.writes = reg_mask(rd);
            }
        }
        _ => return None,
    }
    Some(fx)
}

// ===========================================================================
// Layout and intent
// ===========================================================================

/// One emitted (non-pseudo) instruction with its final word.
#[derive(Clone, Copy)]
struct Emitted<'a> {
    id: trust_cg_ir::InstId,
    offset: u32,
    inst: &'a MachInst,
    word: u32,
}

struct Layout<'a> {
    /// Emitted instructions per block, in `block_order`.
    blocks: Vec<(BlockId, Vec<Emitted<'a>>)>,
    block_offset: HashMap<BlockId, u32>,
    starts: HashMap<u32, Vec<BlockId>>,
    body_len: usize,
}

impl<'a> Layout<'a> {
    fn derive(func: &'a MachFunction, code: &[u8]) -> Result<Self> {
        let mut blocks = Vec::with_capacity(func.block_order.len());
        let mut block_offset = HashMap::new();
        let mut starts: HashMap<u32, Vec<BlockId>> = HashMap::new();
        let mut offset = 0u32;
        for &block in &func.block_order {
            block_offset.insert(block, offset);
            starts.entry(offset).or_default().push(block);
            let mut emitted = Vec::new();
            for &id in &func.block(block).insts {
                let inst = func.inst(id);
                if inst.is_pseudo() {
                    continue;
                }
                let at = offset as usize;
                let word = code
                    .get(at..at + 4)
                    .and_then(|bytes| <[u8; 4]>::try_from(bytes).ok())
                    .map(u32::from_le_bytes)
                    .ok_or(SwitchBindingError::ImageTooShort {
                        layout: at + 4,
                        image: code.len(),
                    })?;
                emitted.push(Emitted {
                    id,
                    offset,
                    inst,
                    word,
                });
                offset = offset
                    .checked_add(4)
                    .ok_or(SwitchBindingError::ImageTooShort {
                        layout: usize::MAX,
                        image: code.len(),
                    })?;
            }
            blocks.push((block, emitted));
        }
        Ok(Self {
            blocks,
            block_offset,
            starts,
            body_len: offset as usize,
        })
    }

    /// The laid-out block that starts at `offset` and is a recorded
    /// successor of `block`, if any.
    fn successor_at(&self, func: &MachFunction, block: BlockId, offset: i64) -> Option<BlockId> {
        let offset = u32::try_from(offset).ok()?;
        let succs = &func.block(block).succs;
        self.starts
            .get(&offset)?
            .iter()
            .copied()
            .find(|candidate| succs.contains(candidate))
    }
}

/// `(hardware number, width in bits)` of a general-register operand.
fn gpr(op: &MachOperand) -> Option<(u8, u32)> {
    match op {
        MachOperand::PReg(p) => match preg_class(*p) {
            RegClass::Gpr64 => Some((hw_encoding(*p), 64)),
            RegClass::Gpr32 => Some((hw_encoding(*p), 32)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::SP | SpecialReg::XZR) => Some((31, 64)),
        MachOperand::Special(SpecialReg::WZR) => Some((31, 32)),
        _ => None,
    }
}

fn gpr_at(inst: &MachInst, index: usize) -> Option<(u8, u32)> {
    inst.operands.get(index).and_then(gpr)
}

fn imm_at(inst: &MachInst, index: usize) -> Option<i64> {
    inst.operands.get(index).and_then(MachOperand::as_imm)
}

/// General registers the machine-IR def model says `inst` writes.
fn intent_writes(inst: &MachInst) -> u32 {
    let mut mask = 0u32;
    trust_cg_opt::effects::aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some((reg, _)) = gpr_at(inst, pos) {
            mask |= reg_mask(u32::from(reg));
        }
    });
    for preg in inst.implicit_defs {
        if matches!(preg_class(*preg), RegClass::Gpr32 | RegClass::Gpr64) {
            mask |= reg_mask(u32::from(hw_encoding(*preg)));
        }
    }
    mask
}

fn intent_text(inst: &MachInst) -> String {
    format!("{:?} {:?}", inst.opcode, inst.operands)
}

fn mismatch(e: &Emitted<'_>, what: &'static str, decoded: impl Into<String>) -> SwitchBindingError {
    SwitchBindingError::IntentMismatch {
        offset: e.offset,
        what,
        decoded: decoded.into(),
        intent: intent_text(e.inst),
    }
}

fn word_effects(e: &Emitted<'_>, what: &'static str) -> Result<Effects> {
    effects(e.word).ok_or(SwitchBindingError::UnmodeledWord {
        offset: e.offset,
        word: e.word,
        what,
    })
}

/// Combined write set: the decoded word's and the intent's.
fn writes_of(e: &Emitted<'_>, what: &'static str) -> Result<u32> {
    Ok(word_effects(e, what)?.writes | intent_writes(e.inst))
}

/// Latest position before `before` whose word or intent writes `reg`.
fn latest_writer(
    es: &[Emitted<'_>],
    before: usize,
    reg: u8,
    what: &'static str,
) -> Result<Option<usize>> {
    let mask = reg_mask(u32::from(reg));
    for i in (0..before).rev() {
        if writes_of(&es[i], what)? & mask != 0 {
            return Ok(Some(i));
        }
    }
    Ok(None)
}

/// Latest position before `before` whose word writes NZCV.
fn latest_nzcv_writer(
    es: &[Emitted<'_>],
    before: usize,
    what: &'static str,
) -> Result<Option<usize>> {
    for i in (0..before).rev() {
        if word_effects(&es[i], what)?.nzcv {
            return Ok(Some(i));
        }
    }
    Ok(None)
}

/// Where a value comes from, followed backwards through 64-bit register
/// copies and spill-slot round trips inside the block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Origin {
    /// Written into `reg` by the word at `writer`, or a block live-in when
    /// `writer` is `None`.
    Reg { writer: Option<usize>, reg: u8 },
    /// Read by a spill reload from the 8-byte slot `[base_reg + offset]`
    /// whose store is not in the block: `base_reg` holds what the word at
    /// `base_writer` wrote (a live-in when `None`), and no word after `epoch`
    /// (the block start when `None`) and before the reload can write the
    /// slot's bytes. Two reloads with one `Slot` origin read one value.
    Slot {
        base_writer: Option<usize>,
        base_reg: u8,
        offset: i64,
        epoch: Option<usize>,
    },
}

impl Origin {
    /// The producing position and register of a value written in the block.
    fn produced(self) -> Option<(usize, u8)> {
        match self {
            Origin::Reg {
                writer: Some(writer),
                reg,
            } => Some((writer, reg)),
            _ => None,
        }
    }
}

/// A single-register load or store with an immediate offset and no base
/// writeback: `LDR`/`STR` (unsigned offset) or `LDUR`/`STUR` (unscaled),
/// general or FP/SIMD, including the sign-extending loads and `PRFM`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ImmAccess {
    store: bool,
    /// A 64-bit general-register `LDR Xt`/`STR Xt` transfer.
    x_form: bool,
    bytes: i64,
    offset: i64,
    rn: u8,
    rt: u8,
}

fn decode_imm_access(word: u32) -> Option<ImmAccess> {
    if bits(word, 29, 27) != 0b111 {
        return None;
    }
    let size = bits(word, 31, 30);
    let v = bits(word, 26, 26) == 1;
    let opc = bits(word, 23, 22);
    let (store, bytes) = if v {
        match (opc, size) {
            (0b00 | 0b01, _) => (opc == 0b00, 1i64 << size),
            (0b10 | 0b11, 0b00) => (opc == 0b10, 16),
            _ => return None,
        }
    } else {
        match (opc, size) {
            (0b00 | 0b01, _) | (0b10, _) | (0b11, 0b00..=0b10) => (opc == 0b00, 1i64 << size),
            _ => return None,
        }
    };
    let offset = match bits(word, 25, 24) {
        0b01 => i64::from(bits(word, 21, 10)) * bytes,
        0b00 if bits(word, 21, 21) == 0 && bits(word, 11, 10) == 0b00 => {
            sext(bits(word, 20, 12), 9)
        }
        _ => return None,
    };
    Some(ImmAccess {
        store,
        x_form: !v && size == 0b11 && opc <= 0b01,
        bytes,
        offset,
        rn: bits(word, 9, 5) as u8,
        rt: bits(word, 4, 0) as u8,
    })
}

/// Whether a word can write memory, classified by its encoding group.
enum MemWrite {
    /// Data processing, a load, `PRFM`, a non-linking branch or `NOP`.
    No,
    /// A single-register immediate store ([`decode_imm_access`]).
    Store(ImmAccess),
    /// Anything else, including every call, pair, exclusive, atomic,
    /// writeback, register-offset and system word: assumed to write any byte.
    Unknown,
}

fn memory_write(e: &Emitted<'_>) -> MemWrite {
    let intent_writes = e.inst.writes_memory() || e.inst.flags.is_call();
    match bits(e.word, 28, 25) {
        0b1000 | 0b1001 | 0b0101 | 0b1101 | 0b0111 | 0b1111 if !intent_writes => MemWrite::No,
        0b1010 | 0b1011 if !intent_writes => match decode(e.word) {
            Word::CondBranch { .. }
            | Word::CmpBranch { .. }
            | Word::TestBranch { .. }
            | Word::Branch { link: false, .. }
            | Word::BranchReg { opc: 0 | 2, .. } => MemWrite::No,
            _ if e.word == 0xd503_201f => MemWrite::No,
            _ => MemWrite::Unknown,
        },
        0b0100 | 0b0110 | 0b1100 | 0b1110 => match decode_imm_access(e.word) {
            Some(access) if access.store => MemWrite::Store(access),
            Some(_) if !intent_writes => MemWrite::No,
            _ => MemWrite::Unknown,
        },
        _ => MemWrite::Unknown,
    }
}

/// The `[base, #offset]` a single-register immediate load or store intent
/// names, in either operand form frame lowering leaves.
fn intent_address(inst: &MachInst) -> Option<(u8, i64)> {
    match (
        inst.operands.len(),
        inst.operands.get(1),
        inst.operands.get(2),
    ) {
        (2, Some(MachOperand::MemOp { base, offset }), None) => {
            match gpr(&MachOperand::PReg(*base))? {
                (reg, 64) => Some((reg, *offset)),
                _ => None,
            }
        }
        (2 | 3, Some(base), offset) => {
            let (reg, width) = gpr(base)?;
            let offset = match offset {
                None => 0,
                Some(MachOperand::Imm(k)) => *k,
                _ => return None,
            };
            (width == 64).then_some((reg, offset))
        }
        _ => None,
    }
}

/// The source of `MOV Xd, Xm` (`ORR Xd, XZR, Xm`) writing `reg`, when its
/// intent is the same 64-bit `MovR`/`MOVXrr` copy.
fn copy_source(e: &Emitted<'_>, reg: u8) -> Option<u8> {
    let Word::LogicalReg {
        sf: 1,
        opc: 0b01,
        shift: 0,
        n: 0,
        rm,
        imm6: 0,
        rn: 31,
        rd,
    } = decode(e.word)
    else {
        return None;
    };
    let intent_ok = matches!(e.inst.opcode, AArch64Opcode::MovR | AArch64Opcode::MOVXrr)
        && gpr_at(e.inst, 0) == Some((rd, 64))
        && gpr_at(e.inst, 1) == Some((rm, 64));
    (rd == reg && intent_ok).then_some(rm)
}

/// `LDR Xt, [Xn, #offset]` writing `reg` from a register-allocation spill
/// slot: the intent is a `SPILL_SLOT_ACCESS`-flagged `LdrRI` of the same
/// register and address, and the base is not `SP` (whose writes the
/// register write sets do not track). A flagged slot is private to the
/// frame, so only this thread's words can change its bytes.
fn spill_reload(e: &Emitted<'_>, reg: u8) -> Option<ImmAccess> {
    let access = decode_imm_access(e.word)?;
    let ok = !access.store
        && access.x_form
        && access.rt == reg
        && access.rn != 31
        && e.inst.opcode == AArch64Opcode::LdrRI
        && e.inst.flags.is_spill_slot_access()
        && gpr_at(e.inst, 0) == Some((access.rt, 64))
        && intent_address(e.inst) == Some((access.rn, access.offset));
    ok.then_some(access)
}

/// The data register of `STR Xt, [Xn, #offset]` when its intent is the same
/// 64-bit `StrRI`.
fn store_source(e: &Emitted<'_>, access: ImmAccess) -> Option<u8> {
    let ok = access.store
        && access.x_form
        && e.inst.opcode == AArch64Opcode::StrRI
        && gpr_at(e.inst, 0) == Some((access.rt, 64))
        && intent_address(e.inst) == Some((access.rn, access.offset));
    ok.then_some(access.rt)
}

enum SlotSource {
    /// The store at `at` wrote `reg` into the slot the reload reads.
    Store { reg: u8, at: usize },
    /// No store to the slot is visible in the block.
    Slot(Origin),
}

/// What the spill reload `access` at `reload_pos` reads: scan back over
/// words that cannot write memory and over immediate stores through the same
/// base value to disjoint bytes; the first word that can write the slot is
/// either the matching 64-bit store (its data register is the value) or the
/// epoch of an opaque slot value.
fn slot_source(
    es: &[Emitted<'_>],
    reload_pos: usize,
    access: ImmAccess,
    what: &'static str,
) -> Result<SlotSource> {
    let base_writer = latest_writer(es, reload_pos, access.rn, what)?;
    let slot = |epoch: Option<usize>| {
        SlotSource::Slot(Origin::Slot {
            base_writer,
            base_reg: access.rn,
            offset: access.offset,
            epoch,
        })
    };
    for i in (0..reload_pos).rev() {
        match memory_write(&es[i]) {
            MemWrite::No => {}
            MemWrite::Unknown => return Ok(slot(Some(i))),
            MemWrite::Store(store) => {
                // One base value: the same register, not rewritten between
                // the store and the reload.
                let same_base = store.rn == access.rn && base_writer.is_none_or(|w| w < i);
                if !same_base {
                    return Ok(slot(Some(i)));
                }
                let disjoint = store.offset + store.bytes <= access.offset
                    || access.offset + 8 <= store.offset;
                if disjoint {
                    continue;
                }
                if store.offset == access.offset
                    && let Some(reg) = store_source(&es[i], store)
                {
                    return Ok(SlotSource::Store { reg, at: i });
                }
                return Ok(slot(Some(i)));
            }
        }
    }
    Ok(slot(None))
}

fn origin(es: &[Emitted<'_>], before: usize, reg: u8, what: &'static str) -> Result<Origin> {
    let mut reg = reg;
    let mut before = before;
    // Every step moves `before` strictly backwards.
    for _ in 0..es.len() + 1 {
        let Some(w) = latest_writer(es, before, reg, what)? else {
            return Ok(Origin::Reg { writer: None, reg });
        };
        if let Some(source) = copy_source(&es[w], reg) {
            reg = source;
            before = w;
            continue;
        }
        if let Some(access) = spill_reload(&es[w], reg) {
            match slot_source(es, w, access, what)? {
                SlotSource::Store { reg: source, at } => {
                    reg = source;
                    before = at;
                    continue;
                }
                SlotSource::Slot(slot) => return Ok(slot),
            }
        }
        return Ok(Origin::Reg {
            writer: Some(w),
            reg,
        });
    }
    Ok(Origin::Reg { writer: None, reg })
}

/// Whether `inst`'s opcode and shift spell a move-wide word of the decoded
/// form `word_form` (`Movz`, `Movn` or `Movk`) at halfword `hw`.
///
/// The canonical intent carries the shift as an optional third operand (absent
/// means `LSL #0`). The encoder also spells MOVZ at `LSL #0` from three
/// shift-free two-operand intents (`aarch64::encode`: `MovI` "encoded as MOVZ
/// at LSL #0", and the width-checked typed aliases `MOVZWi`/`MOVZXi`), so a
/// MOVZ word binds to those only at `hw == 0` and only with exactly two
/// operands. Register, width and `imm16` are compared by the caller.
fn move_wide_form_matches(inst: &MachInst, word_form: AArch64Opcode, hw: u32) -> bool {
    use AArch64Opcode as O;
    if inst.opcode == word_form {
        return imm_at(inst, 2).unwrap_or(0) == i64::from(hw * 16);
    }
    word_form == O::Movz
        && matches!(inst.opcode, O::MovI | O::MOVZWi | O::MOVZXi)
        && hw == 0
        && inst.operands.len() == 2
}

/// Compose the constant a MOVZ/MOVN + MOVK chain leaves in `reg` at position
/// `before`, binding every chain word to its intent.
///
/// The chain is collected backwards to its MOVZ/MOVN base and then evaluated
/// forwards with each word's own width: a W-form word (base or MOVK) leaves
/// the upper 32 bits zero, so it discards halfwords 2 and 3 written by any
/// older word, while an X-form MOVK after a W-form base still sets them.
fn chain_value(es: &[Emitted<'_>], before: usize, reg: u8, what: &'static str) -> Result<u64> {
    let refuse = |offset: u32, detail: String| SwitchBindingError::Constant {
        offset,
        what,
        reg,
        detail,
    };
    // (sf, opc, hw, imm16), youngest first.
    let mut words: Vec<(u32, u32, u32, u32)> = Vec::new();
    let mut before = before;
    for _ in 0..8 {
        let Some(w) = latest_writer(es, before, reg, what)? else {
            return Err(refuse(
                es.get(before).map_or(0, |e| e.offset),
                "no producer in the block".into(),
            ));
        };
        let e = &es[w];
        let Word::MoveWide {
            sf,
            opc,
            hw,
            imm16,
            rd,
        } = decode(e.word)
        else {
            return Err(refuse(
                e.offset,
                format!("producer {:#010x} is not MOVZ/MOVK/MOVN", e.word),
            ));
        };
        if rd != reg {
            return Err(refuse(e.offset, "move-wide destination differs".into()));
        }
        if sf == 0 && hw > 1 {
            return Err(refuse(
                e.offset,
                "32-bit move-wide with an upper halfword".into(),
            ));
        }
        let expected_opcode = match opc {
            0b00 => AArch64Opcode::Movn,
            0b10 => AArch64Opcode::Movz,
            0b11 => AArch64Opcode::Movk,
            _ => return Err(refuse(e.offset, "unallocated move-wide opc".into())),
        };
        let intent_ok = move_wide_form_matches(e.inst, expected_opcode, hw)
            && gpr_at(e.inst, 0) == Some((rd, if sf == 1 { 64 } else { 32 }))
            && imm_at(e.inst, 1) == Some(i64::from(imm16));
        if !intent_ok {
            return Err(mismatch(
                e,
                what,
                format!("{expected_opcode:?} x{rd}, #{imm16}, lsl #{}", hw * 16),
            ));
        }
        words.push((sf, opc, hw, imm16));
        if opc == 0b11 {
            before = w;
            continue;
        }
        let mut value = 0u64;
        for &(sf, opc, hw, imm16) in words.iter().rev() {
            let shift = 16 * hw;
            let field = u64::from(imm16) << shift;
            value = match opc {
                0b10 => field,
                0b00 => !field,
                _ => (value & !(0xFFFFu64 << shift)) | field,
            };
            if sf == 0 {
                value &= 0xFFFF_FFFF;
            }
        }
        return Ok(value);
    }
    Err(refuse(
        es[before].offset,
        "move-wide chain longer than eight words".into(),
    ))
}

fn is_compare_opcode(opcode: AArch64Opcode) -> bool {
    use AArch64Opcode as O;
    matches!(
        opcode,
        O::CmpRI | O::CmpRR | O::CMPWri | O::CMPXri | O::CMPWrr | O::CMPXrr
    )
}

/// A decoded compare: `(register, width, operand)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompareRhs {
    Imm(u64),
    Reg(u8),
}

/// Decode a `CMP` word (SUBS with a discarded result) and bind it to its
/// intent.
fn bind_compare(e: &Emitted<'_>, what: &'static str) -> Result<(u8, u32, CompareRhs)> {
    let (reg, sf, rhs) = match decode(e.word) {
        Word::AddSubImm {
            sf,
            sub: true,
            flags: true,
            sh,
            imm12,
            rn,
            rd: 31,
        } => (rn, sf, CompareRhs::Imm(u64::from(imm12) << (12 * sh))),
        Word::AddSubReg {
            sf,
            sub: true,
            flags: true,
            shift: 0,
            rm,
            imm6: 0,
            rn,
            rd: 31,
        } => (rn, sf, CompareRhs::Reg(rm)),
        _ => return Err(mismatch(e, what, format!("{:#010x} (not CMP)", e.word))),
    };
    let width = if sf == 1 { 64 } else { 32 };
    if !is_compare_opcode(e.inst.opcode) {
        return Err(mismatch(e, what, format!("CMP x{reg}, {rhs:?}")));
    }
    let lhs_ok = gpr_at(e.inst, 0) == Some((reg, width));
    let rhs_ok = match rhs {
        CompareRhs::Imm(value) => {
            imm_at(e.inst, 1).and_then(|k| u64::try_from(k).ok()) == Some(value)
        }
        CompareRhs::Reg(rm) => gpr_at(e.inst, 1).map(|(r, _)| r) == Some(rm),
    };
    if !lhs_ok || !rhs_ok {
        return Err(mismatch(
            e,
            what,
            format!("CMP {}{reg}, {rhs:?}", if sf == 1 { "x" } else { "w" }),
        ));
    }
    Ok((reg, width, rhs))
}

/// Bind a `B.cond` word to its intent and return the absolute target byte.
fn bind_cond_branch(e: &Emitted<'_>, what: &'static str) -> Result<(u32, i64)> {
    let Word::CondBranch { imm19, cond } = decode(e.word) else {
        return Err(mismatch(e, what, format!("{:#010x} (not B.cond)", e.word)));
    };
    let target = i64::from(e.offset) + imm19 * 4;
    if !matches!(e.inst.opcode, AArch64Opcode::BCond | AArch64Opcode::Bcc) {
        return Err(mismatch(
            e,
            what,
            format!("B.cond #{cond} -> byte {target}"),
        ));
    }
    let cond_ok = imm_at(e.inst, 0) == Some(i64::from(cond));
    if !cond_ok || !branch_target_matches(e, 1, imm19) {
        return Err(mismatch(
            e,
            what,
            format!("B.cond #{cond} -> byte {target}"),
        ));
    }
    Ok((cond, target))
}

/// A resolved branch intent is a word displacement that must equal the
/// decoded one; a still-symbolic intent names a block, which
/// [`symbolic_target_ok`] resolves against the layout.
fn branch_target_matches(e: &Emitted<'_>, index: usize, words: i64) -> bool {
    match e.inst.operands.get(index) {
        Some(MachOperand::Imm(k)) => *k == words,
        Some(MachOperand::Block(_)) => true,
        _ => false,
    }
}

fn symbolic_target_ok(layout: &Layout<'_>, e: &Emitted<'_>, index: usize, target: i64) -> bool {
    match e.inst.operands.get(index) {
        Some(MachOperand::Block(b)) => layout
            .block_offset
            .get(b)
            .is_some_and(|start| i64::from(*start) == target),
        _ => true,
    }
}

// ===========================================================================
// Jump-table dispatch
// ===========================================================================

#[allow(clippy::too_many_arguments)]
fn check_jump_table(
    func: &MachFunction,
    layout: &Layout<'_>,
    block: BlockId,
    es: &[Emitted<'_>],
    adr_pos: usize,
    table: u32,
    jt: &JumpTableData,
    table_offset: u32,
    code: &[u8],
    report: &mut SwitchBindingReport,
) -> Result<u32> {
    let chain = |what: &'static str, offset: u32, detail: String| SwitchBindingError::Chain {
        table,
        what,
        offset,
        detail,
    };
    let adr = &es[adr_pos];

    // ADR Xbase, table.
    let Word::Adr { imm, rd: base_reg } = decode(adr.word) else {
        return Err(mismatch(
            adr,
            "jump-table ADR",
            format!("{:#010x} (not ADR)", adr.word),
        ));
    };
    if gpr_at(adr.inst, 0) != Some((base_reg, 64)) {
        return Err(mismatch(adr, "jump-table ADR", format!("ADR x{base_reg}")));
    }
    let (encoded, base_pos) =
        if let Some(expansion) = func.jump_table_address_expansions.get(&adr.id) {
            let add = es
                .get(adr_pos + 1)
                .ok_or_else(|| chain("address ADD", adr.offset, "missing next word".into()))?;
            if add.id != expansion.add || add.offset != adr.offset + 4 {
                return Err(chain(
                    "address ADD",
                    adr.offset,
                    "not the exact adjacent instruction".into(),
                ));
            }
            let address = crate::aarch64_jump_table_address::decode_expanded_address(
                func, adr.id, adr.offset, adr.word, add.word,
            )
            .map_err(SwitchBindingError::AddressExpansion)?;
            (address, adr_pos + 1)
        } else {
            (i64::from(adr.offset) + imm, adr_pos)
        };
    if encoded != i64::from(table_offset) {
        return Err(SwitchBindingError::TableAddress {
            table,
            offset: adr.offset,
            encoded,
            layout: table_offset,
        });
    }

    // Table entries.
    let len = jt.targets.len();
    let start = table_offset as usize;
    let end = start + 4 * len;
    if end > code.len() {
        return Err(SwitchBindingError::TableTruncated {
            table,
            start,
            end,
            image: code.len(),
        });
    }
    let succs = &func.block(block).succs;
    for (entry, target) in jt.targets.iter().enumerate() {
        let expected =
            *layout
                .block_offset
                .get(target)
                .ok_or(SwitchBindingError::TableTargetNotLaidOut {
                    table,
                    entry,
                    target: *target,
                })?;
        let at = start + 4 * entry;
        let encoded = code
            .get(at..at + 4)
            .and_then(|bytes| <[u8; 4]>::try_from(bytes).ok())
            .map(i32::from_le_bytes)
            .unwrap_or_default();
        let lands = i64::from(table_offset) + i64::from(encoded);
        if lands != i64::from(expected) {
            return Err(SwitchBindingError::TableEntry {
                table,
                entry,
                encoded,
                lands,
                target: *target,
                expected,
            });
        }
        if !succs.contains(target) {
            return Err(SwitchBindingError::TableTargetNotSuccessor {
                table,
                entry,
                target: *target,
                block,
            });
        }
    }

    // BR Xt.
    let br_pos = es
        .len()
        .checked_sub(1)
        .ok_or(SwitchBindingError::DispatchTerminator { table, block })?;
    let br = &es[br_pos];
    let Word::BranchReg {
        opc: 0,
        rn: target_reg,
    } = decode(br.word)
    else {
        return Err(SwitchBindingError::DispatchTerminator { table, block });
    };
    if br.inst.opcode != AArch64Opcode::Br || gpr_at(br.inst, 0).map(|(r, _)| r) != Some(target_reg)
    {
        return Err(mismatch(br, "jump-table BR", format!("BR x{target_reg}")));
    }

    // ADD Xt, Xa, Xb.
    let add_pos =
        latest_writer(es, br_pos, target_reg, "the BR register producer")?.ok_or_else(|| {
            chain(
                "BR register",
                br.offset,
                format!("x{target_reg} has no producer in the dispatch block"),
            )
        })?;
    let add = &es[add_pos];
    let Word::AddSubReg {
        sf: 1,
        sub: false,
        flags: false,
        shift: 0,
        rm: add_rm,
        imm6: 0,
        rn: add_rn,
        rd: add_rd,
    } = decode(add.word)
    else {
        return Err(chain(
            "BR register producer",
            add.offset,
            format!("{:#010x} is not ADD Xd, Xn, Xm", add.word),
        ));
    };
    if add.inst.opcode != AArch64Opcode::AddRR
        || gpr_at(add.inst, 0) != Some((add_rd, 64))
        || gpr_at(add.inst, 1) != Some((add_rn, 64))
        || gpr_at(add.inst, 2) != Some((add_rm, 64))
    {
        return Err(mismatch(
            add,
            "jump-table ADD",
            format!("ADD x{add_rd}, x{add_rn}, x{add_rm}"),
        ));
    }

    // One ADD operand is the ADR base, the other the loaded entry.
    let o_n = origin(es, add_pos, add_rn, "the ADD operands")?;
    let o_m = origin(es, add_pos, add_rm, "the ADD operands")?;
    let (ldrsw_pos, entry_origin_reg) = match (o_n.produced(), o_m.produced()) {
        (Some((p, rn)), Some((q, rm))) if p == base_pos && rn == base_reg => (q, rm),
        (Some((q, rn)), Some((p, rm))) if p == base_pos && rm == base_reg => (q, rn),
        _ => {
            return Err(chain(
                "ADD operands",
                add.offset,
                "neither operand is the table base from this ADR while the other is produced in the block".into(),
            ));
        }
    };
    let ldrsw = &es[ldrsw_pos];
    let Word::LdrswRegOffset {
        rm: index_reg,
        option,
        s,
        rn: ldr_base,
        rt: entry_reg,
    } = decode(ldrsw.word)
    else {
        return Err(chain(
            "loaded-entry producer",
            ldrsw.offset,
            format!("{:#010x} is not LDRSW Xt, [Xn, Xm, LSL #2]", ldrsw.word),
        ));
    };
    if option != 0b011 || s != 1 {
        return Err(chain(
            "LDRSW addressing",
            ldrsw.offset,
            format!("option {option:#b} S {s} is not LSL #2"),
        ));
    }
    if entry_origin_reg != entry_reg {
        return Err(chain(
            "loaded entry",
            ldrsw.offset,
            format!("ADD reads x{entry_origin_reg} but LDRSW writes x{entry_reg}"),
        ));
    }
    if ldrsw.inst.opcode != AArch64Opcode::LdrswRO
        || gpr_at(ldrsw.inst, 0) != Some((entry_reg, 64))
        || gpr_at(ldrsw.inst, 1) != Some((ldr_base, 64))
        || gpr_at(ldrsw.inst, 2) != Some((index_reg, 64))
    {
        return Err(mismatch(
            ldrsw,
            "jump-table LDRSW",
            format!("LDRSW x{entry_reg}, [x{ldr_base}, x{index_reg}, LSL #2]"),
        ));
    }
    let o_base = origin(es, ldrsw_pos, ldr_base, "the LDRSW base")?;
    if o_base.produced() != Some((base_pos, base_reg)) {
        return Err(chain(
            "LDRSW base",
            ldrsw.offset,
            format!("x{ldr_base} is not the table base from this ADR"),
        ));
    }
    let o_index = origin(es, ldrsw_pos, index_reg, "the LDRSW index")?;

    // B.HI default: the latest conditional branch before the load.
    let bounds = |offset: u32, detail: String| SwitchBindingError::Bounds {
        table,
        offset,
        detail,
    };
    let hi_pos = (0..ldrsw_pos)
        .rev()
        .find(|&j| matches!(decode(es[j].word), Word::CondBranch { .. }))
        .ok_or_else(|| {
            bounds(
                ldrsw.offset,
                "no conditional branch precedes the table load".into(),
            )
        })?;
    let hi = &es[hi_pos];
    let (cond, target) = bind_cond_branch(hi, "jump-table bounds branch")?;
    if cond != COND_HI {
        return Err(bounds(hi.offset, format!("condition #{cond} is not HI")));
    }
    if !symbolic_target_ok(layout, hi, 1, target) {
        return Err(mismatch(
            hi,
            "jump-table bounds branch",
            format!("B.HI -> byte {target}"),
        ));
    }
    let default_block = layout.successor_at(func, block, target).ok_or_else(|| {
        bounds(
            hi.offset,
            format!("default edge lands at byte {target}, not a recorded successor block start"),
        )
    })?;
    let outside_table: Vec<BlockId> = succs
        .iter()
        .copied()
        .filter(|s| !jt.targets.contains(s))
        .collect();
    if let [only] = outside_table.as_slice()
        && *only != default_block
    {
        return Err(bounds(
            hi.offset,
            format!(
                "default edge lands on {default_block:?} but the only successor outside the table is {only:?}"
            ),
        ));
    }
    if outside_table.len() > 1 {
        return Err(bounds(
            hi.offset,
            format!(
                "{} successors lie outside the table: {outside_table:?}",
                outside_table.len()
            ),
        ));
    }

    // CMP Xindex, #(len - 1).
    let cmp_pos = latest_nzcv_writer(es, hi_pos, "the bounds flag producer")?
        .ok_or_else(|| bounds(hi.offset, "no flag producer in the dispatch block".into()))?;
    let cmp = &es[cmp_pos];
    let (cmp_reg, cmp_width, rhs) = bind_compare(cmp, "jump-table bounds compare")?;
    if cmp_width != 64 {
        return Err(bounds(cmp.offset, "bounds compare is 32-bit".into()));
    }
    let limit = match rhs {
        CompareRhs::Imm(value) => value,
        CompareRhs::Reg(rm) => {
            let value = chain_value(es, cmp_pos, rm, "jump-table bounds constant")?;
            report.materialized_constants += 1;
            value
        }
    };
    if limit != (len as u64).wrapping_sub(1) || len == 0 {
        return Err(bounds(
            cmp.offset,
            format!("bounds constant {limit} does not cover a table of {len} entries"),
        ));
    }
    let o_cmp = origin(es, cmp_pos, cmp_reg, "the bounds index")?;
    if o_cmp != o_index {
        return Err(chain(
            "index identity",
            cmp.offset,
            format!(
                "x{cmp_reg} at the bounds check and x{index_reg} at the table load do not carry one value"
            ),
        ));
    }

    // SUB Xindex, Xsel, #min_val.
    if jt.min_val != 0 {
        let normalization = |offset: u32, detail: String| SwitchBindingError::Normalization {
            table,
            offset,
            detail,
        };
        let (sub_pos, index_at_sub) = match o_index {
            Origin::Reg {
                writer: Some(writer),
                reg,
            } => (writer, reg),
            Origin::Reg { writer: None, .. } => {
                return Err(normalization(
                    cmp.offset,
                    format!("min_val {} but the index is a live-in register", jt.min_val),
                ));
            }
            Origin::Slot { .. } => {
                return Err(normalization(
                    cmp.offset,
                    format!(
                        "min_val {} but the index is reloaded from a spill slot the dispatch block does not store",
                        jt.min_val
                    ),
                ));
            }
        };
        let sub = &es[sub_pos];
        let value = match decode(sub.word) {
            Word::AddSubImm {
                sf: 1,
                sub: true,
                flags: false,
                sh,
                imm12,
                rn,
                rd,
            } if rd == index_at_sub => {
                if sub.inst.opcode != AArch64Opcode::SubRI
                    || gpr_at(sub.inst, 0) != Some((rd, 64))
                    || gpr_at(sub.inst, 1) != Some((rn, 64))
                    || imm_at(sub.inst, 2) != Some(i64::from(imm12 << (12 * sh)))
                {
                    return Err(mismatch(
                        sub,
                        "jump-table normalization",
                        format!("SUB x{rd}, x{rn}, #{}", imm12 << (12 * sh)),
                    ));
                }
                u64::from(imm12 << (12 * sh))
            }
            Word::AddSubReg {
                sf: 1,
                sub: true,
                flags: false,
                shift: 0,
                rm,
                imm6: 0,
                rn,
                rd,
            } if rd == index_at_sub => {
                if sub.inst.opcode != AArch64Opcode::SubRR
                    || gpr_at(sub.inst, 0) != Some((rd, 64))
                    || gpr_at(sub.inst, 1) != Some((rn, 64))
                    || gpr_at(sub.inst, 2) != Some((rm, 64))
                {
                    return Err(mismatch(
                        sub,
                        "jump-table normalization",
                        format!("SUB x{rd}, x{rn}, x{rm}"),
                    ));
                }
                let value = chain_value(es, sub_pos, rm, "jump-table normalization constant")?;
                report.materialized_constants += 1;
                value
            }
            _ => {
                return Err(normalization(
                    sub.offset,
                    format!("index producer {:#010x} is not SUB", sub.word),
                ));
            }
        };
        if value != jt.min_val as u64 {
            return Err(normalization(
                sub.offset,
                format!("subtracts {value} but min_val is {}", jt.min_val),
            ));
        }
    }

    report.jump_tables += 1;
    report.table_entries += len;
    Ok(br.offset)
}

// ===========================================================================
// Compare dispatch groups and fused branches
// ===========================================================================

fn is_terminator_word(word: u32) -> bool {
    matches!(
        decode(word),
        Word::Branch { .. } | Word::BranchReg { .. } | Word::Exception
    )
}

fn check_compare_groups(
    func: &MachFunction,
    layout: &Layout<'_>,
    block: BlockId,
    es: &[Emitted<'_>],
    report: &mut SwitchBindingReport,
) -> Result<()> {
    let block_start = i64::from(layout.block_offset.get(&block).copied().unwrap_or(0));
    let block_end = es.last().map_or(block_start, |e| i64::from(e.offset) + 4);
    let target_ok = |e: &Emitted<'_>, target: i64| -> Result<()> {
        let inside = target >= block_start && target <= block_end;
        if layout.successor_at(func, block, target).is_some() || inside {
            Ok(())
        } else {
            Err(SwitchBindingError::BranchTarget {
                offset: e.offset,
                target,
                block,
            })
        }
    };
    for (i, e) in es.iter().enumerate() {
        if is_compare_opcode(e.inst.opcode) {
            let (_, _, rhs) = bind_compare(e, "compare")?;
            if let CompareRhs::Reg(rm) = rhs
                && let Some(w) = latest_writer(es, i, rm, "the compare operand producer")?
                && matches!(decode(es[w].word), Word::MoveWide { .. })
            {
                chain_value(es, i, rm, "compare constant")?;
                report.materialized_constants += 1;
            }
            let mut consumers = 0usize;
            for c in es.iter().skip(i + 1) {
                if matches!(decode(c.word), Word::CondBranch { .. })
                    || matches!(c.inst.opcode, AArch64Opcode::BCond | AArch64Opcode::Bcc)
                {
                    let (_, target) = bind_cond_branch(c, "compare consumer")?;
                    if !symbolic_target_ok(layout, c, 1, target) {
                        return Err(mismatch(
                            c,
                            "compare consumer",
                            format!("B.cond -> byte {target}"),
                        ));
                    }
                    target_ok(c, target)?;
                    consumers += 1;
                    continue;
                }
                if word_effects(c, "the compare consumer window")?.nzcv
                    || is_terminator_word(c.word)
                    || c.inst.is_terminator()
                {
                    break;
                }
            }
            if consumers > 0 {
                report.compare_groups += 1;
                report.compare_consumers += consumers;
            }
            continue;
        }
        match e.inst.opcode {
            AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
                let Word::CmpBranch {
                    sf,
                    nonzero,
                    imm19,
                    rt,
                } = decode(e.word)
                else {
                    return Err(mismatch(
                        e,
                        "fused compare-branch",
                        format!("{:#010x} (not CBZ/CBNZ)", e.word),
                    ));
                };
                let target = i64::from(e.offset) + imm19 * 4;
                let expected = if nonzero {
                    AArch64Opcode::Cbnz
                } else {
                    AArch64Opcode::Cbz
                };
                let width = if sf == 1 { 64 } else { 32 };
                if e.inst.opcode != expected
                    || gpr_at(e.inst, 0) != Some((rt, width))
                    || !branch_target_matches(e, 1, imm19)
                    || !symbolic_target_ok(layout, e, 1, target)
                {
                    return Err(mismatch(
                        e,
                        "fused compare-branch",
                        format!("{expected:?} x{rt} -> byte {target}"),
                    ));
                }
                target_ok(e, target)?;
                report.fused_branches += 1;
            }
            AArch64Opcode::Tbz | AArch64Opcode::Tbnz => {
                let Word::TestBranch {
                    bit,
                    nonzero,
                    imm14,
                    rt,
                } = decode(e.word)
                else {
                    return Err(mismatch(
                        e,
                        "fused test-branch",
                        format!("{:#010x} (not TBZ/TBNZ)", e.word),
                    ));
                };
                let target = i64::from(e.offset) + imm14 * 4;
                let expected = if nonzero {
                    AArch64Opcode::Tbnz
                } else {
                    AArch64Opcode::Tbz
                };
                if e.inst.opcode != expected
                    || gpr_at(e.inst, 0).map(|(r, _)| r) != Some(rt)
                    || imm_at(e.inst, 1) != Some(i64::from(bit))
                    || !branch_target_matches(e, 2, imm14)
                    || !symbolic_target_ok(layout, e, 2, target)
                {
                    return Err(mismatch(
                        e,
                        "fused test-branch",
                        format!("{expected:?} x{rt}, #{bit} -> byte {target}"),
                    ));
                }
                target_ok(e, target)?;
                report.fused_branches += 1;
            }
            _ => {}
        }
    }
    Ok(())
}

// ===========================================================================
// Entry point
// ===========================================================================

/// Bind every switch dispatch of `func` to the final `code` bytes.
///
/// `code` is the encoded function: the body words followed by the appended
/// jump tables in ADR encounter order. Errors fail the encode closed.
pub fn check_aarch64_switch_dispatch(
    func: &MachFunction,
    code: &[u8],
) -> Result<SwitchBindingReport> {
    crate::aarch64_jump_table_address::validate_expansions(func)
        .map_err(SwitchBindingError::AddressExpansion)?;
    let layout = Layout::derive(func, code)?;
    let mut report = SwitchBindingReport::default();
    let mut table_offset =
        u32::try_from(layout.body_len).map_err(|_| SwitchBindingError::ImageTooShort {
            layout: layout.body_len,
            image: code.len(),
        })?;
    let mut bound_dispatch_branches = Vec::new();
    for (block, es) in &layout.blocks {
        for (pos, e) in es.iter().enumerate() {
            if e.inst.opcode != AArch64Opcode::Adr {
                continue;
            }
            let Some(table) = func.jump_table_at_address(e.id) else {
                continue;
            };
            let jt = func.jump_tables.get(table as usize).ok_or(
                SwitchBindingError::MissingJumpTable {
                    offset: e.offset,
                    table,
                    count: func.jump_tables.len(),
                },
            )?;
            bound_dispatch_branches.push(check_jump_table(
                func,
                &layout,
                *block,
                es,
                pos,
                table,
                jt,
                table_offset,
                code,
                &mut report,
            )?);
            let size = u32::try_from(4 * jt.targets.len())
                .ok()
                .and_then(|s| table_offset.checked_add(s));
            table_offset = size.ok_or(SwitchBindingError::TableTruncated {
                table,
                start: table_offset as usize,
                end: usize::MAX,
                image: code.len(),
            })?;
        }
    }
    // `BR` is emitted only as a jump-table dispatch, and the coverage gate
    // credits it through this binding, so an indirect branch that no bound
    // dispatch ends in is refused rather than passed unbound.
    for (_, es) in &layout.blocks {
        for e in es {
            let is_br = e.inst.opcode == AArch64Opcode::Br
                || matches!(decode(e.word), Word::BranchReg { opc: 0, .. });
            if is_br && !bound_dispatch_branches.contains(&e.offset) {
                return Err(SwitchBindingError::UnboundIndirectBranch {
                    offset: e.offset,
                    word: e.word,
                    intent: intent_text(e.inst),
                });
            }
        }
    }
    for (block, es) in &layout.blocks {
        check_compare_groups(func, &layout, *block, es, &mut report)?;
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::Signature;
    use trust_cg_ir::regs::PReg;

    fn x(n: u16) -> MachOperand {
        MachOperand::PReg(PReg::new(n))
    }

    fn imm(v: i64) -> MachOperand {
        MachOperand::Imm(v)
    }

    /// `dense_sw`-shaped function: entry dispatches through a six-entry table
    /// with min_val 0, every arm returns. Words are hand-encoded from the
    /// Arm ARM, not produced by the encoder.
    fn dense_table() -> (MachFunction, Vec<u8>) {
        let mut f = MachFunction::new("dense".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let arms: Vec<BlockId> = (0..7).map(|_| f.create_block()).collect();
        // entry: CMP X0,#5 ; B.HI +17 ; ADR X1,+72 ; LDRSW X2,[X1,X0,LSL#2] ; ADD X0,X1,X2 ; BR X0
        let seq = vec![
            (AArch64Opcode::CmpRI, vec![x(0), imm(5)]),
            (AArch64Opcode::BCond, vec![imm(8), imm(17)]),
            (
                AArch64Opcode::Adr,
                vec![x(1), MachOperand::JumpTableIndex(0)],
            ),
            (AArch64Opcode::LdrswRO, vec![x(2), x(1), x(0)]),
            (AArch64Opcode::AddRR, vec![x(0), x(1), x(2)]),
            (AArch64Opcode::Br, vec![x(0)]),
        ];
        for (op, ops) in seq {
            let id = f.push_inst(MachInst::new(op, ops));
            f.append_inst(entry, id);
        }
        let mut order = vec![entry];
        for &arm in arms.iter().rev() {
            let id = f.push_inst(MachInst::new(AArch64Opcode::Movz, vec![x(0), imm(1)]));
            f.append_inst(arm, id);
            let id = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![x(30)]));
            f.append_inst(arm, id);
            order.push(arm);
        }
        f.block_order = order;
        f.block_mut(entry).succs = arms.clone();
        f.jump_tables.push(JumpTableData {
            min_val: 0,
            targets: arms[1..].to_vec(),
        });
        let mut words: Vec<u32> = vec![
            0xf100_141f, // CMP X0, #5
            0x5400_0228, // B.HI +17 words (-> byte 72)
            0x1000_0241, // ADR X1, +72
            0xb8a0_7822, // LDRSW X2, [X1, X0, LSL #2]
            0x8b02_0020, // ADD X0, X1, X2
            0xd61f_0000, // BR X0
        ];
        for _ in 0..7 {
            words.push(0xd280_0020); // MOVZ X0, #1
            words.push(0xd65f_03c0); // RET
        }
        let mut code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        // Table at byte 80: arms[1..] laid out at 72-8*k (reverse order) — arm k
        // (k = 1..6) starts at byte 24 + 8 * (6 - k).
        for k in 1..=6u32 {
            let start = 24 + 8 * (6 - k);
            code.extend_from_slice(&(start as i32 - 80).to_le_bytes());
        }
        (f, code)
    }

    #[test]
    fn hand_encoded_dense_table_binds() {
        let (f, code) = dense_table();
        let report = check_aarch64_switch_dispatch(&f, &code).unwrap();
        assert_eq!(report.jump_tables, 1);
        assert_eq!(report.table_entries, 6);
        assert_eq!(report.compare_groups, 1);
        assert_eq!(report.compare_consumers, 1);
    }

    fn patch(code: &[u8], at: usize, word: u32) -> Vec<u8> {
        let mut out = code.to_vec();
        out[at..at + 4].copy_from_slice(&word.to_le_bytes());
        out
    }

    #[test]
    fn dense_table_corruptions_refute() {
        let (f, code) = dense_table();
        let cases: Vec<(&str, Vec<u8>)> = vec![
            ("entry off by one word", {
                let mut c = code.clone();
                let v = i32::from_le_bytes(c[80..84].try_into().unwrap()) + 4;
                c[80..84].copy_from_slice(&v.to_le_bytes());
                c
            }),
            ("entries swapped", {
                let mut c = code.clone();
                let a: [u8; 4] = c[80..84].try_into().unwrap();
                let b: [u8; 4] = c[84..88].try_into().unwrap();
                c[80..84].copy_from_slice(&b);
                c[84..88].copy_from_slice(&a);
                c
            }),
            ("bounds off by one (CMP #6)", patch(&code, 0, 0xf100_181f)),
            ("bounds off by one (CMP #4)", patch(&code, 0, 0xf100_101f)),
            (
                "bounds condition HS instead of HI",
                patch(&code, 4, 0x5400_0222),
            ),
            (
                "bounds target off by one word",
                patch(&code, 4, 0x5400_0248),
            ),
            ("BR register swapped (BR X1)", patch(&code, 20, 0xd61f_0020)),
            (
                "ADD operands swapped in (ADD X0, X1, X1)",
                patch(&code, 16, 0x8b01_0020),
            ),
            (
                "LDRSW index swapped (X1 as index)",
                patch(&code, 12, 0xb8a1_7822),
            ),
            (
                "LDRSW scale LSL #3 (S=0 with UXTX is not scale 2)",
                patch(&code, 12, 0xb8a0_6822),
            ),
            ("ADR displaced by one word", patch(&code, 8, 0x1000_0261)),
            (
                "CMP on the wrong register (X1)",
                patch(&code, 0, 0xf100_143f),
            ),
            ("table truncated", code[..code.len() - 4].to_vec()),
        ];
        for (label, bytes) in cases {
            let result = check_aarch64_switch_dispatch(&f, &bytes);
            assert!(result.is_err(), "{label}: must refute, got {result:?}");
        }
    }

    /// A `BR` that ends no jump-table dispatch is refused, whether the
    /// intent or only the word names it.
    #[test]
    fn stray_indirect_branch_is_refused() {
        let mut f = MachFunction::new("stray".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let id = f.push_inst(MachInst::new(AArch64Opcode::Br, vec![x(0)]));
        f.append_inst(entry, id);
        f.block_order = vec![entry];
        let code = 0xd61f_0000u32.to_le_bytes().to_vec(); // BR X0
        assert!(matches!(
            check_aarch64_switch_dispatch(&f, &code),
            Err(SwitchBindingError::UnboundIndirectBranch { offset: 0, .. })
        ));
        // A RET intent whose word is BR X30.
        let mut g = MachFunction::new("stray_word".into(), Signature::new(vec![], vec![]));
        let entry = g.entry;
        let id = g.push_inst(MachInst::new(AArch64Opcode::Ret, vec![x(30)]));
        g.append_inst(entry, id);
        g.block_order = vec![entry];
        let code = 0xd61f_03c0u32.to_le_bytes().to_vec(); // BR X30
        assert!(matches!(
            check_aarch64_switch_dispatch(&g, &code),
            Err(SwitchBindingError::UnboundIndirectBranch { offset: 0, .. })
        ));
    }

    #[test]
    fn effects_classification_examples() {
        // CMP X0, #5 writes NZCV and no register.
        assert_eq!(
            effects(0xf100_141f),
            Some(Effects {
                writes: 0,
                nzcv: true
            })
        );
        // ADD X0, X1, X2 writes X0.
        assert_eq!(
            effects(0x8b02_0020),
            Some(Effects {
                writes: 1,
                nzcv: false
            })
        );
        // LDRSW X2, [X1, X0, LSL #2] writes X2.
        assert_eq!(
            effects(0xb8a0_7822),
            Some(Effects {
                writes: 1 << 2,
                nzcv: false
            })
        );
        // STR X8, [SP, #16] writes nothing.
        assert_eq!(effects(0xf900_0be8), Some(Effects::default()));
        // LDR X8, [SP, #16] writes X8.
        assert_eq!(
            effects(0xf940_0be8),
            Some(Effects {
                writes: 1 << 8,
                nzcv: false
            })
        );
        // BL writes X30.
        assert_eq!(
            effects(0x9400_0000),
            Some(Effects {
                writes: 1 << 30,
                nzcv: false
            })
        );
        // FCMP D0, D1 writes NZCV.
        assert_eq!(
            effects(0x1e61_2000),
            Some(Effects {
                writes: 0,
                nzcv: true
            })
        );
        // ANDS X3, X4, X5 writes NZCV and X3.
        assert_eq!(
            effects(0xea05_0083),
            Some(Effects {
                writes: 1 << 3,
                nzcv: true
            })
        );
        // NOP.
        assert_eq!(effects(0xd503_201f), Some(Effects::default()));
        // MOVZ X1, #10000 writes X1.
        assert_eq!(
            effects(0xd284_e201),
            Some(Effects {
                writes: 1 << 1,
                nzcv: false
            })
        );
        // An SVE word is unmodeled.
        assert_eq!(effects(0x0420_0000), None);
    }

    #[test]
    fn decode_examples() {
        assert_eq!(
            decode(0x5400_0228),
            Word::CondBranch {
                imm19: 17,
                cond: COND_HI
            }
        );
        assert_eq!(decode(0x1000_0241), Word::Adr { imm: 72, rd: 1 });
        assert_eq!(
            decode(0xb8a0_7822),
            Word::LdrswRegOffset {
                rm: 0,
                option: 0b011,
                s: 1,
                rn: 1,
                rt: 2
            }
        );
        assert_eq!(decode(0xd61f_0040), Word::BranchReg { opc: 0, rn: 2 });
        assert_eq!(decode(0xd65f_03c0), Word::BranchReg { opc: 2, rn: 30 });
        assert_eq!(
            decode(0xb400_0100),
            Word::CmpBranch {
                sf: 1,
                nonzero: false,
                imm19: 8,
                rt: 0
            }
        );
        assert_eq!(
            decode(0x17ff_ffed),
            Word::Branch {
                link: false,
                imm26: -19
            }
        );
        assert_eq!(
            decode(0xaa01_03e2),
            Word::LogicalReg {
                sf: 1,
                opc: 1,
                shift: 0,
                n: 0,
                rm: 1,
                imm6: 0,
                rn: 31,
                rd: 2
            }
        );
    }

    #[test]
    fn move_wide_chain_composes_negative_and_wide_constants() {
        let mut f = MachFunction::new("chain".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        // MOVZ X1,#0xfffd ; MOVK X1,#0xffff,lsl#16 ; MOVK lsl#32 ; MOVK lsl#48 ; SUB X2,X0,X1
        let seq = vec![
            (AArch64Opcode::Movz, vec![x(1), imm(0xfffd)]),
            (AArch64Opcode::Movk, vec![x(1), imm(0xffff), imm(16)]),
            (AArch64Opcode::Movk, vec![x(1), imm(0xffff), imm(32)]),
            (AArch64Opcode::Movk, vec![x(1), imm(0xffff), imm(48)]),
            (AArch64Opcode::SubRR, vec![x(2), x(0), x(1)]),
        ];
        for (op, ops) in seq {
            let id = f.push_inst(MachInst::new(op, ops));
            f.append_inst(entry, id);
        }
        f.block_order = vec![entry];
        let words = [
            0xd29f_ffa1u32,
            0xf2bf_ffe1,
            0xf2df_ffe1,
            0xf2ff_ffe1,
            0xcb01_0002,
        ];
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        let layout = Layout::derive(&f, &code).unwrap();
        let es = &layout.blocks[0].1;
        assert_eq!(chain_value(es, 4, 1, "t").unwrap(), (-3i64) as u64);
        // A wrong MOVK chunk (0xfffe at lsl #16) changes the value.
        let bad = patch(&code, 4, 0xf2bf_ffc1);
        let layout = Layout::derive(&f, &bad).unwrap();
        assert!(chain_value(&layout.blocks[0].1, 4, 1, "t").is_err());
    }

    /// A W-form `MOVK` zeroes the upper 32 bits, so an older X-form chunk in
    /// halfword 2 or 3 does not survive it: `MOVZ X1, #1, LSL #32 ; MOVK W1,
    /// #5` leaves 5, not `0x1_0000_0005`.
    #[test]
    fn move_wide_chain_honours_w_form_zeroing() {
        let mut f = MachFunction::new("wchain".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let w = |n: u16| MachOperand::PReg(PReg::new(32 + n));
        let seq = vec![
            (AArch64Opcode::Movz, vec![x(1), imm(1), imm(32)]),
            (AArch64Opcode::Movk, vec![w(1), imm(5)]),
            (AArch64Opcode::SubRR, vec![x(2), x(0), x(1)]),
        ];
        for (op, ops) in seq {
            let id = f.push_inst(MachInst::new(op, ops));
            f.append_inst(entry, id);
        }
        f.block_order = vec![entry];
        let words = [0xd2c0_0021u32, 0x7280_00a1, 0xcb01_0002];
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        let layout = Layout::derive(&f, &code).unwrap();
        assert_eq!(chain_value(&layout.blocks[0].1, 2, 1, "t").unwrap(), 5);
    }
    // -----------------------------------------------------------------------
    // Configurable dispatch: every word hand-encoded from the Arm ARM field
    // layout (helpers below), not produced by the encoder.
    // -----------------------------------------------------------------------

    /// One entry-block instruction: intent, word, spill-slot flag.
    type Item = (AArch64Opcode, Vec<MachOperand>, u32, bool);

    fn mem(base: u16, offset: i64) -> MachOperand {
        MachOperand::MemOp {
            base: PReg::new(base),
            offset,
        }
    }

    fn cmp_x_imm(rn: u32, imm: u32) -> u32 {
        0xf100_001f | (imm << 10) | (rn << 5)
    }

    fn ldur_x(rt: u32, rn: u32, imm9: i32) -> u32 {
        0xf840_0000 | (((imm9 as u32) & 0x1ff) << 12) | (rn << 5) | rt
    }

    fn stur_x(rt: u32, rn: u32, imm9: i32) -> u32 {
        0xf800_0000 | (((imm9 as u32) & 0x1ff) << 12) | (rn << 5) | rt
    }

    fn sub_x_imm(rd: u32, rn: u32, imm: u32) -> u32 {
        0xd100_0000 | (imm << 10) | (rn << 5) | rd
    }

    fn mov_x(rd: u32, rm: u32) -> u32 {
        0xaa00_03e0 | (rm << 16) | rd
    }

    fn reload(rt: u16, base: u16, offset: i64) -> Item {
        (
            AArch64Opcode::LdrRI,
            vec![x(rt), mem(base, offset)],
            ldur_x(u32::from(rt), u32::from(base), offset as i32),
            true,
        )
    }

    fn spill(rt: u16, base: u16, offset: i64) -> Item {
        (
            AArch64Opcode::StrRI,
            vec![x(rt), mem(base, offset)],
            stur_x(u32::from(rt), u32::from(base), offset as i32),
            true,
        )
    }

    struct Dispatch {
        /// Before the bounds compare.
        pre: Vec<Item>,
        cmp_reg: u16,
        bound: u32,
        /// Between the ADR and the table load.
        mid: Vec<Item>,
        index_reg: u16,
        min_val: i64,
        /// Table entry `k` (1..=6) lands on `arms[k]`; `arms[0]` is the
        /// default. `bhi_arm` names the arm the bounds branch targets.
        bhi_arm: usize,
    }

    impl Default for Dispatch {
        fn default() -> Self {
            Self {
                pre: Vec::new(),
                cmp_reg: 0,
                bound: 5,
                mid: Vec::new(),
                index_reg: 0,
                min_val: 0,
                bhi_arm: 0,
            }
        }
    }

    /// `pre; CMP Xc, #bound; B.HI arms[bhi_arm]; ADR X1, table; mid; LDRSW
    /// X2, [X1, Xi, LSL #2]; ADD X0, X1, X2; BR X0`, then seven `MOVZ X0, #1;
    /// RET` arms laid out in reverse and a six-entry table.
    fn dispatch(d: &Dispatch) -> (MachFunction, Vec<u8>) {
        let mut f = MachFunction::new("dispatch".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let arms: Vec<BlockId> = (0..7).map(|_| f.create_block()).collect();
        let n = (d.pre.len() + d.mid.len() + 6) as i64;
        let arm_at = |k: usize| 4 * n + 8 * (6 - k as i64);
        let table = 4 * n + 56;
        let mut items: Vec<Item> = d.pre.clone();
        let hi_pos = items.len() as i64 + 1;
        let imm19 = (arm_at(d.bhi_arm) - 4 * hi_pos) / 4;
        items.push((
            AArch64Opcode::CmpRI,
            vec![x(d.cmp_reg), imm(i64::from(d.bound))],
            cmp_x_imm(u32::from(d.cmp_reg), d.bound),
            false,
        ));
        items.push((
            AArch64Opcode::BCond,
            vec![imm(8), imm(imm19)],
            0x5400_0000 | (((imm19 as u32) & 0x7ffff) << 5) | 8,
            false,
        ));
        let adr_pos = items.len() as i64;
        let adr = table - 4 * adr_pos;
        items.push((
            AArch64Opcode::Adr,
            vec![x(1), MachOperand::JumpTableIndex(0)],
            0x1000_0000 | (((adr as u32) & 3) << 29) | ((((adr >> 2) as u32) & 0x7ffff) << 5) | 1,
            false,
        ));
        items.extend(d.mid.iter().cloned());
        items.push((
            AArch64Opcode::LdrswRO,
            vec![x(2), x(1), x(d.index_reg)],
            0xb8a0_7822 | (u32::from(d.index_reg) << 16),
            false,
        ));
        items.push((
            AArch64Opcode::AddRR,
            vec![x(0), x(1), x(2)],
            0x8b02_0020,
            false,
        ));
        items.push((AArch64Opcode::Br, vec![x(0)], 0xd61f_0000, false));
        assert_eq!(items.len() as i64, n);
        let mut words = Vec::new();
        for (op, ops, word, flagged) in items {
            let mut inst = MachInst::new(op, ops);
            if flagged {
                inst.flags
                    .insert(trust_cg_ir::inst::InstFlags::SPILL_SLOT_ACCESS);
            }
            let id = f.push_inst(inst);
            f.append_inst(entry, id);
            words.push(word);
        }
        let mut order = vec![entry];
        for &arm in arms.iter().rev() {
            let id = f.push_inst(MachInst::new(AArch64Opcode::Movz, vec![x(0), imm(1)]));
            f.append_inst(arm, id);
            let id = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![x(30)]));
            f.append_inst(arm, id);
            words.push(0xd280_0020);
            words.push(0xd65f_03c0);
            order.push(arm);
        }
        f.block_order = order;
        f.block_mut(entry).succs = arms.clone();
        f.jump_tables.push(JumpTableData {
            min_val: d.min_val,
            targets: arms[1..].to_vec(),
        });
        let mut code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        for k in 1..=6 {
            code.extend_from_slice(&((arm_at(k) - table) as i32).to_le_bytes());
        }
        (f, code)
    }

    fn identity_refused(result: Result<SwitchBindingReport>) -> bool {
        matches!(
            result,
            Err(SwitchBindingError::Chain {
                what: "index identity",
                ..
            })
        )
    }

    #[test]
    fn configurable_dispatch_binds() {
        let (f, code) = dispatch(&Dispatch::default());
        let report = check_aarch64_switch_dispatch(&f, &code).unwrap();
        assert_eq!((report.jump_tables, report.table_entries), (1, 6));
    }

    /// Corruptions that keep word and intent consistent pass the generic
    /// word-versus-intent comparison, so each is refuted only by the semantic
    /// check it targets: removing that check turns its case into an accept.
    #[test]
    fn intent_consistent_corruptions_reach_each_semantic_check() {
        // Bound one past the table.
        let (f, code) = dispatch(&Dispatch {
            bound: 6,
            ..Dispatch::default()
        });
        assert!(matches!(
            check_aarch64_switch_dispatch(&f, &code),
            Err(SwitchBindingError::Bounds { ref detail, .. }) if detail.contains("does not cover")
        ));
        // Bound one short of the table.
        let (f, code) = dispatch(&Dispatch {
            bound: 4,
            ..Dispatch::default()
        });
        assert!(matches!(
            check_aarch64_switch_dispatch(&f, &code),
            Err(SwitchBindingError::Bounds { ref detail, .. }) if detail.contains("does not cover")
        ));
        // Bounds compared on another live-in register than the table index.
        let (f, code) = dispatch(&Dispatch {
            cmp_reg: 3,
            ..Dispatch::default()
        });
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // A table target the recorded CFG does not name.
        let (mut f, code) = dispatch(&Dispatch::default());
        let dropped = f.jump_tables[0].targets[2];
        f.block_mut(f.entry).succs.retain(|b| *b != dropped);
        assert!(matches!(
            check_aarch64_switch_dispatch(&f, &code),
            Err(SwitchBindingError::TableTargetNotSuccessor { entry: 2, .. })
        ));
        // A non-zero min_val with no normalization.
        let (f, code) = dispatch(&Dispatch {
            min_val: 3,
            ..Dispatch::default()
        });
        assert!(matches!(
            check_aarch64_switch_dispatch(&f, &code),
            Err(SwitchBindingError::Normalization { .. })
        ));
        // Normalization by a constant other than min_val.
        let sub = |k: u32| -> Item {
            (
                AArch64Opcode::SubRI,
                vec![x(3), x(0), imm(i64::from(k))],
                sub_x_imm(3, 0, k),
                false,
            )
        };
        let normalized = |k: u32| Dispatch {
            pre: vec![sub(k)],
            cmp_reg: 3,
            index_reg: 3,
            min_val: 3,
            ..Dispatch::default()
        };
        let (f, code) = dispatch(&normalized(3));
        check_aarch64_switch_dispatch(&f, &code).unwrap();
        let (f, code) = dispatch(&normalized(4));
        assert!(matches!(
            check_aarch64_switch_dispatch(&f, &code),
            Err(SwitchBindingError::Normalization { ref detail, .. })
                if detail.contains("subtracts 4 but min_val is 3")
        ));
        // The default edge on a table arm while one successor lies outside.
        let (f, code) = dispatch(&Dispatch {
            bhi_arm: 1,
            ..Dispatch::default()
        });
        assert!(matches!(
            check_aarch64_switch_dispatch(&f, &code),
            Err(SwitchBindingError::Bounds { ref detail, .. })
                if detail.contains("only successor outside the table")
        ));
    }

    /// A 64-bit register copy of the index binds whether its intent is
    /// `MovR` or `MOVXrr`, and only when the intent names the same copy.
    #[test]
    fn index_copies_bind_through_both_copy_intents() {
        for op in [AArch64Opcode::MovR, AArch64Opcode::MOVXrr] {
            let (f, code) = dispatch(&Dispatch {
                mid: vec![(op, vec![x(3), x(0)], mov_x(3, 0), false)],
                index_reg: 3,
                ..Dispatch::default()
            });
            check_aarch64_switch_dispatch(&f, &code).unwrap();
        }
        // The intent copies X4, the word X0: not followed.
        let (f, code) = dispatch(&Dispatch {
            mid: vec![(AArch64Opcode::MOVXrr, vec![x(3), x(4)], mov_x(3, 0), false)],
            index_reg: 3,
            ..Dispatch::default()
        });
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // A copy of another register.
        let (f, code) = dispatch(&Dispatch {
            mid: vec![(AArch64Opcode::MOVXrr, vec![x(3), x(4)], mov_x(3, 4), false)],
            index_reg: 3,
            ..Dispatch::default()
        });
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
    }

    /// The register allocator may reload a spilled index once for the bounds
    /// compare and once for the table load; both reloads read one value only
    /// while nothing between them can write the slot.
    #[test]
    fn spill_reloads_of_the_index_bind_only_without_an_intervening_writer() {
        let reloaded = |mid: Vec<Item>| Dispatch {
            pre: vec![reload(16, 29, -88)],
            cmp_reg: 16,
            mid: [mid, vec![reload(16, 29, -88)]].concat(),
            index_reg: 16,
            ..Dispatch::default()
        };
        let (f, code) = dispatch(&reloaded(vec![]));
        check_aarch64_switch_dispatch(&f, &code).unwrap();
        // A store to a disjoint slot through the same base.
        let (f, code) = dispatch(&reloaded(vec![spill(5, 29, -96)]));
        check_aarch64_switch_dispatch(&f, &code).unwrap();
        // A store to the slot itself.
        let (f, code) = dispatch(&reloaded(vec![spill(5, 29, -88)]));
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // An overlapping 4-byte store: STUR W5, [X29, #-84].
        let (f, code) = dispatch(&reloaded(vec![(
            AArch64Opcode::StrRI,
            vec![MachOperand::PReg(PReg::new(32 + 5)), mem(29, -84)],
            0xb800_0000 | ((((-84i32) as u32) & 0x1ff) << 12) | (29 << 5) | 5,
            false,
        )]));
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // A store through another base register.
        let (f, code) = dispatch(&reloaded(vec![(
            AArch64Opcode::StrRI,
            vec![x(5), mem(8, 0)],
            stur_x(5, 8, 0),
            false,
        )]));
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // A call.
        let (f, code) = dispatch(&reloaded(vec![(
            AArch64Opcode::Bl,
            vec![imm(100)],
            0x9400_0064,
            false,
        )]));
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // A BL word whose intent does not say call: the word alone refuses.
        let mut quiet_call = MachInst::new(AArch64Opcode::Bl, vec![imm(100)]);
        quiet_call.flags = trust_cg_ir::inst::InstFlags::default();
        assert!(!quiet_call.writes_memory() && !quiet_call.flags.is_call());
        let (mut f, code) = dispatch(&reloaded(vec![(
            AArch64Opcode::Nop,
            vec![],
            0x9400_0064,
            false,
        )]));
        let slot = f.block(f.entry).insts[4];
        f.insts[slot.0 as usize] = quiet_call;
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // The base register rewritten between the reloads: ADD X29, X29, #16.
        let add_fp = || -> Item {
            (
                AArch64Opcode::AddRI,
                vec![x(29), x(29), imm(16)],
                0x9100_43bd,
                false,
            )
        };
        let (f, code) = dispatch(&reloaded(vec![add_fp()]));
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // A store before the base is rewritten does not supply a reload
        // after it: `[X29 + 16 - 88]` is another slot than the stored one.
        let (f, code) = dispatch(&Dispatch {
            pre: vec![spill(3, 29, -88), add_fp()],
            cmp_reg: 3,
            mid: vec![reload(16, 29, -88)],
            index_reg: 16,
            ..Dispatch::default()
        });
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // Without the rewrite the same reload is the stored register.
        let (f, code) = dispatch(&Dispatch {
            pre: vec![spill(3, 29, -88)],
            cmp_reg: 3,
            mid: vec![reload(16, 29, -88)],
            index_reg: 16,
            ..Dispatch::default()
        });
        check_aarch64_switch_dispatch(&f, &code).unwrap();
        // A reload whose intent is not a flagged spill access.
        let mut unflagged = reload(16, 29, -88);
        unflagged.3 = false;
        let (f, code) = dispatch(&Dispatch {
            pre: vec![reload(16, 29, -88)],
            cmp_reg: 16,
            mid: vec![unflagged],
            index_reg: 16,
            ..Dispatch::default()
        });
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
        // SP-based reloads are not followed (SP writes are not tracked).
        let (f, code) = dispatch(&Dispatch {
            pre: vec![reload(16, 31, 8)],
            cmp_reg: 16,
            mid: vec![reload(16, 31, 8)],
            index_reg: 16,
            ..Dispatch::default()
        });
        assert!(identity_refused(check_aarch64_switch_dispatch(&f, &code)));
    }

    /// A reload whose spill store is in the block is followed to the stored
    /// register, so the normalization `SUB` is still found.
    #[test]
    fn a_spilled_normalized_index_reaches_its_sub() {
        let normalized = |k: u32| Dispatch {
            pre: vec![
                (
                    AArch64Opcode::SubRI,
                    vec![x(3), x(0), imm(i64::from(k))],
                    sub_x_imm(3, 0, k),
                    false,
                ),
                spill(3, 29, -88),
                spill(7, 29, -96),
                reload(16, 29, -88),
            ],
            cmp_reg: 16,
            mid: vec![reload(17, 29, -88)],
            index_reg: 17,
            min_val: 3,
            ..Dispatch::default()
        };
        let (f, code) = dispatch(&normalized(3));
        check_aarch64_switch_dispatch(&f, &code).unwrap();
        let (f, code) = dispatch(&normalized(2));
        assert!(matches!(
            check_aarch64_switch_dispatch(&f, &code),
            Err(SwitchBindingError::Normalization { .. })
        ));
    }

    /// Forward evaluation with each word's width: an X-form `MOVK` of an
    /// upper halfword after a W-form base sets that halfword.
    #[test]
    fn x_form_movk_after_a_w_form_base_keeps_its_upper_halfword() {
        let mut f = MachFunction::new("wx".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let w = |n: u16| MachOperand::PReg(PReg::new(32 + n));
        let seq = vec![
            (AArch64Opcode::Movz, vec![w(9), imm(5)]),
            (AArch64Opcode::Movk, vec![x(9), imm(1), imm(32)]),
            (AArch64Opcode::CmpRR, vec![x(0), x(9)]),
        ];
        for (op, ops) in seq {
            let id = f.push_inst(MachInst::new(op, ops));
            f.append_inst(entry, id);
        }
        f.block_order = vec![entry];
        // MOVZ W9, #5 ; MOVK X9, #1, LSL #32 ; CMP X0, X9
        let words = [0x5280_00a9u32, 0xf2c0_0029, 0xeb09_001f];
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        let layout = Layout::derive(&f, &code).unwrap();
        assert_eq!(
            chain_value(&layout.blocks[0].1, 2, 9, "t").unwrap(),
            0x1_0000_0005
        );
    }

    /// `entry: <materialize> r1, #23 ; CMP r0, r1 ; B.EQ taken ; RET` and
    /// `taken: RET`, with the materialization spelled by `op`/`ops` and
    /// encoded as `mov_word`. `wide` picks the X (true) or W form of the
    /// compare registers.
    fn materialized_compare(
        op: AArch64Opcode,
        ops: Vec<MachOperand>,
        mov_word: u32,
        wide: bool,
    ) -> (MachFunction, Vec<u8>) {
        let mut f = MachFunction::new("matcmp".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let taken = f.create_block();
        let reg = |n: u16| {
            if wide {
                x(n)
            } else {
                MachOperand::PReg(PReg::new(32 + n))
            }
        };
        for (op, ops) in [
            (op, ops),
            (AArch64Opcode::CmpRR, vec![reg(0), reg(1)]),
            (AArch64Opcode::BCond, vec![imm(0), imm(2)]),
            (AArch64Opcode::Ret, vec![x(30)]),
        ] {
            let id = f.push_inst(MachInst::new(op, ops));
            f.append_inst(entry, id);
        }
        let id = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![x(30)]));
        f.append_inst(taken, id);
        f.block_order = vec![entry, taken];
        f.block_mut(entry).succs = vec![taken];
        // CMP X0, X1 / CMP W0, W1 ; B.EQ +2 words ; RET ; RET
        let cmp = if wide { 0xeb01_001f } else { 0x6b01_001f };
        let words = [mov_word, cmp, 0x5400_0040u32, 0xd65f_03c0, 0xd65f_03c0];
        (f, words.iter().flat_map(|w| w.to_le_bytes()).collect())
    }

    /// The encoder spells `MOVZ Rd, #imm16, LSL #0` from four intents:
    /// canonical `Movz` and the shift-free `MovI`, `MOVZXi` and `MOVZWi`
    /// (`aarch64::encode`). A compare constant materialized by any of them
    /// binds; before the intent class was widened, a `MovI` constant refused
    /// every AArch64 compile that reached this compare shape with
    /// "compare constant decodes as `Movz x0, #K, lsl #0` but the intent is
    /// `MovI [..]`" (eight Trust trust-ir-cg run-make tests, 2026-09-28).
    #[test]
    fn compare_constant_binds_through_every_movz_intent() {
        let w1 = MachOperand::PReg(PReg::new(33));
        let cases = [
            (
                AArch64Opcode::Movz,
                vec![x(1), imm(23)],
                0xd280_02e1u32,
                true,
            ),
            (
                AArch64Opcode::Movz,
                vec![x(1), imm(23), imm(0)],
                0xd280_02e1,
                true,
            ),
            (AArch64Opcode::MovI, vec![x(1), imm(23)], 0xd280_02e1, true),
            (
                AArch64Opcode::MOVZXi,
                vec![x(1), imm(23)],
                0xd280_02e1,
                true,
            ),
            (
                AArch64Opcode::MOVZWi,
                vec![w1.clone(), imm(23)],
                0x5280_02e1,
                false,
            ),
            (AArch64Opcode::MovI, vec![w1, imm(23)], 0x5280_02e1, false),
        ];
        for (op, ops, word, wide) in cases {
            let label = format!("{op:?} {ops:?}");
            let (f, code) = materialized_compare(op, ops, word, wide);
            let report = check_aarch64_switch_dispatch(&f, &code)
                .unwrap_or_else(|e| panic!("{label}: must bind, got {e}"));
            assert_eq!(report.compare_groups, 1, "{label}");
            assert_eq!(report.materialized_constants, 1, "{label}");
        }
    }

    /// Widening the MOVZ intent class keeps every word-versus-intent field
    /// bound: a `MovI` or typed-alias intent whose word differs in value,
    /// register, width, opc or halfword, or whose intent carries a shift
    /// operand the encoder refuses, is still refused.
    #[test]
    fn movz_alias_compare_constant_corruptions_refute() {
        let w1 = MachOperand::PReg(PReg::new(33));
        let movi = || (AArch64Opcode::MovI, vec![x(1), imm(23)]);
        let cases = [
            ("MovI, word #24", movi(), 0xd280_0301u32, true),
            ("MovI, word writes X2", movi(), 0xd280_02e2, true),
            ("MovI, word MOVN", movi(), 0x9280_02e1, true),
            ("MovI, word LSL #16", movi(), 0xd2a0_02e1, true),
            ("MovI, W-form word", movi(), 0x5280_02e1, true),
            (
                "MovI with a shift operand",
                (AArch64Opcode::MovI, vec![x(1), imm(23), imm(0)]),
                0xd280_02e1,
                true,
            ),
            (
                "MOVZXi, word LSL #16",
                (AArch64Opcode::MOVZXi, vec![x(1), imm(23)]),
                0xd2a0_02e1,
                true,
            ),
            (
                "MOVZWi, X-form word",
                (AArch64Opcode::MOVZWi, vec![w1, imm(23)]),
                0xd280_02e1,
                false,
            ),
            (
                "MovR is not a materialization",
                (AArch64Opcode::MovR, vec![x(1), imm(23)]),
                0xd280_02e1,
                true,
            ),
        ];
        for (label, (op, ops), word, wide) in cases {
            let (f, code) = materialized_compare(op, ops, word, wide);
            let result = check_aarch64_switch_dispatch(&f, &code);
            assert!(
                matches!(
                    result,
                    Err(SwitchBindingError::IntentMismatch {
                        what: "compare constant",
                        ..
                    } | SwitchBindingError::Constant {
                        what: "compare constant",
                        ..
                    })
                ),
                "{label}: must refute as a compare-constant refusal, got {result:?}"
            );
        }
    }
}
