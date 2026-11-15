// trust-cg-codegen/aarch64/layout_crosscheck.rs - Final-layout offset cross-check
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Independent AArch64 final-layout cross-check.
//!
//! Late passes (post-RA post-index formation, branch forwarding, loop-head
//! alignment padding, branch resolution and relaxation) all change byte
//! offsets after the structural validators ran. This check re-derives every
//! offset from the final layout alone and compares it with the encoded words,
//! not with the encoder's own bookkeeping:
//!
//! - every laid-out block start is recomputed from `block_order` and the
//!   encoder's one-word-per-non-pseudo emission rule, and the encoder's block
//!   map must agree;
//! - every local branch word (B, B.cond, CBZ/CBNZ, TBZ/TBNZ) is decoded by
//!   bit extraction; its displacement must equal a still-symbolic intent's
//!   layout target, or a resolved intent's immediate, and its target must be
//!   a laid-out block start, a validated one-instruction skip, a branch
//!   internal to an exactly matched expanded LL/SC retry loop
//!   ([`crate::llsc::llsc_internal_branches`]), or (for a resolved tail call
//!   only) outside the function. Under CFG authority the target block and
//!   every non-terminated fallthrough must be a recorded successor;
//! - every jump-table ADR must address its table's recomputed position, and
//!   every table entry must equal its target's recomputed offset from the
//!   table base, with no trailing bytes;
//! - ADR/LDR-literal immediates must stay inside the emitted image;
//! - every symbolic fixup must sit on the exact emitted instruction that
//!   names a symbol, name exactly that symbol (exact-module binding included),
//!   patch the word class its relocation kind requires with the relocated
//!   field still the zero placeholder, and every such instruction must carry
//!   exactly one fixup.
//!
//! This is a consistency check of the final bytes against the final layout
//! and the recorded CFG. It is not a proof of the passes and it cannot
//! distinguish two recorded successors that were exchanged; semantic source
//! binders cover that for their admitted shapes.

use std::collections::BTreeMap;
use trust_cg_ir::fast_hash::FxHashMap as HashMap;

use crate::macho::AArch64RelocKind;
use crate::macho::fixup::{FixupList, FixupTarget};
use trust_cg_ir::{AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand};

/// A restriction on separately encoded bytes before the consuming Core
/// publisher chooses their final image position. No existing layout error or
/// source/encoding contract gains a new accepted shape.
#[cfg(feature = "verify")]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum RebasedFunctionPlacementError {
    #[error("rebased function image has non-word extent {len}")]
    RebasedFunctionExtent { len: usize },
    #[error(
        "rebased function requires an explicit placement contract for {what} word {word:#010x} at byte {offset}"
    )]
    RebasedPcRelativeWord {
        offset: usize,
        word: u32,
        what: &'static str,
    },
    #[error(
        "rebased branch word at byte {offset} targets byte {target} outside its {image}-byte function"
    )]
    RebasedBranchOutOfImage {
        offset: usize,
        target: i128,
        image: usize,
    },
}

/// A final-layout disagreement. Every variant fails the encode closed.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum LayoutCrossCheckError {
    #[error("invalid local table-address expansion: {0}")]
    AddressExpansion(String),
    #[error(
        "block {block:?} starts at byte {layout} in the final layout, but the encoder recorded {encoder:?}"
    )]
    BlockOffset {
        block: BlockId,
        layout: u32,
        encoder: Option<u32>,
    },
    #[error("encoder block map has {encoder} entries for {layout} laid-out blocks")]
    BlockMapSize { encoder: usize, layout: usize },
    #[error("final layout has {layout} body bytes but the image has only {image}")]
    ImageTooShort { layout: usize, image: usize },
    #[error(
        "word {word:#010x} at byte {offset} is not the {expected} encoding its intent {opcode:?} requires"
    )]
    WordClass {
        offset: u32,
        word: u32,
        opcode: AArch64Opcode,
        expected: &'static str,
    },
    #[error(
        "branch word at byte {offset} encodes a {encoded}-word displacement, but the final layout requires {expected}"
    )]
    Displacement {
        offset: u32,
        encoded: i64,
        expected: i64,
    },
    #[error(
        "branch word at byte {offset} targets byte {target}, which is not a laid-out block start, validated skip, expanded LL/SC loop branch or resolved tail call"
    )]
    BranchTarget { offset: u32, target: i64 },
    #[error("branch at byte {offset} names block {target:?}, which is not laid out")]
    UnlaidTarget { offset: u32, target: BlockId },
    #[error(
        "branch word at byte {offset} in block {block:?} targets block {target:?}, which is not a recorded successor"
    )]
    SuccessorMismatch {
        offset: u32,
        block: BlockId,
        target: BlockId,
    },
    #[error("block {block:?} falls through to {next:?}, which is not a recorded successor")]
    FallthroughMismatch { block: BlockId, next: BlockId },
    #[error(
        "{what} word at byte {offset} addresses byte {target}, outside the {image}-byte emitted image"
    )]
    PcRelativeOutOfImage {
        what: &'static str,
        offset: u32,
        target: i64,
        image: usize,
    },
    #[error("jump-table ADR at byte {offset} names missing jump table {table}")]
    MissingJumpTable { offset: u32, table: u32 },
    #[error(
        "jump-table ADR at byte {offset} addresses byte {encoded}, but table {table} is laid out at byte {layout}"
    )]
    JumpTableAddress {
        offset: u32,
        table: u32,
        encoded: i64,
        layout: usize,
    },
    #[error("jump table {table} targets block {target:?}, which is not laid out")]
    JumpTableTarget { table: u32, target: BlockId },
    #[error(
        "jump table {table} entry {entry} encodes {encoded}, but block {target:?} is {expected} bytes from the table"
    )]
    JumpTableEntry {
        table: u32,
        entry: usize,
        target: BlockId,
        encoded: i64,
        expected: i64,
    },
    #[error(
        "jump table {table} in block {block:?} targets block {target:?}, which is not a recorded successor"
    )]
    JumpTableSuccessor {
        table: u32,
        block: BlockId,
        target: BlockId,
    },
    #[error("image is {actual} bytes, but the body and jump tables occupy {expected}")]
    TrailingBytes { expected: usize, actual: usize },
    #[error("fixup {index} ({kind:?}) at byte {offset} is not on an emitted symbolic instruction")]
    FixupSite {
        index: usize,
        offset: u32,
        kind: AArch64RelocKind,
    },
    #[error("fixups {first} and {second} both patch byte {offset}")]
    DuplicateFixup {
        first: usize,
        second: usize,
        offset: u32,
    },
    #[error(
        "fixup {index} ({kind:?}) at byte {offset} patches word {word:#010x}, which is not a {expected} placeholder with a zero relocated field"
    )]
    FixupPlaceholder {
        index: usize,
        offset: u32,
        kind: AArch64RelocKind,
        word: u32,
        expected: &'static str,
    },
    #[error(
        "fixup {index} ({kind:?}) at byte {offset} targets {target:?}, but its instruction requires {expected}"
    )]
    FixupSymbol {
        index: usize,
        offset: u32,
        kind: AArch64RelocKind,
        target: FixupTarget,
        expected: String,
    },
    #[error("symbolic instruction {inst:?} at byte {offset} has no fixup")]
    MissingFixup { inst: InstId, offset: u32 },
}

struct Emitted<'a> {
    offset: u32,
    block: BlockId,
    id: InstId,
    inst: &'a MachInst,
}

fn sign_extend(value: u32, bits: u32) -> i64 {
    let shift = 64 - bits;
    ((u64::from(value) << shift) as i64) >> shift
}

fn word_at(code: &[u8], offset: usize) -> Option<u32> {
    let bytes = code.get(offset..offset.checked_add(4)?)?;
    Some(u32::from_le_bytes(bytes.try_into().ok()?))
}

/// Restrict a separately encoded function to the placement domain currently
/// admitted by the consuming Core publisher. Empty symbolic fixups alone do
/// not establish this: locally resolved ADRP/page-low arithmetic can depend on
/// a function's page position. No placement transport is claimed for address
/// materialization or literal pools here.
///
/// Conservatively inspect every aligned word, including possible data, and
/// refuse the complete Arm ARM PC-relative-address class (ADR/ADRP) and literal
/// load/prefetch class (integer/SIMD/LDRSW/PRFM, reserved variants included).
/// False refusals on data are intentional. Direct relative control-flow must
/// stay within this same function; its CFG and meaning remain the existing
/// final-layout cross-check and function certificate's responsibility.
#[cfg(feature = "verify")]
pub(crate) fn check_rebased_function_placement(
    code: &[u8],
) -> Result<(), RebasedFunctionPlacementError> {
    if code.len() % 4 != 0 {
        return Err(RebasedFunctionPlacementError::RebasedFunctionExtent { len: code.len() });
    }
    for (index, bytes) in code.as_chunks::<4>().0.iter().enumerate() {
        let word = u32::from_le_bytes(*bytes);
        // ADR and ADRP differ only in bit31; immediate and Rd bits are free.
        let what = if word & 0x1F00_0000 == 0x1000_0000 {
            Some("ADR/ADRP")
        // The literal class leaves opc[31:30], V[26], imm19 and Rt free.
        } else if word & 0x3B00_0000 == 0x1800_0000 {
            Some("PC-relative literal load/prefetch")
        } else {
            None
        };
        if let Some(what) = what {
            return Err(RebasedFunctionPlacementError::RebasedPcRelativeWord {
                offset: index * 4,
                word,
                what,
            });
        }
        // Architectural relative branch classes. Reuse this owner's signed
        // field arithmetic; a resolved out-of-function tail edge must not gain
        // rebase authority merely because it has no remaining symbolic fixup.
        let displacement = if word & 0x7C00_0000 == 0x1400_0000 {
            Some(sign_extend(word & 0x03FF_FFFF, 26))
        } else if word & 0xFE00_0000 == 0x5400_0000 || word & 0x7E00_0000 == 0x3400_0000 {
            Some(sign_extend((word >> 5) & 0x7_FFFF, 19))
        } else if word & 0x7E00_0000 == 0x3600_0000 {
            Some(sign_extend((word >> 5) & 0x3FFF, 14))
        } else {
            None
        };
        if let Some(displacement) = displacement {
            let offset = index * 4;
            let target = offset as i128 + i128::from(displacement) * 4;
            if target < 0 || target >= code.len() as i128 {
                return Err(RebasedFunctionPlacementError::RebasedBranchOutOfImage {
                    offset,
                    target,
                    image: code.len(),
                });
            }
        }
    }
    Ok(())
}

/// Operand index of a local branch target for each PC-relative branch form.
fn branch_target_operand(opcode: AArch64Opcode) -> Option<usize> {
    match opcode {
        AArch64Opcode::B | AArch64Opcode::TailCall => Some(0),
        AArch64Opcode::BCond | AArch64Opcode::Bcc | AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
            Some(1)
        }
        AArch64Opcode::Tbz | AArch64Opcode::Tbnz => Some(2),
        _ => None,
    }
}

/// Decode the word displacement of a branch form by independent bit
/// extraction, after checking the word belongs to that form's class.
fn decode_branch(opcode: AArch64Opcode, word: u32) -> Result<i64, &'static str> {
    match opcode {
        AArch64Opcode::B | AArch64Opcode::TailCall if word & 0xFC00_0000 == 0x1400_0000 => {
            Ok(sign_extend(word & 0x03FF_FFFF, 26))
        }
        AArch64Opcode::B | AArch64Opcode::TailCall => Err("B imm26"),
        AArch64Opcode::BCond | AArch64Opcode::Bcc if word & 0xFF00_0010 == 0x5400_0000 => {
            Ok(sign_extend((word >> 5) & 0x7_FFFF, 19))
        }
        AArch64Opcode::BCond | AArch64Opcode::Bcc => Err("B.cond imm19"),
        AArch64Opcode::Cbz | AArch64Opcode::Cbnz if word & 0x7E00_0000 == 0x3400_0000 => {
            Ok(sign_extend((word >> 5) & 0x7_FFFF, 19))
        }
        AArch64Opcode::Cbz | AArch64Opcode::Cbnz => Err("CBZ/CBNZ imm19"),
        AArch64Opcode::Tbz | AArch64Opcode::Tbnz if word & 0x7E00_0000 == 0x3600_0000 => {
            Ok(sign_extend((word >> 5) & 0x3FFF, 14))
        }
        _ => Err("TBZ/TBNZ imm14"),
    }
}

fn decode_adr(word: u32) -> Option<i64> {
    (word & 0x9F00_0000 == 0x1000_0000)
        .then(|| sign_extend((((word >> 5) & 0x7_FFFF) << 2) | ((word >> 29) & 0b11), 21))
}

fn is_symbolic(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::BlrTlsdesc
        || inst
            .operands
            .iter()
            .any(|op| op.is_symbol() || op.as_exact_module_symbol().is_some())
}

/// The fixup target the encoder must record for a symbolic instruction: the
/// single symbol it names, bound exactly when that operand is an exact module
/// symbol or the call carries [`InstFlags::EXACT_MODULE_CALL`]. `None` when
/// the instruction does not name exactly one symbol.
fn expected_fixup_target(inst: &MachInst) -> Option<FixupTarget> {
    let mut symbols = inst.operands.iter().filter_map(|op| {
        op.as_symbol()
            .map(|name| (name, false))
            .or_else(|| op.as_exact_module_symbol().map(|name| (name, true)))
    });
    let (name, exact_operand) = symbols.next()?;
    if symbols.next().is_some() {
        return None;
    }
    let name = name.to_owned();
    Some(
        if exact_operand || inst.flags.contains(InstFlags::EXACT_MODULE_CALL) {
            FixupTarget::ExactNamedSymbol(name)
        } else {
            FixupTarget::NamedSymbol(name)
        },
    )
}

/// The instruction word class a relocation kind patches, with its relocated
/// field required to be the zero placeholder.
fn fixup_placeholder(kind: AArch64RelocKind, word: u32) -> Result<(), &'static str> {
    use AArch64RelocKind as K;
    match kind {
        K::Branch26 => (word & 0x7C00_0000 == 0x1400_0000 && word & 0x03FF_FFFF == 0)
            .then_some(())
            .ok_or("B/BL imm26"),
        K::Page21
        | K::GotLoadPage21
        | K::TlvpLoadPage21
        | K::ElfTlsieAdrGottprelPage21
        | K::ElfTlsdescAdrPage21 => (word & 0x9F00_0000 == 0x9000_0000 && word & 0x60FF_FFE0 == 0)
            .then_some(())
            .ok_or("ADRP immhi:immlo"),
        K::Pageoff12
        | K::ElfTlsleAddTprelHi12
        | K::ElfTlsleAddTprelLo12Nc
        | K::ElfTlsdescAddLo12 => (word & 0x1F80_0000 == 0x1100_0000 && word & 0x003F_FC00 == 0)
            .then_some(())
            .ok_or("ADD imm12"),
        K::GotLoadPageoff12
        | K::TlvpLoadPageoff12
        | K::ElfTlsieLd64GottprelLo12Nc
        | K::ElfTlsdescLd64Lo12
        | K::ElfLdst8AbsLo12Nc
        | K::ElfLdst16AbsLo12Nc
        | K::ElfLdst32AbsLo12Nc
        | K::ElfLdst64AbsLo12Nc
        | K::ElfLdst128AbsLo12Nc => (word & 0x3B00_0000 == 0x3900_0000 && word & 0x003F_FC00 == 0)
            .then_some(())
            .ok_or("LDR/STR unsigned imm12"),
        K::ElfTlsdescCall => (word & 0xFFFF_FC1F == 0xD63F_0000)
            .then_some(())
            .ok_or("BLR"),
        K::Unsigned | K::Subtractor | K::PointerToGot | K::Addend | K::AuthenticatedPointer => {
            Err("instruction (data-only relocation kind)")
        }
    }
}

/// Whether control can continue to the next laid-out block after `inst`.
fn hard_terminator(inst: &MachInst) -> bool {
    inst.is_unconditional_branch()
        || inst.is_return()
        || inst.opcode == AArch64Opcode::Brk
        || (inst.is_terminator() && !inst.is_conditional_branch())
}

/// Check `code` (body followed by jump tables) against the final layout of
/// `func`. `block_byte_offsets` is the encoder's own map. `fixups` is `None`
/// only for encoders that report relocations separately. `cfg_authority`
/// additionally requires every encoded edge to be a recorded successor; it is
/// set on proof-grade routes, whose CFG metadata is validated authority.
pub fn check_final_layout(
    func: &MachFunction,
    code: &[u8],
    fixups: Option<&FixupList>,
    block_byte_offsets: &std::collections::HashMap<BlockId, u32>,
    cfg_authority: bool,
) -> Result<(), LayoutCrossCheckError> {
    use LayoutCrossCheckError as E;
    trust_cg_verify::aarch64_jump_table_address::validate_expansions(func)
        .map_err(E::AddressExpansion)?;

    // 1. Recompute the layout independently of the encoder.
    let mut block_starts: BTreeMap<u32, Vec<BlockId>> = BTreeMap::new();
    let mut block_offset: HashMap<BlockId, u32> = HashMap::default();
    let mut emitted: Vec<Emitted<'_>> = Vec::new();
    let mut offset = 0u32;
    for &block in &func.block_order {
        block_starts.entry(offset).or_default().push(block);
        block_offset.insert(block, offset);
        for &id in &func.block(block).insts {
            let inst = func.inst(id);
            if inst.is_pseudo() {
                continue;
            }
            emitted.push(Emitted {
                offset,
                block,
                id,
                inst,
            });
            offset = offset.checked_add(4).ok_or(E::ImageTooShort {
                layout: usize::MAX,
                image: code.len(),
            })?;
        }
    }
    let body_len = offset as usize;
    if code.len() < body_len {
        return Err(E::ImageTooShort {
            layout: body_len,
            image: code.len(),
        });
    }
    if block_byte_offsets.len() != block_offset.len() {
        return Err(E::BlockMapSize {
            encoder: block_byte_offsets.len(),
            layout: block_offset.len(),
        });
    }
    for &block in &func.block_order {
        let layout = block_offset[&block];
        let encoder = block_byte_offsets.get(&block).copied();
        if encoder != Some(layout) {
            return Err(E::BlockOffset {
                block,
                layout,
                encoder,
            });
        }
    }
    let by_offset: HashMap<u32, usize> = emitted
        .iter()
        .enumerate()
        .map(|(index, entry)| (entry.offset, index))
        .collect();
    // Branches internal to an expanded LL/SC retry loop, by exact template
    // match over each block's pseudo-free layout: the same validated set the
    // resolved-stream CFG derivation excludes from inter-block edges. Their
    // displacements are checked against the intent like every other branch;
    // only the block-start requirement is waived, since the template pins
    // every target inside the loop.
    let mut llsc_internal = std::collections::BTreeSet::new();
    for &block in &func.block_order {
        let real: Vec<(InstId, &MachInst)> = emitted
            .iter()
            .filter(|entry| entry.block == block)
            .map(|entry| (entry.id, entry.inst))
            .collect();
        llsc_internal.extend(crate::llsc::llsc_internal_branches(&real));
    }
    let word = |entry: &Emitted<'_>| word_at(code, entry.offset as usize).unwrap_or_default();

    // 2. Local branches, PC-relative literals and jump-table ADRs.
    let mut jump_table_adrs = Vec::new();
    for (index, entry) in emitted.iter().enumerate() {
        let inst = entry.inst;
        let w = word(entry);
        if inst.opcode == AArch64Opcode::Adr {
            if let Some(table) = func.jump_table_at_address(entry.id) {
                jump_table_adrs.push((entry, table));
            } else if let Some(MachOperand::Imm(_)) = inst.operands.get(1) {
                let displacement = decode_adr(w).ok_or(E::WordClass {
                    offset: entry.offset,
                    word: w,
                    opcode: inst.opcode,
                    expected: "ADR imm21",
                })?;
                let target = i64::from(entry.offset) + displacement;
                if !(0..=code.len() as i64).contains(&target) {
                    return Err(E::PcRelativeOutOfImage {
                        what: "ADR",
                        offset: entry.offset,
                        target,
                        image: code.len(),
                    });
                }
            }
            continue;
        }
        if inst.opcode == AArch64Opcode::LdrLiteral
            && matches!(inst.operands.get(1), Some(MachOperand::Imm(_)))
        {
            let class = w & 0xBF00_0000;
            if class != 0x1800_0000 {
                return Err(E::WordClass {
                    offset: entry.offset,
                    word: w,
                    opcode: inst.opcode,
                    expected: "LDR (literal) imm19",
                });
            }
            let width = if w & 0x4000_0000 != 0 { 8 } else { 4 };
            let target = i64::from(entry.offset) + sign_extend((w >> 5) & 0x7_FFFF, 19) * 4;
            if target < 0 || target + width > code.len() as i64 {
                return Err(E::PcRelativeOutOfImage {
                    what: "LDR (literal)",
                    offset: entry.offset,
                    target,
                    image: code.len(),
                });
            }
            continue;
        }
        let Some(operand_index) = branch_target_operand(inst.opcode) else {
            continue;
        };
        let intent = match inst.operands.get(operand_index) {
            Some(MachOperand::Imm(displacement)) => Ok(*displacement),
            Some(MachOperand::Block(target)) => Err(*target),
            // Symbolic targets are relocation sites, checked below.
            _ => continue,
        };
        let encoded = decode_branch(inst.opcode, w).map_err(|expected| E::WordClass {
            offset: entry.offset,
            word: w,
            opcode: inst.opcode,
            expected,
        })?;
        let expected = match intent {
            Ok(displacement) => displacement,
            Err(target) => {
                let Some(&start) = block_offset.get(&target) else {
                    return Err(E::UnlaidTarget {
                        offset: entry.offset,
                        target,
                    });
                };
                (i64::from(start) - i64::from(entry.offset)) / 4
            }
        };
        if encoded != expected {
            return Err(E::Displacement {
                offset: entry.offset,
                encoded,
                expected,
            });
        }
        let target = i64::from(entry.offset) + encoded * 4;
        // A conditional skip over exactly one following B or BRK in the same
        // block (guard expansion and branch relaxation) is intra-block.
        let skip = inst.opcode.is_conditional_branch()
            && encoded == 2
            && emitted.get(index + 1).is_some_and(|next| {
                next.block == entry.block
                    && matches!(next.inst.opcode, AArch64Opcode::B | AArch64Opcode::Brk)
            });
        if skip || llsc_internal.contains(&entry.id) {
            continue;
        }
        let Some(targets) = u32::try_from(target)
            .ok()
            .and_then(|target| block_starts.get(&target))
        else {
            // Outside the whole emitted image: the body and its trailing jump
            // tables are this function's own bytes, never a tail-call target.
            let outside = target < 0 || target >= code.len() as i64;
            if inst.opcode == AArch64Opcode::TailCall && outside && intent.is_ok() {
                continue;
            }
            return Err(E::BranchTarget {
                offset: entry.offset,
                target,
            });
        };
        if cfg_authority {
            let succs = &func.block(entry.block).succs;
            if !targets.iter().any(|target| succs.contains(target)) {
                return Err(E::SuccessorMismatch {
                    offset: entry.offset,
                    block: entry.block,
                    target: targets[0],
                });
            }
        }
    }

    // Fallthrough edges under CFG authority.
    if cfg_authority {
        for (position, &block) in func.block_order.iter().enumerate() {
            let Some(&next) = func.block_order.get(position + 1) else {
                continue;
            };
            let last = func
                .block(block)
                .insts
                .iter()
                .map(|&id| func.inst(id))
                .rfind(|inst| !inst.is_pseudo());
            if last.is_some_and(hard_terminator) {
                continue;
            }
            // Empty blocks share their successor's start; each falls through.
            if !func.block(block).succs.contains(&next) {
                return Err(E::FallthroughMismatch { block, next });
            }
        }
    }

    // 3. Jump tables: appended after the body in ADR encounter order.
    let mut table_offset = body_len;
    for (entry, table) in jump_table_adrs {
        let w = word(entry);
        let jt = func
            .jump_tables
            .get(table as usize)
            .ok_or(E::MissingJumpTable {
                offset: entry.offset,
                table,
            })?;
        let displacement = decode_adr(w).ok_or(E::WordClass {
            offset: entry.offset,
            word: w,
            opcode: entry.inst.opcode,
            expected: "ADR imm21",
        })?;
        let encoded = if func.jump_table_address_expansions.contains_key(&entry.id) {
            let add_word = word_at(code, entry.offset as usize + 4)
                .ok_or_else(|| E::AddressExpansion("truncated address ADD".into()))?;
            trust_cg_verify::aarch64_jump_table_address::decode_expanded_address(
                func,
                entry.id,
                entry.offset,
                w,
                add_word,
            )
            .map_err(E::AddressExpansion)?
        } else {
            i64::from(entry.offset) + displacement
        };
        if encoded != table_offset as i64 {
            return Err(E::JumpTableAddress {
                offset: entry.offset,
                table,
                encoded,
                layout: table_offset,
            });
        }
        for (index, target) in jt.targets.iter().enumerate() {
            let start = *block_offset.get(target).ok_or(E::JumpTableTarget {
                table,
                target: *target,
            })?;
            let at = table_offset + 4 * index;
            let encoded = code
                .get(at..at + 4)
                .map(|bytes| i32::from_le_bytes(bytes.try_into().unwrap_or_default()))
                .ok_or(E::TrailingBytes {
                    expected: at + 4,
                    actual: code.len(),
                })?;
            let expected = i64::from(start) - table_offset as i64;
            if i64::from(encoded) != expected {
                return Err(E::JumpTableEntry {
                    table,
                    entry: index,
                    target: *target,
                    encoded: i64::from(encoded),
                    expected,
                });
            }
            if cfg_authority && !func.block(entry.block).succs.contains(target) {
                return Err(E::JumpTableSuccessor {
                    table,
                    block: entry.block,
                    target: *target,
                });
            }
        }
        table_offset += 4 * jt.targets.len();
    }
    if table_offset != code.len() {
        return Err(E::TrailingBytes {
            expected: table_offset,
            actual: code.len(),
        });
    }

    // 4. Symbolic fixups sit on exactly the emitted symbolic instructions.
    let Some(fixups) = fixups else {
        return Ok(());
    };
    let mut patched: HashMap<u32, usize> = HashMap::default();
    for (index, fixup) in fixups.iter().enumerate() {
        let site = by_offset
            .get(&fixup.offset)
            .map(|&position| &emitted[position])
            .filter(|entry| is_symbolic(entry.inst))
            .ok_or(E::FixupSite {
                index,
                offset: fixup.offset,
                kind: fixup.kind,
            })?;
        if let Some(first) = patched.insert(fixup.offset, index) {
            return Err(E::DuplicateFixup {
                first,
                second: index,
                offset: fixup.offset,
            });
        }
        let w = word(site);
        fixup_placeholder(fixup.kind, w).map_err(|expected| E::FixupPlaceholder {
            index,
            offset: fixup.offset,
            kind: fixup.kind,
            word: w,
            expected,
        })?;
        // Site, kind and placeholder agreement do not show which definition
        // the relocation reaches: bind the named symbol as well.
        let expected = expected_fixup_target(site.inst);
        if expected.as_ref() != Some(&fixup.target) {
            return Err(E::FixupSymbol {
                index,
                offset: fixup.offset,
                kind: fixup.kind,
                target: fixup.target.clone(),
                expected: expected.map_or_else(
                    || "a single named symbol operand".to_owned(),
                    |target| format!("{target:?}"),
                ),
            });
        }
    }
    if let Some(entry) = emitted
        .iter()
        .find(|entry| is_symbolic(entry.inst) && !patched.contains_key(&entry.offset))
    {
        return Err(E::MissingFixup {
            inst: entry.id,
            offset: entry.offset,
        });
    }
    Ok(())
}

#[cfg(test)]
#[path = "layout_crosscheck_tests.rs"]
mod tests;
