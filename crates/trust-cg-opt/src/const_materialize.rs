// trust-cg-opt - AArch64 Constant Materialization
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 constant materialization optimization.
//!
//! Generates compact instruction sequences to materialize arbitrary constants
//! into registers. Constant materialization is restricted to hw0 MOVZ/MOVN
//! seeds; MOVK repairs and W-form MOVN remain proof-required verification gaps.
//!
//! # Strategies (in priority order)
//!
//! | Constant pattern | Instruction(s) | Count |
//! |------------------|----------------|-------|
//! | Zero | `MOVZ Xd, #0` | 1 |
//! | Fits in 16 bits | `MOVZ Xd, #imm` | 1 |
//! | Single non-zero high chunk | `MOVZ Xd, #0; MOVK Xd, #imm, LSL #shift` | 2 |
//! | Logical immediate (bitmask) | `ORR Xd, XZR, #imm` | 1 |
//! | MOVN (mostly-ones pattern) | `MOVN Xd, #imm` | 1 |
//! | MOVN + MOVK repairs | `MOVN #low-inverse + MOVK×high repairs` | 2-4 |
//! | 32-bit general | `MOVZ + MOVK` | 2 |
//! | 64-bit sparse | `MOVZ + MOVK×(non-zero chunks-1)` | 2-4 |
//! | 64-bit dense | `MOVZ + 3×MOVK` | 4 |
//!
//! # Logical Immediate Encoding
//!
//! ARM logical immediates encode repeating bitmask patterns as `(N, immr, imms)`.
//! The pattern is a repeating element of size 2, 4, 8, 16, 32, or 64 bits,
//! where within each element the set bits form a contiguous rotated block.
//! This encoding is used by AND, ORR, EOR with immediate operands.
//!
//! Reference: ARM Architecture Reference Manual (DDI 0487), C6.2 Data Processing - Immediate

use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::SpecialReg;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Generate a compact AArch64 instruction sequence using hw0 MOVZ/MOVN seeds.
///
/// MOVK repairs and W-form MOVN remain proof-required verification gaps; this
/// function does not claim proof coverage for the whole returned sequence.
///
/// `value` is the unsigned constant to materialize. `width` is 32 or 64.
///
/// Returns a sequence of `MachInst` (Movz, Movk, OrrRI, or Movn) that
/// loads the constant into a register. The caller is responsible for
/// assigning the destination register.
///
/// Operand conventions:
/// - Movz: `[Imm(imm16), Imm(0)]`
/// - Movk: `[Imm(imm16), Imm(hw_shift)]`
/// - Movn: `[Imm(imm16), Imm(0)]`
/// - OrrRI: `[Special(XZR/WZR), Imm(n), Imm(immr), Imm(imms)]`
pub fn materialize_constant(value: u64, width: u32) -> Vec<MachInst> {
    assert!(is_supported_width(width), "width must be 32 or 64");

    let mask = if width == 64 { u64::MAX } else { 0xFFFF_FFFF };
    let value = value & mask;

    // Strategy 1: Zero — single MOVZ with #0
    if value == 0 {
        return vec![movz_inst(0)];
    }

    // Strategy 2: Single 16-bit chunk — single MOVZ
    let chunks = (width / 16) as usize;
    let non_zero = non_zero_chunks(value, chunks);
    if non_zero.len() == 1 {
        let (imm16, hw) = non_zero[0];
        if hw == 0 {
            return vec![movz_inst(imm16 as i64)];
        }
        return vec![movz_inst(0), movk_inst(imm16 as i64, hw as i64 * 16)];
    }

    // Strategy 3: Logical immediate (bitmask pattern) — single ORR
    if let Some((n, immr, imms)) = encode_logical_immediate(value, width) {
        let zr = if width == 64 {
            MachOperand::Special(SpecialReg::XZR)
        } else {
            MachOperand::Special(SpecialReg::WZR)
        };
        return vec![MachInst::new(
            AArch64Opcode::OrrRI,
            vec![
                zr,
                MachOperand::Imm(n as i64),
                MachOperand::Imm(immr as i64),
                MachOperand::Imm(imms as i64),
            ],
        )];
    }

    // Strategy 4: MOVN for mostly-ones patterns
    // If the bitwise NOT has fewer non-zero chunks, MOVN is better.
    let inverted = !value & mask;
    let inv_non_zero = non_zero_chunks(inverted, chunks);
    if inv_non_zero.is_empty() {
        return vec![movn_inst(0)];
    }
    if inv_non_zero.len() == 1 {
        return movn_movk_sequence(value, chunks, &inv_non_zero);
    }
    if inv_non_zero.len() < non_zero.len() {
        return movn_movk_sequence(value, chunks, &inv_non_zero);
    }

    // Strategy 5: MOVZ + MOVK sequence — optimal for general values
    let seq = optimal_movz_movk_sequence(value);
    let mut insts = Vec::with_capacity(seq.len());
    for (i, &(imm16, hw)) in seq.iter().enumerate() {
        if i == 0 {
            debug_assert_eq!(hw, 0);
            insts.push(movz_inst(imm16 as i64));
        } else {
            insts.push(movk_inst(imm16 as i64, hw as i64 * 16));
        }
    }
    insts
}

/// Build a MOVN base plus MOVK repairs for a mostly-ones constant.
///
/// `inverted_non_zero` contains the halfwords where `value` is not `0xFFFF`.
/// MOVN is always seeded at hw0 with the inverse of the desired low halfword;
/// every non-ones high halfword is repaired with MOVK.
fn movn_movk_sequence(value: u64, chunks: usize, inverted_non_zero: &[(u16, u8)]) -> Vec<MachInst> {
    debug_assert!(!inverted_non_zero.is_empty());
    let low = value as u16;
    let movn_imm = !low;
    let mut insts = Vec::with_capacity(inverted_non_zero.len() + 1);
    insts.push(movn_inst(i64::from(movn_imm)));

    for hw in 1..chunks {
        let hw = hw as u8;
        let chunk = ((value >> (hw * 16)) & 0xFFFF) as u16;
        if chunk != 0xFFFF {
            insts.push(movk_inst(chunk as i64, hw as i64 * 16));
        }
    }

    insts
}

/// Detect whether a value is a valid ARM logical immediate for the given width.
///
/// ARM logical immediates encode repeating bitmask patterns. The value must
/// not be zero or all-ones for the given width. The pattern consists of a
/// repeating element of size 2, 4, 8, 16, 32, or 64 bits, where within
/// each element the set bits form a contiguous (possibly rotated) block.
pub fn is_logical_immediate(value: u64, width: u32) -> bool {
    encode_logical_immediate(value, width).is_some()
}

/// Encode a value as ARM logical immediate fields `(N, immr, imms)`.
///
/// Returns `None` if the value is not a valid logical immediate.
///
/// The encoding:
/// - `N`: 1 if element size is 64, else 0
/// - `immr`: rotation amount within the element (6 bits)
/// - `imms`: encodes element size and number of set bits (6 bits)
///
/// The `imms` field is: `(NOT(element_size - 1) & 0x3F) | (num_ones - 1)`
///
/// Reference: ARM ARM, "DecodeBitMasks" pseudocode.
pub fn encode_logical_immediate(value: u64, width: u32) -> Option<(u8, u8, u8)> {
    if !is_supported_width(width) {
        return None;
    }

    let mask = if width == 64 {
        u64::MAX
    } else {
        0xFFFF_FFFFu64
    };
    let v = value & mask;

    // All-zeros and all-ones are not encodable.
    if v == 0 || v == mask {
        return None;
    }

    // Try each element size from smallest to largest.
    let sizes: &[u32] = if width == 64 {
        &[2, 4, 8, 16, 32, 64]
    } else {
        &[2, 4, 8, 16, 32]
    };

    for &size in sizes {
        if !width.is_multiple_of(size) {
            continue;
        }

        let elem_mask = if size == 64 {
            u64::MAX
        } else {
            (1u64 << size) - 1
        };
        let elem = v & elem_mask;

        // Check that the value is a repetition of this element.
        if replicate_element(elem, size, width) != v {
            continue;
        }

        // Element must not be all-zeros or all-ones within its size.
        if elem == 0 || elem == elem_mask {
            continue;
        }

        // Try to find a rotation such that `rotate_right(ones_mask, rot) == elem`
        // where `ones_mask` has `num_ones` consecutive set bits starting from bit 0.
        for num_ones in 1..size {
            let base = if num_ones == 64 {
                u64::MAX
            } else {
                (1u64 << num_ones) - 1
            };
            for rot in 0..size {
                if rotate_right(base, rot, size) == elem {
                    let n: u8 = if size == 64 { 1 } else { 0 };
                    // imms: high bits encode element size (inverted), low bits encode (num_ones - 1)
                    let size_encoding = (!(size - 1)) as u8 & 0x3F;
                    let imms: u8 = size_encoding | ((num_ones - 1) as u8);
                    let immr: u8 = rot as u8;
                    return Some((n, immr, imms));
                }
            }
        }
    }

    None
}

/// Find the minimal MOVZ/MOVK sequence for a 64-bit value.
///
/// Returns `(imm16, hw_index)` pairs. The first entry is always hw0 and must be
/// emitted as MOVZ; later nonzero halfwords are MOVKs. A zero low halfword is
/// retained so callers never need a shifted MOVZ.
pub fn optimal_movz_movk_sequence(value: u64) -> Vec<(u16, u8)> {
    let mut chunks = vec![(value as u16, 0)];
    chunks.extend(
        (1..4)
            .map(|hw| {
                let chunk = ((value >> (hw * 16)) & 0xFFFF) as u16;
                (chunk, hw as u8)
            })
            .filter(|(chunk, _)| *chunk != 0),
    );

    chunks
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Create a shift-zero MOVZ instruction.
fn movz_inst(imm16: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::Imm(imm16), MachOperand::Imm(0)],
    )
}

/// Create a MOVK instruction with the given immediate and shift.
fn movk_inst(imm16: i64, hw_shift: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::Movk,
        vec![MachOperand::Imm(imm16), MachOperand::Imm(hw_shift)],
    )
}

/// Create a shift-zero MOVN instruction.
fn movn_inst(imm16: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::Movn,
        vec![MachOperand::Imm(imm16), MachOperand::Imm(0)],
    )
}

fn is_supported_width(width: u32) -> bool {
    matches!(width, 32 | 64)
}

/// Replicate an element of `size` bits across `width` bits.
fn replicate_element(elem: u64, size: u32, width: u32) -> u64 {
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let mut result = 0u64;
    let mut offset = 0;
    while offset < width {
        result |= elem << offset;
        offset += size;
    }
    result & mask
}

/// Rotate a value right within a given bit size.
fn rotate_right(value: u64, amount: u32, size: u32) -> u64 {
    if size == 0 || amount == 0 {
        return value;
    }
    let amount = amount % size;
    if amount == 0 {
        return value;
    }
    let mask = if size == 64 {
        u64::MAX
    } else {
        (1u64 << size) - 1
    };
    let v = value & mask;
    ((v >> amount) | (v << (size - amount))) & mask
}

/// Find all non-zero 16-bit chunks in a value, up to `max_chunks` halfwords.
fn non_zero_chunks(value: u64, max_chunks: usize) -> Vec<(u16, u8)> {
    (0..max_chunks)
        .map(|hw| {
            let chunk = ((value >> (hw * 16)) & 0xFFFF) as u16;
            (chunk, hw as u8)
        })
        .filter(|(chunk, _)| *chunk != 0)
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::inst::AArch64Opcode;
    use trust_cg_ir::operand::MachOperand;

    // ---- Helper functions ----

    fn assert_single_movz(insts: &[MachInst], expected_imm: i64, expected_shift: i64) {
        assert_eq!(
            insts.len(),
            1,
            "expected single instruction, got {}",
            insts.len()
        );
        assert_eq!(insts[0].opcode, AArch64Opcode::Movz);
        assert_eq!(insts[0].operands[0].as_imm(), Some(expected_imm));
        assert_eq!(insts[0].operands[1].as_imm(), Some(expected_shift));
    }

    fn assert_movz_movk(insts: &[MachInst], expected_imm: i64, expected_shift: i64) {
        assert_eq!(insts.len(), 2);
        assert_eq!(insts[0].opcode, AArch64Opcode::Movz);
        assert_eq!(insts[0].operands[0].as_imm(), Some(0));
        assert_eq!(insts[0].operands[1].as_imm(), Some(0));
        assert_eq!(insts[1].opcode, AArch64Opcode::Movk);
        assert_eq!(insts[1].operands[0].as_imm(), Some(expected_imm));
        assert_eq!(insts[1].operands[1].as_imm(), Some(expected_shift));
    }

    fn assert_single_movn(insts: &[MachInst], expected_imm: i64, expected_shift: i64) {
        assert_eq!(
            insts.len(),
            1,
            "expected single instruction, got {}",
            insts.len()
        );
        assert_eq!(insts[0].opcode, AArch64Opcode::Movn);
        assert_eq!(insts[0].operands[0].as_imm(), Some(expected_imm));
        assert_eq!(insts[0].operands[1].as_imm(), Some(expected_shift));
    }

    fn count_opcodes(insts: &[MachInst], opcode: AArch64Opcode) -> usize {
        insts.iter().filter(|i| i.opcode == opcode).count()
    }

    // ---- Zero ----

    #[test]
    fn zero_32bit() {
        let insts = materialize_constant(0, 32);
        assert_single_movz(&insts, 0, 0);
    }

    #[test]
    fn zero_64bit() {
        let insts = materialize_constant(0, 64);
        assert_single_movz(&insts, 0, 0);
    }

    #[test]
    #[should_panic(expected = "width must be 32 or 64")]
    fn materialize_rejects_invalid_width() {
        let _ = materialize_constant(0x1234, 16);
    }

    // ---- Small positives (fits in 16 bits) ----

    #[test]
    fn small_positive_1() {
        let insts = materialize_constant(1, 64);
        assert_single_movz(&insts, 1, 0);
    }

    #[test]
    fn small_positive_42() {
        let insts = materialize_constant(42, 32);
        assert_single_movz(&insts, 42, 0);
    }

    #[test]
    fn small_positive_0xff() {
        let insts = materialize_constant(0xFF, 64);
        assert_single_movz(&insts, 0xFF, 0);
    }

    #[test]
    fn small_positive_max_u16() {
        let insts = materialize_constant(0xFFFF, 32);
        assert_single_movz(&insts, 0xFFFF, 0);
    }

    // ---- Values whose only nonzero halfword is above hw0 ----

    #[test]
    fn shifted_16bit_hw1() {
        // 0x10000 = 1 << 16
        let insts = materialize_constant(0x10000, 32);
        assert_movz_movk(&insts, 1, 16);
    }

    #[test]
    fn shifted_16bit_hw1_full() {
        // 0xFFFF_0000
        let insts = materialize_constant(0xFFFF_0000, 32);
        assert_movz_movk(&insts, 0xFFFF, 16);
    }

    #[test]
    fn shifted_16bit_hw2_64bit() {
        // 0x1_0000_0000
        let insts = materialize_constant(0x1_0000_0000, 64);
        assert_movz_movk(&insts, 1, 32);
    }

    #[test]
    fn shifted_16bit_hw3_64bit() {
        // 0xFFFF_0000_0000_0000
        let insts = materialize_constant(0xFFFF_0000_0000_0000, 64);
        assert_movz_movk(&insts, 0xFFFF, 48);
    }

    // ---- Logical immediate (bitmask patterns) ----

    #[test]
    fn logical_imm_0xff_64bit() {
        assert!(is_logical_immediate(0xFF, 64));
        let enc = encode_logical_immediate(0xFF, 64);
        assert!(enc.is_some());
        let (n, immr, imms) = enc.unwrap();
        assert_eq!(n, 1); // element size 64
        assert_eq!(immr, 0);
        assert_eq!(imms, 7); // 8 ones - 1
    }

    #[test]
    fn logical_imm_0xffff_64bit() {
        assert!(is_logical_immediate(0xFFFF, 64));
        let enc = encode_logical_immediate(0xFFFF, 64);
        assert!(enc.is_some());
        let (n, immr, imms) = enc.unwrap();
        assert_eq!(n, 1);
        assert_eq!(immr, 0);
        assert_eq!(imms, 15); // 16 ones - 1
    }

    #[test]
    fn logical_imm_alternating_bits_32bit() {
        // 0x55555555 = 0101...0101 — element size 2, 1 set bit
        assert!(is_logical_immediate(0x55555555, 32));
        let (n, immr, imms) = encode_logical_immediate(0x55555555, 32).unwrap();
        assert_eq!(n, 0);
        assert_eq!(immr, 0);
        assert_eq!(imms, 0x3E); // ~(2-1) & 0x3F | (1-1) = 0x3E | 0 = 0x3E
    }

    #[test]
    fn logical_imm_alternating_bits_inverted_32bit() {
        // 0xAAAAAAAA = 1010...1010 — element size 2, 1 set bit, rotated
        assert!(is_logical_immediate(0xAAAAAAAA, 32));
        let (n, immr, imms) = encode_logical_immediate(0xAAAAAAAA, 32).unwrap();
        assert_eq!(n, 0);
        assert_eq!(immr, 1);
        assert_eq!(imms, 0x3E);
    }

    #[test]
    fn logical_imm_byte_repeat_32bit() {
        // 0x01010101 — element size 8, 1 set bit
        assert!(is_logical_immediate(0x01010101, 32));
        let (n, immr, imms) = encode_logical_immediate(0x01010101, 32).unwrap();
        assert_eq!(n, 0);
        assert_eq!(immr, 0);
        assert_eq!(imms, 0x38); // ~(8-1) & 0x3F | (1-1) = 0x38
    }

    #[test]
    fn logical_imm_halfword_repeat_32bit() {
        // 0x00FF00FF — element size 16, 8 set bits
        assert!(is_logical_immediate(0x00FF00FF, 32));
        let (n, immr, imms) = encode_logical_immediate(0x00FF00FF, 32).unwrap();
        assert_eq!(n, 0);
        assert_eq!(immr, 0);
        assert_eq!(imms, 0x37); // ~(16-1) & 0x3F | (8-1) = 0x30 | 7 = 0x37
    }

    #[test]
    fn logical_imm_materialize_uses_orr() {
        // 0x00FF00FF should use a single ORR instruction
        let insts = materialize_constant(0x00FF00FF, 32);
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0].opcode, AArch64Opcode::OrrRI);
    }

    #[test]
    fn logical_imm_edge_case_all_zeros() {
        assert!(!is_logical_immediate(0, 32));
        assert!(!is_logical_immediate(0, 64));
    }

    #[test]
    fn logical_imm_edge_case_all_ones_32bit() {
        assert!(!is_logical_immediate(0xFFFFFFFF, 32));
    }

    #[test]
    fn logical_imm_edge_case_all_ones_64bit() {
        assert!(!is_logical_immediate(u64::MAX, 64));
    }

    #[test]
    fn logical_imm_invalid_width_fails_closed() {
        assert_eq!(encode_logical_immediate(0xFF, 16), None);
        assert!(!is_logical_immediate(0xFF, 16));
    }

    #[test]
    fn logical_imm_0x7f_64bit() {
        // 0x7F = 7 consecutive bits, element size 64
        assert!(is_logical_immediate(0x7F, 64));
        let (n, immr, imms) = encode_logical_immediate(0x7F, 64).unwrap();
        assert_eq!(n, 1);
        assert_eq!(immr, 0);
        assert_eq!(imms, 6); // 7 ones - 1
    }

    #[test]
    fn logical_imm_rotated_32bit() {
        // 0xC0000003 = 4 consecutive bits rotated in 32-bit element
        assert!(is_logical_immediate(0xC0000003, 32));
        let (n, immr, imms) = encode_logical_immediate(0xC0000003, 32).unwrap();
        assert_eq!(n, 0);
        assert_eq!(immr, 2);
        // imms = ~(32-1) & 0x3F | (4-1) = 0x20 | 3 = 0x23
        assert_eq!(imms, 0x23);
    }

    // ---- MOVN (mostly-ones patterns) ----

    #[test]
    fn movn_all_ones_except_low16_32bit() {
        // Only the high halfword is nonzero. Shifted MOVZ is outside the
        // emittable subset, so seed zero and repair hw1 with MOVK.
        let insts = materialize_constant(0xFFFF_0000, 32);
        assert_movz_movk(&insts, 0xFFFF, 16);
    }

    #[test]
    fn movn_minus_one_32bit() {
        let insts = materialize_constant(0xFFFF_FFFF, 32);
        assert_single_movn(&insts, 0, 0);
    }

    #[test]
    fn movn_minus_one_64bit() {
        let insts = materialize_constant(u64::MAX, 64);
        assert_single_movn(&insts, 0, 0);
    }

    #[test]
    fn movn_single_hole_64bit() {
        // 0xFFFF_FFFF_FFFF_0000 is a valid logical immediate (contiguous ones),
        // so ORR is preferred over MOVN. Still a single instruction.
        let insts = materialize_constant(0xFFFF_FFFF_FFFF_0000, 64);
        assert_eq!(insts.len(), 1);
        // It's a logical imm, so ORR is used.
        assert_eq!(insts[0].opcode, AArch64Opcode::OrrRI);
    }

    #[test]
    fn movn_non_logical_imm_mostly_ones() {
        // To test MOVN, we need a value that is NOT a logical immediate
        // but has only 1 non-zero chunk when inverted.
        // 0xFFFF_FFFF_FFFF_1234: NOT = 0x0000_0000_0000_EDCB
        // Check: 0xFFFF_FFFF_FFFF_1234 is NOT a repeating bitmask pattern.
        // The low 16 bits are 0x1234, not 0xFFFF, so not all-ones in the low chunk.
        // It has 3 chunks of 0xFFFF and one chunk of 0x1234, so 4 non-zero chunks.
        // Inverted: 0x0000_0000_0000_EDCB -> 1 non-zero chunk.
        // But first let's verify it's not a logical immediate.
        assert!(!is_logical_immediate(0xFFFF_FFFF_FFFF_1234, 64));
        let insts = materialize_constant(0xFFFF_FFFF_FFFF_1234, 64);
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0].opcode, AArch64Opcode::Movn);
        assert_eq!(insts[0].operands[0].as_imm(), Some(0xEDCB_i64));
        assert_eq!(insts[0].operands[1].as_imm(), Some(0)); // hw=0
    }

    #[test]
    fn movn_high_hole_uses_hw0_seed_and_movk_repair() {
        let value = 0xFFFF_1234_FFFF_FFFF;
        assert!(!is_logical_immediate(value, 64));
        let insts = materialize_constant(value, 64);
        assert_eq!(insts.len(), 2);
        assert_eq!(insts[0].opcode, AArch64Opcode::Movn);
        assert_eq!(insts[0].operands[0].as_imm(), Some(0));
        assert_eq!(insts[0].operands[1].as_imm(), Some(0));
        assert_eq!(insts[1].opcode, AArch64Opcode::Movk);
        assert_eq!(insts[1].operands[0].as_imm(), Some(0x1234));
        assert_eq!(insts[1].operands[1].as_imm(), Some(32));
    }

    #[test]
    fn movn_movk_two_hole_mostly_ones_64bit() {
        // NOT = 0x0000_0000_EDCB_A987, so MOVN can seed one hole and
        // MOVK repairs the other in 2 instructions instead of MOVZ+3 MOVK.
        let value = 0xFFFF_FFFF_1234_5678;
        assert!(!is_logical_immediate(value, 64));

        let insts = materialize_constant(value, 64);

        assert_eq!(insts.len(), 2);
        assert_eq!(insts[0].opcode, AArch64Opcode::Movn);
        assert_eq!(insts[0].operands[0].as_imm(), Some(0xA987_i64));
        assert_eq!(insts[0].operands[1].as_imm(), Some(0));
        assert_eq!(insts[1].opcode, AArch64Opcode::Movk);
        assert_eq!(insts[1].operands[0].as_imm(), Some(0x1234));
        assert_eq!(insts[1].operands[1].as_imm(), Some(16));
    }

    #[test]
    fn movn_movk_not_used_for_equal_cost_32bit_constant() {
        let insts = materialize_constant(0x1234_5678, 32);

        assert_eq!(insts.len(), 2);
        assert_eq!(insts[0].opcode, AArch64Opcode::Movz);
        assert_eq!(insts[0].operands[0].as_imm(), Some(0x5678));
        assert_eq!(insts[0].operands[1].as_imm(), Some(0));
        assert_eq!(insts[1].opcode, AArch64Opcode::Movk);
        assert_eq!(insts[1].operands[0].as_imm(), Some(0x1234));
        assert_eq!(insts[1].operands[1].as_imm(), Some(16));
    }

    // ---- 32-bit large values ----

    #[test]
    fn large_32bit_deadbeef() {
        // 0xDEADBEEF: low16 = 0xBEEF, high16 = 0xDEAD
        let insts = materialize_constant(0xDEADBEEF, 32);
        assert_eq!(insts.len(), 2);
        assert_eq!(insts[0].opcode, AArch64Opcode::Movz);
        assert_eq!(insts[1].opcode, AArch64Opcode::Movk);
    }

    #[test]
    fn large_32bit_with_zero_low() {
        // 0xABCD0000: low16=0, high16=0xABCD -> MOVZ#0 + MOVK hw1.
        let insts = materialize_constant(0xABCD0000, 32);
        assert_movz_movk(&insts, 0xABCD, 16);
    }

    // ---- 64-bit values ----

    #[test]
    fn full_64bit_value() {
        // 0xDEAD_BEEF_CAFE_BABE — all four chunks non-zero
        let insts = materialize_constant(0xDEAD_BEEF_CAFE_BABE, 64);
        assert_eq!(insts.len(), 4);
        assert_eq!(insts[0].opcode, AArch64Opcode::Movz);
        assert_eq!(count_opcodes(&insts, AArch64Opcode::Movk), 3);
    }

    #[test]
    fn sparse_64bit_value() {
        // 0x0001_0000_0001_0000 is a repeating 32-bit pattern (0x00010000 repeated),
        // which is a valid logical immediate. So ORR is used (1 instruction).
        let insts = materialize_constant(0x0001_0000_0001_0000, 64);
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0].opcode, AArch64Opcode::OrrRI);
    }

    #[test]
    fn sparse_64bit_movz_movk() {
        // Use a value with 2 non-zero chunks that is NOT a logical immediate.
        // 0x0001_0000_0002_0000: chunks at hw=1 (0x0002) and hw=3 (0x0001)
        // This is not a repeating pattern since the two 32-bit halves differ.
        assert!(!is_logical_immediate(0x0001_0000_0002_0000, 64));
        let insts = materialize_constant(0x0001_0000_0002_0000, 64);
        assert_eq!(insts.len(), 3);
        assert_eq!(insts[0].opcode, AArch64Opcode::Movz);
        assert_eq!(insts[1].opcode, AArch64Opcode::Movk);
        assert_eq!(insts[2].opcode, AArch64Opcode::Movk);
    }

    #[test]
    fn single_chunk_hw2_64bit() {
        // 0x0000_ABCD_0000_0000 — zero seed plus one hw2 repair.
        let insts = materialize_constant(0x0000_ABCD_0000_0000, 64);
        assert_movz_movk(&insts, 0xABCD, 32);
    }

    // ---- optimal_movz_movk_sequence tests ----

    #[test]
    fn optimal_sequence_zero() {
        let seq = optimal_movz_movk_sequence(0);
        assert_eq!(seq, vec![(0, 0)]);
    }

    #[test]
    fn optimal_sequence_small() {
        let seq = optimal_movz_movk_sequence(42);
        assert_eq!(seq, vec![(42, 0)]);
    }

    #[test]
    fn optimal_sequence_retains_zero_hw0_seed() {
        // 0x0001_0000_0001_0000 — chunks at hw=1 and hw=3 are non-zero
        let seq = optimal_movz_movk_sequence(0x0001_0000_0001_0000);
        assert_eq!(seq.len(), 3);
        assert_eq!(seq[0], (0, 0)); // hw0 MOVZ seed
        assert_eq!(seq[1], (1, 1));
        assert_eq!(seq[2], (1, 3));
    }

    #[test]
    fn optimal_sequence_all_chunks() {
        let seq = optimal_movz_movk_sequence(0xDEAD_BEEF_CAFE_BABE);
        assert_eq!(seq.len(), 4);
        assert_eq!(seq[0].0, 0xBABE); // hw=0
        assert_eq!(seq[1].0, 0xCAFE); // hw=1
        assert_eq!(seq[2].0, 0xBEEF); // hw=2
        assert_eq!(seq[3].0, 0xDEAD); // hw=3
    }

    #[test]
    fn optimal_sequence_shift_values() {
        let seq = optimal_movz_movk_sequence(0xFFFF_0000_0000);
        assert_eq!(seq, vec![(0, 0), (0xFFFF, 2)]);
    }

    // ---- Instruction count optimality ----

    #[test]
    fn instruction_count_in_proof_covered_subset() {
        // 0 -> 1
        assert_eq!(materialize_constant(0, 64).len(), 1);
        // Small -> 1
        assert_eq!(materialize_constant(100, 64).len(), 1);
        // 0xFFFF -> 1
        assert_eq!(materialize_constant(0xFFFF, 64).len(), 1);
        // 0x10000 -> MOVZ#0 + MOVK#1,LSL#16.
        assert_eq!(materialize_constant(0x10000, 64).len(), 2);
        // 0xFF (logical imm) -> 1
        assert_eq!(materialize_constant(0xFF, 64).len(), 1);
        // 0x00FF00FF (logical imm) -> 1
        assert_eq!(materialize_constant(0x00FF00FF, 32).len(), 1);
        // 0xDEADBEEF (32-bit, 2 chunks) -> 2
        assert_eq!(materialize_constant(0xDEADBEEF, 32).len(), 2);
        // mostly-ones with two repaired halfwords -> 2
        assert_eq!(materialize_constant(0xFFFF_FFFF_1234_5678, 64).len(), 2);
    }

    // ---- Correctness: hw0 MOVZ seeds plus shifted MOVK repairs ----

    #[test]
    fn move_wide_shift_values_correct() {
        let insts = materialize_constant(0x1234, 64);
        assert_eq!(insts[0].operands[1].as_imm(), Some(0));

        for (value, shift) in [
            (0x1234_0000, 16),
            (0x1234_0000_0000, 32),
            (0x1234_0000_0000_0000, 48),
        ] {
            let insts = materialize_constant(value, 64);
            assert_movz_movk(&insts, 0x1234, shift);
        }
    }

    // ---- Encode logical immediate: specific known encodings ----

    #[test]
    fn encode_logical_imm_0xff00ff_32bit() {
        // 0x00FF00FF at 32-bit: element 16, 8 ones, rot 0
        let enc = encode_logical_immediate(0x00FF00FF, 32);
        assert!(enc.is_some());
    }

    #[test]
    fn encode_logical_imm_repeating_64bit() {
        // 0x00FF00FF00FF00FF at 64-bit: element 16, 8 ones
        let enc = encode_logical_immediate(0x00FF00FF00FF00FF, 64);
        assert!(enc.is_some());
        let (n, immr, imms) = enc.unwrap();
        assert_eq!(n, 0); // element size 16, not 64
        assert_eq!(immr, 0);
        // imms = ~(16-1) & 0x3F | (8-1) = 0x30 | 7 = 0x37
        assert_eq!(imms, 0x37);
    }

    #[test]
    fn encode_logical_imm_not_encodable() {
        // 0xDEADBEEF at 32-bit is NOT a logical immediate
        assert!(encode_logical_immediate(0xDEADBEEF, 32).is_none());
    }

    // ---- Width masking ----

    #[test]
    fn width_32_masks_upper_bits() {
        // If caller passes a 64-bit value but width=32, upper bits are ignored
        let insts = materialize_constant(0xFFFF_FFFF_0000_0042, 32);
        // Only low 32 bits = 0x0000_0042 = 66
        assert_single_movz(&insts, 0x42, 0);
    }

    // ---- replicate_element helper ----

    #[test]
    fn replicate_element_works() {
        assert_eq!(replicate_element(0x55, 8, 32), 0x55555555);
        assert_eq!(replicate_element(0x01, 2, 8), 0x55);
        assert_eq!(replicate_element(0xFF, 8, 32), 0xFFFFFFFF);
        assert_eq!(replicate_element(0xABCD, 16, 64), 0xABCDABCDABCDABCD);
    }

    // ---- rotate_right helper ----

    #[test]
    fn rotate_right_works() {
        assert_eq!(rotate_right(0b11, 1, 4), 0b1001);
        assert_eq!(rotate_right(0b1, 0, 8), 0b1);
        assert_eq!(rotate_right(0b1, 1, 8), 0b10000000);
        assert_eq!(rotate_right(0b11, 2, 8), 0b11000000);
    }

    // ---- Materialize constant for logical imm values uses OrrRI ----

    #[test]
    fn materialize_logical_imm_orr_operands() {
        let insts = materialize_constant(0x55555555, 32);
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0].opcode, AArch64Opcode::OrrRI);
        // First operand should be WZR for 32-bit
        assert_eq!(insts[0].operands[0], MachOperand::Special(SpecialReg::WZR));
        // Then N, immr, imms as Imm operands
        assert_eq!(insts[0].operands[1].as_imm(), Some(0)); // N=0
        assert_eq!(insts[0].operands[2].as_imm(), Some(0)); // immr=0
        assert_eq!(insts[0].operands[3].as_imm(), Some(0x3E)); // imms
    }

    #[test]
    fn materialize_logical_imm_64bit_uses_xzr() {
        // 0xFF fits in 16 bits, so single MOVZ is preferred.
        // Use a value that is ONLY encodable as logical imm, not as single chunk.
        // 0x00FF00FF00FF00FF is a repeating bitmask that needs >1 MOVZ but can use ORR.
        let insts = materialize_constant(0x00FF00FF00FF00FF, 64);
        assert_eq!(insts.len(), 1);
        assert_eq!(insts[0].opcode, AArch64Opcode::OrrRI);
        assert_eq!(insts[0].operands[0], MachOperand::Special(SpecialReg::XZR));
    }
}
