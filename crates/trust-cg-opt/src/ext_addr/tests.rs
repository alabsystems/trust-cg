// trust-cg-opt - Extended-register addressing fold tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::pass_manager::MachinePass;
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, RegClass, Signature};

fn g64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn g32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn f32r(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr32))
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}

fn make_func(insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new("test_ext_addr".to_string(), Signature::new(vec![], vec![]));
    let block = func.entry;
    for inst in insts {
        let id = func.push_inst(inst);
        func.append_inst(block, id);
    }
    func
}

fn block_opcodes(func: &MachFunction) -> Vec<AArch64Opcode> {
    func.block(func.entry)
        .insts
        .iter()
        .map(|&id| func.inst(id).opcode)
        .collect()
}

/// The canonical isel chain: MOVZ #4 scale (hoisted), SXTW of the i32
/// index, MADD address, 32-bit load at offset 0. The consumer AddRR keeps
/// the loaded value and the index alive.
fn sxtw_madd_load_chain() -> Vec<MachInst> {
    vec![
        // v0 = base pointer def (via AddRI so it has a def)
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        // v1 = i32 index def
        MachInst::new(AArch64Opcode::AddRI, vec![g32(1), g32(91), imm(0)]),
        // v2 = MOVZ #4 (scale)
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(4)]),
        // v3 = SXTW v1
        MachInst::new(AArch64Opcode::Sxtw, vec![g64(3), g32(1)]),
        // v4 = MADD v3, v2, v0
        MachInst::new(AArch64Opcode::Madd, vec![g64(4), g64(3), g64(2), g64(0)]),
        // v5 = LDR [v4, #0]
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(4), imm(0)]),
        // consumer
        MachInst::new(AArch64Opcode::AddRR, vec![g32(6), g32(5), g32(1)]),
    ]
}

#[test]
fn folds_sxtw_madd_ldr_to_ldr_ro_sxtw_shifted() {
    let mut func = make_func(sxtw_madd_load_chain());
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));

    let ops = block_opcodes(&func);
    assert!(!ops.contains(&AArch64Opcode::Sxtw), "SXTW must be folded");
    assert!(!ops.contains(&AArch64Opcode::Madd), "MADD must be folded");
    assert!(ops.contains(&AArch64Opcode::LdrRO));

    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrRO)
        .unwrap();
    let ldr = func.inst(ldr_id);
    assert_eq!(ldr.operands.len(), 4);
    assert_eq!(ldr.operands[0], g32(5), "transfer register preserved");
    assert_eq!(ldr.operands[1], g64(0), "base register");
    assert_eq!(ldr.operands[2], g32(1), "32-bit index register");
    // SXTW (option 0b110), shifted (S=1): packed = (0b110 << 1) | 1 = 13.
    assert_eq!(ldr.operands[3], imm(13));
}

#[test]
fn folds_store_to_str_ro() {
    let mut insts = sxtw_madd_load_chain();
    // Replace the load with a store of an unrelated value.
    insts[5] = MachInst::new(AArch64Opcode::StrRI, vec![g32(91), g64(4), imm(0)]);
    // Replace the consumer (no loaded value anymore).
    insts[6] = MachInst::new(AArch64Opcode::AddRR, vec![g32(6), g32(1), g32(1)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));

    let ops = block_opcodes(&func);
    assert!(ops.contains(&AArch64Opcode::StrRO));
    assert!(!ops.contains(&AArch64Opcode::Madd));
}

#[test]
fn folds_fpr32_load() {
    let mut insts = sxtw_madd_load_chain();
    insts[5] = MachInst::new(AArch64Opcode::LdrRI, vec![f32r(5), g64(4), imm(0)]);
    insts[6] = MachInst::new(AArch64Opcode::AddRR, vec![g32(6), g32(1), g32(1)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));

    let ops = block_opcodes(&func);
    assert!(ops.contains(&AArch64Opcode::LdrRO));
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrRO)
        .unwrap();
    assert_eq!(func.inst(ldr_id).operands[0], f32r(5));
    assert_eq!(func.inst(ldr_id).operands[3], imm(13));
}

#[test]
fn folds_64bit_index_to_lsl_form() {
    // MADD with a plain 64-bit index (no SXTW link) and a 64-bit load:
    // scale 8 → LSL #3 (packed = (0b011 << 1) | 1 = 7).
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::AddRI, vec![g64(1), g64(91), imm(0)]),
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(8)]),
        MachInst::new(AArch64Opcode::Madd, vec![g64(4), g64(1), g64(2), g64(0)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g64(5), g64(4), imm(0)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g64(6), g64(5), g64(1)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));

    let ops = block_opcodes(&func);
    assert!(!ops.contains(&AArch64Opcode::Madd));
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrRO)
        .unwrap();
    let ldr = func.inst(ldr_id);
    assert_eq!(ldr.operands[1], g64(0));
    assert_eq!(ldr.operands[2], g64(1));
    assert_eq!(ldr.operands[3], imm(7));
}

#[test]
fn byte_scale_folds_unshifted() {
    // MOVZ #1 scale with a 32-bit load → SXTW, S=0 (packed = 0b110<<1 = 12).
    let mut insts = sxtw_madd_load_chain();
    insts[2] = MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(1)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrRO)
        .unwrap();
    assert_eq!(func.inst(ldr_id).operands[3], imm(12));
}

#[test]
fn no_fold_when_scale_mismatches_access_size() {
    // MOVZ #2 with a 32-bit load: 2 != 4 and 2 != 1 → keep the chain.
    let mut insts = sxtw_madd_load_chain();
    insts[2] = MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(2)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(!pass.run(&mut func));
    assert!(block_opcodes(&func).contains(&AArch64Opcode::Madd));
}

#[test]
fn no_fold_when_offset_nonzero() {
    let mut insts = sxtw_madd_load_chain();
    insts[5] = MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(4), imm(8)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(!pass.run(&mut func));
}

#[test]
fn no_fold_when_address_multi_use() {
    let mut insts = sxtw_madd_load_chain();
    // Second use of the MADD address.
    insts.push(MachInst::new(
        AArch64Opcode::AddRR,
        vec![g64(7), g64(4), g64(0)],
    ));
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(!pass.run(&mut func));
    assert!(block_opcodes(&func).contains(&AArch64Opcode::Madd));
}

#[test]
fn multi_use_sxtw_falls_back_to_lsl_on_extended_index() {
    // The SXTW result has a second use → the SXTW must stay, but the MADD
    // can still fold to the LSL form over the 64-bit extended index.
    let mut insts = sxtw_madd_load_chain();
    insts.push(MachInst::new(
        AArch64Opcode::AddRR,
        vec![g64(7), g64(3), g64(0)],
    ));
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(ops.contains(&AArch64Opcode::Sxtw), "multi-use SXTW stays");
    assert!(!ops.contains(&AArch64Opcode::Madd));
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrRO)
        .unwrap();
    let ldr = func.inst(ldr_id);
    assert_eq!(ldr.operands[2], g64(3), "64-bit index register");
    assert_eq!(ldr.operands[3], imm(7), "LSL shifted");
}

#[test]
fn folds_swap_address_shared_by_load_and_store() {
    // A read-modify-write / swap: ONE Madd address (i64 index, scale 4) feeds
    // BOTH a load and a store of the SAME element (`perm[i]` read then written
    // — the fannkuch flip). Both uses are offset-0 memory ops, so BOTH fold to
    // the RO form and the shared Madd is deleted (freeing the scale register).
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]), // base
        MachInst::new(AArch64Opcode::AddRI, vec![g64(1), g64(91), imm(0)]), // index (i64)
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(4)]),           // scale #4
        MachInst::new(AArch64Opcode::Madd, vec![g64(4), g64(1), g64(2), g64(0)]), // i*4+base
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(4), imm(0)]),  // load  [addr]
        MachInst::new(AArch64Opcode::StrRI, vec![g32(5), g64(4), imm(0)]),  // store [addr]
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(!ops.contains(&AArch64Opcode::Madd), "shared Madd deleted");
    assert!(ops.contains(&AArch64Opcode::LdrRO), "load folded to LdrRO");
    assert!(ops.contains(&AArch64Opcode::StrRO), "store folded to StrRO");
    for id in func.block(func.entry).insts.clone() {
        let inst = func.inst(id);
        if matches!(inst.opcode, AArch64Opcode::LdrRO | AArch64Opcode::StrRO) {
            assert_eq!(inst.operands[1], g64(0), "base survives");
            assert_eq!(inst.operands[2], g64(1), "64-bit index");
            assert_eq!(inst.operands[3], imm(7), "LSL #2 (es=4: (011<<1)|1)");
        }
    }
}

#[test]
fn no_fold_when_one_shared_use_is_not_foldable() {
    // The Madd address feeds a foldable offset-0 load AND an offset-BEARING
    // store (register-offset mode has no extra immediate, so the store cannot
    // fold). Because the Madd cannot be deleted, folding ONLY the load would
    // leave the Madd live — a pure pessimization — so NEITHER use is rewritten
    // and the whole chain is preserved (all-or-nothing per address).
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::AddRI, vec![g64(1), g64(91), imm(0)]),
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(4)]),
        MachInst::new(AArch64Opcode::Madd, vec![g64(4), g64(1), g64(2), g64(0)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(4), imm(0)]), // foldable
        MachInst::new(AArch64Opcode::StrRI, vec![g32(5), g64(4), imm(8)]), // offset 8 — NOT foldable
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(!pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(ops.contains(&AArch64Opcode::Madd), "Madd preserved");
    assert!(
        !ops.contains(&AArch64Opcode::LdrRO),
        "load NOT folded (all-or-nothing)"
    );
}

/// The scale-1 byte gather the isel emits for `gep i8, ptr, idx`: a plain
/// `SXTW + ADD` address (no Movz-scaled MADD) feeding an `LDRB`, with a
/// redundant `UXTB` of the loaded byte. The measured crc/histogram shape.
fn sxtw_add_ldrb_uxtb_chain() -> Vec<MachInst> {
    vec![
        // v0 = base pointer
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        // v1 = i32 index
        MachInst::new(AArch64Opcode::AddRI, vec![g32(1), g32(91), imm(0)]),
        // v3 = SXTW v1
        MachInst::new(AArch64Opcode::Sxtw, vec![g64(3), g32(1)]),
        // v4 = ADD v0, v3  (base + sxtw(index), scale 1)
        MachInst::new(AArch64Opcode::AddRR, vec![g64(4), g64(0), g64(3)]),
        // v5 = LDRB [v4, #0]
        MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(4), imm(0)]),
        // v6 = UXTB v5  (redundant — LDRB already zero-extended)
        MachInst::new(AArch64Opcode::Uxtb, vec![g32(6), g32(5)]),
        // consumer of the zero-extended byte
        MachInst::new(AArch64Opcode::AddRR, vec![g32(7), g32(6), g32(1)]),
    ]
}

#[test]
fn folds_narrow_byte_madd_to_ldrb_ro_sxtw_unshifted() {
    // MOVZ #1 scale + MADD + LDRB → LDRB RO, SXTW, S=0 (packed = 0b110<<1 = 12).
    let mut insts = sxtw_madd_load_chain();
    insts[2] = MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(1)]);
    insts[5] = MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(4), imm(0)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));

    let ops = block_opcodes(&func);
    assert!(!ops.contains(&AArch64Opcode::Sxtw), "SXTW folded");
    assert!(!ops.contains(&AArch64Opcode::Madd), "MADD folded");
    assert!(ops.contains(&AArch64Opcode::LdrbRO));
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrbRO)
        .unwrap();
    let ldr = func.inst(ldr_id);
    assert_eq!(ldr.operands[0], g32(5), "transfer register preserved");
    assert_eq!(ldr.operands[1], g64(0), "base register");
    assert_eq!(ldr.operands[2], g32(1), "32-bit index register");
    assert_eq!(ldr.operands[3], imm(12), "SXTW, S=0 (byte)");
}

#[test]
fn folds_byte_gather_add_chain_and_strips_uxtb() {
    // The full crc/histogram shape: SXTW + ADD + LDRB + UXTB → one LDRB RO
    // (SXTW, S=0) writing the UXTB's destination directly.
    let mut func = make_func(sxtw_add_ldrb_uxtb_chain());
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));

    let ops = block_opcodes(&func);
    assert!(
        !ops.contains(&AArch64Opcode::Sxtw),
        "SXTW folded into the RO extend"
    );
    assert!(
        !ops.contains(&AArch64Opcode::Uxtb),
        "redundant UXTB folded away"
    );
    assert!(ops.contains(&AArch64Opcode::LdrbRO));
    // The ADD that derived the address is gone (only the two setup AddRIs and
    // the consumer AddRR remain).
    let addrr_count = ops.iter().filter(|&&o| o == AArch64Opcode::AddRR).count();
    assert_eq!(addrr_count, 1, "only the consumer AddRR remains");

    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrbRO)
        .unwrap();
    let ldr = func.inst(ldr_id);
    assert_eq!(
        ldr.operands[0],
        g32(6),
        "load writes the UXTB's dst directly"
    );
    assert_eq!(ldr.operands[1], g64(0), "base register");
    assert_eq!(ldr.operands[2], g32(1), "32-bit index register");
    assert_eq!(ldr.operands[3], imm(12), "SXTW, S=0 (byte)");
}

#[test]
fn byte_gather_add_lsl_form() {
    // A 64-bit index with no SXTW link: ADD of two X registers → LDRB RO, LSL,
    // S=0 (packed = 0b011<<1 = 6). The loaded byte is consumed directly (no
    // UXTB), so nothing is stripped.
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::AddRI, vec![g64(1), g64(91), imm(0)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g64(4), g64(0), g64(1)]),
        MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(4), imm(0)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(6), g32(5), g32(5)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrbRO)
        .unwrap();
    let ldr = func.inst(ldr_id);
    assert_eq!(ldr.operands[1], g64(0), "base");
    assert_eq!(ldr.operands[2], g64(1), "64-bit index");
    assert_eq!(ldr.operands[3], imm(6), "LSL, S=0");
}

#[test]
fn folds_halfword_madd_to_ldrh_ro_sxtw_shifted() {
    // MOVZ #2 scale + MADD + LDRH → LDRH RO, SXTW, S=1 (shift by 1); packed =
    // (0b110<<1)|1 = 13.
    let mut insts = sxtw_madd_load_chain();
    insts[2] = MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(2)]);
    insts[5] = MachInst::new(AArch64Opcode::LdrhRI, vec![g32(5), g64(4), imm(0)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrhRO)
        .unwrap();
    let ldr = func.inst(ldr_id);
    assert_eq!(ldr.operands[2], g32(1), "32-bit index");
    assert_eq!(ldr.operands[3], imm(13), "SXTW, S=1 (halfword)");
}

#[test]
fn keeps_sxtb_after_byte_load() {
    // A SIGN-extend of a byte-load result is NOT redundant (LDRB zero-extends;
    // SXTB sign-extends) — it must be kept.
    let mut insts = sxtw_add_ldrb_uxtb_chain();
    insts[5] = MachInst::new(AArch64Opcode::Sxtb, vec![g32(6), g32(5)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    // The address fold still fires (SXTW+ADD → LDRB RO), but the SXTB stays.
    assert!(pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(ops.contains(&AArch64Opcode::LdrbRO));
    assert!(
        ops.contains(&AArch64Opcode::Sxtb),
        "SXTB is not redundant — kept"
    );
    // The load result feeds the SXTB, so it is NOT redirected.
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrbRO)
        .unwrap();
    assert_eq!(func.inst(ldr_id).operands[0], g32(5), "load dst unchanged");
}

#[test]
fn strips_redundant_uxtb_without_address_fold() {
    // Even when the address is already simple (no SXTW/ADD chain to fold), a
    // redundant UXTB of a byte-load result is stripped and the load rewritten
    // to write the extend's destination.
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(0), imm(3)]),
        MachInst::new(AArch64Opcode::Uxtb, vec![g32(6), g32(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(7), g32(6), g32(6)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(
        !ops.contains(&AArch64Opcode::Uxtb),
        "redundant UXTB stripped"
    );
    let ldr_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrbRI)
        .unwrap();
    assert_eq!(
        func.inst(ldr_id).operands[0],
        g32(6),
        "load writes extend dst"
    );
}

#[test]
fn keeps_uxth_after_byte_load_but_strips_after_half_load() {
    // UXTH after a BYTE load is redundant (byte already clears bits 31:8 ⊃
    // 31:16). Verify it is stripped.
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(0), imm(0)]),
        MachInst::new(AArch64Opcode::Uxth, vec![g32(6), g32(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(7), g32(6), g32(6)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    assert!(!block_opcodes(&func).contains(&AArch64Opcode::Uxth));
}

#[test]
fn no_strip_uxtb_after_word_load() {
    // UXTB after a WORD load is NOT redundant (bits 31:8 may be set) — kept.
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(0), imm(0)]),
        MachInst::new(AArch64Opcode::Uxtb, vec![g32(6), g32(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(7), g32(6), g32(6)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(
        !pass.run(&mut func),
        "no fold: UXTB after word load is real"
    );
}

#[test]
fn no_fold_when_scale_not_single_def_movz() {
    // The scale register is redefined → its value is not the pattern
    // constant at the MADD; keep the chain.
    let mut insts = sxtw_madd_load_chain();
    insts.insert(3, MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(8)]));
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(!pass.run(&mut func));
}

#[test]
fn idempotent() {
    let mut func = make_func(sxtw_madd_load_chain());
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    assert!(!pass.run(&mut func), "second run must be a no-op");
}

#[test]
fn provenance_records_merge() {
    use trust_cg_ir::{PassId, ProvenanceMap, TrustIrInstId};
    let mut func = make_func(sxtw_madd_load_chain());
    let insts = func.block(func.entry).insts.clone();
    let sxtw_id = insts[3];
    let madd_id = insts[4];
    let ldr_id = insts[5];

    let mut provenance = ProvenanceMap::new();
    provenance.record_lowering(TrustIrInstId(1), &[sxtw_id], PassId::new("isel"));
    provenance.record_lowering(TrustIrInstId(2), &[madd_id], PassId::new("isel"));
    provenance.record_lowering(TrustIrInstId(3), &[ldr_id], PassId::new("isel"));

    let mut pass = ExtRegAddrFold;
    assert!(pass.run_with_provenance(&mut func, &mut provenance));

    let entry = provenance.get_entry(ldr_id).expect("folded load entry");
    assert!(entry.trust_ir_origins.contains(&TrustIrInstId(1)));
    assert!(entry.trust_ir_origins.contains(&TrustIrInstId(2)));
    assert!(entry.trust_ir_origins.contains(&TrustIrInstId(3)));
}

// ---------------------------------------------------------------------------
// Fold (A): cross-block read-modify-write STORE
// ---------------------------------------------------------------------------

/// Build the nsieve-bits shape: block A holds `Movz/Uxtw/Madd` + the load;
/// block B (whose sole predecessor is A) holds the conditional store back to the
/// same `base[index]`. `extra_b` lets a test insert instructions into B before
/// the store; `extra_preds` adds additional predecessor blocks to B.
fn make_cross_block_rmw(scale: i64, extra_b: &[MachInst], extra_preds: usize) -> MachFunction {
    let mut func = MachFunction::new("test_xblock".to_string(), Signature::new(vec![], vec![]));
    let a = func.entry;
    let b = func.create_block();
    let a_insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]), // base
        MachInst::new(AArch64Opcode::AddRI, vec![g32(1), g32(91), imm(0)]), // i32 index
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(scale)]),       // scale
        MachInst::new(AArch64Opcode::Uxtw, vec![g64(3), g32(1)]),           // zext idx
        MachInst::new(AArch64Opcode::Madd, vec![g64(4), g64(3), g64(2), g64(0)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(4), imm(0)]), // load [addr]
    ];
    for inst in a_insts {
        let id = func.push_inst(inst);
        func.append_inst(a, id);
    }
    // Block B: (optional extra insts) then EOR + store back to [addr].
    for inst in extra_b {
        let id = func.push_inst(inst.clone());
        func.append_inst(b, id);
    }
    for inst in [
        MachInst::new(AArch64Opcode::EorRR, vec![g32(6), g32(5), g32(1)]),
        MachInst::new(AArch64Opcode::StrRI, vec![g32(6), g64(4), imm(0)]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(b, id);
    }
    func.add_edge(a, b);
    for _ in 0..extra_preds {
        let p = func.create_block();
        func.add_edge(p, b);
    }
    func
}

fn ops_of(func: &MachFunction, block: BlockId) -> Vec<AArch64Opcode> {
    func.block(block)
        .insts
        .iter()
        .map(|&id| func.inst(id).opcode)
        .collect()
}

#[test]
fn folds_cross_block_rmw_store_to_str_ro() {
    // The nsieve-bits bit-flip: the load's Madd address is shared with a store
    // in a dominated single-predecessor successor. BOTH fold to the RO form and
    // the shared Uxtw/Madd chain is deleted.
    // Fold (A) is opt-in (default-off, do-no-harm); enable it for this test.
    // The thread-local opt-in is restored on scope exit, even on panic.
    let (func, a, b, fired) =
        crate::env_lock::with_env_overrides(&[("TCG_EXT_ADDR_XBLOCK_STORE", "1")], || {
            let mut func = make_cross_block_rmw(4, &[], 0);
            let a = func.entry;
            let b = func.block_order[1];
            let mut pass = ExtRegAddrFold;
            let fired = pass.run(&mut func);
            (func, a, b, fired)
        });
    assert!(fired);

    let a_ops = ops_of(&func, a);
    assert!(!a_ops.contains(&AArch64Opcode::Uxtw), "shared Uxtw deleted");
    assert!(!a_ops.contains(&AArch64Opcode::Madd), "shared Madd deleted");
    assert!(
        a_ops.contains(&AArch64Opcode::LdrRO),
        "load folded to LdrRO"
    );

    let b_ops = ops_of(&func, b);
    assert!(
        b_ops.contains(&AArch64Opcode::StrRO),
        "cross-block store folded"
    );

    // The folded store carries [store_val, base, index32, packed]; UXTW option
    // (0b010) shifted by log2(4)=1 → packed = (0b010<<1)|1 = 5.
    let str_id = *func
        .block(b)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::StrRO)
        .unwrap();
    let st = func.inst(str_id);
    assert_eq!(st.operands[0], g32(6), "store value preserved");
    assert_eq!(st.operands[1], g64(0), "base register");
    assert_eq!(st.operands[2], g32(1), "32-bit index register");
    assert_eq!(st.operands[3], imm(5), "UXTW, S=1 (word)");
}

#[test]
fn no_cross_block_fold_when_store_reused_in_loop() {
    // A store reused INSIDE A LOOP (the nsieve-bits bit flip / Bubblesort-Perm
    // swap store-back — a memory-bound RMW) is deferred to the OPT-IN Fold (A),
    // not folded by the default cross-block path (the do-no-harm boundary:
    // folding it adds AGU work off the critical path). With the store unfolded,
    // the all-or-nothing grouping leaves the load's chain intact too.
    let mut func = MachFunction::new(
        "test_loop_store".to_string(),
        Signature::new(vec![], vec![]),
    );
    let a = func.entry;
    let b = func.create_block();
    let c = func.create_block();
    for inst in [
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::AddRI, vec![g32(1), g32(91), imm(0)]),
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(4)]),
        MachInst::new(AArch64Opcode::Uxtw, vec![g64(3), g32(1)]),
        MachInst::new(AArch64Opcode::Madd, vec![g64(4), g64(3), g64(2), g64(0)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(4), imm(0)]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(a, id);
    }
    let st = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![g32(5), g64(4), imm(0)],
    ));
    func.append_inst(b, st);
    func.add_edge(a, b);
    func.add_edge(b, c);
    func.add_edge(c, b); // back-edge: B is a loop header, the store lives in the loop

    let mut pass = ExtRegAddrFold;
    assert!(
        !pass.run(&mut func),
        "store reused in a loop must defer to opt-in Fold (A)"
    );
    assert!(
        ops_of(&func, a).contains(&AArch64Opcode::Madd),
        "Madd preserved"
    );
    assert!(!ops_of(&func, b).contains(&AArch64Opcode::StrRO));
}

/// The Towers `stack[s]` shape (the SEXT-SCALE lever): a scaled-index `Madd`
/// address computed once in the entry block, its load in that block AND a second
/// load + a store back at a control-flow JOIN the entry dominates. All three uses
/// fold and the shared `Sxtw`/`Madd` chain is deleted. The store's block is a
/// dominated JOIN (2 predecessors, and the Madd's block is NOT a direct
/// predecessor of it), so it is folded by default — not deferred to Fold (A).
#[test]
fn folds_cross_block_join_reuse_load_and_store() {
    let mut func = MachFunction::new("test_join".to_string(), Signature::new(vec![], vec![]));
    let a = func.entry;
    let bl = func.create_block();
    let cl = func.create_block();
    let d = func.create_block();
    for inst in [
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]), // base
        MachInst::new(AArch64Opcode::AddRI, vec![g32(1), g32(91), imm(0)]), // i32 index
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(4)]),           // scale
        MachInst::new(AArch64Opcode::Sxtw, vec![g64(3), g32(1)]),
        MachInst::new(AArch64Opcode::Madd, vec![g64(4), g64(3), g64(2), g64(0)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(4), imm(0)]), // load1 (same block)
    ] {
        let id = func.push_inst(inst);
        func.append_inst(a, id);
    }
    for inst in [
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(6), g64(4), imm(0)]), // load2 (join)
        MachInst::new(AArch64Opcode::StrRI, vec![g32(6), g64(4), imm(0)]), // store  (join)
    ] {
        let id = func.push_inst(inst);
        func.append_inst(d, id);
    }
    func.add_edge(a, bl);
    func.add_edge(a, cl);
    func.add_edge(bl, d);
    func.add_edge(cl, d);

    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));

    let a_ops = ops_of(&func, a);
    assert!(!a_ops.contains(&AArch64Opcode::Sxtw), "shared Sxtw deleted");
    assert!(!a_ops.contains(&AArch64Opcode::Madd), "shared Madd deleted");
    assert!(
        a_ops.contains(&AArch64Opcode::LdrRO),
        "entry-block load folded"
    );

    let d_ops = ops_of(&func, d);
    assert!(
        d_ops.contains(&AArch64Opcode::LdrRO),
        "cross-block join load folded"
    );
    assert!(
        d_ops.contains(&AArch64Opcode::StrRO),
        "cross-block join store folded"
    );

    // Every folded op carries [.., base, index32, packed]; SXTW (0b110) shifted
    // by log2(4)=1 → packed = (0b110 << 1) | 1 = 13.
    for &id in &func.block(d).insts {
        let inst = func.inst(id);
        if matches!(inst.opcode, AArch64Opcode::LdrRO | AArch64Opcode::StrRO) {
            assert_eq!(inst.operands[1], g64(0), "base register");
            assert_eq!(inst.operands[2], g32(1), "32-bit index register");
            assert_eq!(inst.operands[3], imm(13), "SXTW, S=1 (word)");
        }
    }
}

/// Genuine non-dominance: the `Madd` sits in block A which the store's block D is
/// ALSO reachable WITHOUT passing through (an `entry → D` bypass edge), so A does
/// not dominate D and the address the store would read is not the one this Madd
/// derived — fail closed. The all-or-nothing grouping then keeps the load's chain
/// too.
#[test]
fn no_cross_block_fold_when_madd_does_not_dominate() {
    let mut func = MachFunction::new("test_nodom".to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let am = func.create_block();
    let d = func.create_block();
    for inst in [
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::AddRI, vec![g32(1), g32(91), imm(0)]),
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(4)]),
        MachInst::new(AArch64Opcode::Sxtw, vec![g64(3), g32(1)]),
        MachInst::new(AArch64Opcode::Madd, vec![g64(4), g64(3), g64(2), g64(0)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(5), g64(4), imm(0)]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(am, id);
    }
    let st = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![g32(5), g64(4), imm(0)],
    ));
    func.append_inst(d, st);
    func.add_edge(entry, am);
    func.add_edge(entry, d); // bypass: reaches D without the Madd
    func.add_edge(am, d);

    let mut pass = ExtRegAddrFold;
    assert!(
        !pass.run(&mut func),
        "non-dominating store must fail closed"
    );
    assert!(
        ops_of(&func, am).contains(&AArch64Opcode::Madd),
        "Madd preserved"
    );
}

#[test]
fn no_cross_block_fold_when_index_redefined_in_successor() {
    // The 32-bit index is redefined in B before the store, so it no longer holds
    // the derivation-time value at the store → fail closed (and, since the store
    // cannot fold, the whole chain is preserved).
    let redef = [MachInst::new(
        AArch64Opcode::AddRI,
        vec![g32(1), g32(92), imm(0)],
    )];
    let mut func = make_cross_block_rmw(4, &redef, 0);
    let mut pass = ExtRegAddrFold;
    assert!(!pass.run(&mut func));
    assert!(
        ops_of(&func, func.entry).contains(&AArch64Opcode::Madd),
        "Madd preserved"
    );
}

// NOTE: the two kill switches (`TCG_NO_EXT_ADDR_XBLOCK_STORE` /
// `TCG_NO_EXT_ADDR_NARROW_SEXT`) are validated out-of-band via object-code
// identity (kill-switch on vs off) in the mini-sweep harness, not here — an
// in-process `set_var` would race the parallel test threads that also read
// those vars through the pass.

// ---------------------------------------------------------------------------
// Fold (B): narrow LOAD feeding a SIGN-extend
// ---------------------------------------------------------------------------

#[test]
fn folds_ldrb_sxtb_to_ldrsb_gpr32() {
    // LDRB + SXTB (32-bit dst) → LDRSB writing the extend's dst; the SXTB is
    // deleted. This is the methcall `return this->state` (signed char) shape.
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(0), imm(0)]),
        MachInst::new(AArch64Opcode::Sxtb, vec![g32(6), g32(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(7), g32(6), g32(6)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(
        !ops.contains(&AArch64Opcode::Sxtb),
        "SXTB folded into the load"
    );
    assert!(ops.contains(&AArch64Opcode::LdrsbRI), "load became LDRSB");
    let ld_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrsbRI)
        .unwrap();
    assert_eq!(
        func.inst(ld_id).operands[0],
        g32(6),
        "load writes the SXTB dst"
    );
}

#[test]
fn folds_ldrb_sxtb_to_ldrsb_gpr64() {
    // A 64-bit SXTB destination (the isel emits this for a `signext` return via
    // the X-register extension path) folds to a 64-bit LDRSB (the encoder picks
    // opc=10 from the Gpr64 transfer class) — sound because the load performs the
    // full 64-bit sign extension the SXTB did.
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(0), imm(0)]),
        MachInst::new(AArch64Opcode::Sxtb, vec![g64(6), g32(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g64(7), g64(6), g64(6)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(!ops.contains(&AArch64Opcode::Sxtb));
    let ld_id = *func
        .block(func.entry)
        .insts
        .iter()
        .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrsbRI)
        .unwrap();
    assert_eq!(
        func.inst(ld_id).operands[0],
        g64(6),
        "load writes the 64-bit SXTB dst"
    );
}

#[test]
fn folds_ldrh_sxth_to_ldrsh() {
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::LdrhRI, vec![g32(5), g64(0), imm(0)]),
        MachInst::new(AArch64Opcode::Sxth, vec![g32(6), g32(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(7), g32(6), g32(6)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(!ops.contains(&AArch64Opcode::Sxth));
    assert!(ops.contains(&AArch64Opcode::LdrshRI));
}

#[test]
fn no_sext_fold_on_ldrb_ro() {
    // A byte GATHER folds its address to LDRB RO in phase 1; the following SXTB
    // must NOT be folded (no LDRSB RO opcode exists) — fail closed, SXTB kept.
    let mut insts = sxtw_add_ldrb_uxtb_chain();
    insts[5] = MachInst::new(AArch64Opcode::Sxtb, vec![g32(6), g32(5)]);
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(
        ops.contains(&AArch64Opcode::LdrbRO),
        "address still folds to LDRB RO"
    );
    assert!(
        ops.contains(&AArch64Opcode::Sxtb),
        "SXTB over a RO load is kept"
    );
    assert!(!ops.contains(&AArch64Opcode::LdrsbRI));
}

#[test]
fn no_sext_fold_on_width_mismatch() {
    // SXTH over a BYTE load is not a plain width-fold (the byte load's bits 31:8
    // are already zero) → left untouched.
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(0), imm(0)]),
        MachInst::new(AArch64Opcode::Sxth, vec![g32(6), g32(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(7), g32(6), g32(6)]),
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(!pass.run(&mut func));
    assert!(
        block_opcodes(&func).contains(&AArch64Opcode::Sxth),
        "mismatched SXTH kept"
    );
}

#[test]
fn no_sext_fold_when_load_multi_use() {
    // The byte load feeds the SXTB AND another consumer → not single-use, so the
    // opcode is NOT swapped (swapping would sign-extend the OTHER use's value).
    let insts = vec![
        MachInst::new(AArch64Opcode::AddRI, vec![g64(0), g64(90), imm(0)]),
        MachInst::new(AArch64Opcode::LdrbRI, vec![g32(5), g64(0), imm(0)]),
        MachInst::new(AArch64Opcode::Sxtb, vec![g32(6), g32(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(7), g32(5), g32(6)]), // 2nd use of g32(5)
    ];
    let mut func = make_func(insts);
    let mut pass = ExtRegAddrFold;
    assert!(!pass.run(&mut func));
    let ops = block_opcodes(&func);
    assert!(
        ops.contains(&AArch64Opcode::LdrbRI),
        "load opcode unchanged"
    );
    assert!(ops.contains(&AArch64Opcode::Sxtb), "SXTB kept");
}
