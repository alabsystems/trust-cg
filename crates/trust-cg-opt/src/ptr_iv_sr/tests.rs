// trust-cg-opt - Pointer-IV strength reduction tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::pass_manager::MachinePass;
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, RegClass, Signature};

fn g64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn f64r(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr64))
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}

/// Vreg ids used by the builders (kept well clear of `alloc_vreg`'s counter,
/// which the builders advance past them).
const BASE: u32 = 0; // loop-invariant base pointer
const INV: u32 = 1; // loop-invariant non-constant (e.g. sxtw(np))
const STRIDE: u32 = 2; // Movz #72 (row stride)
const SCALE: u32 = 3; // Movz #8 (element size)
const IV: u32 = 4; // conventional IV carrier V
const IV_INIT: u32 = 5; // IV init value
const MUL: u32 = 6; // MulRR IV, SCALE
const IDX: u32 = 7; // Madd INV, STRIDE, MUL
const XFER: u32 = 8; // transfer register
const NEXT: u32 = 9; // AddRI IV, #1
const LIMIT: u32 = 10; // trip bound

fn append(func: &mut MachFunction, block: trust_cg_ir::BlockId, inst: MachInst) {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
}

/// The almabench planetpv shape: a 2-block rotated loop walking
/// `base + INV*STRIDE + IV*SCALE`.
///
/// ```text
/// bb0 (preheader): defs of BASE/INV/STRIDE/SCALE/LIMIT, MovR IV, IV_INIT; b bb1
/// bb1 (header):    MulRR MUL, IV, SCALE
///                  Madd  IDX, INV, STRIDE, MUL
///                  LdrRO XFER, [BASE, IDX]        (3-operand plain form)
///                  AddRI NEXT, IV, #1
///                  CmpRR NEXT, LIMIT
///                  BCond exit ; B latch
/// bb2 (latch):     MovR IV, NEXT ; b bb1
/// bb3 (exit):      Ret
/// ```
fn make_two_block_loop(mem: MachInst) -> MachFunction {
    let mut func = MachFunction::new("test_ptr_iv_sr".to_string(), Signature::new(vec![], vec![]));
    // Reserve the named ids.
    while func.next_vreg <= 40 {
        func.alloc_vreg();
    }
    let bb0 = func.entry;
    let bb1 = func.create_block();
    let bb2 = func.create_block();
    let bb3 = func.create_block();

    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(BASE), g64(30), imm(0)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(INV), g64(31), imm(0)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::Movz, vec![g64(STRIDE), imm(72)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::Movz, vec![g64(SCALE), imm(8)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::Movz, vec![g64(LIMIT), imm(8)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::Movz, vec![g64(IV_INIT), imm(0)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::MovR, vec![g64(IV), g64(IV_INIT)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );

    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::MulRR, vec![g64(MUL), g64(IV), g64(SCALE)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(
            AArch64Opcode::Madd,
            vec![g64(IDX), g64(INV), g64(STRIDE), g64(MUL)],
        ),
    );
    append(&mut func, bb1, mem);
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(NEXT), g64(IV), imm(1)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(NEXT), g64(LIMIT)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb3)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
    );

    append(
        &mut func,
        bb2,
        MachInst::new(AArch64Opcode::MovR, vec![g64(IV), g64(NEXT)]),
    );
    append(
        &mut func,
        bb2,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );

    append(&mut func, bb3, MachInst::new(AArch64Opcode::Ret, vec![]));

    func.add_edge(bb0, bb1);
    func.add_edge(bb1, bb3);
    func.add_edge(bb1, bb2);
    func.add_edge(bb2, bb1);

    func
}

fn ldro_plain() -> MachInst {
    MachInst::new(AArch64Opcode::LdrRO, vec![f64r(XFER), g64(BASE), g64(IDX)])
}

fn opcodes(func: &MachFunction, block: u32) -> Vec<AArch64Opcode> {
    func.block(trust_cg_ir::BlockId(block))
        .insts
        .iter()
        .map(|&id| func.inst(id).opcode)
        .collect()
}

#[test]
fn rewrites_two_block_madd_walk_to_walking_pointer() {
    let mut func = make_two_block_loop(ldro_plain());
    let mut pass = PtrIvStrengthReduce;
    assert!(pass.run(&mut func));

    // Header: chain deleted, access now a zero-offset LdrRI.
    let header = opcodes(&func, 1);
    assert!(!header.contains(&AArch64Opcode::MulRR), "chain must die");
    assert!(!header.contains(&AArch64Opcode::Madd), "chain must die");
    assert!(!header.contains(&AArch64Opcode::LdrRO));
    assert!(header.contains(&AArch64Opcode::LdrRI));
    let ldr = func
        .block(trust_cg_ir::BlockId(1))
        .insts
        .iter()
        .map(|&id| func.inst(id))
        .find(|i| i.opcode == AArch64Opcode::LdrRI)
        .unwrap();
    assert_eq!(ldr.operands[2].as_imm(), Some(0));

    // Latch: AddRI #8 + MovR carrier inserted BEFORE the IV's MovR.
    let latch = opcodes(&func, 2);
    assert_eq!(
        latch,
        vec![
            AArch64Opcode::AddRI,
            AArch64Opcode::MovR,
            AArch64Opcode::MovR,
            AArch64Opcode::B
        ]
    );
    let adv = func.inst(func.block(trust_cg_ir::BlockId(2)).insts[0]);
    assert_eq!(
        adv.operands[2].as_imm(),
        Some(8),
        "C = 1*8 (scale) * step 1"
    );

    // Preheader: cloned chain + P0 AddRR + carrier MovR before the branch.
    let pre = opcodes(&func, 0);
    assert!(pre.contains(&AArch64Opcode::MulRR));
    assert!(pre.contains(&AArch64Opcode::Madd));
    assert!(pre.contains(&AArch64Opcode::AddRR));
    assert_eq!(*pre.last().unwrap(), AArch64Opcode::B);
}

#[test]
fn rewrites_store_and_load_sharing_one_index_chain() {
    let mut func = make_two_block_loop(ldro_plain());
    // Add a second access (a store) reusing IDX, before the IV increment.
    let str_inst = func.push_inst(MachInst::new(
        AArch64Opcode::StrRO,
        vec![f64r(XFER), g64(BASE), g64(IDX)],
    ));
    let header = trust_cg_ir::BlockId(1);
    let pos = func
        .block(header)
        .insts
        .iter()
        .position(|&id| func.inst(id).opcode == AArch64Opcode::AddRI)
        .unwrap();
    func.block_mut(header).insts.insert(pos, str_inst);

    let mut pass = PtrIvStrengthReduce;
    assert!(pass.run(&mut func));

    let ops = opcodes(&func, 1);
    assert!(ops.contains(&AArch64Opcode::LdrRI));
    assert!(ops.contains(&AArch64Opcode::StrRI));
    assert!(!ops.contains(&AArch64Opcode::Madd));
    // The shared chain is cloned ONCE (one MulRR + one Madd in the preheader),
    // but each access gets its own P0 + carrier.
    let pre = opcodes(&func, 0);
    assert_eq!(
        pre.iter().filter(|op| **op == AArch64Opcode::MulRR).count(),
        1
    );
    assert_eq!(
        pre.iter().filter(|op| **op == AArch64Opcode::Madd).count(),
        1
    );
    assert_eq!(
        pre.iter().filter(|op| **op == AArch64Opcode::AddRR).count(),
        2
    );
}

#[test]
fn gates_out_chain_with_remaining_uses() {
    let mut func = make_two_block_loop(ldro_plain());
    // IDX has a second, non-memory consumer: the chain cannot die, so the
    // rewrite would ADD a carrier while deleting nothing — the profitability
    // gate must drop the plan entirely.
    let user = func.push_inst(MachInst::new(
        AArch64Opcode::AddRR,
        vec![g64(33), g64(IDX), g64(IDX)],
    ));
    let header = trust_cg_ir::BlockId(1);
    let pos = func
        .block(header)
        .insts
        .iter()
        .position(|&id| func.inst(id).opcode == AArch64Opcode::CmpRR)
        .unwrap();
    func.block_mut(header).insts.insert(pos, user);

    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    let ops = opcodes(&func, 1);
    assert!(ops.contains(&AArch64Opcode::LdrRO), "access left untouched");
    assert!(ops.contains(&AArch64Opcode::Madd));
}

#[test]
fn gates_out_plain_iv_register_offset() {
    // The Stanford-Perm shape: the index IS the IV (empty chain), so the
    // register-offset form is already optimal — the profitability gate must
    // leave it alone (rewriting measurably regressed Perm by adding carried
    // pointers across a recursive call).
    let mem = MachInst::new(
        AArch64Opcode::LdrRO,
        vec![f64r(XFER), g64(BASE), g64(IV), imm(0b0111)],
    );
    let mut func = make_two_block_loop(mem);
    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}

#[test]
fn rewrites_self_loop_shifted_ldro() {
    // Single-block rotated loop with the packed LSL S=1 form and a two-op
    // index chain: idx = (IV via MovR) + 2; ldr d, [base, idx, lsl #3].
    let mut func = MachFunction::new("self_loop".to_string(), Signature::new(vec![], vec![]));
    while func.next_vreg <= 40 {
        func.alloc_vreg();
    }
    let bb0 = func.entry;
    let bb1 = func.create_block();
    let bb2 = func.create_block();

    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(BASE), g64(30), imm(0)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::Movz, vec![g64(LIMIT), imm(8)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::Movz, vec![g64(IV_INIT), imm(0)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::MovR, vec![g64(IV), g64(IV_INIT)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );

    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::MovR, vec![g64(MUL), g64(IV)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(IDX), g64(MUL), imm(2)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(
            AArch64Opcode::LdrRO,
            vec![f64r(XFER), g64(BASE), g64(IDX), imm(0b0111)],
        ),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(NEXT), g64(IV), imm(1)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::MovR, vec![g64(IV), g64(NEXT)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(NEXT), g64(LIMIT)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb1)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
    );
    append(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

    func.add_edge(bb0, bb1);
    func.add_edge(bb1, bb1);
    func.add_edge(bb1, bb2);

    let mut pass = PtrIvStrengthReduce;
    assert!(pass.run(&mut func));

    let ops = opcodes(&func, 1);
    assert!(!ops.contains(&AArch64Opcode::LdrRO));
    assert!(ops.contains(&AArch64Opcode::LdrRI));
    // The chain (MovR + AddRI #2) is deleted from the loop and cloned into
    // the preheader, where P0 = AddRRShift base, idx_clone, #3; the carrier
    // advances by 1 << 3 = 8.
    let bb1_insts: Vec<&MachInst> = func
        .block(trust_cg_ir::BlockId(1))
        .insts
        .iter()
        .map(|&id| func.inst(id))
        .collect();
    assert!(
        !bb1_insts
            .iter()
            .any(|i| i.opcode == AArch64Opcode::AddRI && i.operands[2].as_imm() == Some(2)),
        "index chain must be deleted from the loop"
    );
    let pre = opcodes(&func, 0);
    assert!(pre.contains(&AArch64Opcode::AddRRShift));
    let bb1_id = trust_cg_ir::BlockId(1);
    let adv = func
        .block(bb1_id)
        .insts
        .iter()
        .map(|&id| func.inst(id))
        .find(|i| i.opcode == AArch64Opcode::AddRI && i.operands[2].as_imm() == Some(8))
        .expect("carrier advance AddRI #8 in the (self-)latch");
    assert!(adv.operands[0].as_vreg().unwrap().id > LIMIT);
}

#[test]
fn bails_on_sxtw_packed_extend() {
    // SXTW option ((0b110 << 1) | 1): sign-extend of a loop-variant index —
    // must never be touched.
    let mem = MachInst::new(
        AArch64Opcode::LdrRO,
        vec![f64r(XFER), g64(BASE), g64(IDX), imm(0b1101)],
    );
    let mut func = make_two_block_loop(mem);
    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}

#[test]
fn bails_when_header_has_extra_loop_block() {
    // Split the back path into TWO blocks (header -> mid -> latch): the body
    // is no longer {header, latch} and the pass must bail.
    let mut func = make_two_block_loop(ldro_plain());
    let bb1 = trust_cg_ir::BlockId(1);
    let bb2 = trust_cg_ir::BlockId(2);
    let mid = func.create_block();
    append(
        &mut func,
        mid,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
    );
    // Rewire header -> mid -> latch.
    let term = *func.block(bb1).insts.last().unwrap();
    if let MachOperand::Block(t) = &mut func.inst_mut(term).operands[0] {
        *t = mid;
    }
    func.block_mut(bb1).succs.retain(|s| *s != bb2);
    func.block_mut(bb2).preds.retain(|p| *p != bb1);
    func.add_edge(bb1, mid);
    func.add_edge(mid, bb2);

    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}

#[test]
fn bails_on_multi_def_base() {
    let mut func = make_two_block_loop(ldro_plain());
    // Second def of BASE (outside the loop): no longer provably invariant at
    // the P0 computation.
    let redef = func.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![g64(BASE), g64(30), imm(16)],
    ));
    let bb0 = func.entry;
    let len = func.block(bb0).insts.len();
    func.block_mut(bb0).insts.insert(len - 1, redef);

    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}

#[test]
fn bails_on_loop_variant_scale() {
    // The multiply's "constant" factor is loop-variant (defined in the
    // header): no compile-time derivative — bail.
    let mut func = make_two_block_loop(ldro_plain());
    let bb1 = trust_cg_ir::BlockId(1);
    let variant_scale = func.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![g64(34), g64(NEXT), imm(0)],
    ));
    func.block_mut(bb1).insts.insert(0, variant_scale);
    // Retarget the MulRR to the variant scale.
    let mul_id = func
        .block(bb1)
        .insts
        .iter()
        .copied()
        .find(|&id| func.inst(id).opcode == AArch64Opcode::MulRR)
        .unwrap();
    func.inst_mut(mul_id).operands[2] = g64(34);

    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}

#[test]
fn bails_on_step_beyond_imm12() {
    // Element stride 4096: the per-iteration advance no longer fits the
    // AddRI imm12 — bail rather than emit an unencodable immediate.
    let mut func = make_two_block_loop(ldro_plain());
    let scale_id = func
        .block(func.entry)
        .insts
        .iter()
        .copied()
        .find(|&id| {
            let i = func.inst(id);
            i.opcode == AArch64Opcode::Movz && i.operands[0].as_vreg().map(|v| v.id) == Some(SCALE)
        })
        .unwrap();
    func.inst_mut(scale_id).operands[1] = imm(4096);

    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}

#[test]
fn negative_step_advances_with_subri() {
    // Downward IV: V = V - 1 (SubRI). The carrier must retreat by 8.
    let mut func = make_two_block_loop(ldro_plain());
    let bb1 = trust_cg_ir::BlockId(1);
    let next_id = func
        .block(bb1)
        .insts
        .iter()
        .copied()
        .find(|&id| func.inst(id).opcode == AArch64Opcode::AddRI)
        .unwrap();
    func.inst_mut(next_id).opcode = AArch64Opcode::SubRI;

    let mut pass = PtrIvStrengthReduce;
    assert!(pass.run(&mut func));
    let latch = opcodes(&func, 2);
    assert_eq!(
        latch,
        vec![
            AArch64Opcode::SubRI,
            AArch64Opcode::MovR,
            AArch64Opcode::MovR,
            AArch64Opcode::B
        ]
    );
    let adv = func.inst(func.block(trust_cg_ir::BlockId(2)).insts[0]);
    assert_eq!(adv.operands[2].as_imm(), Some(8));
}

#[test]
fn bails_without_preheader() {
    // A second outside predecessor of the header removes the preheader.
    let mut func = make_two_block_loop(ldro_plain());
    let bb1 = trust_cg_ir::BlockId(1);
    let extra = func.create_block();
    append(
        &mut func,
        extra,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );
    func.add_edge(extra, bb1);

    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}

#[test]
fn bails_when_iv_has_third_def() {
    // A conditional extra def of the IV (three defs total): not a
    // conventional carrier — bail.
    let mut func = make_two_block_loop(ldro_plain());
    let redef = func.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![g64(IV), g64(IV), imm(2)],
    ));
    let bb2 = trust_cg_ir::BlockId(2);
    func.block_mut(bb2).insts.insert(0, redef);

    let mut pass = PtrIvStrengthReduce;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}

#[test]
fn kill_switch_disables_pass() {
    let env_scope = crate::env_lock::override_scope();
    let _kill_switch = crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_NO_PTR_IV_SR", "1");
    let mut func = make_two_block_loop(ldro_plain());
    let mut pass = PtrIvStrengthReduce;
    let changed = pass.run(&mut func);
    assert!(!changed);
    assert!(opcodes(&func, 1).contains(&AArch64Opcode::LdrRO));
}
