// Tests for scalar post-index formation.
//
// The pass turns a header-resident `LdrRO` whose index is `base + (inv<<k) +
// (V<<s)` into `LdrPostIndex [P], #elem`. Its soundness rests on the LOAD and
// the IV each running exactly once per iteration, so the refusals below pin the
// shapes where that stops being true.

use super::*;
use trust_cg_ir::Signature;

const BASE: u32 = 1;
const INV: u32 = 2;
const IV: u32 = 3;
const IDX: u32 = 4;
const T: u32 = 5;
const XFER: u32 = 6;
const LIMIT: u32 = 7;

fn g64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn g32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn append(func: &mut MachFunction, block: BlockId, inst: MachInst) {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
}

fn folded(func: &MachFunction) -> bool {
    func.block_order.iter().any(|&b| {
        func.block(b)
            .insts
            .iter()
            .any(|&i| func.inst(i).opcode == AArch64Opcode::LdrPostIndex)
    })
}

/// ```text
/// bb0 (preheader): defs of BASE/INV/LIMIT, IV = 0 ; b bb1
/// bb1 (header):    LslRI  T,   IV, #shift
///                  AddRRShift IDX, T, INV, #11
///                  LdrRO  XFER, [BASE, IDX]
///                  AddRI  IV, IV, #step
///                  CmpRR  IV, LIMIT ; BCond bb2 ; B bb1
/// bb2 (exit):      Ret
/// ```
fn make_loop(shift: i64, dst32: bool, step: i64) -> (MachFunction, BlockId) {
    let mut func = MachFunction::new(
        "post_index_test".to_string(),
        Signature::new(vec![], vec![]),
    );
    while func.next_vreg <= 20 {
        func.alloc_vreg();
    }
    let bb0 = func.entry;
    let bb1 = func.create_block();
    let bb2 = func.create_block();

    for r in [BASE, INV, LIMIT] {
        append(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![g64(r), imm(0)]),
        );
    }
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::Movz, vec![g64(IV), imm(0)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );

    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::LslRI, vec![g64(T), g64(IV), imm(shift)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(
            AArch64Opcode::AddRRShift,
            vec![g64(IDX), g64(T), g64(INV), imm(11)],
        ),
    );
    let dst = if dst32 { g32(XFER) } else { g64(XFER) };
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::LdrRO, vec![dst, g64(BASE), g64(IDX)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(IV), g64(IV), imm(step)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(IV), g64(LIMIT)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb2)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );
    append(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

    // The CFG is stored on the blocks, not derived from terminators.
    func.block_mut(bb0).succs = vec![bb1];
    func.block_mut(bb1).preds = vec![bb0, bb1];
    func.block_mut(bb1).succs = vec![bb2, bb1];
    func.block_mut(bb2).preds = vec![bb1];
    (func, bb1)
}

#[test]
fn folds_a_header_load_whose_index_is_affine_in_a_unit_stride_iv() {
    let (mut f, _) = make_loop(2, true, 1);
    assert!(PostIndexForm.run(&mut f), "expected the fold to fire");
    assert!(folded(&f), "expected an LdrPostIndex");
}

/// The pointer advances by the LOAD's transfer width, so a shift that does not
/// match the element size would desynchronise `P` from the index.
#[test]
fn refuses_when_the_shift_does_not_match_the_transfer_width() {
    let (mut f, _) = make_loop(3, true, 1); // 1<<3 = 8, but the load moves 4
    assert!(
        !PostIndexForm.run(&mut f),
        "shift/width mismatch must refuse"
    );
    assert!(!folded(&f));
}

/// A step != 1 moves the index by more than one element per iteration, which a
/// single post-index writeback cannot track.
#[test]
fn refuses_a_non_unit_iv_step() {
    let (mut f, _) = make_loop(2, true, 2);
    assert!(!PostIndexForm.run(&mut f), "non-unit IV step must refuse");
    assert!(!folded(&f));
}

/// The packed-extend `LdrRO` forms carry SXTW/UXTW, where extending a
/// loop-variant 32-bit index does not commute with the 64-bit step — the
/// historic matrix-multiply miscompile. Never fold those.
#[test]
fn refuses_the_packed_extend_ldrro_form() {
    let (mut f, hdr) = make_loop(2, true, 1);
    let load = f.block(hdr).insts[2];
    f.inst_mut(load).operands.push(imm(0b0111));
    assert!(!PostIndexForm.run(&mut f), "packed-extend must refuse");
    assert!(!folded(&f));
}

/// If the index feeds anything besides the load, deleting the chain would drop
/// a live value.
#[test]
fn refuses_when_the_index_has_another_use() {
    let (mut f, hdr) = make_loop(2, true, 1);
    append(
        &mut f,
        hdr,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(19), g64(IDX), imm(1)]),
    );
    assert!(!PostIndexForm.run(&mut f), "extra use must refuse");
    assert!(!folded(&f));
}

/// A base redefined inside the loop is not loop-invariant, so `P0` seeded in
/// the preheader would not track it.
#[test]
fn refuses_when_the_base_is_not_loop_invariant() {
    let (mut f, hdr) = make_loop(2, true, 1);
    append(
        &mut f,
        hdr,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(BASE), g64(BASE), imm(8)]),
    );
    assert!(!PostIndexForm.run(&mut f), "variant base must refuse");
    assert!(!folded(&f));
}

#[test]
fn kill_switch_makes_the_pass_inert() {
    trust_cg_process_env::with_env_overrides(&[("TCG_NO_POST_INDEX", "1")], || {
        let (mut f, _) = make_loop(2, true, 1);
        assert!(!PostIndexForm.run(&mut f), "kill switch must disable");
        assert!(!folded(&f));
    });
}
