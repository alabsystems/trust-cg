// Unit tests for the neon-butterfly AoS complex-butterfly vectorizer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::Signature;

fn v64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn f32r(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr32))
}
fn i(x: i64) -> MachOperand {
    MachOperand::Imm(x)
}
fn b(x: BlockId) -> MachOperand {
    MachOperand::Block(x)
}

fn count(func: &MachFunction, op: AArch64Opcode) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}

/// Count `BCond` instructions whose condition-code (operand 0) is `cc`.
fn count_bcond(func: &MachFunction, cc: i64) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::BCond && imm_of(&inst.operands[0]) == Some(cc)
        })
        .count()
}

/// Variants of the butterfly loop built by [`build_butterfly`].
///  0 => the exact Oscar `Fft` inner-loop machine shape (MUST fire)
///  1 => COMMUTED sum operands in the ip fadd (order mismatch => BAIL)
///  2 => a FIFTH store (extra memory effect => BAIL)
///  3 => a loop temp (`dr`) used in the exit block (live-out => BAIL)
///  4 => non-adjacent twiddle fields (`e.ip` at +16, not +4 => BAIL)
///  5 => missing FNEG on the rp twiddle product (different rounding => BAIL)
///  6 => induction step +2 (=> BAIL)
///
/// Register map mirrors the real Oscar dump: v1=z, v2=w, v29=e cell root,
/// v10=m, v27=k, v21=j (bound), v28=Movz(8), v38=iv, v85=iv+1.
fn build_butterfly(variant: u8) -> MachFunction {
    let mut func = MachFunction::new("Fft".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader: invariant bases/indices (self-copy = opaque invariant), the
    // element size, and the induction seed.
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // z base
    push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // w base
    push(&mut func, bb0, Copy, vec![v64(29), v64(29)]); // e cell root
    push(&mut func, bb0, Copy, vec![v64(10), v64(10)]); // m
    push(&mut func, bb0, Copy, vec![v64(27), v64(27)]); // k
    push(&mut func, bb0, Copy, vec![v64(21), v64(21)]); // j (bound)
    push(&mut func, bb0, Movz, vec![v64(28), i(8)]); // element size
    push(&mut func, bb0, Copy, vec![v64(20), v64(20)]); // i0 seed
    push(&mut func, bb0, MovR, vec![v64(38), v64(20)]); // iv = i0
    push(&mut func, bb0, B, vec![b(header)]);

    // Header: the exact butterfly body (see the module docs / Oscar dump).
    let e_ip_off = if variant == 4 { 16 } else { 12 };
    push(
        &mut func,
        header,
        Madd,
        vec![v64(40), v64(38), v64(28), v64(1)],
    );
    push(&mut func, header, LdrRI, vec![f32r(41), v64(40), i(0)]); // z[i].rp
    push(
        &mut func,
        header,
        Madd,
        vec![v64(43), v64(10), v64(28), v64(40)],
    );
    push(&mut func, header, LdrRI, vec![f32r(44), v64(43), i(0)]); // z[i+m].rp
    push(
        &mut func,
        header,
        FaddRR,
        vec![f32r(45), f32r(41), f32r(44)],
    );
    push(
        &mut func,
        header,
        Madd,
        vec![v64(47), v64(38), v64(28), v64(2)],
    );
    push(
        &mut func,
        header,
        Madd,
        vec![v64(49), v64(27), v64(28), v64(47)],
    );
    push(&mut func, header, StrRI, vec![f32r(45), v64(49), i(0)]); // w[i+k].rp
    push(&mut func, header, AddRI, vec![v64(51), v64(40), i(4)]);
    push(&mut func, header, LdrRI, vec![f32r(52), v64(51), i(0)]); // z[i].ip
    push(&mut func, header, AddRI, vec![v64(54), v64(43), i(4)]);
    push(&mut func, header, LdrRI, vec![f32r(55), v64(54), i(0)]); // z[i+m].ip
    if variant == 1 {
        push(
            &mut func,
            header,
            FaddRR,
            vec![f32r(56), f32r(55), f32r(52)],
        );
    } else {
        push(
            &mut func,
            header,
            FaddRR,
            vec![f32r(56), f32r(52), f32r(55)],
        );
    }
    push(&mut func, header, StrRI, vec![f32r(56), v64(49), i(4)]); // w[i+k].ip
    push(&mut func, header, LdrRI, vec![f32r(59), v64(29), i(8)]); // e.rp
    push(&mut func, header, LdrRI, vec![f32r(60), v64(40), i(0)]); // reload
    push(&mut func, header, LdrRI, vec![f32r(61), v64(43), i(0)]); // reload
    push(
        &mut func,
        header,
        FsubRR,
        vec![f32r(62), f32r(60), f32r(61)],
    ); // dr
    push(
        &mut func,
        header,
        LdrRI,
        vec![f32r(63), v64(29), i(e_ip_off)],
    ); // e.ip
    push(&mut func, header, LdrRI, vec![f32r(64), v64(51), i(0)]); // reload
    push(&mut func, header, LdrRI, vec![f32r(65), v64(54), i(0)]); // reload
    push(
        &mut func,
        header,
        FsubRR,
        vec![f32r(66), f32r(64), f32r(65)],
    ); // di
    if variant == 5 {
        push(
            &mut func,
            header,
            FmulRR,
            vec![f32r(68), f32r(63), f32r(66)],
        );
    } else {
        push(&mut func, header, FnegRR, vec![f32r(67), f32r(66)]);
        push(
            &mut func,
            header,
            FmulRR,
            vec![f32r(68), f32r(63), f32r(67)],
        );
    }
    push(
        &mut func,
        header,
        FmaddRR,
        vec![f32r(69), f32r(59), f32r(62), f32r(68)],
    );
    push(
        &mut func,
        header,
        Madd,
        vec![v64(71), v64(21), v64(28), v64(47)],
    );
    push(&mut func, header, StrRI, vec![f32r(69), v64(71), i(0)]); // w[i+j].rp
    push(&mut func, header, LdrRI, vec![f32r(72), v64(29), i(8)]); // e.rp
    push(&mut func, header, LdrRI, vec![f32r(73), v64(51), i(0)]); // reload
    push(&mut func, header, LdrRI, vec![f32r(74), v64(54), i(0)]); // reload
    push(
        &mut func,
        header,
        FsubRR,
        vec![f32r(75), f32r(73), f32r(74)],
    ); // di
    push(
        &mut func,
        header,
        LdrRI,
        vec![f32r(76), v64(29), i(e_ip_off)],
    ); // e.ip
    push(&mut func, header, LdrRI, vec![f32r(77), v64(40), i(0)]); // reload
    push(&mut func, header, LdrRI, vec![f32r(78), v64(43), i(0)]); // reload
    push(
        &mut func,
        header,
        FsubRR,
        vec![f32r(79), f32r(77), f32r(78)],
    ); // dr
    push(
        &mut func,
        header,
        FmulRR,
        vec![f32r(80), f32r(76), f32r(79)],
    );
    push(
        &mut func,
        header,
        FmaddRR,
        vec![f32r(81), f32r(72), f32r(75), f32r(80)],
    );
    push(&mut func, header, StrRI, vec![f32r(81), v64(71), i(4)]); // w[i+j].ip
    if variant == 2 {
        push(&mut func, header, StrRI, vec![f32r(45), v64(49), i(0)]);
    }
    let step = if variant == 6 { 2 } else { 1 };
    push(&mut func, header, AddRI, vec![v64(85), v64(38), i(step)]);
    push(&mut func, header, CmpRR, vec![v64(38), v64(21)]);
    push(&mut func, header, BCond, vec![i(CC_LT), b(latch)]);
    push(&mut func, header, B, vec![b(exit)]);

    // Latch: the induction writeback.
    push(&mut func, latch, MovR, vec![v64(38), v64(85)]);
    push(&mut func, latch, B, vec![b(header)]);

    // Exit.
    if variant == 3 {
        push(&mut func, exit, FaddRR, vec![f32r(99), f32r(62), f32r(62)]);
    }
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, header);
    func.add_edge(header, latch);
    func.add_edge(header, exit);
    func.add_edge(latch, header);
    func
}

fn run(func: &mut MachFunction) -> usize {
    let mut pass = NeonButterflyPass::new();
    pass.run(func);
    pass.fired()
}

#[test]
fn fires_on_oscar_fft_shape() {
    let mut func = build_butterfly(0);
    assert_eq!(run(&mut func), 1, "the exact Oscar shape must vectorize");

    // Vector body shape: two pair loads, two pair stores, one of each op.
    assert_eq!(count(&func, AArch64Opcode::NeonLd1Post), 2);
    assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 2);
    assert_eq!(count(&func, AArch64Opcode::NeonFaddV), 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFsubV), 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFmulV), 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFmlaV), 1);
    assert_eq!(count(&func, AArch64Opcode::NeonRev64V), 1);
    assert_eq!(count(&func, AArch64Opcode::NeonEorV), 1);
    assert_eq!(count(&func, AArch64Opcode::NeonOrrV), 1);
    // Twiddle broadcasts + the sign-mask splat.
    assert_eq!(count(&func, AArch64Opcode::NeonDupElem), 2);
    assert_eq!(count(&func, AArch64Opcode::NeonDupGen), 1);
    // 7 wrap-safe range pairs x 2 unsigned sub-tests.
    assert_eq!(count_bcond(&func, CC_LO), 14);
    // Magnitude gates.
    assert_eq!(count(&func, AArch64Opcode::Cbnz), 2);

    // REV64 carries the `.4S` arrangement (32-bit pair swap, NOT the byte
    // form) and EOR is register-only (no arrangement immediate).
    for blk in &func.blocks {
        for &id in &blk.insts {
            let inst = func.inst(id);
            if inst.opcode == AArch64Opcode::NeonRev64V {
                assert_eq!(imm_of(inst.operands.last().unwrap()), Some(ARR_S4));
            }
            if inst.opcode == AArch64Opcode::NeonEorV {
                assert_eq!(inst.operands.len(), 3);
            }
        }
    }

    // The scalar loop is left in place (fallback + tail): all 16 scalar loads
    // and 4 stores survive.
    assert_eq!(count(&func, AArch64Opcode::LdrRI), 16 + 2);
    assert_eq!(count(&func, AArch64Opcode::StrRI), 4);
}

#[test]
fn preheader_reroutes_into_gate_chain() {
    let mut func = build_butterfly(0);
    let header = BlockId(1);
    assert_eq!(run(&mut func), 1);
    // The entry block's terminator no longer targets the scalar header.
    let entry_term = *func.block(func.entry).insts.last().unwrap();
    assert!(!branch_targets(func.inst(entry_term)).contains(&header));
    // The scalar header is still reachable (fallback edges from the gates).
    assert!(!func.block(header).preds.is_empty());
}

#[test]
fn bails_on_commuted_sum_operands() {
    let mut func = build_butterfly(1);
    assert_eq!(
        run(&mut func),
        0,
        "operand order is bit-exactness: must bail"
    );
}

#[test]
fn bails_on_extra_store() {
    let mut func = build_butterfly(2);
    assert_eq!(run(&mut func), 0);
}

#[test]
fn bails_on_loop_temp_live_out() {
    let mut func = build_butterfly(3);
    assert_eq!(run(&mut func), 0, "a loop temp used outside must bail");
}

#[test]
fn bails_on_non_adjacent_twiddle_fields() {
    let mut func = build_butterfly(4);
    assert_eq!(run(&mut func), 0);
}

#[test]
fn bails_on_missing_fneg() {
    let mut func = build_butterfly(5);
    assert_eq!(run(&mut func), 0, "sign structure differs: must bail");
}

#[test]
fn bails_on_non_unit_step() {
    let mut func = build_butterfly(6);
    assert_eq!(run(&mut func), 0);
}
