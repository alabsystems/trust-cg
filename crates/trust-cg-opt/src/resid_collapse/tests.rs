// Unit tests for the single-trip residual-loop collapse.
//
// Each test builds the scalar-unroll full-unroll tail shape in miniature — a
// preheader materializing the iv constant, a header body with the
// `AddRI step; Cmp; BCond exit; B latch` counted-exit, and a writeback latch —
// and checks that the pass collapses exactly the proven-single-trip case and
// fails closed on every perturbation.

use super::*;
use crate::pass_manager::MachinePass;
use trust_cg_ir::{MachFunction, RegClass, Signature};

fn g64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn g32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn i(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn blk(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn push(func: &mut MachFunction, b: BlockId, op: AArch64Opcode, ops: Vec<MachOperand>) {
    let id = func.push_inst(MachInst::new(op, ops));
    func.append_inst(b, id);
}
fn run(func: &mut MachFunction) -> bool {
    ResidTripCollapse.run(func)
}
fn last_opcode(func: &MachFunction, b: BlockId) -> AArch64Opcode {
    let &id = func.block(b).insts.last().unwrap();
    func.inst(id).opcode
}

/// Knobs for the canonical two-block tail: iv enters as `#init`, body steps
/// `step = iv + 1`, exits on `step == #bound` (CmpRR against a Movz).
struct Shape {
    init: i64,
    bound: i64,
    /// Use `CmpRI #bound` instead of `CmpRR` vs a materialized bound.
    cmp_imm: bool,
    /// Backedge goes straight to the header (no separate latch block).
    self_loop: bool,
    /// Redefine the iv inside the header BEFORE the AddRI (kills the entry
    /// constant).
    clobber_iv_early: bool,
    /// Make the iv's entry value non-constant (copy of an unknown).
    unknown_iv: bool,
    /// Give the latch a second predecessor.
    extra_latch_pred: bool,
}

impl Shape {
    fn base() -> Self {
        Shape {
            init: 9,
            bound: 10,
            cmp_imm: false,
            self_loop: false,
            clobber_iv_early: false,
            unknown_iv: false,
            extra_latch_pred: false,
        }
    }
}

/// vreg ids: 1=iv, 2=step, 3=bound, 4=iv-const source, 5=scratch, 6=unknown.
fn build(shape: Shape) -> (MachFunction, BlockId, BlockId, Option<BlockId>) {
    let mut func = MachFunction::new("t".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry;
    let hdr = func.create_block();
    let latch = if shape.self_loop {
        None
    } else {
        Some(func.create_block())
    };
    let exit = func.create_block();

    // Preheader: iv = #init (through the MovR copy scalar-unroll emits),
    // bound = #bound.
    push(
        &mut func,
        ph,
        AArch64Opcode::Movz,
        vec![g64(4), i(shape.init)],
    );
    if shape.unknown_iv {
        // iv <- copy of an unresolvable value (no def of v6 anywhere).
        push(&mut func, ph, AArch64Opcode::MovR, vec![g64(1), g64(6)]);
    } else {
        push(&mut func, ph, AArch64Opcode::MovR, vec![g64(1), g64(4)]);
    }
    push(
        &mut func,
        ph,
        AArch64Opcode::Movz,
        vec![g64(3), i(shape.bound)],
    );
    push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph, hdr);

    // Header: [optional iv clobber], some body work, step = iv + 1,
    // cmp step, bound; b.eq exit; b latch-or-header.
    if shape.clobber_iv_early {
        push(&mut func, hdr, AArch64Opcode::Movz, vec![g64(1), i(0)]);
    }
    push(
        &mut func,
        hdr,
        AArch64Opcode::AddRI,
        vec![g64(5), g64(1), i(0)],
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::AddRI,
        vec![g64(2), g64(1), i(1)],
    );
    if shape.cmp_imm {
        push(
            &mut func,
            hdr,
            AArch64Opcode::CmpRI,
            vec![g64(2), i(shape.bound)],
        );
    } else {
        push(&mut func, hdr, AArch64Opcode::CmpRR, vec![g64(2), g64(3)]);
    }
    push(
        &mut func,
        hdr,
        AArch64Opcode::BCond,
        vec![i(CC_EQ), blk(exit)],
    );
    let back = latch.unwrap_or(hdr);
    push(&mut func, hdr, AArch64Opcode::B, vec![blk(back)]);
    func.add_edge(hdr, exit);
    func.add_edge(hdr, back);

    // Latch: writeback + backedge.
    if let Some(l) = latch {
        push(&mut func, l, AArch64Opcode::MovR, vec![g64(1), g64(2)]);
        push(&mut func, l, AArch64Opcode::B, vec![blk(hdr)]);
        func.add_edge(l, hdr);
        if shape.extra_latch_pred {
            // A second entry into the latch breaks the only-via-fallthrough
            // proof.
            push(&mut func, exit, AArch64Opcode::B, vec![blk(l)]);
            func.add_edge(exit, l);
        }
    }
    if !shape.extra_latch_pred {
        push(&mut func, exit, AArch64Opcode::Ret, vec![]);
    }
    (func, hdr, exit, latch)
}

#[test]
fn canonical_two_block_tail_collapses() {
    let (mut func, hdr, exit, latch) = build(Shape::base());
    let latch = latch.unwrap();
    assert!(run(&mut func), "pass must fire");
    // Terminator rewritten to a single unconditional B(exit).
    assert_eq!(last_opcode(&func, hdr), AArch64Opcode::B);
    let &term = func.block(hdr).insts.last().unwrap();
    assert_eq!(func.inst(term).operands[0], blk(exit));
    // No BCond left; backedge and latch unlinked.
    assert!(!func.block(hdr).succs.contains(&latch));
    assert!(!func.block_order.contains(&latch));
    // Idempotent: a second run reports no change.
    assert!(!run(&mut func), "collapsed shape must not re-match");
}

#[test]
fn cmp_ri_variant_collapses() {
    let (mut func, hdr, exit, _) = build(Shape {
        cmp_imm: true,
        ..Shape::base()
    });
    assert!(run(&mut func));
    let &term = func.block(hdr).insts.last().unwrap();
    assert_eq!(func.inst(term).operands[0], blk(exit));
}

#[test]
fn self_loop_backedge_collapses() {
    let (mut func, hdr, exit, _) = build(Shape {
        self_loop: true,
        ..Shape::base()
    });
    assert!(run(&mut func));
    assert!(!func.block(hdr).succs.contains(&hdr), "backedge removed");
    let &term = func.block(hdr).insts.last().unwrap();
    assert_eq!(func.inst(term).operands[0], blk(exit));
}

#[test]
fn not_taken_constant_fails_closed() {
    // init 5, bound 10: 6 != 10, the loop genuinely iterates — no change.
    let (mut func, ..) = build(Shape {
        init: 5,
        ..Shape::base()
    });
    assert!(!run(&mut func));
}

#[test]
fn unknown_entry_iv_fails_closed() {
    let (mut func, ..) = build(Shape {
        unknown_iv: true,
        ..Shape::base()
    });
    assert!(!run(&mut func));
}

#[test]
fn iv_clobbered_before_step_fails_closed() {
    // The header rewrites the iv before the AddRI: even though the clobber is
    // ALSO the constant 0 here, the entry-value contract (no def before the
    // AddRI) must fail closed.
    let (mut func, ..) = build(Shape {
        clobber_iv_early: true,
        ..Shape::base()
    });
    assert!(!run(&mut func));
}

#[test]
fn latch_with_second_pred_fails_closed() {
    let (mut func, ..) = build(Shape {
        extra_latch_pred: true,
        ..Shape::base()
    });
    assert!(!run(&mut func));
}

#[test]
fn hs_condition_collapses_unsigned() {
    // b.hs with step == bound: unsigned 10 >= 10 — taken.
    let (mut func, hdr, exit, _) = build(Shape::base());
    // Patch the BCond's condition code to HS.
    let &bc = &func.block(hdr).insts[func.block(hdr).insts.len() - 2];
    func.inst_mut(bc).operands[0] = i(CC_HS);
    assert!(run(&mut func));
    let &term = func.block(hdr).insts.last().unwrap();
    assert_eq!(func.inst(term).operands[0], blk(exit));
}

#[test]
fn unsupported_condition_fails_closed() {
    // b.ne (cc=1) is not a supported taken-exit shape.
    let (mut func, hdr, ..) = build(Shape::base());
    let &bc = &func.block(hdr).insts[func.block(hdr).insts.len() - 2];
    func.inst_mut(bc).operands[0] = i(1);
    assert!(!run(&mut func));
}

#[test]
fn gpr32_width_collapse() {
    // Same tail at W width: iv/step/bound Gpr32, 9+1 == 10.
    let mut func = MachFunction::new("t32".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry;
    let hdr = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    push(&mut func, ph, AArch64Opcode::Movz, vec![g32(4), i(9)]);
    push(&mut func, ph, AArch64Opcode::MovR, vec![g32(1), g32(4)]);
    push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph, hdr);
    push(
        &mut func,
        hdr,
        AArch64Opcode::AddRI,
        vec![g32(2), g32(1), i(1)],
    );
    push(&mut func, hdr, AArch64Opcode::CmpRI, vec![g32(2), i(10)]);
    push(
        &mut func,
        hdr,
        AArch64Opcode::BCond,
        vec![i(CC_EQ), blk(exit)],
    );
    push(&mut func, hdr, AArch64Opcode::B, vec![blk(latch)]);
    func.add_edge(hdr, exit);
    func.add_edge(hdr, latch);
    push(&mut func, latch, AArch64Opcode::MovR, vec![g32(1), g32(2)]);
    push(&mut func, latch, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(latch, hdr);
    push(&mut func, exit, AArch64Opcode::Ret, vec![]);
    assert!(run(&mut func));
    assert!(!func.block_order.contains(&latch));
}

#[test]
fn latch_with_noncopy_inst_fails_closed() {
    // A latch carrying a non-copy instruction (a store) must not be unlinked.
    let (mut func, _, _, latch) = build(Shape::base());
    let latch = latch.unwrap();
    // Insert a store before the latch terminator.
    let id = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![g64(2), g64(3), i(0)],
    ));
    let pos = func.block(latch).insts.len() - 1;
    func.block_mut(latch).insts.insert(pos, id);
    assert!(!run(&mut func));
}

/// Split the single-entry shape into TWO reachable entries: the preheader
/// conditionally branches to a second block that re-materializes the iv as
/// `#second_init` and falls into the header.
fn add_second_entry(func: &mut MachFunction, hdr: BlockId, second_init: i64) {
    let ph = func.entry;
    let ph2 = func.create_block();
    // Rewrite the preheader terminator `B hdr` into `BCond -> ph2; B hdr`.
    let &term = func.block(ph).insts.last().unwrap();
    assert_eq!(func.inst(term).opcode, AArch64Opcode::B);
    func.block_mut(ph).insts.pop();
    push(func, ph, AArch64Opcode::CmpRI, vec![g64(4), i(1)]);
    push(func, ph, AArch64Opcode::BCond, vec![i(CC_EQ), blk(ph2)]);
    push(func, ph, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph, ph2);
    push(func, ph2, AArch64Opcode::Movz, vec![g64(7), i(second_init)]);
    push(func, ph2, AArch64Opcode::MovR, vec![g64(1), g64(7)]);
    push(func, ph2, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph2, hdr);
}

#[test]
fn two_matching_entries_collapse() {
    // Two reachable entries delivering the SAME constant: still proven.
    let (mut func, hdr, exit, latch) = build(Shape::base());
    let latch = latch.unwrap();
    add_second_entry(&mut func, hdr, 9);
    assert!(run(&mut func));
    assert!(!func.block_order.contains(&latch));
    let &term = func.block(hdr).insts.last().unwrap();
    assert_eq!(func.inst(term).operands[0], blk(exit));
}

#[test]
fn mismatched_entry_constants_fail_closed() {
    // A second entry delivering a DIFFERENT constant poisons the proof.
    let (mut func, hdr, ..) = build(Shape::base());
    add_second_entry(&mut func, hdr, 3);
    assert!(!run(&mut func));
}
