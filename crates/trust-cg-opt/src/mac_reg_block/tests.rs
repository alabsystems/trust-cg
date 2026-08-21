// Unit tests for mac-reg-block. The end-to-end soundness gate is the
// differential matmul fuzz (fire on every N%8==0 square nest; fail-closed on
// aliasing / non-distinct-local / rectangular / non-multiple-of-8 shapes); here
// we white-box the subtle counted-loop recognizer (`resolve_to_carried` /
// `verify_counted_0_n`) that must see through the conventional-SSA MovR-phi,
// body-copy and self-copy forms, plus the kill switch.

use std::collections::HashSet;

use trust_cg_ir::{
    AArch64Opcode as Op, BlockId, MachFunction, MachInst, MachOperand, RegClass, Signature, VReg,
};

use super::*;

fn g(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr64)
}
fn vr(id: u32) -> MachOperand {
    MachOperand::VReg(g(id))
}
fn im(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn bl(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn push(f: &mut MachFunction, b: BlockId, op: Op, ops: Vec<MachOperand>) {
    let id = f.push_inst(MachInst::new(op, ops));
    f.append_inst(b, id);
}

/// Build a canonical `for iv in 0..N` counted loop in the header-phi / body-copy
/// form (the shape p4's i/k loops take after copy coalescing), optionally with a
/// degenerate `body_iv = MovR(body_iv)` self-copy artifact, an off-by init, or a
/// stride-2 step. Returns `(func, body, header, index_iv)`.
fn build_counted_loop(
    n: i64,
    init: i64,
    step: i64,
    self_copy: bool,
) -> (MachFunction, HashSet<BlockId>, BlockId, VReg) {
    // vregs: 1=phi, 2=t(header), 3=body_iv, 4=index_iv, 5=inc
    let mut f = MachFunction::new("cl".into(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let hdr = f.create_block();
    let body = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();

    // bb0 preheader: phi = init ; -> hdr
    push(&mut f, bb0, Op::Movz, vec![vr(1), im(init)]);
    push(&mut f, bb0, Op::B, vec![bl(hdr)]);
    // hdr: t = MovR(phi) ; Cmp(t, n) ; BCond LO -> body ; B -> exit
    push(&mut f, hdr, Op::MovR, vec![vr(2), vr(1)]);
    push(&mut f, hdr, Op::CmpRI, vec![vr(2), im(n)]);
    push(&mut f, hdr, Op::BCond, vec![im(3), bl(body)]); // LO
    push(&mut f, hdr, Op::B, vec![bl(exit)]);
    // body: body_iv = MovR(phi) ; [self-copy] ; index_iv = MovR(body_iv) ; -> latch
    push(&mut f, body, Op::MovR, vec![vr(3), vr(1)]);
    if self_copy {
        push(&mut f, body, Op::MovR, vec![vr(3), vr(3)]);
    }
    push(&mut f, body, Op::MovR, vec![vr(4), vr(3)]);
    push(&mut f, body, Op::B, vec![bl(latch)]);
    // latch: inc = AddRI(body_iv, step) ; phi = MovR(inc) ; -> hdr
    push(&mut f, latch, Op::AddRI, vec![vr(5), vr(3), im(step)]);
    push(&mut f, latch, Op::MovR, vec![vr(1), vr(5)]);
    push(&mut f, latch, Op::B, vec![bl(hdr)]);
    // exit
    push(&mut f, exit, Op::Ret, vec![]);

    f.add_edge(bb0, hdr);
    f.add_edge(hdr, body);
    f.add_edge(hdr, exit);
    f.add_edge(body, latch);
    f.add_edge(latch, hdr);

    let body_set: HashSet<BlockId> = [hdr, body, latch].into_iter().collect();
    (f, body_set, hdr, g(4))
}

#[test]
fn tile_is_eight() {
    assert_eq!(TILE, 8);
}

#[test]
fn counted_loop_phi_copy_form_recognized() {
    let (f, body, hdr, idx) = build_counted_loop(24, 0, 1, false);
    let def = build_def_map(&f);
    assert!(verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false));
}

#[test]
fn counted_loop_survives_self_copy_artifact() {
    // The exact fragility that first broke recognition: a `body_iv = MovR(body_iv)`
    // self-copy that `build_def_map` (last-def-wins) resolves to. Must still work.
    let (f, body, hdr, idx) = build_counted_loop(24, 0, 1, true);
    let def = build_def_map(&f);
    assert!(verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false));
    // resolve_to_carried must land on the loop-carried phi (vreg 1), not spin on
    // the self-copy (vreg 3).
    assert_eq!(
        resolve_to_carried(&f, idx, latch_of(&f, hdr, &body)),
        Some(g(1))
    );
}

#[test]
fn counted_loop_rejects_nonzero_init() {
    let (f, body, hdr, idx) = build_counted_loop(24, 3, 1, false);
    let def = build_def_map(&f);
    assert!(!verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false));
}

#[test]
fn counted_loop_rejects_stride_two() {
    let (f, body, hdr, idx) = build_counted_loop(24, 0, 2, false);
    let def = build_def_map(&f);
    assert!(!verify_counted_0_n(&f, &def, &body, hdr, idx, 24, false));
}

#[test]
fn counted_loop_rejects_wrong_bound() {
    let (f, body, hdr, idx) = build_counted_loop(24, 0, 1, false);
    let def = build_def_map(&f);
    // header tests against 24, but caller expects N=16 -> reject.
    assert!(!verify_counted_0_n(&f, &def, &body, hdr, idx, 16, false));
}

fn latch_of(f: &MachFunction, header: BlockId, body: &HashSet<BlockId>) -> BlockId {
    single_latch(f, header, body).expect("latch")
}

#[test]
fn kill_switch_disables_pass() {
    // With TCG_NO_MAC_REG_BLOCK set, run() is a no-op even on a fireable shape.
    // (We only assert the enable gate here; end-to-end firing is covered by the
    // differential matmul fuzz.)
    // SAFETY: opt lib tests run with --test-threads=1 (no concurrent env races).
    unsafe { std::env::set_var("TCG_NO_MAC_REG_BLOCK", "1") };
    let mut pass = MacRegBlock::new();
    let (mut f, _, _, _) = build_counted_loop(24, 0, 1, false);
    assert!(!<MacRegBlock as MachinePass>::run(&mut pass, &mut f));
    assert_eq!(pass.fired(), 0);
    unsafe { std::env::remove_var("TCG_NO_MAC_REG_BLOCK") };
}

/// WRONG-CODE REGRESSION (2026-08-17): recognition used to accept any positive
/// element scale while `apply` emits 64-bit lanes unconditionally, so an i32
/// matmul (scale 4) became 64-bit loads at 4-byte strides — two packed i32s per
/// lane and a 4-byte over-read past the array. It miscompiled silently and
/// NON-DETERMINISTICALLY (repeat runs of one binary disagreed) at O2/O3 for
/// square i32 N in {8,16,24,32,64,128}, all now matching LLVM.
///
/// The end-to-end differential coverage for this pass was i64-only, which is
/// exactly how it survived; this pins the width invariant directly.
#[test]
fn kernel_rejects_non_eight_byte_elements() {
    assert!(kernel_supports_scale(8), "i64 lanes are what apply() emits");
    for bad in [1, 2, 4, 16, 3, -8, 0] {
        assert!(
            !kernel_supports_scale(bad),
            "scale {bad} must fail closed: apply() would emit 64-bit lanes for it"
        );
    }
}

// --- k-loop pointer-writeback gate ---------------------------------------
//
// `pair_writeback_ok` is the fail-closed guard in front of the `LdrPostIndex` /
// `LdpRI` / `LdpPostIndex` k-loop shape. Anything it rejects must fall back to
// the original `LdrRI` + two `AddRI` body, so the pass never emits a pair
// offset outside the LDP signed-imm7 range or a pair load of the wrong width.

#[test]
fn pair_writeback_accepts_the_shipped_tile() {
    // TILE = 8, i64 elements, N = 24 -> lane offsets 0..48, writeback 192.
    assert!(pair_writeback_ok(8, 24 * 8, TILE));
}

#[test]
fn pair_writeback_rejects_non_i64_scale() {
    // LDP of a Gpr64 pair always transfers 8 bytes per lane; a 4-byte element
    // scale would silently load the wrong width.
    assert!(!pair_writeback_ok(4, 24 * 4, TILE));
    assert!(!pair_writeback_ok(1, 24, TILE));
}

#[test]
fn pair_writeback_rejects_odd_tile() {
    // Lanes are consumed two at a time.
    assert!(!pair_writeback_ok(8, 24 * 8, 7));
    assert!(!pair_writeback_ok(8, 24 * 8, 1));
    assert!(!pair_writeback_ok(8, 24 * 8, 0));
}

#[test]
fn pair_writeback_rejects_out_of_range_writeback() {
    // The post-index amount is N*scale; LDP's scaled imm7 tops out at 504.
    assert!(pair_writeback_ok(8, 504, TILE)); // N = 63, exactly encodable
    assert!(!pair_writeback_ok(8, 512, TILE)); // N = 64, one step too far
    assert!(!pair_writeback_ok(8, 8 * 1024, TILE));
}

#[test]
fn pair_writeback_rejects_out_of_range_lane_offset() {
    // Highest lane offset is (TILE-2)*scale, so at scale 8 the last encodable
    // tile is TILE = 64 ((64-2)*8 = 496 <= 504) and TILE = 66 is one past it.
    assert!(pair_writeback_ok(8, 8, 64));
    assert!(!pair_writeback_ok(8, 8, 66)); // (66-2)*8 = 512 > 504
}
