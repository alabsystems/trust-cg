// trust-cg-opt - AArch64 bounds-check-elimination unit tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::{
    AArch64Opcode as Op, MachInst, MachOperand as MO, ProofAnnotation, Signature, VReg,
};

fn g64(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr64)
}
fn g32(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr32)
}

fn push(func: &mut MachFunction, b: BlockId, inst: MachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(b, id);
    id
}

fn movr(d: VReg, s: VReg) -> MachInst {
    MachInst::new(Op::MovR, vec![MO::VReg(d), MO::VReg(s)])
}
fn movi(d: VReg, imm: i64) -> MachInst {
    MachInst::new(Op::MovI, vec![MO::VReg(d), MO::Imm(imm)])
}
fn movz(d: VReg, imm: i64) -> MachInst {
    MachInst::new(Op::Movz, vec![MO::VReg(d), MO::Imm(imm)])
}
fn movk(d: VReg, imm: i64, sh: i64) -> MachInst {
    MachInst::new(Op::Movk, vec![MO::VReg(d), MO::Imm(imm), MO::Imm(sh)])
}
fn cmprr(a: VReg, b: VReg) -> MachInst {
    MachInst::new(Op::CmpRR, vec![MO::VReg(a), MO::VReg(b)])
}
fn cmpri(a: VReg, imm: i64) -> MachInst {
    MachInst::new(Op::CmpRI, vec![MO::VReg(a), MO::Imm(imm)])
}
fn addri(d: VReg, s: VReg, imm: i64) -> MachInst {
    MachInst::new(Op::AddRI, vec![MO::VReg(d), MO::VReg(s), MO::Imm(imm)])
}
fn bcond(cc: CondCode, taken: BlockId) -> MachInst {
    MachInst::new(
        Op::BCond,
        vec![MO::Imm(cc.encoding() as i64), MO::Block(taken)],
    )
}
fn br(t: BlockId) -> MachInst {
    MachInst::new(Op::B, vec![MO::Block(t)])
}
fn ret() -> MachInst {
    MachInst::new(Op::Ret, vec![])
}
fn carrier(idx: VReg, k: i64) -> MachInst {
    MachInst::new(
        Op::TrapBoundsCheckExact,
        vec![MO::VReg(idx), MO::VReg(idx), MO::Imm(k)],
    )
}

/// Knobs for the canonical own-length counted loop.
struct LoopCfg {
    cc: CondCode,
    /// Guard bound `K'` (materialized by `Movz` in `CmpRR`, or the immediate in `CmpRI`).
    bound_val: i64,
    /// Carrier bound `K`.
    carrier_k: i64,
    /// True: the guarded (bounded) edge is the `BCond` taken target (LO/LS);
    /// false: the guarded edge is the fall-through (HS/HI).
    taken_is_body: bool,
    /// True: guard is `CmpRI iv, bound_val`; false: `Movz bound; CmpRR iv, bound`.
    use_imm_cmp: bool,
}

/// Build:
///   bb0 entry:  iv=MovI 0 ; [bound=Movz(bound_val)] ; B header
///   bb1 header: cIV=MovR iv ; Cmp(cIV, bound) ; BCond[cc] <taken> ; B <other>
///   bb2 body:   cIdx=MovR iv ; TrapBoundsCheckExact[cIdx,cIdx,carrier_k] ; B latch
///   bb3 latch:  iv=AddRI iv,1 ; B header
///   bb4 exit:   Ret
///
/// vreg ids: iv=1, bound=2, cIV=3, cIdx=4.
/// Returns (func, body BlockId, carrier InstId).
fn build_own_length_loop(cfg: &LoopCfg) -> (MachFunction, BlockId, InstId) {
    let mut f = MachFunction::new("loop".into(), Signature::new(vec![], vec![]));
    let entry = f.entry; // bb0
    let header = f.create_block(); // bb1
    let body = f.create_block(); // bb2
    let latch = f.create_block(); // bb3
    let exit = f.create_block(); // bb4

    let iv = g64(1);
    let bound = g64(2);
    let civ = g64(3);
    let cidx = g64(4);

    // entry
    push(&mut f, entry, movi(iv, 0));
    if !cfg.use_imm_cmp {
        push(&mut f, entry, movz(bound, cfg.bound_val));
    }
    push(&mut f, entry, br(header));

    // header
    push(&mut f, header, movr(civ, iv));
    if cfg.use_imm_cmp {
        push(&mut f, header, cmpri(civ, cfg.bound_val));
    } else {
        push(&mut f, header, cmprr(civ, bound));
    }
    let (taken, other) = if cfg.taken_is_body {
        (body, exit)
    } else {
        (exit, body)
    };
    push(&mut f, header, bcond(cfg.cc, taken));
    push(&mut f, header, br(other));

    // body
    push(&mut f, body, movr(cidx, iv));
    let cid = push(&mut f, body, carrier(cidx, cfg.carrier_k));
    push(&mut f, body, br(latch));

    // latch
    push(&mut f, latch, addri(iv, iv, 1));
    push(&mut f, latch, br(header));

    // exit
    push(&mut f, exit, ret());

    // edges
    f.add_edge(entry, header);
    f.add_edge(header, taken);
    f.add_edge(header, other);
    f.add_edge(body, latch);
    f.add_edge(latch, header);

    (f, body, cid)
}

fn present(func: &MachFunction, b: BlockId, id: InstId) -> bool {
    func.block(b).insts.contains(&id)
}

// ---------------------------------------------------------------------------
// ELIMINATE cases
// ---------------------------------------------------------------------------

#[test]
fn eliminate_p7_late_shape_cmprr_movz_bound() {
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LO,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    assert!(present(&f, body, cid));
    let mut pass = AArch64BoundsCheckElimination::new();
    let changed = pass.run_on_function(&mut f);
    assert!(changed, "carrier should be eliminated");
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, body, cid), "carrier must be unlinked");
}

#[test]
fn eliminate_immediate_guard() {
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LO,
        bound_val: 512,
        carrier_k: 512,
        taken_is_body: true,
        use_imm_cmp: true,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, body, cid));
}

#[test]
fn eliminate_nonstrict_ls_taken() {
    // LS (<=u): Kprime = K-1 implies index < K.
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LS,
        bound_val: 1023,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, body, cid));
}

#[test]
fn eliminate_hs_fallthrough_edge() {
    // HS (>=u) taken => the FALL-THROUGH edge carries `index <u bound` (strict).
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::HS,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: false,
        use_imm_cmp: false,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, body, cid));
}

#[test]
fn eliminate_hi_fallthrough_edge_nonstrict() {
    // HI (>u) taken => the FALL-THROUGH edge carries `index <=u bound` (non-strict).
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::HI,
        bound_val: 1023,
        carrier_k: 1024,
        taken_is_body: false,
        use_imm_cmp: false,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, body, cid));
}

// ---------------------------------------------------------------------------
// KEEP cases (fail-safe)
// ---------------------------------------------------------------------------

#[test]
fn keep_cross_bound_kprime_gt_k() {
    // Guard proves index < 2000, but the carrier needs index < 1024: NOT implied.
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LO,
        bound_val: 2000,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    let changed = pass.run_on_function(&mut f);
    assert!(!changed);
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid), "carrier must be kept");
}

#[test]
fn keep_nonstrict_ls_equal_bound() {
    // LS proves index <=u K, which does NOT imply index <u K.
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LS,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn keep_redefined_index_in_body_before_carrier() {
    // Redefine the root iv in the body BEFORE the carrier: value may differ from
    // the guard's snapshot, so the check is kept.
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LO,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    // Insert `iv = AddRI iv, 1` at the very top of the body (before cIdx/carrier).
    let iv = g64(1);
    let redef = f.push_inst(addri(iv, iv, 1));
    f.block_mut(body).insts.insert(0, redef);

    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn keep_no_dominating_guard() {
    // A carrier in the entry block with no dominating unsigned guard on its index.
    let mut f = MachFunction::new("noguard".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let idx = g64(1);
    push(&mut f, entry, movi(idx, 0));
    let cid = push(&mut f, entry, carrier(idx, 1024));
    push(&mut f, entry, ret());

    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, entry, cid));
}

#[test]
fn keep_second_predecessor_breaks_edge_dominance() {
    // The body has a SECOND predecessor besides the header, so the guarded edge
    // does not dominate every path to the carrier.
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LO,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    // Add an extra block that also jumps to `body`.
    let side = f.create_block();
    push(&mut f, side, br(body));
    f.add_edge(f.entry, side);
    f.add_edge(side, body);

    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn keep_signed_guard_condition() {
    // A signed LT guard does not prove an unsigned bound.
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LT,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn keep_equality_guard_condition() {
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::NE,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn keep_width_hole_gpr32_guard() {
    // Guard compares 32-bit values; the carrier index is a distinct 64-bit vreg.
    // A 32-bit fact must not prove a 64-bit bound.
    let mut f = MachFunction::new("width".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();

    let wiv = g32(1); // 32-bit induction/compare value
    let wbound = g32(2);
    let xidx = g64(3); // 64-bit carrier index (unrelated width)

    push(&mut f, entry, movi(wiv, 0));
    push(&mut f, entry, movz(wbound, 1024));
    push(&mut f, entry, movi(xidx, 0));
    push(&mut f, entry, br(header));

    push(&mut f, header, cmprr(wiv, wbound)); // 32-bit CmpRR
    push(&mut f, header, bcond(CondCode::LO, body));
    push(&mut f, header, br(exit));

    let cid = push(&mut f, body, carrier(xidx, 1024));
    push(&mut f, body, br(latch));

    push(&mut f, latch, br(header));
    push(&mut f, exit, ret());

    f.add_edge(entry, header);
    f.add_edge(header, body);
    f.add_edge(header, exit);
    f.add_edge(body, latch);
    f.add_edge(latch, header);

    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn keep_non_constant_guard_rhs_movz_movk() {
    // The bound register is completed by a MOVK, so it is multi-def and its
    // value is unresolved: keep the carrier.
    let mut f = MachFunction::new("movk".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();

    let iv = g64(1);
    let bound = g64(2);
    let civ = g64(3);
    let cidx = g64(4);

    push(&mut f, entry, movi(iv, 0));
    push(&mut f, entry, movz(bound, 0)); // low16
    push(&mut f, entry, movk(bound, 16, 16)); // second def of `bound`
    push(&mut f, entry, br(header));

    push(&mut f, header, movr(civ, iv));
    push(&mut f, header, cmprr(civ, bound));
    push(&mut f, header, bcond(CondCode::LO, body));
    push(&mut f, header, br(exit));

    push(&mut f, body, movr(cidx, iv));
    let cid = push(&mut f, body, carrier(cidx, 1024));
    push(&mut f, body, br(latch));

    push(&mut f, latch, addri(iv, iv, 1));
    push(&mut f, latch, br(header));
    push(&mut f, exit, ret());

    f.add_edge(entry, header);
    f.add_edge(header, body);
    f.add_edge(header, exit);
    f.add_edge(body, latch);
    f.add_edge(latch, header);

    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn keep_root_redefined_in_guard_after_compare() {
    // Redefine the root iv inside the header AFTER the compare's anchor. Because
    // the guard-side compare uses iv DIRECTLY (no copy), the anchor is the
    // compare position and the later redef falls in the scanned region -> keep.
    let mut f = MachFunction::new("dredef".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();

    let iv = g64(1);
    let bound = g64(2);
    let cidx = g64(4);

    push(&mut f, entry, movi(iv, 0));
    push(&mut f, entry, movz(bound, 1024));
    push(&mut f, entry, br(header));

    // header: cmp iv,bound ; iv = add iv,0 (redef AFTER compare) ; b.lo body ; b exit
    push(&mut f, header, cmprr(iv, bound));
    push(&mut f, header, addri(iv, iv, 0)); // redef of root in D at/after anchor
    push(&mut f, header, bcond(CondCode::LO, body));
    push(&mut f, header, br(exit));

    push(&mut f, body, movr(cidx, iv));
    let cid = push(&mut f, body, carrier(cidx, 1024));
    push(&mut f, body, br(latch));

    push(&mut f, latch, addri(iv, iv, 1));
    push(&mut f, latch, br(header));
    push(&mut f, exit, ret());

    f.add_edge(entry, header);
    f.add_edge(header, body);
    f.add_edge(header, exit);
    f.add_edge(body, latch);
    f.add_edge(latch, header);

    let mut pass = AArch64BoundsCheckElimination::new();
    // Note: with the redef immediately after the compare, the compare is no
    // longer directly before the BCond, so the guard decode also fails safe.
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn keep_proof_owned_carrier() {
    // A proof-annotated carrier is owned by the kernel proof path; skip it.
    let (mut f, body, _cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LO,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    // Rebuild the carrier with a proof annotation in place.
    let cidx = g64(4);
    let proven = f.push_inst(carrier(cidx, 1024).with_proof(ProofAnnotation::InBounds));
    // Replace the plain carrier (position 1 in body) with the proven one.
    f.block_mut(body).insts[1] = proven;

    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, proven));
}

#[test]
fn kill_switch_disables_pass() {
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LO,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    let mut pass = AArch64BoundsCheckElimination::new();
    let changed = pass.run_on_function_enabled(&mut f, false);
    assert!(!changed, "kill switch must make run() a no-op");
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(present(&f, body, cid));
}

#[test]
fn two_carriers_same_block_both_eliminated() {
    // Two chained own-length checks at the same guarded bound in one body block.
    let (mut f, body, cid1) = build_own_length_loop(&LoopCfg {
        cc: CondCode::LO,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: true,
        use_imm_cmp: false,
    });
    // Add a second copy + carrier right after the first carrier.
    let iv = g64(1);
    let cidx2 = g64(5);
    let mov2 = f.push_inst(movr(cidx2, iv));
    let cid2 = f.push_inst(carrier(cidx2, 1024));
    // Insert after the first carrier (position 1): mov2 at 2, carrier2 at 3.
    let pos = f.block(body).insts.iter().position(|&i| i == cid1).unwrap();
    f.block_mut(body).insts.insert(pos + 1, cid2);
    f.block_mut(body).insts.insert(pos + 1, mov2);

    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 2);
    assert!(!present(&f, body, cid1));
    assert!(!present(&f, body, cid2));
}

#[test]
fn name_is_stable() {
    let pass = AArch64BoundsCheckElimination::new();
    assert_eq!(MachinePass::name(&pass), "aarch64-bounds-check-elim");
}

// ===========================================================================
// NARROW-INDEX arm (mask / byte-range) — additive, guard-independent.
// ===========================================================================

fn andri(d: VReg, s: VReg, imm: i64) -> MachInst {
    MachInst::new(Op::AndRI, vec![MO::VReg(d), MO::VReg(s), MO::Imm(imm)])
}
fn uxtb(d: VReg, s: VReg) -> MachInst {
    MachInst::new(Op::Uxtb, vec![MO::VReg(d), MO::VReg(s)])
}
fn uxth(d: VReg, s: VReg) -> MachInst {
    MachInst::new(Op::Uxth, vec![MO::VReg(d), MO::VReg(s)])
}
fn uxtw(d: VReg, s: VReg) -> MachInst {
    MachInst::new(Op::Uxtw, vec![MO::VReg(d), MO::VReg(s)])
}

/// A single-block function: `<def>; carrier(idx, k); ret`. Returns the func and
/// the carrier InstId. `def_insts` builds the index's definition chain.
fn narrow_fn(def_insts: Vec<MachInst>, idx: VReg, k: i64) -> (MachFunction, BlockId, InstId) {
    let mut f = MachFunction::new("narrow".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    for inst in def_insts {
        push(&mut f, entry, inst);
    }
    let cid = push(&mut f, entry, carrier(idx, k));
    push(&mut f, entry, ret());
    (f, entry, cid)
}

#[test]
fn narrow_eliminate_byte_range_uxtb() {
    // `idx = uxtb(_)` -> value in [0,255]; array len 256 -> in bounds.
    let (mut f, b, cid) = narrow_fn(vec![uxtb(g64(2), g32(1))], g64(2), 256);
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, b, cid));
}

#[test]
fn narrow_keep_byte_range_uxtb_array_255() {
    // len 255: a uxtb value CAN equal 255 == len -> out of bounds -> KEEP.
    let (mut f, b, cid) = narrow_fn(vec![uxtb(g64(2), g32(1))], g64(2), 255);
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert!(present(&f, b, cid));
}

#[test]
fn narrow_eliminate_half_range_uxth() {
    let (mut f, b, cid) = narrow_fn(vec![uxth(g64(2), g32(1))], g64(2), 65536);
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, b, cid));
}

#[test]
fn narrow_eliminate_mask_uxtw_of_andri() {
    // `t = _ & 63 ; idx = uxtw(t)` -> value in [0,63]; array len 64 -> in bounds.
    let (mut f, b, cid) = narrow_fn(
        vec![andri(g32(1), g32(0), 63), uxtw(g64(2), g32(1))],
        g64(2),
        64,
    );
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, b, cid));
}

#[test]
fn narrow_keep_mask_equal_len() {
    // mask 64 with len 64: `_ & 64` yields 0 or 64 == len -> KEEP (64 not < 64).
    let (mut f, b, cid) = narrow_fn(
        vec![andri(g32(1), g32(0), 64), uxtw(g64(2), g32(1))],
        g64(2),
        64,
    );
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert!(present(&f, b, cid));
}

#[test]
fn narrow_eliminate_mask_direct_gpr64_andri() {
    // `idx = _ & 15` directly on a Gpr64; array len 16 -> in bounds.
    let (mut f, b, cid) = narrow_fn(vec![andri(g64(2), g64(0), 15)], g64(2), 16);
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, b, cid));
}

#[test]
fn narrow_keep_negative_mask() {
    // A negative mask immediate (high-bit mask) is never a proven bound -> KEEP.
    let (mut f, b, cid) = narrow_fn(vec![andri(g64(2), g64(0), -1)], g64(2), 16);
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert!(present(&f, b, cid));
}

#[test]
fn narrow_keep_multi_def_index() {
    // The index root has TWO definitions -> not single-def -> unproven -> KEEP.
    let mut f = MachFunction::new("multidef".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let idx = g64(2);
    push(&mut f, entry, uxtb(idx, g32(1)));
    push(&mut f, entry, movi(idx, 5)); // second def of idx
    let cid = push(&mut f, entry, carrier(idx, 256));
    push(&mut f, entry, ret());
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert!(present(&f, entry, cid));
}

#[test]
fn narrow_eliminate_through_gpr64_copy() {
    // `t = uxtb(_) ; idx = mov t` (Gpr64 copy) -> follows to the uxtb root.
    let (mut f, b, cid) = narrow_fn(
        vec![uxtb(g64(2), g32(1)), movr(g64(3), g64(2))],
        g64(3),
        256,
    );
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 1);
    assert!(!present(&f, b, cid));
}
