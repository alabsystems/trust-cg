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

/// Build a guarded region whose carrier block `C` is an inner loop that does
/// not pass back through the guard `D`:
///
///   bb0 entry:  iv=MovI 0 ; bound=Movz 1024 ; B header
///   bb1 header: cIV=MovR iv ; CmpRR(cIV, bound) ; BCond LO body ; B exit     (D)
///   bb2 body:   B inner                                                       (T)
///   bb3 inner:  cIdx=MovR iv ; carrier[cIdx, 1024] ; iv=AddRI iv,1 ;
///               CmpRI(iv, 5000) ; BCond LO inner ; B header                  (C)
///   bb4 exit:   Ret
///
/// The increment after the carrier runs before the carrier's next execution
/// without re-passing the guard, so `iv` can reach 1024 there.
fn build_reentered_carrier_block() -> (MachFunction, BlockId, InstId) {
    let mut f = MachFunction::new("reenter".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let inner = f.create_block();
    let exit = f.create_block();
    let (iv, bound, civ, cidx) = (g64(1), g64(2), g64(3), g64(4));

    push(&mut f, entry, movi(iv, 0));
    push(&mut f, entry, movz(bound, 1024));
    push(&mut f, entry, br(header));

    push(&mut f, header, movr(civ, iv));
    push(&mut f, header, cmprr(civ, bound));
    push(&mut f, header, bcond(CondCode::LO, body));
    push(&mut f, header, br(exit));

    push(&mut f, body, br(inner));

    push(&mut f, inner, movr(cidx, iv));
    let cid = push(&mut f, inner, carrier(cidx, 1024));
    push(&mut f, inner, addri(iv, iv, 1));
    push(&mut f, inner, cmpri(iv, 5000));
    push(&mut f, inner, bcond(CondCode::LO, inner));
    push(&mut f, inner, br(header));

    push(&mut f, exit, ret());

    f.add_edge(entry, header);
    f.add_edge(header, body);
    f.add_edge(header, exit);
    f.add_edge(body, inner);
    f.add_edge(inner, inner);
    f.add_edge(inner, header);
    (f, inner, cid)
}

#[test]
fn keep_carrier_whose_block_reenters_without_the_guard() {
    let (mut f, inner, cid) = build_reentered_carrier_block();
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_eliminations, 0);
    assert!(
        present(&f, inner, cid),
        "the index is incremented after the carrier and the block loops without the guard"
    );
}

// ---------------------------------------------------------------------------
// Register-bound trap-branch arm
// ---------------------------------------------------------------------------

fn ldr(d: VReg, base: VReg, off: i64) -> MachInst {
    MachInst::new(Op::LdrRI, vec![MO::VReg(d), MO::VReg(base), MO::Imm(off)])
}
fn brk() -> MachInst {
    MachInst::new(Op::Brk, vec![])
}

/// How the check's length is obtained.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CheckLen {
    /// The guard's own length register.
    Same,
    /// A second `LdrRI [base, #16]` right after the guard's in the entry block.
    EqualLoad,
    /// As `EqualLoad`, with a store between the two loads.
    LoadAfterStore,
    /// A load of a different field (`[base, #8]`).
    OtherField,
    /// A reload inside the check block, after the guard.
    ReloadInCheck,
}

/// The check's failing successor.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FailBlock {
    /// `Brk`: a backend checked-trap guard.
    Trap,
    /// A source bounds check's RAISE: the payload / Location argument setup,
    /// `Bl panic_bounds_check`, then the `Brk` of its `Unreachable`.
    Raise,
    /// `Ret`: the failing edge returns — an ordinary branch, not a check.
    Ret,
    /// A call that returns into `Ret`: no `Brk`, so not a diverging sink.
    CallThenRet,
    /// The raise, plus a CFG successor (an unwind landing pad that returns):
    /// a block with successors is not a sink.
    RaiseWithSuccessor,
}

/// Knobs for the `while k < v.len() { .. v[k] .. }` shape.
#[derive(Clone, Copy)]
struct TrapCfg {
    len: CheckLen,
    /// Guard condition (taken edge enters the body).
    guard_cc: CondCode,
    /// Check form: `true` is `BCond HS trap ; B cont`, `false` `BCond LO cont ; B trap`.
    hs_form: bool,
    /// What the failing successor does.
    fail: FailBlock,
    /// Redefine `k` at the top of the check block.
    redefine_index: bool,
}

impl TrapCfg {
    fn canonical() -> Self {
        Self {
            len: CheckLen::Same,
            guard_cc: CondCode::LO,
            hs_form: true,
            fail: FailBlock::Trap,
            redefine_index: false,
        }
    }
}

/// Build:
///
/// ```text
///   bb0 entry:  base=MovI ; len=Ldr[base,#16] ; [len2 per cfg] ; k=MovI 0 ; B header
///   bb1 header: ck=MovR k ; CmpRR(ck, len) ; BCond[guard_cc] body ; B exit     (D)
///   bb2 body:   [k+=1] ; ci=MovR k ; [len2 reload] ; CmpRR(ci, len2) ;
///               BCond HS trap ; B cont     (or BCond LO cont ; B trap)         (C = T)
///   bb3 trap:   Brk                        (or Ret)
///   bb4 cont:   k=AddRI k,1 ; B header
///   bb5 exit:   Ret
/// ```
///
/// vreg ids: base=1, len=2, len2=3 (or 2), k=4, ck=5, ci=6, stored value=7.
/// Returns `(func, body, trap, cont)`.
fn build_len_guarded_loop(cfg: TrapCfg) -> (MachFunction, BlockId, BlockId, BlockId) {
    let mut f = MachFunction::new("vecsum".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let trap = f.create_block();
    let cont = f.create_block();
    let exit = f.create_block();
    let (base, len, k, ck, ci) = (g64(1), g64(2), g64(4), g64(5), g64(6));

    push(&mut f, entry, movi(base, 4096));
    push(&mut f, entry, ldr(len, base, 16));
    let len2 = match cfg.len {
        CheckLen::Same => len,
        CheckLen::EqualLoad => {
            push(&mut f, entry, ldr(g64(3), base, 16));
            g64(3)
        }
        CheckLen::LoadAfterStore => {
            push(&mut f, entry, movi(g64(7), 0));
            push(
                &mut f,
                entry,
                MachInst::new(
                    Op::StrRI,
                    vec![MO::VReg(g64(7)), MO::VReg(base), MO::Imm(16)],
                ),
            );
            push(&mut f, entry, ldr(g64(3), base, 16));
            g64(3)
        }
        CheckLen::OtherField => {
            push(&mut f, entry, ldr(g64(3), base, 8));
            g64(3)
        }
        CheckLen::ReloadInCheck => g64(3),
    };
    push(&mut f, entry, movi(k, 0));
    push(&mut f, entry, br(header));

    push(&mut f, header, movr(ck, k));
    push(&mut f, header, cmprr(ck, len));
    push(&mut f, header, bcond(cfg.guard_cc, body));
    push(&mut f, header, br(exit));

    if cfg.redefine_index {
        push(&mut f, body, addri(k, k, 1));
    }
    push(&mut f, body, movr(ci, k));
    if cfg.len == CheckLen::ReloadInCheck {
        push(&mut f, body, ldr(len2, base, 16));
    }
    push(&mut f, body, cmprr(ci, len2));
    if cfg.hs_form {
        push(&mut f, body, bcond(CondCode::HS, trap));
        push(&mut f, body, br(cont));
    } else {
        push(&mut f, body, bcond(CondCode::LO, cont));
        push(&mut f, body, br(trap));
    }

    let mut fail_succ = None;
    match cfg.fail {
        FailBlock::Trap => {
            push(&mut f, trap, brk());
        }
        FailBlock::Ret => {
            push(&mut f, trap, ret());
        }
        FailBlock::Raise | FailBlock::RaiseWithSuccessor => {
            push_raise(&mut f, trap, ci, len2);
            if cfg.fail == FailBlock::RaiseWithSuccessor {
                let pad = f.create_block();
                push(&mut f, pad, ret());
                fail_succ = Some(pad);
            }
        }
        FailBlock::CallThenRet => {
            push(&mut f, trap, bl("_observe"));
            push(&mut f, trap, ret());
        }
    }

    push(&mut f, cont, addri(k, k, 1));
    push(&mut f, cont, br(header));

    push(&mut f, exit, ret());

    f.add_edge(entry, header);
    f.add_edge(header, body);
    f.add_edge(header, exit);
    if cfg.hs_form {
        f.add_edge(body, trap);
        f.add_edge(body, cont);
    } else {
        f.add_edge(body, cont);
        f.add_edge(body, trap);
    }
    f.add_edge(cont, header);
    if let Some(pad) = fail_succ {
        f.add_edge(trap, pad);
    }
    (f, body, trap, cont)
}

fn bl(symbol: &str) -> MachInst {
    MachInst::new(Op::Bl, vec![MO::Symbol(symbol.into())])
}

/// A source bounds check's raise block, as the bridge's
/// `emit_assert_panic_raise` lowers it: index and length into the argument
/// registers, the Location address, `Bl panic_bounds_check`, `Brk`.
fn push_raise(f: &mut MachFunction, b: BlockId, idx: VReg, len: VReg) {
    push(f, b, movr(g64(20), idx));
    push(f, b, movr(g64(21), len));
    push(
        f,
        b,
        MachInst::new(Op::Adrp, vec![MO::VReg(g64(22)), MO::Symbol("loc".into())]),
    );
    push(f, b, bl("__RNvNtCs0_4core9panicking18panic_bounds_check"));
    push(f, b, brk());
}

/// The body's check was folded: it ends `CmpRR ; B cont` with `cont` its only
/// successor, and the trap block lost the edge.
fn assert_folded(f: &MachFunction, body: BlockId, trap: BlockId, cont: BlockId) {
    let insts = &f.block(body).insts;
    let last = f.inst(*insts.last().expect("body terminator"));
    assert_eq!(last.opcode, Op::B);
    assert_eq!(last.operands, vec![MO::Block(cont)]);
    assert!(
        insts.iter().all(|&id| f.inst(id).opcode != Op::BCond),
        "the check's conditional branch must be gone"
    );
    assert_eq!(f.block(body).succs, vec![cont]);
    assert!(!f.block(trap).preds.contains(&body));
}

fn assert_kept(f: &MachFunction, body: BlockId) {
    assert!(
        f.block(body)
            .insts
            .iter()
            .any(|&id| f.inst(id).opcode == Op::BCond),
        "the check must stay"
    );
    assert_eq!(f.block(body).succs.len(), 2);
}

fn run_fold(f: &mut MachFunction) -> (bool, usize) {
    let mut pass = AArch64BoundsCheckElimination::new();
    let changed = pass.run_on_function(f);
    (changed, pass.last_run_trap_branch_folds)
}

#[test]
fn trap_branch_folds_check_against_the_guards_length() {
    let (mut f, body, trap, cont) = build_len_guarded_loop(TrapCfg::canonical());
    assert_eq!(run_fold(&mut f), (true, 1));
    assert_folded(&f, body, trap, cont);
}

#[test]
fn trap_branch_folds_lo_form() {
    let (mut f, body, trap, cont) = build_len_guarded_loop(TrapCfg {
        hs_form: false,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (true, 1));
    assert_folded(&f, body, trap, cont);
}

#[test]
fn trap_branch_folds_equal_length_loads() {
    // Two loads of `[base, #16]` in one block with nothing between them.
    let (mut f, body, trap, cont) = build_len_guarded_loop(TrapCfg {
        len: CheckLen::EqualLoad,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (true, 1));
    assert_folded(&f, body, trap, cont);
}

#[test]
fn trap_branch_keeps_check_when_a_store_separates_the_loads() {
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        len: CheckLen::LoadAfterStore,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_check_against_another_field() {
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        len: CheckLen::OtherField,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_check_against_a_reload_after_the_guard() {
    // The check reloads the length after the guard: a different value source.
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        len: CheckLen::ReloadInCheck,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_check_after_a_non_strict_guard() {
    // `k <=u len` does not imply `k <u len`.
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        guard_cc: CondCode::LS,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_check_after_a_signed_guard() {
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        guard_cc: CondCode::LT,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_a_branch_to_a_non_trap_block() {
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        fail: FailBlock::Ret,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

// --- The widened failing successor: a source panic's RAISE block. ---------
//
// The guard proves the failing edge is never taken, so the fold is sound
// whatever that edge runs; what it may drop is restricted to a DIVERGING sink
// (no successors, last instruction `Brk`). Each rule below has a refutation.

#[test]
fn trap_branch_folds_check_whose_failing_block_raises() {
    for hs_form in [true, false] {
        let (mut f, body, trap, cont) = build_len_guarded_loop(TrapCfg {
            fail: FailBlock::Raise,
            hs_form,
            ..TrapCfg::canonical()
        });
        assert_eq!(run_fold(&mut f), (true, 1), "hs_form={hs_form}");
        assert_folded(&f, body, trap, cont);
    }
}

#[test]
fn trap_branch_keeps_raising_check_the_guard_does_not_prove() {
    // The widening is ONLY about the failing block: every proof obligation
    // still applies to a raising check exactly as to a trapping one.
    let refuted: [(&str, TrapCfg); 5] = [
        (
            "non-strict guard",
            TrapCfg {
                guard_cc: CondCode::LS,
                ..TrapCfg::canonical()
            },
        ),
        (
            "signed guard",
            TrapCfg {
                guard_cc: CondCode::LT,
                ..TrapCfg::canonical()
            },
        ),
        (
            "index redefined",
            TrapCfg {
                redefine_index: true,
                ..TrapCfg::canonical()
            },
        ),
        (
            "another field",
            TrapCfg {
                len: CheckLen::OtherField,
                ..TrapCfg::canonical()
            },
        ),
        (
            "store between loads",
            TrapCfg {
                len: CheckLen::LoadAfterStore,
                ..TrapCfg::canonical()
            },
        ),
    ];
    for (what, cfg) in refuted {
        let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
            fail: FailBlock::Raise,
            ..cfg
        });
        assert_eq!(run_fold(&mut f), (false, 0), "{what}");
        assert_kept(&f, body);
    }
}

#[test]
fn trap_branch_keeps_a_branch_to_a_block_whose_call_returns() {
    // A call followed by `Ret` is not a diverging sink: the failing edge would
    // CONTINUE (return), so this is an ordinary branch, not a check.
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        fail: FailBlock::CallThenRet,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_a_raise_with_an_unwind_successor() {
    // A raise that names a landing pad has a CFG successor; dropping the edge
    // into it would leave a dead predecessor on the pad. Not a sink: kept.
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        fail: FailBlock::RaiseWithSuccessor,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn diverging_sink_requires_no_successors_and_a_final_brk() {
    let mut f = MachFunction::new("sinks".into(), Signature::new(vec![], vec![]));
    let (raise, trap, ret_blk, brk_then_succ, empty) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    push_raise(&mut f, raise, g64(1), g64(2));
    push(&mut f, trap, brk());
    push(&mut f, ret_blk, bl("_observe"));
    push(&mut f, ret_blk, ret());
    push(&mut f, brk_then_succ, brk());
    f.add_edge(brk_then_succ, ret_blk);
    assert!(is_diverging_sink(&f, raise));
    assert!(is_diverging_sink(&f, trap));
    assert!(!is_diverging_sink(&f, ret_blk));
    assert!(!is_diverging_sink(&f, brk_then_succ));
    assert!(!is_diverging_sink(&f, empty));
}

#[test]
fn trap_branch_keeps_check_when_the_index_is_redefined() {
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg {
        redefine_index: true,
        ..TrapCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_proof_annotated_check() {
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg::canonical());
    let cmp = f
        .block(body)
        .insts
        .iter()
        .copied()
        .find(|&id| f.inst(id).opcode == Op::CmpRR)
        .expect("check compare");
    f.inst_mut(cmp).proof = Some(ProofAnnotation::InBounds);
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_checks_in_a_function_with_volatile_access() {
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg::canonical());
    let entry = f.entry;
    let volatile = f.push_inst(MachInst::new(
        Op::VolatileLdrRI,
        vec![MO::VReg(g64(9)), MO::VReg(g64(1)), MO::Imm(0)],
    ));
    f.block_mut(entry).insts.insert(0, volatile);
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_arm_off_keeps_every_check() {
    let (mut f, body, _, _) = build_len_guarded_loop(TrapCfg::canonical());
    let mut pass = AArch64BoundsCheckElimination::new().without_trap_branch_folds();
    assert!(!pass.run_on_function(&mut f));
    assert_eq!(pass.last_run_trap_branch_folds, 0);
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_check_on_a_cycle_that_bypasses_the_guard() {
    // The check's continuation loops back to the check (incrementing `k`)
    // without passing the header's guard, so a later check can see `k == len`:
    //   body: ci=MovR k ; CmpRR(ci,len) ; BCond HS trap ; B inner
    //   inner: k=AddRI k,1 ; CmpRI(k,7) ; BCond LO body ; B cont
    let (mut f, body, trap, cont) = build_len_guarded_loop(TrapCfg::canonical());
    let k = g64(4);
    let inner = f.create_block();
    let last = *f.block(body).insts.last().expect("B");
    f.inst_mut(last).operands = vec![MO::Block(inner)];
    f.block_mut(body).succs.retain(|&s| s != cont);
    f.block_mut(cont).preds.retain(|&p| p != body);
    push(&mut f, inner, addri(k, k, 1));
    push(&mut f, inner, cmpri(k, 7));
    push(&mut f, inner, bcond(CondCode::LO, body));
    push(&mut f, inner, br(cont));
    f.add_edge(body, inner);
    f.add_edge(inner, body);
    f.add_edge(inner, cont);
    assert!(f.block(body).succs.contains(&trap));
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn trap_branch_keeps_check_after_an_if_else_join() {
    // `if k < len { .. } ; v[k]`: the guard's `<` edge enters `t`, but the
    // check block `j` is also reached through `e`, where `k >=u len`. `t`
    // does not dominate the check, so the check must stay.
    //
    //   bb0 (D): base ; len=Ldr[base,#16] ; k=MovI 5 ; ck=MovR k ;
    //            CmpRR(ck, len) ; BCond LO t ; B e
    //   t: B j            e: B j
    //   j (C): ci=MovR k ; CmpRR(ci, len) ; BCond HS trap ; B cont
    //   trap: Brk         cont: Ret
    let mut f = MachFunction::new("join".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let (t, e, j) = (f.create_block(), f.create_block(), f.create_block());
    let (trap, cont) = (f.create_block(), f.create_block());
    let (base, len, k, ck, ci) = (g64(1), g64(2), g64(4), g64(5), g64(6));

    push(&mut f, entry, movi(base, 4096));
    push(&mut f, entry, ldr(len, base, 16));
    push(&mut f, entry, movi(k, 5));
    push(&mut f, entry, movr(ck, k));
    push(&mut f, entry, cmprr(ck, len));
    push(&mut f, entry, bcond(CondCode::LO, t));
    push(&mut f, entry, br(e));
    push(&mut f, t, br(j));
    push(&mut f, e, br(j));
    push(&mut f, j, movr(ci, k));
    push(&mut f, j, cmprr(ci, len));
    push(&mut f, j, bcond(CondCode::HS, trap));
    push(&mut f, j, br(cont));
    push(&mut f, trap, brk());
    push(&mut f, cont, ret());
    for (from, to) in [(entry, t), (entry, e), (t, j), (e, j), (j, trap), (j, cont)] {
        f.add_edge(from, to);
    }
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, j);
}

#[test]
fn trap_branch_keeps_check_of_an_index_snapshot_taken_outside_the_guarded_window() {
    // The check tests `ci`, a copy of `k` taken in `skip` BEFORE `k` is
    // decremented and the guard re-tested. `ci` chains to the guard's root
    // `k`, but it holds `k + 1` of the guarded value: at `k == len - 1` the
    // guard passes and `ci == len`, so the check must trap. A check-side copy
    // link outside the window (not in `C` before the compare, not in `D`, not
    // in a block `T` dominates) keeps the check.
    //
    //   bb0: base ; len=Ldr[base,#16] ; k=MovI 10 ; B header
    //   header (D): ck=MovR k ; CmpRR(ck, len) ; BCond LO body ; B skip
    //   skip: ci=MovR k ; k=SubRI k,1 ; B header
    //   body (T = C): CmpRR(ci, len) ; BCond HS trap ; B cont
    //   trap: Brk          cont: Ret
    let mut f = MachFunction::new("snapshot".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let (header, skip, body) = (f.create_block(), f.create_block(), f.create_block());
    let (trap, cont) = (f.create_block(), f.create_block());
    let (base, len, k, ck, ci) = (g64(1), g64(2), g64(4), g64(5), g64(6));

    push(&mut f, entry, movi(base, 4096));
    push(&mut f, entry, ldr(len, base, 16));
    push(&mut f, entry, movi(k, 10));
    push(&mut f, entry, br(header));
    push(&mut f, header, movr(ck, k));
    push(&mut f, header, cmprr(ck, len));
    push(&mut f, header, bcond(CondCode::LO, body));
    push(&mut f, header, br(skip));
    push(&mut f, skip, movr(ci, k));
    push(
        &mut f,
        skip,
        MachInst::new(Op::SubRI, vec![MO::VReg(k), MO::VReg(k), MO::Imm(1)]),
    );
    push(&mut f, skip, br(header));
    push(&mut f, body, cmprr(ci, len));
    push(&mut f, body, bcond(CondCode::HS, trap));
    push(&mut f, body, br(cont));
    push(&mut f, trap, brk());
    push(&mut f, cont, ret());
    for (from, to) in [
        (entry, header),
        (header, body),
        (header, skip),
        (skip, header),
        (body, trap),
        (body, cont),
    ] {
        f.add_edge(from, to);
    }
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

// --- NARROW-INDEX arm on an explicit check against a CONSTANT bound. -------
//
// `h[b as usize]` over a `[u32; 256]` is an explicit `Cmp(idx, #256) ; BCond HS
// fail ; B cont` once the failing edge raises `panic_bounds_check` instead of
// being a `TrapBoundsCheckExact` carrier. The index's own single definition
// (a byte zero-extension, a constant mask) proves it, exactly as for the
// carrier arm; refuted below for every non-proving shape.

/// `entry: <def> ; Cmp(idx, bound) ; BCond HS fail ; B cont`,
/// `fail: <raise or trap>`, `cont: Ret`. `bound` is an immediate (`CmpRI`) or,
/// for `Err(k)`, a `Movz k` register (`CmpRR`). Returns `(func, entry, fail,
/// cont)`.
fn narrow_check_fn(
    def_insts: Vec<MachInst>,
    idx: VReg,
    bound: Result<i64, i64>,
    raise: bool,
) -> (MachFunction, BlockId, BlockId, BlockId) {
    let mut f = MachFunction::new("narrow_check".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let (fail, cont) = (f.create_block(), f.create_block());
    for inst in def_insts {
        push(&mut f, entry, inst);
    }
    let len = g64(30);
    match bound {
        Ok(k) => {
            push(&mut f, entry, cmpri(idx, k));
        }
        Err(k) => {
            push(&mut f, entry, movz(len, k));
            push(&mut f, entry, cmprr(idx, len));
        }
    }
    push(&mut f, entry, bcond(CondCode::HS, fail));
    push(&mut f, entry, br(cont));
    if raise {
        push_raise(&mut f, fail, idx, len);
    } else {
        push(&mut f, fail, brk());
    }
    push(&mut f, cont, ret());
    f.add_edge(entry, fail);
    f.add_edge(entry, cont);
    (f, entry, fail, cont)
}

#[test]
fn narrow_check_folds_a_byte_index_against_256() {
    for raise in [true, false] {
        for bound in [Ok(256), Err(256)] {
            let (mut f, b, fail, cont) =
                narrow_check_fn(vec![uxtb(g64(2), g32(1))], g64(2), bound, raise);
            assert_eq!(run_fold(&mut f), (true, 1), "raise={raise} bound={bound:?}");
            assert_folded(&f, b, fail, cont);
        }
    }
}

#[test]
fn narrow_check_folds_a_masked_index() {
    let (mut f, b, fail, cont) = narrow_check_fn(
        vec![andri(g32(1), g32(0), 63), uxtw(g64(2), g32(1))],
        g64(2),
        Ok(64),
        true,
    );
    assert_eq!(run_fold(&mut f), (true, 1));
    assert_folded(&f, b, fail, cont);
}

#[test]
fn narrow_check_keeps_every_unproven_shape() {
    let refuted: Vec<(&str, Vec<MachInst>, Result<i64, i64>)> = vec![
        // A byte CAN equal 255 == len.
        ("byte vs 255", vec![uxtb(g64(2), g32(1))], Ok(255)),
        ("byte vs Movz 255", vec![uxtb(g64(2), g32(1))], Err(255)),
        // `_ & 64` yields 64 == len.
        (
            "mask 64 vs 64",
            vec![andri(g32(1), g32(0), 64), uxtw(g64(2), g32(1))],
            Ok(64),
        ),
        // A plain value carries no bound.
        ("unbounded index", vec![movr(g64(2), g64(9))], Ok(256)),
        // Two definitions: not single-def.
        (
            "multi-def index",
            vec![uxtb(g64(2), g32(1)), movi(g64(2), 300)],
            Ok(256),
        ),
        // A half-word zero-extension against a byte table.
        ("half vs 256", vec![uxth(g64(2), g32(1))], Ok(256)),
    ];
    for (what, def, bound) in refuted {
        let (mut f, b, _, _) = narrow_check_fn(def, g64(2), bound, true);
        assert_eq!(run_fold(&mut f), (false, 0), "{what}");
        assert_kept(&f, b);
    }
}

#[test]
fn narrow_check_keeps_a_register_bound_that_is_not_a_plain_movz() {
    // `len = Movz 1 ; Movk len, #0, lsl 16` is a Movk-completed constant: the
    // bound is unresolved, so the narrow arm cannot use it.
    let (mut f, b, _, _) = narrow_check_fn(vec![uxtb(g64(2), g32(1))], g64(2), Err(256), true);
    let movz_id = f
        .block(b)
        .insts
        .iter()
        .copied()
        .find(|&id| f.inst(id).opcode == Op::Movz)
        .expect("movz");
    let pos = f
        .block(b)
        .insts
        .iter()
        .position(|&id| id == movz_id)
        .expect("pos");
    let movk_id = f.push_inst(movk(g64(30), 0, 16));
    f.block_mut(b).insts.insert(pos + 1, movk_id);
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, b);
}

// --- Operand-shape and CFG-shape hardening. ---------------------------------

/// The encoder's pre-decomposed `AndRI [dst, src, N, immr, imms]`: operand 2 is
/// the `N` bit, not a mask. `N = 1, immr = 0, imms = 7` encodes `& 0xff`, so the
/// value is NOT below 255 — and reading `N` as the mask would claim `< 2`.
fn andri_decomposed(d: VReg, s: VReg) -> MachInst {
    MachInst::new(
        Op::AndRI,
        vec![MO::VReg(d), MO::VReg(s), MO::Imm(1), MO::Imm(0), MO::Imm(7)],
    )
}

#[test]
fn narrow_keeps_a_decomposed_five_operand_andri() {
    // Carrier arm.
    let (mut f, b, cid) = narrow_fn(vec![andri_decomposed(g64(2), g64(0))], g64(2), 255);
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert!(present(&f, b, cid));
    // Same root behind a Gpr32 copy chain and a zero-extension.
    let (mut f, b, cid) = narrow_fn(
        vec![andri_decomposed(g32(1), g32(0)), uxtw(g64(2), g32(1))],
        g64(2),
        255,
    );
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert!(present(&f, b, cid));
    // Explicit-check arm, raising and trapping, immediate and register bound.
    for raise in [true, false] {
        for bound in [Ok(255), Err(255)] {
            let (mut f, b, _, _) =
                narrow_check_fn(vec![andri_decomposed(g64(2), g64(0))], g64(2), bound, raise);
            assert_eq!(
                run_fold(&mut f),
                (false, 0),
                "raise={raise} bound={bound:?}"
            );
            assert_kept(&f, b);
        }
    }
}

#[test]
fn keep_guard_block_with_a_third_successor() {
    // A guard block whose CFG has a third edge: which successor the BCond falls
    // through to is no longer determined by "the one that is not taken".
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::HS,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: false,
        use_imm_cmp: false,
    });
    let header = BlockId(1);
    let extra = f.create_block();
    push(&mut f, extra, ret());
    f.add_edge(header, extra);
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert!(present(&f, body, cid));
}

#[test]
fn keep_guard_whose_trailing_branch_disagrees_with_the_cfg() {
    // HS guard: the bounded edge is the fall-through. The trailing `B` names a
    // block that is not the guard's other CFG successor, so the fall-through
    // edge is ill-formed and proves nothing.
    let (mut f, body, cid) = build_own_length_loop(&LoopCfg {
        cc: CondCode::HS,
        bound_val: 1024,
        carrier_k: 1024,
        taken_is_body: false,
        use_imm_cmp: false,
    });
    let header = BlockId(1);
    let latch = BlockId(3);
    let last = *f.block(header).insts.last().expect("header terminator");
    f.inst_mut(last).operands = vec![MO::Block(latch)];
    let mut pass = AArch64BoundsCheckElimination::new();
    assert!(!pass.run_on_function(&mut f));
    assert!(present(&f, body, cid));
}

// --- CONSTANT-BOUND GUARD arm on an explicit check. --------------------------
//
// `while i < N { .. a[i] .. }` over an array of `N` elements: before the
// failing edge raised `panic_bounds_check` the check was a `TrapBoundsCheckExact`
// carrier the carrier arm deleted under the loop guard; it is now an explicit
// `Cmp(idx, #K) ; BCond HS raise ; B cont` the register-bound arm cannot read
// (no length register). The carrier arm's guard rule decides it: every proof
// condition is the carrier arm's, refuted below for each one.

/// Knobs for the constant-bound counted loop with an explicit check.
#[derive(Clone, Copy)]
struct ConstCheckCfg {
    /// Guard condition and which edge enters the body (as `LoopCfg`).
    guard_cc: CondCode,
    taken_is_body: bool,
    /// Guard bound `K'`: `CmpRI` immediate, or `Movz` + `CmpRR`.
    guard_k: i64,
    guard_imm: bool,
    /// Check bound `K`: `CmpRI` immediate, or `Movz` + `CmpRR`.
    check_k: i64,
    check_imm: bool,
    /// Check form: `BCond HS fail ; B latch` or `BCond LO latch ; B fail`.
    hs_form: bool,
    /// The failing block raises (`push_raise`) or is a bare `Brk`.
    raise: bool,
}

impl ConstCheckCfg {
    fn canonical() -> Self {
        Self {
            guard_cc: CondCode::LO,
            taken_is_body: true,
            guard_k: 1024,
            guard_imm: true,
            check_k: 1024,
            check_imm: true,
            hs_form: true,
            raise: true,
        }
    }
}

/// Build:
///
/// ```text
///   bb0 entry:  iv=MovI 0 ; [gb=Movz K'] ; [cb=Movz K] ; B header
///   bb1 header: civ=MovR iv ; Cmp(civ, K') ; BCond[cc] <taken> ; B <other>  (D)
///   bb2 body:   cidx=MovR iv ; Cmp(cidx, K) ; BCond HS fail ; B latch        (C)
///               (or BCond LO latch ; B fail)
///   bb3 fail:   <raise(cidx, cb)> or Brk
///   bb4 latch:  iv=AddRI iv,1 ; B header
///   bb5 exit:   Ret
/// ```
///
/// vreg ids: iv=1, gb=2, civ=3, cidx=4, cb=5. Returns `(func, body, fail, latch)`.
fn build_const_checked_loop(cfg: ConstCheckCfg) -> (MachFunction, BlockId, BlockId, BlockId) {
    let mut f = MachFunction::new("constcheck".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let fail = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    let (iv, gb, civ, cidx, cb) = (g64(1), g64(2), g64(3), g64(4), g64(5));

    push(&mut f, entry, movi(iv, 0));
    if !cfg.guard_imm {
        push(&mut f, entry, movz(gb, cfg.guard_k));
    }
    if !cfg.check_imm {
        push(&mut f, entry, movz(cb, cfg.check_k));
    }
    push(&mut f, entry, br(header));

    push(&mut f, header, movr(civ, iv));
    if cfg.guard_imm {
        push(&mut f, header, cmpri(civ, cfg.guard_k));
    } else {
        push(&mut f, header, cmprr(civ, gb));
    }
    let (taken, other) = if cfg.taken_is_body {
        (body, exit)
    } else {
        (exit, body)
    };
    push(&mut f, header, bcond(cfg.guard_cc, taken));
    push(&mut f, header, br(other));

    push(&mut f, body, movr(cidx, iv));
    if cfg.check_imm {
        push(&mut f, body, cmpri(cidx, cfg.check_k));
    } else {
        push(&mut f, body, cmprr(cidx, cb));
    }
    if cfg.hs_form {
        push(&mut f, body, bcond(CondCode::HS, fail));
        push(&mut f, body, br(latch));
    } else {
        push(&mut f, body, bcond(CondCode::LO, latch));
        push(&mut f, body, br(fail));
    }

    if cfg.raise {
        push_raise(&mut f, fail, cidx, cb);
    } else {
        push(&mut f, fail, brk());
    }

    push(&mut f, latch, addri(iv, iv, 1));
    push(&mut f, latch, br(header));
    push(&mut f, exit, ret());

    f.add_edge(entry, header);
    f.add_edge(header, taken);
    f.add_edge(header, other);
    if cfg.hs_form {
        f.add_edge(body, fail);
        f.add_edge(body, latch);
    } else {
        f.add_edge(body, latch);
        f.add_edge(body, fail);
    }
    f.add_edge(latch, header);
    (f, body, fail, latch)
}

#[test]
fn const_check_folds_under_a_guard_with_the_same_constant() {
    for raise in [true, false] {
        for hs_form in [true, false] {
            for (guard_imm, check_imm) in
                [(true, true), (false, false), (true, false), (false, true)]
            {
                let (mut f, body, fail, latch) = build_const_checked_loop(ConstCheckCfg {
                    raise,
                    hs_form,
                    guard_imm,
                    check_imm,
                    ..ConstCheckCfg::canonical()
                });
                assert_eq!(
                    run_fold(&mut f),
                    (true, 1),
                    "raise={raise} hs_form={hs_form} guard_imm={guard_imm} check_imm={check_imm}"
                );
                assert_folded(&f, body, fail, latch);
            }
        }
    }
}

#[test]
fn const_check_folds_under_every_proving_guard_form() {
    let proving: [(&str, CondCode, bool, i64, i64); 5] = [
        // `<u K'` with K' <= K.
        ("LO taken, K' < K", CondCode::LO, true, 1000, 1024),
        // `>=u K'` taken leaves: the fall-through edge carries `<u K'`.
        ("HS fall-through", CondCode::HS, false, 1024, 1024),
        // `<=u K'` with K' < K.
        ("LS taken, K' = K-1", CondCode::LS, true, 1023, 1024),
        // `>u K'` taken leaves: the fall-through carries `<=u K'`.
        ("HI fall-through, K' = K-1", CondCode::HI, false, 1023, 1024),
        ("LO, K' = 1", CondCode::LO, true, 1, 1),
    ];
    for (what, guard_cc, taken_is_body, guard_k, check_k) in proving {
        let (mut f, body, fail, latch) = build_const_checked_loop(ConstCheckCfg {
            guard_cc,
            taken_is_body,
            guard_k,
            check_k,
            ..ConstCheckCfg::canonical()
        });
        assert_eq!(run_fold(&mut f), (true, 1), "{what}");
        assert_folded(&f, body, fail, latch);
    }
}

#[test]
fn const_check_keeps_every_check_the_guard_does_not_prove() {
    let refuted: [(&str, ConstCheckCfg); 8] = [
        (
            // The loop runs to 1025 over 1024 elements: the last trip fails.
            "K' = K+1",
            ConstCheckCfg {
                guard_k: 1025,
                ..ConstCheckCfg::canonical()
            },
        ),
        (
            "K' > K, Movz bounds",
            ConstCheckCfg {
                guard_k: 2000,
                guard_imm: false,
                check_imm: false,
                ..ConstCheckCfg::canonical()
            },
        ),
        (
            // `<=u K` admits `idx == K`.
            "non-strict LS with K' = K",
            ConstCheckCfg {
                guard_cc: CondCode::LS,
                ..ConstCheckCfg::canonical()
            },
        ),
        (
            "non-strict HI fall-through with K' = K",
            ConstCheckCfg {
                guard_cc: CondCode::HI,
                taken_is_body: false,
                ..ConstCheckCfg::canonical()
            },
        ),
        (
            "signed LT guard",
            ConstCheckCfg {
                guard_cc: CondCode::LT,
                ..ConstCheckCfg::canonical()
            },
        ),
        (
            "NE guard",
            ConstCheckCfg {
                guard_cc: CondCode::NE,
                ..ConstCheckCfg::canonical()
            },
        ),
        (
            // The guarded edge is the one that LEAVES: the body is on `>=u`.
            "HS taken into the body",
            ConstCheckCfg {
                guard_cc: CondCode::HS,
                taken_is_body: true,
                ..ConstCheckCfg::canonical()
            },
        ),
        (
            "zero-length array",
            ConstCheckCfg {
                check_k: 0,
                ..ConstCheckCfg::canonical()
            },
        ),
    ];
    for (what, cfg) in refuted {
        for raise in [true, false] {
            let (mut f, body, _, _) = build_const_checked_loop(ConstCheckCfg { raise, ..cfg });
            assert_eq!(run_fold(&mut f), (false, 0), "{what} raise={raise}");
            assert_kept(&f, body);
        }
    }
}

#[test]
fn const_check_keeps_a_check_on_another_register() {
    // The guard bounds `iv`, the check tests `j`, an unrelated register.
    let (mut f, body, _, _) = build_const_checked_loop(ConstCheckCfg::canonical());
    let j = g64(9);
    let entry = f.entry;
    let def_j = f.push_inst(movi(j, 0));
    f.block_mut(entry).insts.insert(0, def_j);
    let cmp = f
        .block(body)
        .insts
        .iter()
        .copied()
        .find(|&id| f.inst(id).opcode == Op::CmpRI)
        .expect("check compare");
    f.inst_mut(cmp).operands[0] = MO::VReg(j);
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn const_check_keeps_a_check_after_the_index_is_redefined() {
    // `iv += 1` at the top of the body: the check sees the NEXT index, which
    // is `K` on the last trip.
    let (mut f, body, _, _) = build_const_checked_loop(ConstCheckCfg::canonical());
    let iv = g64(1);
    let redef = f.push_inst(addri(iv, iv, 1));
    f.block_mut(body).insts.insert(0, redef);
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn const_check_keeps_a_check_of_an_index_snapshot_taken_outside_the_guarded_window() {
    // As `trap_branch_keeps_check_of_an_index_snapshot_taken_outside_the_
    // guarded_window`, against a constant: `ci` copies `k` in `skip` before
    // `k` is decremented and re-tested, so at `k == K - 1` the guard passes
    // and `ci == K`.
    //
    //   bb0: k=MovI 10 ; B header
    //   header (D): ck=MovR k ; CmpRI(ck, #10) ; BCond LO body ; B skip
    //   skip: ci=MovR k ; k=SubRI k,1 ; B header
    //   body (T = C): CmpRI(ci, #10) ; BCond HS fail ; B cont
    //   fail: raise        cont: Ret
    let mut f = MachFunction::new("constsnapshot".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let (header, skip, body) = (f.create_block(), f.create_block(), f.create_block());
    let (fail, cont) = (f.create_block(), f.create_block());
    let (k, ck, ci) = (g64(4), g64(5), g64(6));
    push(&mut f, entry, movi(k, 10));
    push(&mut f, entry, br(header));
    push(&mut f, header, movr(ck, k));
    push(&mut f, header, cmpri(ck, 10));
    push(&mut f, header, bcond(CondCode::LO, body));
    push(&mut f, header, br(skip));
    push(&mut f, skip, movr(ci, k));
    push(
        &mut f,
        skip,
        MachInst::new(Op::SubRI, vec![MO::VReg(k), MO::VReg(k), MO::Imm(1)]),
    );
    push(&mut f, skip, br(header));
    push(&mut f, body, cmpri(ci, 10));
    push(&mut f, body, bcond(CondCode::HS, fail));
    push(&mut f, body, br(cont));
    push_raise(&mut f, fail, ci, g64(7));
    push(&mut f, cont, ret());
    for (from, to) in [
        (entry, header),
        (header, body),
        (header, skip),
        (skip, header),
        (body, fail),
        (body, cont),
    ] {
        f.add_edge(from, to);
    }
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn const_check_keeps_a_check_the_guarded_edge_does_not_dominate() {
    // A second way into the body that bypasses the guard.
    let (mut f, body, _, _) = build_const_checked_loop(ConstCheckCfg::canonical());
    let side = f.create_block();
    push(&mut f, side, br(body));
    f.add_edge(f.entry, side);
    f.add_edge(side, body);
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn const_check_keeps_an_unresolved_or_out_of_range_constant() {
    // A Movk-completed guard bound is unresolved.
    let (mut f, body, _, _) = build_const_checked_loop(ConstCheckCfg {
        guard_imm: false,
        ..ConstCheckCfg::canonical()
    });
    let entry = f.entry;
    let movk_id = f.push_inst(movk(g64(2), 0, 16));
    let at = f.block(entry).insts.len() - 1;
    f.block_mut(entry).insts.insert(at, movk_id);
    assert_eq!(run_fold(&mut f), (false, 0), "Movk-completed guard bound");
    assert_kept(&f, body);
    // A Movk-completed check bound is unresolved too.
    let (mut f, body, _, _) = build_const_checked_loop(ConstCheckCfg {
        check_imm: false,
        ..ConstCheckCfg::canonical()
    });
    let movk_id = f.push_inst(movk(g64(5), 0, 16));
    let at = f.block(entry).insts.len() - 1;
    f.block_mut(entry).insts.insert(at, movk_id);
    assert_eq!(run_fold(&mut f), (false, 0), "Movk-completed check bound");
    assert_kept(&f, body);
    // A negative guard constant is outside the comparable range.
    let (mut f, body, _, _) = build_const_checked_loop(ConstCheckCfg {
        guard_k: -1,
        ..ConstCheckCfg::canonical()
    });
    assert_eq!(run_fold(&mut f), (false, 0), "negative guard bound");
    assert_kept(&f, body);
}

#[test]
fn const_check_keeps_a_branch_to_a_block_that_does_not_diverge() {
    // The failing edge returns: an ordinary branch, never folded.
    let (mut f, body, fail, _) = build_const_checked_loop(ConstCheckCfg {
        raise: false,
        ..ConstCheckCfg::canonical()
    });
    let only = f.block(fail).insts[0];
    f.inst_mut(only).opcode = Op::Ret;
    assert_eq!(run_fold(&mut f), (false, 0));
    assert_kept(&f, body);
}

#[test]
fn const_check_arm_follows_the_trap_branch_switch() {
    let (mut f, body, _, _) = build_const_checked_loop(ConstCheckCfg::canonical());
    let mut pass = AArch64BoundsCheckElimination::new().without_trap_branch_folds();
    assert!(!pass.run_on_function(&mut f));
    assert_kept(&f, body);
}
