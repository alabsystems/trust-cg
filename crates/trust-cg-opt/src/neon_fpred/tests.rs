// Unit tests for the IV-synthesized FP-reduction vectorizer (neon-fpred).

use super::*;
use trust_cg_ir::Signature;

fn g(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn f(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr64))
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

/// How the reduction accumulate is formed (to exercise every recognized shape
/// and the fail-closed bails).
#[derive(Clone, Copy)]
enum Accum {
    /// acc_src = FaddRR(acc, term)  — the recognized plain-fadd reduction.
    PlainFadd,
    /// acc_src = FmaddRR(coef, u, acc) — FUSED accumulate, accumulator in the
    /// ADDEND position (operand 3). Recognized: drained scalar+fused+ordered.
    FusedFmadd,
    /// acc_src = FmaddRR(u, coef, acc) — same fused accumulate with the
    /// multiplicands COMMUTED. Recognized identically.
    FusedFmaddCommuted,
    /// acc_src = FmaddRR(acc, coef, one) — accumulator is a MULTIPLICAND, not the
    /// addend (a rounding-sensitive scaling recurrence). Must BAIL.
    FusedAccMultiplicand,
    /// acc_src = FsubRR(acc, term) — a subtract-into-acc root (neither fadd nor
    /// fmadd-addend). Not handled ⇒ must BAIL (fail-closed).
    Subtract,
}

/// Build a rotated IV-synthesized FP-reduction loop:
///   guard: x, coeffs, iv=1, acc=0.0 -> header
///   header: ufi=ucvtf(iv); u=fmul(x,ufi); t=fmadd(coef,u,one); acc'=acc (+) t;
///           iv'=iv+step; movz bound; cmp(iv', bound); b.eq exit; b latch
///   latch: acc=acc'; iv=iv'; b header
///   exit: use acc'; ret
///
/// `step` controls the induction stride (2 => not recognized); `accum` toggles the
/// plain-fadd vs fused-fmadd accumulate; `store_in_loop` injects a StrRI (must
/// BAIL); `leak_intermediate` makes a term intermediate live-out (must BAIL).
fn build_loop(
    step: i64,
    accum: Accum,
    store_in_loop: bool,
    leak_intermediate: bool,
) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb_guard = func.entry;
    let bb_hdr = func.create_block();
    let bb_latch = func.create_block();
    let bb_exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Loop-invariant leaves (defined in the guard, dominating the header):
    //   f(1)=x, f(3)=coef, f(5)=one ; iv=g(10), acc=f(11).
    push(&mut func, bb_guard, FmovGprFpr, vec![f(1), g(90)]); // x   (invariant)
    push(&mut func, bb_guard, FmovGprFpr, vec![f(3), g(91)]); // coef(invariant)
    push(&mut func, bb_guard, FmovGprFpr, vec![f(5), g(92)]); // one (invariant)
    push(&mut func, bb_guard, Movz, vec![g(93), i(1)]); // iv seed const
    push(&mut func, bb_guard, MovR, vec![g(10), g(93)]); // iv = 1
    push(&mut func, bb_guard, Movz, vec![g(94), i(0)]);
    push(&mut func, bb_guard, FmovGprFpr, vec![f(11), g(94)]); // acc = 0.0
    push(&mut func, bb_guard, B, vec![b(bb_hdr)]);

    // Header: term dataflow + accumulate + step + exit test.
    push(&mut func, bb_hdr, UcvtfRR, vec![f(20), g(10)]); // ufi = (double)iv
    push(&mut func, bb_hdr, FmulRR, vec![f(21), f(1), f(20)]); // u = x * ufi
    push(&mut func, bb_hdr, FmaddRR, vec![f(22), f(3), f(21), f(5)]); // t = one + coef*u
    if store_in_loop {
        push(&mut func, bb_hdr, StrRI, vec![f(22), g(95), i(0)]); // illegal store
    }
    match accum {
        Accum::PlainFadd => {
            push(&mut func, bb_hdr, FaddRR, vec![f(30), f(11), f(22)]); // acc' = acc + t
        }
        Accum::FusedFmadd => {
            // acc' = acc + coef*u  (the multiply-add fused INTO the accumulator's
            // ADDEND position: FmaddRR(d, n, m, a) = a + n*m, a = acc).
            push(&mut func, bb_hdr, FmaddRR, vec![f(30), f(3), f(21), f(11)]);
        }
        Accum::FusedFmaddCommuted => {
            // acc' = acc + u*coef  (multiplicands swapped; addend still acc).
            push(&mut func, bb_hdr, FmaddRR, vec![f(30), f(21), f(3), f(11)]);
        }
        Accum::FusedAccMultiplicand => {
            // acc' = one + acc*coef  (accumulator is a FACTOR, addend = one).
            push(&mut func, bb_hdr, FmaddRR, vec![f(30), f(11), f(3), f(5)]);
        }
        Accum::Subtract => {
            push(&mut func, bb_hdr, FsubRR, vec![f(30), f(11), f(22)]); // acc' = acc - t
        }
    }
    push(&mut func, bb_hdr, AddRI, vec![g(12), g(10), i(step)]); // iv' = iv + step
    push(&mut func, bb_hdr, Movz, vec![g(13), i(100)]); // bound = 100
    push(&mut func, bb_hdr, CmpRR, vec![g(12), g(13)]);
    push(&mut func, bb_hdr, BCond, vec![i(CC_EQ), b(bb_exit)]);
    push(&mut func, bb_hdr, B, vec![b(bb_latch)]);

    // Latch: writebacks + back-branch.
    push(&mut func, bb_latch, FmovFprFpr, vec![f(11), f(30)]); // acc = acc'
    push(&mut func, bb_latch, MovR, vec![g(10), g(12)]); // iv = iv'
    push(&mut func, bb_latch, B, vec![b(bb_hdr)]);

    // Exit: consume the reduction result (and, for the leak case, a term
    // intermediate — making it live-out).
    push(&mut func, bb_exit, FmovFprFpr, vec![f(40), f(30)]); // read acc' (live-out OK)
    if leak_intermediate {
        push(&mut func, bb_exit, FmovFprFpr, vec![f(41), f(21)]); // leak `u` (BAIL)
    }
    push(&mut func, bb_exit, Ret, vec![]);

    func.add_edge(bb_guard, bb_hdr);
    func.add_edge(bb_hdr, bb_latch);
    func.add_edge(bb_hdr, bb_exit);
    func.add_edge(bb_latch, bb_hdr);
    func.next_vreg = 200;
    func
}

#[test]
fn vectorizes_ivfp_reduction() {
    let mut func = build_loop(1, Accum::PlainFadd, false, false);
    let mut pass = NeonFPRedPass::new();
    let changed = pass.run(&mut func);
    assert!(
        changed,
        "pass should fire on the recognized IV-FP-reduction shape"
    );
    assert_eq!(pass.fired(), 1);
    // Vector body: UNROLL ucvtf.2d, at least UNROLL fmla.2d (the fused term), and
    // the ordered drain = 2*UNROLL lane extracts + fadds.
    assert_eq!(
        count(&func, AArch64Opcode::NeonUcvtfV),
        UNROLL as usize,
        "UNROLL ucvtf.2d"
    );
    assert!(
        count(&func, AArch64Opcode::NeonFmlaV) + count(&func, AArch64Opcode::NeonFmlaLaneV)
            >= UNROLL as usize,
        "fused term -> fmla.2d (register or by-element form)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupScalarD),
        (VF * UNROLL) as usize,
        "ordered drain: one lane extract per element"
    );
    assert!(
        count(&func, AArch64Opcode::FaddRR) >= (VF * UNROLL) as usize,
        "ordered drain: one scalar fadd per element (in iteration order)"
    );
}

#[test]
fn ordered_drain_structure_is_lane0_then_lane1_per_pair() {
    let mut func = build_loop(1, Accum::PlainFadd, false, false);
    let mut pass = NeonFPRedPass::new();
    assert!(pass.run(&mut func));
    // Assert the drain lane immediates run 0,1,0,1,... — each DUP immediately
    // feeding a scalar FADD (the bit-exactness order).
    let mut lanes = Vec::new();
    let mut fadd_after_dup = 0usize;
    for blk in &func.blocks {
        let ids: Vec<_> = blk.insts.clone();
        for w in ids.windows(2) {
            let a = func.inst(w[0]);
            let bb = func.inst(w[1]);
            if a.opcode == AArch64Opcode::NeonDupScalarD {
                if let MachOperand::Imm(l) = a.operands[2] {
                    lanes.push(l);
                }
                if bb.opcode == AArch64Opcode::FaddRR {
                    fadd_after_dup += 1;
                }
            }
        }
    }
    assert_eq!(
        lanes.len(),
        (VF * UNROLL) as usize,
        "one extract per element"
    );
    for (idx, &l) in lanes.iter().enumerate() {
        assert_eq!(
            l,
            (idx as i64) % VF,
            "drain lane order must be 0,1 per pair"
        );
    }
    assert_eq!(
        fadd_after_dup,
        (VF * UNROLL) as usize,
        "every lane extract is immediately followed by its ordered scalar fadd"
    );
}

/// Count `FmaddRR`s whose destination equals their addend (operand 0 == operand
/// 3) — the ordered SCALAR FUSED drain signature `acc = fmadd(n, m, acc)`.
fn scalar_fused_drain_count(func: &MachFunction) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| {
            let ins = func.inst(id);
            ins.opcode == AArch64Opcode::FmaddRR
                && ins.operands.len() == 4
                && ins.operands[0] == ins.operands[3]
        })
        .count()
}

#[test]
fn vectorizes_fused_accumulate() {
    // acc = acc + coef*u fused via FMADD-into-ADDEND. Now vectorized: the vector
    // body computes only the coef/u lanes; the accumulate stays SCALAR + FUSED +
    // ORDERED in the drain, so it is bit-exact (no split, no reassociation).
    let mut func = build_loop(1, Accum::FusedFmadd, false, false);
    let mut pass = NeonFPRedPass::new();
    assert!(
        pass.run(&mut func),
        "must vectorize a fused (fmadd-into-addend) accumulate"
    );
    assert_eq!(pass.fired(), 1);
    // Each index pair is converted once.
    assert_eq!(
        count(&func, AArch64Opcode::NeonUcvtfV),
        UNROLL as usize,
        "UNROLL ucvtf.2d"
    );
    // The drain extracts BOTH multiplicand lanes (n and m) per element.
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupScalarD),
        (2 * VF * UNROLL) as usize,
        "fused drain: two lane extracts (n and m) per element",
    );
    // The accumulate itself: one scalar FUSED FMADD per element, accumulator in
    // the addend AND destination — never split into a vector fmul + scalar fadd.
    assert_eq!(
        scalar_fused_drain_count(&func),
        (VF * UNROLL) as usize,
        "ordered fused drain: one scalar FMADD (acc in the addend) per element",
    );
}

#[test]
fn fused_accumulate_drain_preserves_source_unfuse_license() {
    for licensed in [false, true] {
        let mut func = build_loop(1, Accum::FusedFmadd, false, false);
        let source = func
            .block_order
            .iter()
            .flat_map(|&block| func.block(block).insts.iter().copied())
            .find(|&id| {
                let inst = func.inst(id);
                inst.opcode == AArch64Opcode::FmaddRR
                    && inst
                        .operands
                        .first()
                        .and_then(MachOperand::as_vreg)
                        .is_some_and(|dst| dst.id == 30)
            })
            .expect("source fused accumulator");
        if licensed {
            func.inst_mut(source)
                .flags
                .insert(InstFlags::FMULADD_MAY_UNFUSE);
        }

        let mut pass = NeonFPRedPass::new();
        assert!(pass.run(&mut func));
        let drains: Vec<_> = func
            .block_order
            .iter()
            .flat_map(|&block| func.block(block).insts.iter().copied())
            .filter(|&id| {
                let inst = func.inst(id);
                inst.opcode == AArch64Opcode::FmaddRR
                    && inst.operands.len() == 4
                    && inst.operands[0] == inst.operands[3]
            })
            .collect();
        assert!(
            !drains.is_empty(),
            "vectorizer must emit an ordered FMADD drain"
        );
        assert!(drains.iter().all(|&id| {
            func.inst(id).flags.contains(InstFlags::FMULADD_MAY_UNFUSE) == licensed
        }));
    }
}

#[test]
fn vectorizes_fused_accumulate_commuted_multiplicands() {
    // acc = acc + u*coef — the multiplicands swapped. Recognized identically:
    // both are per-lane term DAGs; only their ORDER as fmadd operands differs.
    let mut func = build_loop(1, Accum::FusedFmaddCommuted, false, false);
    let mut pass = NeonFPRedPass::new();
    assert!(
        pass.run(&mut func),
        "commuted multiplicands must vectorize too"
    );
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        scalar_fused_drain_count(&func),
        (VF * UNROLL) as usize,
        "commuted fused accumulate drains with the same ordered scalar FMADDs",
    );
}

#[test]
fn drain_lane_order_is_preserved_for_fused_accumulate() {
    // The fused drain must fold lanes in ORIGINAL iteration order: for each pair,
    // lane 0 then lane 1, each pair of (n,m) extracts feeding its scalar FMADD.
    let mut func = build_loop(1, Accum::FusedFmadd, false, false);
    let mut pass = NeonFPRedPass::new();
    assert!(pass.run(&mut func));
    // Walk the vector body: DUP(n,lane), DUP(m,lane), FMADD, repeating with lanes
    // 0,1,0,1,… The lane immediate on each *pair* of consecutive DUPs must match.
    let mut lanes = Vec::new();
    for blk in &func.blocks {
        let ids: Vec<_> = blk.insts.clone();
        for &id in &ids {
            let ins = func.inst(id);
            if ins.opcode == AArch64Opcode::NeonDupScalarD
                && let MachOperand::Imm(l) = ins.operands[2]
            {
                lanes.push(l);
            }
        }
    }
    assert_eq!(
        lanes.len(),
        (2 * VF * UNROLL) as usize,
        "two extracts per element"
    );
    // Grouped in twos (n,m of the same element): 0,0, 1,1, 0,0, 1,1, …
    for (idx, chunk) in lanes.chunks(2).enumerate() {
        assert_eq!(
            chunk[0], chunk[1],
            "n and m extract the SAME lane per element"
        );
        assert_eq!(
            chunk[0],
            (idx as i64) % VF,
            "elements drain in lane order 0,1 per pair"
        );
    }
}

#[test]
fn bails_on_fused_accumulator_as_multiplicand() {
    // acc = one + acc*coef: the accumulator is a FACTOR, not the addend — a
    // scaling recurrence that cannot be folded without changing the result.
    let mut func = build_loop(1, Accum::FusedAccMultiplicand, false, false);
    let mut pass = NeonFPRedPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL when the accumulator is a multiplicand"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUcvtfV),
        0,
        "no NEON emitted"
    );
}

#[test]
fn bails_on_non_fadd_non_fmadd_root() {
    // acc = acc - term: a subtract-into-acc root is neither a plain fadd nor a
    // fused fmadd-addend, and is not handled ⇒ fail-closed (leave it scalar).
    let mut func = build_loop(1, Accum::Subtract, false, false);
    let mut pass = NeonFPRedPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL on a non-fadd/non-fmadd accumulate root"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUcvtfV),
        0,
        "no NEON emitted"
    );
}

#[test]
fn bails_on_store_in_loop() {
    let mut func = build_loop(1, Accum::PlainFadd, true, false);
    let mut pass = NeonFPRedPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL on any store in the loop body"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUcvtfV), 0);
}

#[test]
fn bails_on_non_unit_step() {
    let mut func = build_loop(2, Accum::PlainFadd, false, false);
    let mut pass = NeonFPRedPass::new();
    assert!(!pass.run(&mut func), "must BAIL on a non-+1 induction step");
    assert_eq!(count(&func, AArch64Opcode::NeonUcvtfV), 0);
}

#[test]
fn bails_on_extra_liveout() {
    // A term intermediate (`u`) is used after the loop — if the vector consumed
    // all n it would be read stale, so the pass MUST bail.
    let mut func = build_loop(1, Accum::PlainFadd, false, true);
    let mut pass = NeonFPRedPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL when a term intermediate is live-out"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUcvtfV), 0);
}

/// Recognize the built loop and apply with an explicit `pressure_tune` flag
/// (race-free alternative to toggling `TRUST_CG_DISABLE_FPRED_PRESSURE_TUNE`).
fn apply_with_tune(func: &mut MachFunction, pressure_tune: bool) -> bool {
    let dom = crate::dom::DomTree::compute(func);
    let loops = crate::loops::LoopAnalysis::compute(func, &dom);
    let mut fired = false;
    let mut plans = Vec::new();
    for lp in loops.all_loops() {
        if let Some(rec) = Recognized::recognize(func, &dom, lp.header, lp.latch, &lp.body) {
            plans.push(rec);
        }
    }
    for rec in plans {
        if apply(func, &rec, pressure_tune) {
            fired = true;
        }
    }
    fired
}

#[test]
fn by_element_fmla_replaces_invariant_multiplicand_broadcast() {
    // The term `t = one + coef*u` has EXACTLY ONE invariant multiplicand
    // (`coef`): the PRESSURE tune must lower it as the by-element
    // `FMLA Vd, Vu, Vcoef.D[0]` (no DUP broadcast for `coef`), while the other
    // invariants (`x` in the FMUL, the addend `one`) are still broadcast.
    let mut func = build_loop(1, Accum::PlainFadd, false, false);
    assert!(apply_with_tune(&mut func, true));
    assert_eq!(
        count(&func, AArch64Opcode::NeonFmlaLaneV),
        UNROLL as usize,
        "one by-element FMLA per pair"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonFmlaV),
        0,
        "no register-broadcast FMLA remains"
    );
    // Broadcasts: `x` (FMUL operand) + `one` (FMLA addend) only — NOT `coef`.
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupElem),
        2,
        "coef needs no broadcast register"
    );
}

#[test]
fn pressure_tune_off_reproduces_broadcast_lowering() {
    // Kill switch (`TRUST_CG_DISABLE_FPRED_PRESSURE_TUNE`): the untuned lowering
    // must use the register-broadcast FMLA and broadcast ALL THREE invariants.
    let mut func = build_loop(1, Accum::PlainFadd, false, false);
    assert!(apply_with_tune(&mut func, false));
    assert_eq!(count(&func, AArch64Opcode::NeonFmlaLaneV), 0);
    assert_eq!(count(&func, AArch64Opcode::NeonFmlaV), UNROLL as usize);
    assert_eq!(count(&func, AArch64Opcode::NeonDupElem), 3);
}

#[test]
fn tuned_and_untuned_drains_fold_identical_lane_sequences() {
    // The interleaved (tuned) drain must fold the SAME per-lane sequence into
    // the accumulator as the deferred (untuned) drain: pair order, lane 0 then
    // lane 1 — the bit-exactness linchpin. Compare the two lowerings' ordered
    // (extract-lane, fold-op) traces.
    let trace = |func: &MachFunction| {
        let mut t = Vec::new();
        for blk in &func.blocks {
            for &id in &blk.insts {
                let inst = func.inst(id);
                match inst.opcode {
                    AArch64Opcode::NeonDupScalarD => {
                        if let MachOperand::Imm(l) = inst.operands[2] {
                            t.push(("dup", l));
                        }
                    }
                    AArch64Opcode::FaddRR => t.push(("fadd", -1)),
                    _ => {}
                }
            }
        }
        t
    };
    let mut tuned = build_loop(1, Accum::PlainFadd, false, false);
    assert!(apply_with_tune(&mut tuned, true));
    let mut untuned = build_loop(1, Accum::PlainFadd, false, false);
    assert!(apply_with_tune(&mut untuned, false));
    assert_eq!(
        trace(&tuned),
        trace(&untuned),
        "identical ordered lane-extract/fold sequence"
    );
}
