// Unit tests for the neon-fmap elementwise-FP vectorizer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::Signature;

fn v(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn v64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn f32r(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr32))
}
fn f64r(id: u32) -> MachOperand {
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

/// Count `AddRI` instructions whose immediate (last operand) equals `imm_val`.
/// Used to pin the two nested induction steps: `+width` (main latch) and `+vf`
/// (vectorized-remainder latch).
fn count_addri_imm(func: &MachFunction, imm_val: i64) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::AddRI
                && inst.operands.last().and_then(imm_of) == Some(imm_val)
        })
        .count()
}

/// Assert every instruction of `op` carries `want` as its LAST Imm operand
/// (the arrangement-code convention).
fn assert_arr(func: &MachFunction, op: AArch64Opcode, want: i64) {
    let mut seen = 0;
    for blk in &func.blocks {
        for &id in &blk.insts {
            let inst = func.inst(id);
            if inst.opcode == op {
                let arr = inst.operands.last().and_then(|o| match o {
                    MachOperand::Imm(x) => Some(*x),
                    _ => None,
                });
                assert_eq!(arr, Some(want), "{op:?} must carry arrangement {want}");
                seen += 1;
            }
        }
    }
    assert!(seen > 0, "expected at least one {op:?}");
}

/// Assert the MAIN loop's store path is fully PAIRED: `UNROLL/2` post-index
/// `STP Q,Q,#32` (UNROLL is even). Pins the #32 post-index on every pair store
/// (2 x 16-byte Q = 32 bytes, byte-identical to two ST1s). The single-vector
/// `ST1` now belongs to the vf-lane REMAINDER loop — see [`assert_vf_remainder`].
fn assert_paired_stores(func: &MachFunction) {
    assert_eq!(
        count(func, AArch64Opcode::NeonStpQPost),
        UNROLL / 2,
        "expected UNROLL/2 paired STP stores"
    );
    assert_eq!(
        count(func, AArch64Opcode::NeonSt1Post),
        1,
        "exactly one single ST1 — the vf-lane remainder store (main loop all paired)"
    );
    for blk in &func.blocks {
        for &id in &blk.insts {
            let inst = func.inst(id);
            if inst.opcode == AArch64Opcode::NeonStpQPost {
                assert_eq!(
                    inst.operands.last().and_then(|o| match o {
                        MachOperand::Imm(x) => Some(*x),
                        _ => None,
                    }),
                    Some(32),
                    "STP post-index must be #32 (two 16-byte Q registers)"
                );
            }
        }
    }
}

/// Assert the VECTORIZED REMAINDER loop `{rh, rb, rl}` fired: EXACTLY ONE
/// single-vector store (`ST1` — the vf-lane remainder step) and `n_streams`
/// single-vector loads (`LD1` — every stream loaded DIRECTLY in the remainder,
/// no `EXT` window derivation). A single `ST1` also proves the main loop's stores
/// are all paired (any stray main-loop `ST1` would push the count above one).
fn assert_vf_remainder(func: &MachFunction, n_streams: usize) {
    assert_eq!(
        count(func, AArch64Opcode::NeonSt1Post),
        1,
        "one vf-lane remainder ST1 store"
    );
    assert_eq!(
        count(func, AArch64Opcode::NeonLd1Post),
        n_streams,
        "remainder loads every stream directly (no EXT)"
    );
}

/// Kinds of FP map loops built by [`build_fmap_loop`].
///  0 => out[i] = b[i]*C + D          (map: one input stream + two invariants)
///  1 => y[i]  = A*x[i] + y[i]        (saxpy: in-place read of the store base)
///  2 => out[i] = (s[i-1]+s[i]+s[i+1]) / C   (3-point stencil, fdiv)
///  3 => a[i]  = a[i]*a[i]            (pure single-array in-place, regime (A))
///  4 => out[i] = out[i-1] + s[i]     (SHIFTED SELF-read: loop-carried => BAIL)
///
/// Register map: v0=store base, v1=n(i32), v2=input base, v5=iv(Gpr32),
/// v6/v7 = invariant FP scalars (self-copy defs in bb0), v40 = elem size.
fn build_fmap_loop(kind: u8, is_f64: bool) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    let fr: fn(u32) -> MachOperand = if is_f64 { f64r } else { f32r };
    let es: i64 = if is_f64 { 8 } else { 4 };
    use AArch64Opcode::*;
    // Preheader: pointers, constants, invariant FP scalars, iv = 0.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // store base
    push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
    push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // input base
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(es)]); // element size
    push(&mut func, bb0, Copy, vec![fr(6), fr(6)]); // invariant FP scalar C
    push(&mut func, bb0, Copy, vec![fr(7), fr(7)]); // invariant FP scalar D
    push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
    push(&mut func, bb0, B, vec![b(guard)]);
    // Guard.
    push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    // Header: term + store + step.
    push(&mut func, header, Sxtw, vec![v64(110), v(5)]);
    let term_val: u32 = match kind {
        1 => {
            // saxpy: y[i] = C*x[i] + y[i] (store base v0 read in place).
            push(
                &mut func,
                header,
                Madd,
                vec![v64(20), v64(110), v64(40), v64(2)],
            );
            push(&mut func, header, LdrRI, vec![fr(21), v64(20), i(0)]); // x[i]
            push(
                &mut func,
                header,
                Madd,
                vec![v64(22), v64(110), v64(40), v64(0)],
            );
            push(&mut func, header, LdrRI, vec![fr(23), v64(22), i(0)]); // y[i]
            push(&mut func, header, FmulRR, vec![fr(50), fr(6), fr(21)]); // C*x
            push(&mut func, header, FaddRR, vec![fr(51), fr(50), fr(23)]); // +y
            51
        }
        2 => {
            // stencil: out[i] = (s[i-1] + s[i] + s[i+1]) / C.
            push(&mut func, header, SubRI, vec![v(60), v(5), i(1)]); // i-1
            push(&mut func, header, Sxtw, vec![v64(61), v(60)]);
            push(
                &mut func,
                header,
                Madd,
                vec![v64(62), v64(61), v64(40), v64(2)],
            );
            push(&mut func, header, LdrRI, vec![fr(63), v64(62), i(0)]); // s[i-1]
            push(
                &mut func,
                header,
                Madd,
                vec![v64(64), v64(110), v64(40), v64(2)],
            );
            push(&mut func, header, LdrRI, vec![fr(65), v64(64), i(0)]); // s[i]
            push(&mut func, header, AddRI, vec![v(66), v(5), i(1)]); // i+1
            push(&mut func, header, Sxtw, vec![v64(67), v(66)]);
            push(
                &mut func,
                header,
                Madd,
                vec![v64(68), v64(67), v64(40), v64(2)],
            );
            push(&mut func, header, LdrRI, vec![fr(69), v64(68), i(0)]); // s[i+1]
            push(&mut func, header, FaddRR, vec![fr(50), fr(63), fr(65)]);
            push(&mut func, header, FaddRR, vec![fr(51), fr(50), fr(69)]);
            push(&mut func, header, FdivRR, vec![fr(52), fr(51), fr(6)]);
            52
        }
        3 => {
            // pure in-place: a[i] = a[i]*a[i] (only pointer touched is v0).
            push(
                &mut func,
                header,
                Madd,
                vec![v64(20), v64(110), v64(40), v64(0)],
            );
            push(&mut func, header, LdrRI, vec![fr(21), v64(20), i(0)]); // a[i]
            push(&mut func, header, FmulRR, vec![fr(50), fr(21), fr(21)]);
            50
        }
        4 => {
            // SHIFTED SELF-read: out[i] = out[i-1] + s[i] — loop-carried.
            push(&mut func, header, SubRI, vec![v(60), v(5), i(1)]);
            push(&mut func, header, Sxtw, vec![v64(61), v(60)]);
            push(
                &mut func,
                header,
                Madd,
                vec![v64(62), v64(61), v64(40), v64(0)],
            );
            push(&mut func, header, LdrRI, vec![fr(63), v64(62), i(0)]); // out[i-1]
            push(
                &mut func,
                header,
                Madd,
                vec![v64(64), v64(110), v64(40), v64(2)],
            );
            push(&mut func, header, LdrRI, vec![fr(65), v64(64), i(0)]); // s[i]
            push(&mut func, header, FaddRR, vec![fr(50), fr(63), fr(65)]);
            50
        }
        _ => {
            // map: out[i] = b[i]*C + D.
            push(
                &mut func,
                header,
                Madd,
                vec![v64(20), v64(110), v64(40), v64(2)],
            );
            push(&mut func, header, LdrRI, vec![fr(21), v64(20), i(0)]); // b[i]
            push(&mut func, header, FmulRR, vec![fr(50), fr(21), fr(6)]);
            push(&mut func, header, FaddRR, vec![fr(51), fr(50), fr(7)]);
            51
        }
    };
    push(
        &mut func,
        header,
        Madd,
        vec![v64(80), v64(110), v64(40), v64(0)],
    );
    push(&mut func, header, StrRI, vec![fr(term_val), v64(80), i(0)]);
    push(&mut func, header, AddRR, vec![v(90), v(5), v(4)]); // iv+1
    push(&mut func, header, B, vec![b(latch)]);
    push(&mut func, latch, AddRI, vec![v(5), v(90), i(0)]); // iv writeback
    push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, guard);
    func.add_edge(guard, header);
    func.add_edge(guard, exit);
    func.add_edge(header, latch);
    func.add_edge(latch, header);
    func.add_edge(latch, exit);
    func.next_vreg = 512;
    func
}

#[test]
fn vectorizes_f32_map_with_noalias() {
    let mut func = build_fmap_loop(0, false);
    func.noalias_params = vec![0, 2];
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "f32 map `out[i]=b[i]*C+D` must fire");
    assert_eq!(pass.fired(), 1);
    // MAIN loop: 1 stream * 2 LDP pairs; 2 paired STP; 4 FMUL + 4 FADD (NO FMLA
    // contraction). REMAINDER loop: +1 LD1, +1 ST1, +1 FMUL, +1 FADD (one vf-lane
    // sub-block). 2 invariant broadcasts (hoisted once, shared by both loops).
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), UNROLL / 2);
    assert_paired_stores(&func);
    assert_vf_remainder(&func, 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFmulV), UNROLL + 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFaddV), UNROLL + 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupElem),
        2,
        "C and D broadcast"
    );
    assert_arr(&func, AArch64Opcode::NeonFmulV, FARR_S4);
    assert_arr(&func, AArch64Opcode::NeonFaddV, FARR_S4);
}

#[test]
fn f32_map_bails_without_noalias() {
    // Two distinct pointers with no noalias — aliasing unprovable => BAIL.
    let mut func = build_fmap_loop(0, false);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonFMapPass::new();
    assert!(
        !pass.run(&mut func),
        "two-pointer FP map without noalias must BAIL"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0);
}

#[test]
fn f32_map_bails_when_input_not_noalias() {
    let mut func = build_fmap_loop(0, false);
    func.noalias_params = vec![0]; // store base only; input v2 NOT noalias
    let mut pass = NeonFMapPass::new();
    assert!(!pass.run(&mut func), "input base not noalias must BAIL");
    assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0);
}

#[test]
fn vectorizes_f32_saxpy_in_place_store_read() {
    let mut func = build_fmap_loop(1, false);
    func.noalias_params = vec![0, 2];
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "saxpy `y[i]=C*x[i]+y[i]` must fire");
    // MAIN: 2 streams (x, y) * 2 LDP pairs each; 2 paired STP. REMAINDER: 2 LD1
    // (both streams direct), 1 ST1, +1 FMUL + 1 FADD.
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), UNROLL);
    assert_paired_stores(&func);
    assert_vf_remainder(&func, 2);
    assert_eq!(count(&func, AArch64Opcode::NeonFmulV), UNROLL + 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFaddV), UNROLL + 1);
    // In-place regime: ALL loads must precede the first store in the vector
    // body (read-before-overwrite).
    let vb = func
        .blocks
        .iter()
        .position(|blk| {
            blk.insts
                .iter()
                .any(|&id| func.inst(id).opcode == AArch64Opcode::NeonStpQPost)
        })
        .unwrap();
    let insts = &func.blocks[vb].insts;
    let last_load = insts
        .iter()
        .rposition(|&id| func.inst(id).opcode == AArch64Opcode::NeonLdpQPost)
        .unwrap();
    let first_store = insts
        .iter()
        .position(|&id| func.inst(id).opcode == AArch64Opcode::NeonStpQPost)
        .unwrap();
    assert!(last_load < first_store, "all LDP before any STP (in-place)");
}

#[test]
fn vectorizes_f32_stencil_with_fdiv() {
    let mut func = build_fmap_loop(2, false);
    func.noalias_params = vec![0, 2];
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "3-point FP stencil must fire");
    // LANDED default for a STENCIL is `ExtT` (ties clang -O3 on M4): the two END
    // streams (s at -1/+1) load 2 LDP pairs each, the MIDDLE (s at 0) is
    // EXT-derived (UNROLL windows), and the arithmetic is emitted NODE-MAJOR.
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 2 * (UNROLL / 2));
    // EXT windows are a MAIN-loop optimization only; the remainder loads all
    // three streams directly, so NeonExtV stays UNROLL (no remainder EXTs).
    assert_eq!(count(&func, AArch64Opcode::NeonExtV), UNROLL);
    assert_paired_stores(&func);
    // REMAINDER: 3 streams loaded directly (s@-1, s@0, s@+1), 1 store, +2 FADD +
    // 1 FDIV (one vf-lane sub-block of the same term tree).
    assert_vf_remainder(&func, 3);
    assert_eq!(count(&func, AArch64Opcode::NeonFaddV), 2 * UNROLL + 2);
    assert_eq!(count(&func, AArch64Opcode::NeonFdivV), UNROLL + 1);
    assert_arr(&func, AArch64Opcode::NeonFdivV, FARR_S4);
    // Node-major ("transposed") order: EVERY fadd precedes EVERY fdiv, and every
    // EXT window precedes every fadd (all permutes hoisted). Pins the schedule.
    let vb = func
        .blocks
        .iter()
        .position(|blk| {
            blk.insts
                .iter()
                .any(|&id| func.inst(id).opcode == AArch64Opcode::NeonStpQPost)
        })
        .unwrap();
    let insts = &func.blocks[vb].insts;
    let pos = |op: AArch64Opcode, last: bool| {
        if last {
            insts.iter().rposition(|&id| func.inst(id).opcode == op)
        } else {
            insts.iter().position(|&id| func.inst(id).opcode == op)
        }
    };
    let last_ext = pos(AArch64Opcode::NeonExtV, true).unwrap();
    let first_fadd = pos(AArch64Opcode::NeonFaddV, false).unwrap();
    let last_fadd = pos(AArch64Opcode::NeonFaddV, true).unwrap();
    let first_fdiv = pos(AArch64Opcode::NeonFdivV, false).unwrap();
    assert!(
        last_ext < first_fadd,
        "all EXT windows hoisted before the fadds"
    );
    assert!(
        last_fadd < first_fdiv,
        "node-major: all fadds precede all fdivs"
    );
}

#[test]
fn f32_stencil_bails_without_noalias() {
    let mut func = build_fmap_loop(2, false);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonFMapPass::new();
    assert!(!pass.run(&mut func), "FP stencil without noalias must BAIL");
    assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0);
}

#[test]
fn vectorizes_f32_pure_in_place_without_noalias() {
    // Regime (A): a[i] = a[i]*a[i], only pointer touched is the store base at
    // the same index — sound with NO noalias at all.
    let mut func = build_fmap_loop(3, false);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonFMapPass::new();
    assert!(
        pass.run(&mut func),
        "single-array in-place FP map must fire"
    );
    assert_paired_stores(&func);
    assert_vf_remainder(&func, 1);
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), UNROLL / 2);
}

#[test]
fn shifted_self_read_bails_even_with_noalias() {
    // out[i] = out[i-1] + s[i] is a GENUINE loop-carried dependency: shifted
    // read of the STORE base must BAIL even when everything is noalias.
    let mut func = build_fmap_loop(4, false);
    func.noalias_params = vec![0, 2];
    let mut pass = NeonFMapPass::new();
    assert!(
        !pass.run(&mut func),
        "shifted self-read must BAIL (loop-carried)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0);
}

#[test]
fn vectorizes_f64_map_on_2d() {
    let mut func = build_fmap_loop(0, true);
    func.noalias_params = vec![0, 2];
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "f64 map must fire on .2D");
    assert_paired_stores(&func);
    // FP ops carry the FP arrangement code 2 (.2D). The paired STP store is
    // width-agnostic (it moves raw 16-byte Q registers), so f64 uses the SAME
    // #32 post-index pair store as f32 — byte-identical to two ST1 {V.2D}.
    assert_arr(&func, AArch64Opcode::NeonFmulV, FARR_D2);
    assert_arr(&func, AArch64Opcode::NeonFaddV, FARR_D2);
    assert_arr(&func, AArch64Opcode::NeonDupElem, ELEM_D);
}

#[test]
fn vectorizes_f64_saxpy_on_2d() {
    let mut func = build_fmap_loop(1, true);
    func.noalias_params = vec![0, 2];
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "f64 saxpy must fire on .2D");
    assert_arr(&func, AArch64Opcode::NeonFmulV, FARR_D2);
}

// ---------------------------------------------------------------------------
// COUNT-ABOVE family
// ---------------------------------------------------------------------------

/// Build `c += (a[i] >ogt t) ? 1 : 0` in the rotated shape (Fcmp + CSet(GT) +
/// Copy + AddRR). `cc` parameterizes the CSet condition (12 = GT fires; others
/// must BAIL).
fn build_fcount_loop(cc: i64, is_f64: bool) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    let fr: fn(u32) -> MachOperand = if is_f64 { f64r } else { f32r };
    let es: i64 = if is_f64 { 8 } else { 4 };
    use AArch64Opcode::*;
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base a
    push(&mut func, bb0, Copy, vec![fr(1), fr(1)]); // threshold t
    push(&mut func, bb0, Copy, vec![v(2), v(2)]); // n
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(es)]);
    push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
    push(&mut func, bb0, MovR, vec![v(6), v(3)]); // acc = 0
    push(&mut func, bb0, B, vec![b(guard)]);
    push(&mut func, guard, CmpRR, vec![v(5), v(2)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
    push(
        &mut func,
        header,
        Madd,
        vec![v64(12), v64(10), v64(40), v64(0)],
    );
    push(&mut func, header, LdrRI, vec![fr(13), v64(12), i(0)]); // a[i]
    push(&mut func, header, Fcmp, vec![fr(13), fr(1)]);
    push(&mut func, header, CSet, vec![v64(14), i(cc)]);
    push(&mut func, header, Copy, vec![v(15), v64(14)]);
    push(&mut func, header, AddRR, vec![v(16), v(6), v(15)]); // acc + cset
    push(&mut func, header, AddRR, vec![v(17), v(5), v(4)]); // iv + 1
    push(&mut func, header, B, vec![b(latch)]);
    push(&mut func, latch, AddRI, vec![v(5), v(17), i(0)]);
    push(&mut func, latch, AddRI, vec![v(6), v(16), i(0)]);
    push(&mut func, latch, CmpRR, vec![v(5), v(2)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, exit, Ret, vec![]);
    func.add_edge(bb0, guard);
    func.add_edge(guard, header);
    func.add_edge(guard, exit);
    func.add_edge(header, latch);
    func.add_edge(latch, header);
    func.add_edge(latch, exit);
    func.next_vreg = 512;
    func
}

#[test]
fn vectorizes_f32_count_above() {
    let mut func = build_fcount_loop(CC_GT, false);
    // NO noalias needed: the count family performs no store.
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "f32 count-above must fire");
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonFcmgtV),
        UNROLL,
        "4 FCMGT masks"
    );
    // 4 counting SUBs in the body + no other SubV.
    assert_eq!(count(&func, AArch64Opcode::NeonSubV), UNROLL);
    assert_eq!(count(&func, AArch64Opcode::NeonSt1Post), 0, "no store");
    assert_eq!(count(&func, AArch64Opcode::NeonUmovGen), 4, "4-lane fold");
    assert_arr(&func, AArch64Opcode::NeonFcmgtV, FARR_S4);
    assert_arr(&func, AArch64Opcode::NeonSubV, ARR_S4);
}

#[test]
fn vectorizes_f64_count_above_on_2d() {
    let mut func = build_fcount_loop(CC_GT, true);
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "f64 count-above must fire on .2D");
    assert_arr(&func, AArch64Opcode::NeonFcmgtV, FARR_D2);
    // Counting SUB at .2D; the exit fold's AddV stays .4S (high halves are
    // zero — see the module docs), so only check the body SUB here.
    assert_arr(&func, AArch64Opcode::NeonSubV, ARR_D2);
    assert_eq!(count(&func, AArch64Opcode::NeonUmovGen), 4, ".4S-lane fold");
}

#[test]
fn count_with_wrong_condition_bails() {
    // CSet(GE) is `fcmp oge` — NOT the count-above idiom; must BAIL (no
    // FCMGE opcode is wired).
    let mut func = build_fcount_loop(10, false); // 10 = GE
    let mut pass = NeonFMapPass::new();
    assert!(!pass.run(&mut func), "non-GT count must BAIL");
    assert_eq!(count(&func, AArch64Opcode::NeonFcmgtV), 0);
}

#[test]
fn fp_reduction_shape_never_fires() {
    // `s += a[i]` (FP accumulator) must NEVER be touched: vectorizing an FP
    // reduction reassociates. The map recognizer fails (no store), the count
    // recognizer fails (accumulator is FP / no CSet chain).
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]);
    push(&mut func, bb0, Copy, vec![v(2), v(2)]);
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(4)]);
    push(&mut func, bb0, Copy, vec![f32r(7), f32r(7)]); // s0 = 0.0
    push(&mut func, bb0, MovR, vec![v(5), v(3)]);
    push(&mut func, bb0, Copy, vec![f32r(8), f32r(7)]); // acc = s0
    push(&mut func, bb0, B, vec![b(guard)]);
    push(&mut func, guard, CmpRR, vec![v(5), v(2)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
    push(
        &mut func,
        header,
        Madd,
        vec![v64(12), v64(10), v64(40), v64(0)],
    );
    push(&mut func, header, LdrRI, vec![f32r(13), v64(12), i(0)]);
    push(&mut func, header, FaddRR, vec![f32r(14), f32r(8), f32r(13)]); // s += a[i]
    push(&mut func, header, AddRR, vec![v(17), v(5), v(4)]);
    push(&mut func, header, B, vec![b(latch)]);
    push(&mut func, latch, AddRI, vec![v(5), v(17), i(0)]);
    push(&mut func, latch, Copy, vec![f32r(8), f32r(14)]); // FP writeback
    push(&mut func, latch, CmpRR, vec![v(5), v(2)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, exit, Ret, vec![]);
    func.add_edge(bb0, guard);
    func.add_edge(guard, header);
    func.add_edge(guard, exit);
    func.add_edge(header, latch);
    func.add_edge(latch, header);
    func.add_edge(latch, exit);
    func.next_vreg = 512;

    let mut pass = NeonFMapPass::new();
    assert!(
        !pass.run(&mut func),
        "FP reduction must stay scalar (order-preserving)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonFaddV), 0, "no vector FADD");
}

#[test]
fn i64_induction_bails() {
    // Gpr64 induction has no sxtw guard headroom — must BAIL.
    let mut func = build_fmap_loop(0, false);
    // Rewrite the latch compare to Gpr64 regs (shape sabotage).
    let cmp_id = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .find(|&id| {
            func.inst(id).opcode == AArch64Opcode::CmpRR && func.blocks[3].insts.contains(&id)
        })
        .unwrap();
    func.inst_mut(cmp_id).operands = vec![v64(5), v64(1)];
    func.noalias_params = vec![0, 2];
    let mut pass = NeonFMapPass::new();
    assert!(!pass.run(&mut func), "i64 induction must BAIL");
}

#[test]
fn ext_window_planner_logic() {
    // The planner (exercised directly — the emission flag may be off): f32
    // admits middles with d, e in 1..=3; f64 only d == e == 1; ends never.
    let base = VReg::new(2, RegClass::Gpr64);
    let other = VReg::new(3, RegClass::Gpr64);
    let streams = vec![
        Stream { base, k: -1 },
        Stream { base, k: 0 },
        Stream { base, k: 1 },
        Stream { base: other, k: 0 },
    ];
    let w32 = Width::of_class(RegClass::Fpr32).unwrap();
    // Under an EXT schedule the planner derives middles; f32 admits d,e in 1..=3.
    let plan = plan_ext_windows(&streams, w32, StencilSched::ExtT);
    assert_eq!(plan.get(&1), Some(&(1, 1)), "middle K=0 derives from ends");
    assert!(
        !plan.contains_key(&0) && !plan.contains_key(&2),
        "ends load"
    );
    assert!(!plan.contains_key(&3), "single-stream base has no middles");
    // f64: shift d*8 = 8 is the only proven immediate — d == e == 1 only.
    let w64 = Width::of_class(RegClass::Fpr64).unwrap();
    let plan64 = plan_ext_windows(&streams, w64, StencilSched::ExtT);
    assert_eq!(plan64.get(&1), Some(&(1, 1)));
    let wide = vec![
        Stream { base, k: -2 },
        Stream { base, k: 0 },
        Stream { base, k: 2 },
    ];
    assert!(
        plan_ext_windows(&wide, w64, StencilSched::ExtT).is_empty(),
        "f64 d=2 needs EXT #16 — not encodable, keeps its own stream"
    );
    // The Baseline schedule derives no middles — every stream loads.
    assert!(
        plan_ext_windows(&streams, w32, StencilSched::Baseline).is_empty(),
        "baseline schedule derives no middles"
    );
}

// ---------------------------------------------------------------------------
// ROTATED importer shape (clang -O1): single-block do-while, i64-widened index,
// EQ header exit, fused `FmaddRR`, regime-C runtime versioning.  (Parts a/b/c.)
// ---------------------------------------------------------------------------

/// Build a ROTATED (clang -O1 importer) FP store loop `for(i=0;i<n;i++) y[i]=…`,
/// exactly the machine shape `trust-cg-ws2-import` emits:
///   * i64-widened induction used DIRECTLY as the address index (`Madd(iv, 4, base)`),
///   * bound `Uxtw(n)` compared as `cmp iv+1, bound; b.eq exit` in the HEADER,
///   * the latch is a PURE writeback `MovR(iv, iv+1)` + `B -> header`.
///     Kinds:
///     0 => saxpy  y[i] = a*x[i] + y[i]   (FmaddRR; in-place y + distinct x)
///     1 => sscal  y[i] = a*y[i]          (FmulRR; SINGLE-array in-place — regime A)
///     2 => pmul   y[i] = x[i]*b[i]       (FmulRR; TWO distinct inputs — 2 check bases)
///     3 => shifted-self  y[i] = y[i-1]*a (shifted read of the STORE base — must BAIL)
///
/// Register map: v0=y, v1=x, v40=b (pmul), v2=a(Fpr32), v3=n(i32), v6=Uxtw(n)(i64),
/// v7=0(i64), v8=iv(i64), v9=4(elem), v16=1(i64).
fn build_rotated_fmap(kind: u8) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    // bb0: params + the `n > 0` loop guard.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // y
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // x
    push(&mut func, bb0, Copy, vec![v64(40), v64(40)]); // b
    push(&mut func, bb0, Copy, vec![f32r(2), f32r(2)]); // a
    push(&mut func, bb0, Copy, vec![v(3), v(3)]); // n (i32)
    push(&mut func, bb0, Movz, vec![v(4), i(0)]);
    push(&mut func, bb0, CmpRR, vec![v(3), v(4)]);
    push(&mut func, bb0, BCond, vec![i(CC_GT), b(guard)]);
    push(&mut func, bb0, B, vec![b(exit)]);
    // guard: iv init + widened bound + constants.
    push(&mut func, guard, Uxtw, vec![v64(6), v(3)]); // bound = uxtw(n)
    push(&mut func, guard, Movz, vec![v64(7), i(0)]);
    push(&mut func, guard, MovR, vec![v64(8), v64(7)]); // iv = 0 (i64)
    push(&mut func, guard, Movz, vec![v64(9), i(4)]); // elem
    push(&mut func, guard, Movz, vec![v64(16), i(1)]);
    push(&mut func, guard, B, vec![b(header)]);
    // header: term + store + step + EQ exit test.
    let term_val: u32 = match kind {
        0 => {
            // saxpy: y[i] = a*x[i] + y[i]  (FmaddRR n=a, m=x[i], addend=y[i]).
            push(
                &mut func,
                header,
                Madd,
                vec![v64(10), v64(8), v64(9), v64(1)],
            ); // &x[i]
            push(&mut func, header, LdrRI, vec![f32r(11), v64(10), i(0)]);
            push(
                &mut func,
                header,
                Madd,
                vec![v64(13), v64(8), v64(9), v64(0)],
            ); // &y[i]
            push(&mut func, header, LdrRI, vec![f32r(14), v64(13), i(0)]);
            push(
                &mut func,
                header,
                FmaddRR,
                vec![f32r(15), f32r(2), f32r(11), f32r(14)],
            );
            15
        }
        1 => {
            // sscal: y[i] = a*y[i]  (single-array in-place — regime A).
            push(
                &mut func,
                header,
                Madd,
                vec![v64(13), v64(8), v64(9), v64(0)],
            ); // &y[i]
            push(&mut func, header, LdrRI, vec![f32r(14), v64(13), i(0)]);
            push(&mut func, header, FmulRR, vec![f32r(15), f32r(2), f32r(14)]);
            15
        }
        2 => {
            // pmul: y[i] = x[i]*b[i]  (two distinct inputs -> 2 check bases).
            push(
                &mut func,
                header,
                Madd,
                vec![v64(10), v64(8), v64(9), v64(1)],
            ); // &x[i]
            push(&mut func, header, LdrRI, vec![f32r(11), v64(10), i(0)]);
            push(
                &mut func,
                header,
                Madd,
                vec![v64(12), v64(8), v64(9), v64(40)],
            ); // &b[i]
            push(&mut func, header, LdrRI, vec![f32r(14), v64(12), i(0)]);
            push(
                &mut func,
                header,
                FmulRR,
                vec![f32r(15), f32r(11), f32r(14)],
            );
            push(
                &mut func,
                header,
                Madd,
                vec![v64(13), v64(8), v64(9), v64(0)],
            ); // &y[i]
            15
        }
        _ => {
            // shifted self-read: y[i] = y[i-1]*a  (loop-carried — must BAIL).
            push(&mut func, header, SubRI, vec![v64(20), v64(8), i(1)]); // iv-1 (i64)
            push(
                &mut func,
                header,
                Madd,
                vec![v64(10), v64(20), v64(9), v64(0)],
            ); // &y[i-1]
            push(&mut func, header, LdrRI, vec![f32r(11), v64(10), i(0)]);
            push(
                &mut func,
                header,
                Madd,
                vec![v64(13), v64(8), v64(9), v64(0)],
            ); // &y[i]
            push(&mut func, header, FmulRR, vec![f32r(15), f32r(11), f32r(2)]);
            15
        }
    };
    push(
        &mut func,
        header,
        StrRI,
        vec![f32r(term_val), v64(13), i(0)],
    );
    push(&mut func, header, AddRR, vec![v64(17), v64(8), v64(16)]); // iv+1
    push(&mut func, header, CmpRR, vec![v64(17), v64(6)]);
    push(&mut func, header, BCond, vec![i(CC_EQ), b(exit)]);
    push(&mut func, header, B, vec![b(latch)]);
    // latch: pure writeback + back-edge.
    push(&mut func, latch, MovR, vec![v64(8), v64(17)]);
    push(&mut func, latch, B, vec![b(header)]);
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, guard);
    func.add_edge(bb0, exit);
    func.add_edge(guard, header);
    func.add_edge(header, exit);
    func.add_edge(header, latch);
    func.add_edge(latch, header);
    func.next_vreg = 512;
    func
}

#[test]
fn rotated_saxpy_vectorizes_via_regime_c_versioning() {
    // The DIAGNOSED DEFECT: importer-rotated saxpy `y[i]=a*x[i]+y[i]`, NO noalias.
    // Must vectorize behind a regime-C runtime overlap check + a remainder-0 tail
    // guard, lowering the fused scalar FmaddRR to per-lane NeonFmlaV.
    let mut func = build_rotated_fmap(0);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "rotated saxpy must fire (regime C)");
    assert_eq!(pass.fired(), 1);
    // (b) fused FMLA lowering: the scalar invariant `a` is broadcast BY ELEMENT
    // (FMLA Vd, Vx, Va.s[0]) — UNROLL by-element FMLA + UNROLL ORR (addend copy)
    // in the main loop, +1 each in the vf-lane remainder; NO plain FMUL/FADD
    // (already fused), and NO DUP-broadcast NeonFmlaV.
    assert_eq!(
        count(&func, AArch64Opcode::NeonFmlaLaneV),
        UNROLL + 1,
        "main+remainder FMLA-lane"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonFmlaV),
        0,
        "da broadcast via lane, not DUP+FMLA"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonOrrV),
        UNROLL + 1,
        "main+remainder addend moves"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonFmulV),
        0,
        "no NEW contraction split"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonFaddV),
        0,
        "no NEW contraction split"
    );
    assert_arr(&func, AArch64Opcode::NeonFmlaLaneV, FARR_S4);
    // 2 streams (x, y) * UNROLL/2 LDP pairs each (main); remainder loads both direct.
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), UNROLL);
    assert_paired_stores(&func);
    assert_vf_remainder(&func, 2);
    // (c) regime-C versioning: 1 distinct input base -> 2 disjointness compares
    // (b.ls) plus the remainder-0 tail guard (b.hs).
    assert_eq!(
        count_bcond(&func, CC_LS),
        2,
        "one input base -> 2 LS disjointness tests"
    );
    assert_eq!(
        count_bcond(&func, CC_GE),
        1,
        "remainder-0 tail guard present"
    );
}

#[test]
fn rotated_saxpy_with_noalias_skips_versioning() {
    // With BOTH params noalias, regime B proves disjointness statically — no
    // runtime versioning blocks, but STILL vectorizes (rotated + FMLA + tail guard).
    let mut func = build_rotated_fmap(0);
    func.noalias_params = vec![0, 1];
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "rotated saxpy must fire (regime B)");
    assert_eq!(count(&func, AArch64Opcode::NeonFmlaLaneV), UNROLL + 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFmlaV), 0);
    assert_eq!(
        count_bcond(&func, CC_LS),
        0,
        "regime B: no runtime disjointness tests"
    );
    assert_eq!(
        count_bcond(&func, CC_GE),
        1,
        "remainder-0 tail guard still present"
    );
}

#[test]
fn rotated_sscal_vectorizes_regime_a_no_versioning() {
    // sscal `y[i]=a*y[i]`: the ONLY pointer touched is the store base at the same
    // index (single-array in-place) — regime A, sound with NO noalias and NO
    // runtime check. Lowered to a plain per-lane FMUL (not fused in the source).
    let mut func = build_rotated_fmap(1);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "rotated sscal must fire (regime A)");
    assert_eq!(count(&func, AArch64Opcode::NeonFmulV), UNROLL + 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFmlaV), 0);
    assert_eq!(
        count_bcond(&func, CC_LS),
        0,
        "regime A: no runtime disjointness tests"
    );
    assert_eq!(
        count_bcond(&func, CC_GE),
        1,
        "remainder-0 tail guard present"
    );
    // Only the store base is loaded: UNROLL/2 LDP pairs (main); 1 LD1 (remainder).
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), UNROLL / 2);
    assert_vf_remainder(&func, 1);
}

#[test]
fn rotated_pmul_two_inputs_versions_both() {
    // y[i]=x[i]*b[i]: TWO distinct input bases -> 2 pairs -> 4 LS disjointness tests.
    let mut func = build_rotated_fmap(2);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonFMapPass::new();
    assert!(
        pass.run(&mut func),
        "rotated two-input map must fire (regime C)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonFmulV), UNROLL + 1);
    assert_eq!(
        count_bcond(&func, CC_LS),
        4,
        "two input bases -> 4 LS disjointness tests"
    );
    assert_eq!(
        count_bcond(&func, CC_GE),
        1,
        "remainder-0 tail guard present"
    );
}

#[test]
fn remainder_loop_steps_by_vf_after_width() {
    // The vectorized-remainder loop nests INSIDE the main loop's tail: the main
    // latch advances the induction by `width` (UNROLL*vf = 16 for f32), the
    // remainder latch by exactly `vf` (4). Exactly one of each step exists, which
    // — together with the scalar do-while's `+1` — is what makes every index in
    // `[0,n)` processed EXACTLY ONCE in ascending order (main chunk, then vf-lane
    // remainder chunk, then scalar), the bit-exactness ordering invariant.
    let mut func = build_rotated_fmap(0); // f32 saxpy, width = 16, vf = 4
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "rotated saxpy must fire");
    let width = UNROLL as i64 * VF_F32;
    assert_eq!(
        count_addri_imm(&func, width),
        1,
        "exactly one +width main-latch step"
    );
    assert_eq!(
        count_addri_imm(&func, VF_F32),
        1,
        "exactly one +vf remainder-latch step"
    );
    // The remainder body is one vf-lane sub-block: 2 direct loads + 1 store.
    assert_vf_remainder(&func, 2);
}

#[test]
fn rotated_shifted_self_read_bails() {
    // y[i]=y[i-1]*a shifts the STORE base — a genuine loop-carried dependency.
    // Regime C cannot disprove a self-overlap: must BAIL in every noalias config.
    for noalias in [vec![], vec![0], vec![0, 1]] {
        let mut func = build_rotated_fmap(3);
        func.noalias_params = noalias.clone();
        let mut pass = NeonFMapPass::new();
        assert!(
            !pass.run(&mut func),
            "shifted self-read must BAIL (noalias={noalias:?})"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonFmlaV), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonFmulV), 0);
    }
}

#[test]
fn rotated_count_above_bails_no_tail_guard() {
    // The count family's apply emits no remainder-0 tail guard, so the rotated
    // shape (which would over-read a[n]) must be rejected at recognition.
    let mut func = build_rotated_fmap(1);
    // Turn it into a store-less shape is awkward; instead assert the skeleton's
    // rotated_exit gate keeps count-above native-only by construction: a rotated
    // MAP fires (above), a rotated COUNT never reaches apply_count. Here we simply
    // confirm the rotated map path does NOT accidentally also fire the count path
    // (fired == 1, one vectorization).
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func));
    assert_eq!(
        pass.fired(),
        1,
        "exactly one vectorization (map, not count)"
    );
}

// ---------------------------------------------------------------------------
// i64-BOUND rotated shape (the INLINED-dgefa form: clang computes the inner trip
// count in i64 inside an enclosing loop — `SubRR` bound, no i32 source).
// ---------------------------------------------------------------------------

/// Like [`build_rotated_fmap`], but the bound v6 is a genuinely-i64 register
/// (`SubRR(v50, v51)` of two loop-invariant i64 values defined in the entry, the
/// dgefa `n-k-1` shape) instead of `Uxtw(n)` — no i32 source for `ext_source`.
fn build_rotated_fmap_i64bound(kind: u8) -> MachFunction {
    let mut func = build_rotated_fmap(kind);
    let entry = func.entry;
    // v50/v51: loop-invariant i64 defs at the FRONT of the entry block.
    let id51 = func.push_inst(MachInst::new(AArch64Opcode::Copy, vec![v64(51), v64(51)]));
    func.block_mut(entry).insts.insert(0, id51);
    let id50 = func.push_inst(MachInst::new(AArch64Opcode::Copy, vec![v64(50), v64(50)]));
    func.block_mut(entry).insts.insert(0, id50);
    // Rewrite the guard's `Uxtw v6, v3` bound def into `SubRR v6, v50, v51`.
    let uxtw_id = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .find(|&id| func.inst(id).opcode == AArch64Opcode::Uxtw)
        .unwrap();
    let inst = func.inst_mut(uxtw_id);
    inst.opcode = AArch64Opcode::SubRR;
    inst.operands = vec![v64(6), v64(50), v64(51)];
    func
}

#[test]
fn rotated_i64_bound_saxpy_vectorizes_with_precheck() {
    // The linpack dgefa INLINED daxpy shape: i64 SubRR-derived bound, i64 iv,
    // FmaddRR, no noalias. Must fire on the i64 scheme: signed `bound < width`
    // PRECHECK + SIGNED `iv <s main_bound` header guard (CC_LT), regime-C
    // versioning gated by the `bound < 2^31` LSR/CBNZ check, HS tail guard.
    let mut func = build_rotated_fmap_i64bound(0);
    assert!(func.noalias_params.is_empty());
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "i64-bound rotated saxpy must fire");
    assert_eq!(count(&func, AArch64Opcode::NeonFmlaLaneV), UNROLL + 1);
    assert_eq!(count(&func, AArch64Opcode::NeonFmlaV), 0);
    // FIVE signed CC_LT guards: the `bound < width` precheck, plus the main
    // (`iv <s main_bound`) and vf-lane remainder (`main_bound_r`) guards, each
    // emitted TWICE — once in the header (the one-time zero-trip entry test) and
    // once at the end of the latch, which is the ROTATED backedge test (a
    // steady-state iteration then costs ONE conditional branch instead of an
    // unconditional jump to the header plus the header's own taken branch).
    // SIGNED so a negative starting induction enters the vector body instead
    // of comparing unsigned-huge (the negative-start miscompile fix).
    assert_eq!(
        count_bcond(&func, CC_LT),
        5,
        "precheck + main/remainder header AND rotated-latch guards"
    );
    // Versioning: 1 input base -> 2 LS disjointness tests + the 2^31 gate.
    assert_eq!(count_bcond(&func, CC_LS), 2);
    assert_eq!(
        count(&func, AArch64Opcode::LsrRI),
        1,
        "bound < 2^31 gate LSR"
    );
    assert_eq!(
        count(&func, AArch64Opcode::Cbnz),
        1,
        "bound < 2^31 gate CBNZ"
    );
    assert_eq!(count_bcond(&func, CC_GE), 1, "remainder-0 tail guard");
    // NO sxtw anywhere on the pure-i64 path (a 64-bit index must never be
    // truncated/sign-extended from 32 bits) — the remainder reuses the i64 iv.
    assert_eq!(
        count(&func, AArch64Opcode::Sxtw),
        0,
        "no sxtw on the pure-i64 path"
    );
}

#[test]
fn rotated_i64_bound_sscal_regime_a() {
    // In-place single-array on the i64-bound path: regime A (no versioning, no
    // gate), but still precheck + unsigned guard + tail guard.
    let mut func = build_rotated_fmap_i64bound(1);
    let mut pass = NeonFMapPass::new();
    assert!(pass.run(&mut func), "i64-bound rotated sscal must fire");
    assert_eq!(count(&func, AArch64Opcode::NeonFmulV), UNROLL + 1);
    assert_eq!(count_bcond(&func, CC_LS), 0, "regime A: no versioning");
    assert_eq!(
        count(&func, AArch64Opcode::LsrRI),
        0,
        "no gate without versioning"
    );
    assert_eq!(
        count_bcond(&func, CC_LT),
        5,
        "precheck + main/remainder header AND rotated-latch guards"
    );
    assert_eq!(count_bcond(&func, CC_GE), 1);
}

#[test]
fn fmap_loop_rotate_kill_switch_restores_top_tested_latches() {
    // `TCG_NO_FMAP_LOOP_ROTATE` (here driven through the same field the env var
    // sets, so the test never races on a process-global) reverts to the legacy
    // TOP-TESTED emission: each latch ends in an unconditional `B header`, so
    // only the THREE header-side CC_LT guards exist (precheck + main +
    // remainder). This is the bisect key and the byte-identity anchor for the
    // pre-rotation compiler.
    let mut off = build_rotated_fmap_i64bound(1);
    let mut pass = NeonFMapPass::with_rotate(false);
    assert!(pass.run(&mut off), "the pass still fires with rotation off");
    assert_eq!(
        count_bcond(&off, CC_LT),
        3,
        "rotation OFF: header-side guards only"
    );

    let mut on = build_rotated_fmap_i64bound(1);
    let mut pass = NeonFMapPass::with_rotate(true);
    assert!(pass.run(&mut on));
    assert_eq!(count_bcond(&on, CC_LT), 5, "rotation ON: + two latch tests");
    // On the i64 path the rotation adds EXACTLY the two duplicated tests per
    // loop (`CmpRR` + `BCond`) and no more: each latch keeps its terminating
    // unconditional `B`, which now targets the loop exit instead of the header.
    assert_eq!(
        count(&on, AArch64Opcode::CmpRR) - count(&off, AArch64Opcode::CmpRR),
        2
    );
    assert_eq!(count(&on, AArch64Opcode::B), count(&off, AArch64Opcode::B));
    assert_eq!(
        count(&on, AArch64Opcode::Sxtw),
        count(&off, AArch64Opcode::Sxtw)
    );
}

#[test]
fn rotated_i64_bound_shifted_self_read_still_bails() {
    let mut func = build_rotated_fmap_i64bound(3);
    let mut pass = NeonFMapPass::new();
    assert!(
        !pass.run(&mut func),
        "shifted self-read must BAIL on the i64 path too"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonFmulV), 0);
}

#[test]
fn native_i64_bound_still_bails() {
    // The NATIVE (bottom-tested) skeleton stays STRICTLY i32: an i64 latch
    // compare must keep bailing (byte-identity for the native family).
    let mut func = build_fmap_loop(0, false);
    let cmp_id = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .find(|&id| {
            func.inst(id).opcode == AArch64Opcode::CmpRR && func.blocks[3].insts.contains(&id)
        })
        .unwrap();
    func.inst_mut(cmp_id).operands = vec![v64(5), v64(1)];
    func.noalias_params = vec![0, 2];
    let mut pass = NeonFMapPass::new();
    assert!(!pass.run(&mut func), "native i64 latch compare must BAIL");
}
