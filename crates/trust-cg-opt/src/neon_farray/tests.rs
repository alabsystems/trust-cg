// Unit tests for the FP array-reduction vectorizer (neon-farray).

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

/// Which reduction root to build.
#[derive(Clone, Copy)]
enum Kind {
    /// acc' = FMADD(la, lb, acc)  — fused f64 dot (`acc += a[i]*b[i]`).
    FusedDot,
    /// acc' = FADD(acc, la)       — plain f64 sum (`acc += a[i]`).
    PlainSum,
    /// acc' = FADD(acc, FMUL(la, lb)) — UNFUSED dot (vectorizable multiply).
    UnfusedDot,
}

/// Build a ROTATED f64 array-reduction do-while:
///   guard: base_a, base_b, c8=8, iv=0, acc=0.0 -> header
///   header: addr_a=Madd(iv,c8,base_a); la=Ldr[Fpr64](addr_a,0); (same for b)
///           acc' = <root>; iv'=iv+step; movz bound; cmp(iv',bound); b.eq exit; b latch
///   latch: acc=acc'; iv=iv'; b header
///   exit: use acc'; ret
///
/// `f32_widen` swaps BOTH the a- and b-loads to `f32` loads + `FcvtSD` widen
/// (the fp-convert kernel — now VECTORIZED via `FCVTL/FCVTL2`; use `elem = 4`);
/// `store_in_loop` injects a StrRI (must BAIL); `stride` != 1 must BAIL.
fn build_loop(
    kind: Kind,
    step: i64,
    elem: i64,
    f32_widen: bool,
    store_in_loop: bool,
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

    // Loop-invariant leaves in the guard (dominating the header).
    push(&mut func, bb_guard, MovR, vec![g(1), g(80)]); // base_a (invariant ptr)
    push(&mut func, bb_guard, MovR, vec![g(2), g(81)]); // base_b (invariant ptr)
    push(&mut func, bb_guard, Movz, vec![g(3), i(elem)]); // element size const
    push(&mut func, bb_guard, Movz, vec![g(93), i(0)]);
    push(&mut func, bb_guard, MovR, vec![g(10), g(93)]); // iv = 0
    push(&mut func, bb_guard, Movz, vec![g(94), i(0)]);
    push(&mut func, bb_guard, FmovGprFpr, vec![f(11), g(94)]); // acc = 0.0
    push(&mut func, bb_guard, B, vec![b(bb_hdr)]);

    // Header: address + loads + accumulate + step + exit test.
    push(&mut func, bb_hdr, Madd, vec![g(20), g(10), g(3), g(1)]); // addr_a = base_a + iv*es
    if f32_widen {
        // f32 load + widening FcvtSD — the fp-convert kernel's `(double)a_f32[i]`.
        let la32 = MachOperand::VReg(VReg::new(21, RegClass::Fpr32));
        push(&mut func, bb_hdr, LdrRI, vec![la32.clone(), g(20), i(0)]);
        push(&mut func, bb_hdr, FcvtSD, vec![f(23), la32]); // la = (double)a_f32[i]
    } else {
        push(&mut func, bb_hdr, LdrRI, vec![f(23), g(20), i(0)]); // la = a[i]
    }
    push(&mut func, bb_hdr, Madd, vec![g(24), g(10), g(3), g(2)]); // addr_b
    if f32_widen {
        let lb32 = MachOperand::VReg(VReg::new(26, RegClass::Fpr32));
        push(&mut func, bb_hdr, LdrRI, vec![lb32.clone(), g(24), i(0)]);
        push(&mut func, bb_hdr, FcvtSD, vec![f(25), lb32]); // lb = (double)b_f32[i]
    } else {
        push(&mut func, bb_hdr, LdrRI, vec![f(25), g(24), i(0)]); // lb = b[i]
    }
    if store_in_loop {
        push(&mut func, bb_hdr, StrRI, vec![f(23), g(95), i(0)]); // illegal store
    }
    match kind {
        Kind::FusedDot => {
            push(&mut func, bb_hdr, FmaddRR, vec![f(30), f(23), f(25), f(11)]); // acc + la*lb
        }
        Kind::PlainSum => {
            push(&mut func, bb_hdr, FaddRR, vec![f(30), f(11), f(23)]); // acc + la
        }
        Kind::UnfusedDot => {
            push(&mut func, bb_hdr, FmulRR, vec![f(28), f(23), f(25)]); // t = la*lb
            push(&mut func, bb_hdr, FaddRR, vec![f(30), f(11), f(28)]); // acc + t
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

    // Exit: consume the reduction result.
    push(&mut func, bb_exit, FmovFprFpr, vec![f(40), f(30)]);
    push(&mut func, bb_exit, Ret, vec![]);

    func.add_edge(bb_guard, bb_hdr);
    func.add_edge(bb_hdr, bb_latch);
    func.add_edge(bb_hdr, bb_exit);
    func.add_edge(bb_latch, bb_hdr);
    func.next_vreg = 200;
    func
}

#[test]
fn vectorizes_fused_f64_dot() {
    let mut func = build_loop(Kind::FusedDot, 1, 8, false, false);
    let mut pass = NeonFArrayPass::new();
    assert!(pass.run(&mut func), "should fire on the fused f64 dot");
    assert_eq!(pass.fired(), 1);
    // Two bases => two LDP-Q post-index load groups (UNROLL/2 each).
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        2 * (UNROLL / 2) as usize,
        "coalesced vector loads per base"
    );
    // Ordered drain: per element, extract n & m lanes + one scalar fused FMADD.
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupScalarD),
        (2 * VF * UNROLL) as usize,
        "two lane extracts (n,m) per element"
    );
    // The fused contraction is preserved: one scalar FMADD per drained element
    // (plus none split into vector FMUL for the multiplicands themselves).
    assert!(
        count(&func, AArch64Opcode::FmaddRR) >= (VF * UNROLL) as usize,
        "one scalar fused fmadd per element (in order)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonFmulV),
        0,
        "fused dot must NOT vectorize the multiply (single rounding preserved)"
    );
}

#[test]
fn ordered_fmadd_drain_preserves_source_unfuse_license() {
    for licensed in [false, true] {
        let mut func = build_loop(Kind::FusedDot, 1, 8, false, false);
        let source = func
            .block_order
            .iter()
            .flat_map(|&block| func.block(block).insts.iter().copied())
            .find(|&id| func.inst(id).opcode == AArch64Opcode::FmaddRR)
            .expect("source fused reduction");
        if licensed {
            func.inst_mut(source)
                .flags
                .insert(InstFlags::FMULADD_MAY_UNFUSE);
        }

        let mut pass = NeonFArrayPass::new();
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
fn vectorizes_plain_f64_sum() {
    let mut func = build_loop(Kind::PlainSum, 1, 8, false, false);
    let mut pass = NeonFArrayPass::new();
    assert!(pass.run(&mut func), "should fire on the plain f64 sum");
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        (UNROLL / 2) as usize,
        "one base => one LDP-Q group"
    );
    // Ordered drain: one lane extract + one scalar FADD per element.
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupScalarD),
        (VF * UNROLL) as usize
    );
    assert!(count(&func, AArch64Opcode::FaddRR) >= (VF * UNROLL) as usize);
}

#[test]
fn vectorizes_unfused_dot_with_vector_multiply() {
    let mut func = build_loop(Kind::UnfusedDot, 1, 8, false, false);
    let mut pass = NeonFArrayPass::new();
    assert!(pass.run(&mut func), "should fire on the unfused dot");
    // The multiply IS vectorized here (per-lane exact FMUL.2D), then a scalar
    // FADD drain (bit-identical to `t=a*b; acc+=t`).
    assert!(
        count(&func, AArch64Opcode::NeonFmulV) >= UNROLL as usize,
        "vectorized multiply"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupScalarD),
        (VF * UNROLL) as usize
    );
}

#[test]
fn ordered_drain_lane_order_is_0_then_1_per_pair() {
    let mut func = build_loop(Kind::PlainSum, 1, 8, false, false);
    let mut pass = NeonFArrayPass::new();
    assert!(pass.run(&mut func));
    let mut lanes = Vec::new();
    for blk in &func.blocks {
        for &id in &blk.insts {
            let inst = func.inst(id);
            if inst.opcode == AArch64Opcode::NeonDupScalarD
                && let MachOperand::Imm(l) = inst.operands[2]
            {
                lanes.push(l);
            }
        }
    }
    assert_eq!(lanes.len(), (VF * UNROLL) as usize);
    for (idx, &l) in lanes.iter().enumerate() {
        assert_eq!(
            l,
            (idx as i64) % VF,
            "drain lane order must be 0,1 per pair"
        );
    }
}

#[test]
fn vectorizes_f32_widening_fused_dot() {
    // The fp-convert kernel: `sum += (double)a_f32[i] * (double)b_f32[i]` (FUSED
    // fmadd). With the proven vector FCVTL/FCVTL2, the coalesced f32 loads are
    // widened off-chain and the multiply STAYS FUSED in the per-lane scalar
    // drain (single rounding preserved) — bit-identical to the scalar loop.
    let mut func = build_loop(Kind::FusedDot, 1, 4, true, false);
    let mut pass = NeonFArrayPass::new();
    assert!(
        pass.run(&mut func),
        "should FIRE on the f32-widening fused dot"
    );
    assert_eq!(pass.fired(), 1);
    // Two f32-widen bases => one LDP-Q of f32 each (UNROLL/4 = 1).
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        2 * (UNROLL / 4) as usize,
        "one coalesced f32 LDP-Q per widen base"
    );
    // Each f32 Q (2 per base) widens via FCVTL (low half) + FCVTL2 (high half).
    assert_eq!(
        count(&func, AArch64Opcode::NeonFcvtlV),
        (2 * (UNROLL / 4) * 2) as usize
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonFcvtl2V),
        (2 * (UNROLL / 4) * 2) as usize
    );
    // Ordered fused drain: two lane extracts (n,m) + one scalar FMADD per element.
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupScalarD),
        (2 * VF * UNROLL) as usize
    );
    assert!(count(&func, AArch64Opcode::FmaddRR) >= (VF * UNROLL) as usize);
    // The fused contraction is PRESERVED: the multiply is NOT vectorized (that
    // would double-round vs the scalar `llvm.fmuladd`).
    assert_eq!(
        count(&func, AArch64Opcode::NeonFmulV),
        0,
        "fused widening dot must NOT vectorize the multiply (single rounding preserved)"
    );
}

#[test]
fn default_mode_fires_on_f32_widening_dot() {
    // ASYMMETRIC DEFAULT: widening recognition is DEFAULT-ENABLED — the
    // widening-only pass (the pipeline's default construction) must fire on the
    // fp-convert kernel exactly like full mode.
    let mut func = build_loop(Kind::FusedDot, 1, 4, true, false);
    let mut pass = NeonFArrayPass::widening_only();
    assert!(
        pass.run(&mut func),
        "DEFAULT (widening-only) must FIRE on the f32-widening dot"
    );
    assert_eq!(pass.fired(), 1);
    assert!(
        count(&func, AArch64Opcode::NeonFcvtlV) > 0,
        "FCVTL emitted by default"
    );
}

#[test]
fn default_mode_bails_on_pure_f64_reductions() {
    // ASYMMETRIC DEFAULT: NON-widening recognition requires the full opt-in.
    // The widening-only pass must leave every pure-f64 reduction ENTIRELY to the
    // scalar path (measured: firing regresses the fused ddot ~5% by stealing the
    // loop from scalar_unroll's extract-free unroll).
    for kind in [Kind::FusedDot, Kind::PlainSum, Kind::UnfusedDot] {
        let mut func = build_loop(kind, 1, 8, false, false);
        let mut pass = NeonFArrayPass::widening_only();
        assert!(
            !pass.run(&mut func),
            "DEFAULT (widening-only) must BAIL on a pure-f64 reduction"
        );
        assert_eq!(
            count(&func, AArch64Opcode::NeonLdpQPost),
            0,
            "no NEON emitted"
        );
    }
}

#[test]
fn default_trait_is_widening_only() {
    // The pipeline's default construction is the widening-only mode; pin the
    // Default trait to it so a refactor cannot silently flip the default to full.
    let mut func = build_loop(Kind::FusedDot, 1, 8, false, false);
    let mut pass = NeonFArrayPass::default();
    assert!(
        !pass.run(&mut func),
        "Default must be widening-only (bails on pure f64)"
    );
}

#[test]
fn bails_on_store_in_loop() {
    let mut func = build_loop(Kind::FusedDot, 1, 8, false, true);
    let mut pass = NeonFArrayPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL on any store in the loop body"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
}

#[test]
fn bails_on_non_unit_stride() {
    let mut func = build_loop(Kind::FusedDot, 2, 8, false, false);
    let mut pass = NeonFArrayPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL on a non-unit induction stride"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
}

#[test]
fn bails_on_wrong_element_size() {
    // stride 1 but element-size const is 4 (not 8) => not a unit-stride f64 load.
    let mut func = build_loop(Kind::FusedDot, 1, 4, false, false);
    let mut pass = NeonFArrayPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL when the load stride != 8 bytes (f64)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
}

// ===========================================================================
// IOTA-FILL (`.4S`) vectorizer tests: `x[j] = a + (float)j` etc.
// ===========================================================================

fn s(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr32))
}
fn w(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}

/// Build a ROTATED iota-fill do-while mirroring the fp-convert fill:
///   guard: base_x, base_y, es=4, iv=0, a, b -> hdr
///   hdr:   w = trunc(iv); cvt = (float)j; [val_x = a + cvt]; addr_x = Madd(iv,4,base_x);
///          StrRI x[j]; [second store to y]; iv'=iv+1; movz bound; cmp; b.eq exit; b latch
///   latch: iv = iv'; b hdr
///   exit:  ret
///
/// `two_store` adds the y-stream; `invariant_add` wraps the cvt in `a + cvt`
/// (else stores the raw cvt); `signed` uses `ScvtfRR` (else `UcvtfRR`);
/// `load_in_loop` injects a `LdrRI` (must BAIL — a fill READS no memory);
/// `pure_invariant_store` stores a value that does NOT flow through the cvt
/// (must BAIL — not an iota fill).
fn build_fill(
    two_store: bool,
    invariant_add: bool,
    signed: bool,
    bound: i64,
    load_in_loop: bool,
    pure_invariant_store: bool,
) -> MachFunction {
    let mut func = MachFunction::new("fill".to_string(), Signature::new(vec![], vec![]));
    let bb_guard = func.entry;
    let bb_hdr = func.create_block();
    let bb_latch = func.create_block();
    let bb_exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Guard: loop-invariant leaves (dominate the header).
    push(&mut func, bb_guard, MovR, vec![g(1), g(80)]); // base_x
    push(&mut func, bb_guard, MovR, vec![g(2), g(81)]); // base_y
    push(&mut func, bb_guard, Movz, vec![g(3), i(4)]); // es = 4 (f32)
    push(&mut func, bb_guard, Movz, vec![g(93), i(0)]);
    push(&mut func, bb_guard, MovR, vec![g(10), g(93)]); // iv = 0
    push(&mut func, bb_guard, FmovGprFpr, vec![s(4), g(82)]); // a (invariant f32)
    push(&mut func, bb_guard, FmovGprFpr, vec![s(5), g(83)]); // b (invariant f32)
    push(&mut func, bb_guard, B, vec![b(bb_hdr)]);

    // Header.
    push(&mut func, bb_hdr, MovR, vec![w(6), g(10)]); // trunc iv -> i32
    push(
        &mut func,
        bb_hdr,
        if signed { ScvtfRR } else { UcvtfRR },
        vec![s(7), w(6)],
    ); // (float)j
    // val_x
    let val_x = if pure_invariant_store {
        s(4) // a pure invariant (does NOT depend on the cvt) — must BAIL
    } else if invariant_add {
        push(&mut func, bb_hdr, FaddRR, vec![s(8), s(4), s(7)]); // a + (float)j
        s(8)
    } else {
        s(7)
    };
    if load_in_loop {
        push(&mut func, bb_hdr, LdrRI, vec![s(50), g(1), i(0)]); // illegal: a fill has NO loads
    }
    push(&mut func, bb_hdr, Madd, vec![g(20), g(10), g(3), g(1)]); // addr_x = iv*4 + base_x
    push(&mut func, bb_hdr, StrRI, vec![val_x, g(20), i(0)]); // x[j] = val_x
    if two_store {
        push(&mut func, bb_hdr, FaddRR, vec![s(9), s(5), s(7)]); // b + (float)j
        push(&mut func, bb_hdr, Madd, vec![g(24), g(10), g(3), g(2)]); // addr_y
        push(&mut func, bb_hdr, StrRI, vec![s(9), g(24), i(0)]); // y[j]
    }
    push(&mut func, bb_hdr, AddRI, vec![g(12), g(10), i(1)]); // iv' = iv + 1
    push(&mut func, bb_hdr, Movz, vec![g(13), i(bound)]);
    push(&mut func, bb_hdr, CmpRR, vec![g(12), g(13)]);
    push(&mut func, bb_hdr, BCond, vec![i(CC_EQ), b(bb_exit)]);
    push(&mut func, bb_hdr, B, vec![b(bb_latch)]);

    // Latch + exit.
    push(&mut func, bb_latch, MovR, vec![g(10), g(12)]);
    push(&mut func, bb_latch, B, vec![b(bb_hdr)]);
    push(&mut func, bb_exit, Ret, vec![]);

    func.add_edge(bb_guard, bb_hdr);
    func.add_edge(bb_hdr, bb_latch);
    func.add_edge(bb_hdr, bb_exit);
    func.add_edge(bb_latch, bb_hdr);
    func.next_vreg = 200;
    func
}

#[test]
fn fill_vectorizes_two_store_invariant_add_by_default() {
    // The fp-convert fill: `x[j]=a+(float)j; y[j]=b+(float)j`. Fires in the DEFAULT
    // (widening-only) config — the iota fill is not gated behind the full opt-in.
    let mut func = build_fill(true, true, false, 100, false, false);
    let mut pass = NeonFArrayPass::default();
    assert!(pass.run(&mut func), "iota fill must fire by default");
    assert_eq!(pass.fired(), 1);
    // Two output streams => two `STP Qt1, Qt2` (one per stream).
    assert_eq!(
        count(&func, AArch64Opcode::NeonStpQPost),
        2,
        "one STP-Q per stream"
    );
    // `.4S` int->float convert (unsigned) is emitted, per pair (UNROLL_S = 2).
    assert_eq!(count(&func, AArch64Opcode::NeonUcvtfV), UNROLL_S as usize);
    assert_eq!(count(&func, AArch64Opcode::NeonScvtfV), 0);
    // Two DISTINCT bases => a runtime disjointness guard (`x_end <=u y` / `y_end <=u x`).
    assert!(
        count(&func, AArch64Opcode::LslRI) >= 1 && count(&func, AArch64Opcode::AddRR) >= 2,
        "regime-C disjointness range setup present"
    );
    // The ORIGINAL scalar stores are left intact (additive splice).
    assert!(
        count(&func, AArch64Opcode::StrRI) >= 2,
        "scalar tail stores preserved"
    );
}

#[test]
fn fill_single_store_needs_no_disjointness_guard() {
    // `x[j] = (float)j` — one stream, no store/store hazard => NO runtime guard.
    let mut func = build_fill(false, false, false, 100, false, false);
    let mut pass = NeonFArrayPass::default();
    assert!(pass.run(&mut func), "single-store iota fill must fire");
    assert_eq!(
        count(&func, AArch64Opcode::NeonStpQPost),
        1,
        "one stream => one STP-Q"
    );
    // No disjointness ranges (a single stream needs no versioning).
    assert_eq!(
        count(&func, AArch64Opcode::LslRI),
        0,
        "no disjointness guard for one stream"
    );
}

#[test]
fn fill_signed_uses_scvtf() {
    let mut func = build_fill(false, true, true, 100, false, false);
    let mut pass = NeonFArrayPass::default();
    assert!(pass.run(&mut func), "signed iota fill must fire");
    assert_eq!(
        count(&func, AArch64Opcode::NeonScvtfV),
        UNROLL_S as usize,
        "SCVTF for signed cvt"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUcvtfV), 0);
}

#[test]
fn fill_builds_iota_index_vector() {
    // The lane vector `[j, j+1, j+2, j+3]` = broadcast(iv) + const step, advanced by
    // the width each iteration: a DUP-from-GPR + `.4S` integer ADDs.
    let mut func = build_fill(false, false, false, 100, false, false);
    let mut pass = NeonFArrayPass::default();
    assert!(pass.run(&mut func));
    assert!(
        count(&func, AArch64Opcode::NeonDupGen) >= 1,
        "iota base broadcast"
    );
    assert!(
        count(&func, AArch64Opcode::NeonAddV) >= 1,
        "iota step / advance adds"
    );
}

#[test]
fn fill_bails_on_load_in_body() {
    // A fill READS no memory; any load => an aliasing surface we do not model => BAIL.
    let mut func = build_fill(true, true, false, 100, true, false);
    let mut pass = NeonFArrayPass::default();
    assert!(
        !pass.run(&mut func),
        "must BAIL on any load in the fill body"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), 0);
}

#[test]
fn fill_bails_on_pure_invariant_store() {
    // A store whose value never flows through the induction cvt is not an iota fill.
    let mut func = build_fill(false, false, false, 100, false, true);
    let mut pass = NeonFArrayPass::default();
    assert!(
        !pass.run(&mut func),
        "must BAIL when the stored value is not iota-derived"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), 0);
}

#[test]
fn fill_bails_on_overflow_risk_bound() {
    // A bound outside the `[1, i32::MAX]` exactness/consistency envelope => BAIL
    // (fail-closed: the `.4S` int index add could wrap differently than the scalar
    // i64 induction).
    let mut func = build_fill(false, false, false, i32::MAX as i64 + 1, false, false);
    let mut pass = NeonFArrayPass::default();
    assert!(
        !pass.run(&mut func),
        "must BAIL when the trip could exceed i32 range"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), 0);
}

#[test]
fn fill_is_byte_identical_without_the_shape() {
    // A pure-f64 reduction (no stores) must be untouched by the fill recognizer
    // (it belongs to the reduction path / scalar unroll).
    let mut func = build_loop(Kind::FusedDot, 1, 8, false, false);
    let before = func.insts.len();
    let mut pass = NeonFArrayPass::widening_only();
    // widening-only bails on the pure-f64 reduction AND there is no fill shape.
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.insts.len(),
        before,
        "no fill => byte-identical (no new insts)"
    );
}

#[test]
fn guards_are_signed_for_negative_start_induction() {
    // The vector header guard (`iv <s main_bound`) and the remainder-0 exit
    // guard (`iv >=s bound`) MUST be SIGNED: with the previous unsigned codes
    // (`LO`/`HS`), a NEGATIVE starting induction (`for (i=-k; i<n; i++)` over a
    // mid-array base) compared unsigned-huge, skipping the vector loop AND the
    // scalar tail — dropping every iteration (caught by differential test).
    let count_bcond = |func: &MachFunction, cc: i64| {
        func.blocks
            .iter()
            .flat_map(|blk| blk.insts.iter().copied())
            .filter(|&id| {
                let inst = func.inst(id);
                inst.opcode == AArch64Opcode::BCond && imm_of(&inst.operands[0]) == Some(cc)
            })
            .count()
    };
    let mut func = build_loop(Kind::FusedDot, 1, 4, true, false);
    let mut pass = NeonFArrayPass::new();
    assert!(pass.run(&mut func));
    const CC_LO: i64 = 3;
    const CC_HS: i64 = 2;
    assert_eq!(count_bcond(&func, CC_LO), 0, "no unsigned header guard");
    assert_eq!(count_bcond(&func, CC_HS), 0, "no unsigned exit guard");
    // Signed replacements: `bound < width` precheck + `iv <s main_bound` header
    // (both CC_LT) and the `iv >=s bound` remainder-0 exit guard (CC_GE).
    assert_eq!(
        count_bcond(&func, CC_LT),
        2,
        "signed precheck + header guard"
    );
    assert_eq!(
        count_bcond(&func, CC_GE),
        1,
        "signed remainder-0 exit guard"
    );
}
