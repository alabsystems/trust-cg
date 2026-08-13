// Unit tests for the `neon-bytesum` u64-accumulator byte-widening reduction
// vectorizer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::Signature;

fn x(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn w(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn i(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn bl(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn count(func: &MachFunction, op: AArch64Opcode) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}

/// How the reduction body should be built.
#[derive(Clone, Copy, PartialEq)]
enum Body {
    /// `acc(u64) += popcount(a[i])` — the v3_popcount shape (must FIRE).
    Popcount,
    /// `acc(u64) += a[i] as u64` — plain widen sum (must FIRE).
    Sum,
    /// popcount but the loop also STORES to the array (must BAIL).
    PopcountStore,
    /// popcount but the array index is a SIGNED byte load `Sxtb` (must BAIL).
    SignedByte,
}

/// Build the neon-time `for i in 0..N { acc += TERM(a[i]) }` loop over `[u8; N]`,
/// in the 3-block `{header, bounds-guard, body}` shape the bridge emits (with the
/// un-eliminated `TrapBoundsCheckExact`). Register map: v0=base(ptr), v4=N,
/// v47=iv, v49=acc.
fn build_bytesum_loop(body: Body, n: i64) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let guard = func.create_block();
    let latch = func.create_block(); // the body/latch
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader: base, N, iv=0, acc=0.
    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base ptr (loop-invariant)
    assert!(n >= 0, "test fixture only models non-negative trip counts");
    let n_bits = n as u64;
    push(
        &mut func,
        bb0,
        Movz,
        vec![x(4), i((n_bits & 0xFFFF) as i64)],
    ); // N, low halfword
    for shift in [16u32, 32, 48] {
        let halfword = (n_bits >> shift) & 0xFFFF;
        if halfword != 0 {
            push(
                &mut func,
                bb0,
                Movk,
                vec![x(4), i(halfword as i64), i(shift as i64)],
            );
        }
    }
    push(&mut func, bb0, Movz, vec![x(47), i(0)]); // iv = 0
    push(&mut func, bb0, Movz, vec![x(49), i(0)]); // acc = 0
    push(&mut func, bb0, B, vec![bl(header)]);

    // Header: cmp iv,N (unsigned); enter guard else exit.
    push(&mut func, header, MovR, vec![x(50), x(47)]);
    push(&mut func, header, CmpRR, vec![x(50), x(4)]);
    push(&mut func, header, BCond, vec![i(CC_LO), bl(guard)]);
    push(&mut func, header, B, vec![bl(exit)]);

    // Bounds guard: TrapBoundsCheckExact(iv, iv, N).
    push(&mut func, guard, MovR, vec![x(53), x(47)]);
    push(
        &mut func,
        guard,
        TrapBoundsCheckExact,
        vec![x(53), x(53), i(n)],
    );
    push(&mut func, guard, B, vec![bl(latch)]);

    // Body: load a[iv], compute the term, reduce, advance.
    match body {
        Body::SignedByte => {
            push(&mut func, latch, LdrbRO, vec![w(60), x(0), x(53), i(0)]);
            push(&mut func, latch, Sxtb, vec![w(61), w(60)]);
            push(&mut func, latch, Sxtw, vec![x(85), w(61)]);
        }
        _ => {
            // LdrbRO zero-extends the byte into a Gpr64.
            push(&mut func, latch, LdrbRO, vec![x(63), x(0), x(53), i(0)]);
        }
    }
    if body == Body::Popcount || body == Body::PopcountStore {
        // `& 0xFFFFFFFF` (the `as u32`), built Movz+Movk.
        push(&mut func, latch, Movz, vec![x(64), i(0xFFFF)]);
        push(&mut func, latch, Movk, vec![x(64), i(0xFFFF), i(16)]);
        push(&mut func, latch, AndRR, vec![x(65), x(63), x(64)]);
        // 64-bit SWAR popcount of v65 -> v81.
        push(&mut func, latch, LsrRI, vec![x(66), x(65), i(1)]);
        push(&mut func, latch, AndRI, vec![x(67), x(66), i(M55)]);
        push(&mut func, latch, SubRR, vec![x(68), x(65), x(67)]);
        push(&mut func, latch, AndRI, vec![x(69), x(68), i(M33)]);
        push(&mut func, latch, LsrRI, vec![x(70), x(68), i(2)]);
        push(&mut func, latch, AndRI, vec![x(71), x(70), i(M33)]);
        push(&mut func, latch, AddRR, vec![x(72), x(69), x(71)]);
        push(&mut func, latch, LsrRI, vec![x(73), x(72), i(4)]);
        push(&mut func, latch, AddRR, vec![x(74), x(72), x(73)]);
        push(&mut func, latch, AndRI, vec![x(75), x(74), i(M0F)]);
        push(&mut func, latch, LsrRI, vec![x(76), x(75), i(8)]);
        push(&mut func, latch, AddRR, vec![x(77), x(75), x(76)]);
        push(&mut func, latch, LsrRI, vec![x(78), x(77), i(16)]);
        push(&mut func, latch, AddRR, vec![x(79), x(77), x(78)]);
        push(&mut func, latch, LsrRI, vec![x(80), x(79), i(32)]);
        push(&mut func, latch, AddRR, vec![x(81), x(79), x(80)]);
        push(&mut func, latch, AndRI, vec![x(82), x(81), i(127)]);
        push(&mut func, latch, MovR, vec![w(83), x(82)]);
        push(&mut func, latch, Uxtw, vec![x(85), w(83)]);
    } else if body == Body::Sum {
        // acc += a[i] as u64: the byte (already zext in v63) widened.
        push(&mut func, latch, Uxtw, vec![x(85), w(63)]);
    }
    if body == Body::PopcountStore {
        // Store back into the array — must force a BAIL (whitelist rejects StrbRI).
        push(&mut func, latch, StrbRI, vec![w(83), x(0), i(0)]);
    }
    // Reduction + induction + writebacks.
    push(&mut func, latch, AddRR, vec![x(86), x(49), x(85)]); // acc + term
    push(&mut func, latch, Movz, vec![x(88), i(1)]);
    push(&mut func, latch, AddRR, vec![x(89), x(47), x(88)]); // iv + 1
    push(&mut func, latch, MovR, vec![x(49), x(86)]); // acc writeback
    push(&mut func, latch, MovR, vec![x(47), x(89)]); // iv writeback
    push(&mut func, latch, B, vec![bl(header)]);

    // Exit.
    push(&mut func, exit, B, vec![bl(exit)]);

    func.add_edge(bb0, header);
    func.add_edge(header, guard);
    func.add_edge(header, exit);
    func.add_edge(guard, latch);
    func.add_edge(latch, header);
    func
}

#[test]
fn fires_on_byte_popcount_sum_u64() {
    let mut func = build_bytesum_loop(Body::Popcount, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        pass.run(&mut func),
        "should vectorize acc(u64) += popcount(a[i])"
    );
    assert_eq!(pass.fired(), 1);
    // 4 zeroed accumulators + the ones vector, 2 LDP q,q (4 Q regs), CNT +
    // UDOT-by-ones per acc (the widen chain is fused into the proven UDOT).
    assert_eq!(
        count(&func, AArch64Opcode::NeonMovi),
        unroll(TermKind::Popcount) + 1,
        "zeroed accs + ones"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        unroll(TermKind::Popcount) / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCntV),
        unroll(TermKind::Popcount),
        "per-byte popcount"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        unroll(TermKind::Popcount),
        "UDOT-by-ones fold"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUaddlpV),
        0,
        "no UADDLP chain (fused into UDOT)"
    );
    assert!(count(&func, AArch64Opcode::NeonAddV) >= 3, "combine adds");
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        4,
        "reduce 4 lanes"
    );
    // The horizontal fold zero-extends each i32 lane to u64 before the scalar add.
    assert!(
        count(&func, AArch64Opcode::Uxtw) >= 4,
        "lane zero-extend to u64"
    );
}

#[test]
fn fires_on_plain_byte_sum_u64() {
    let mut func = build_bytesum_loop(Body::Sum, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        pass.run(&mut func),
        "should vectorize acc(u64) += a[i] as u64"
    );
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonCntV),
        0,
        "no popcount for a plain sum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        unroll(TermKind::ByteSum),
        "UDOT-by-ones fold (8 accumulators for the plain byte sum)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUaddlpV),
        0,
        "no UADDLP chain (fused into UDOT)"
    );
}

#[test]
fn wide_trip_bound_uses_movz_movk_chain() {
    // REGRESSION (#366 / large-stack-array O3 completeness): a big compile-time
    // bound `N` makes the vector trip bound `N - (width-1)` exceed the 16-bit
    // `MOVZ` immediate field. It MUST be materialized as a `MOVZ`(lo16) +
    // `MOVK`(hi16, LSL #16) chain — a single `Movz #<wide>` fails closed at the
    // encoder (`MovImmTooWide`), which previously blocked e.g. a `[u8; 100_000]`
    // byte-sum at O3. Here N = 100_000, width = unroll(ByteSum)*16 = 128, so the
    // bound is 99_873 = 0x1_8621 (lo = 0x8621, hi = 0x1).
    let n: i64 = 100_000;
    let mut func = build_bytesum_loop(Body::Sum, n);
    let mut pass = NeonBytesumPass::new();
    assert!(pass.run(&mut func), "should vectorize the large-N byte sum");
    assert_eq!(pass.fired(), 1);

    let width = unroll(TermKind::ByteSum) as i64 * LANES_PER_Q;
    let bound = n - (width - 1);
    assert!(
        bound > 0xFFFF,
        "test premise: the bound must exceed 16 bits"
    );
    let lo = bound & 0xFFFF;
    let hi = (bound >> 16) & 0xFFFF;

    // (1) The pass must NOT emit the bound as one wide `Movz #bound` — that is the
    //     exact instruction that fails closed at the encoder.
    let wide_movz = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .filter(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::Movz
                && inst.operands.len() == 2
                && matches!(inst.operands[1], MachOperand::Imm(v) if v == bound)
        })
        .count();
    assert_eq!(
        wide_movz, 0,
        "the vector trip bound must not be a single Movz #{bound}"
    );

    // (2) It must instead be an ADJACENT `Movz Rd,#lo` ; `Movk Rd,#hi,LSL #16`
    //     into the SAME register, reconstructing the bound EXACTLY.
    let mut found_chain = false;
    for blk in &func.blocks {
        for pair in blk.insts.windows(2) {
            let a = func.inst(pair[0]);
            let b = func.inst(pair[1]);
            if a.opcode != AArch64Opcode::Movz || b.opcode != AArch64Opcode::Movk {
                continue;
            }
            let same_dst = a.operands.first() == b.operands.first();
            let a_lo = matches!(a.operands.get(1), Some(&MachOperand::Imm(v)) if v == lo);
            let b_hi = matches!(b.operands.get(1), Some(&MachOperand::Imm(v)) if v == hi);
            let b_shift = matches!(b.operands.get(2), Some(&MachOperand::Imm(s)) if s == 16);
            if same_dst && a_lo && b_hi && b_shift {
                found_chain = true;
            }
        }
    }
    assert!(
        found_chain,
        "expected an adjacent Movz #{lo:#x} ; Movk #{hi:#x}, LSL #16 reconstructing the bound {bound:#x}"
    );

    // The input fixture and transformed function must contain no impossible
    // wide MOVZ immediate. This makes the optimizer regression representative
    // of a function that can actually proceed to code emission.
    for inst in func
        .blocks
        .iter()
        .flat_map(|block| block.insts.iter().map(|&id| func.inst(id)))
        .filter(|inst| inst.opcode == AArch64Opcode::Movz)
    {
        assert!(
            matches!(inst.operands.get(1), Some(MachOperand::Imm(v)) if (0..=0xFFFF).contains(v)),
            "fixture/pass emitted an unencodable MOVZ: {:?}",
            inst.operands
        );
        assert!(
            matches!(inst.operands.get(2), None | Some(MachOperand::Imm(0))),
            "fixture/pass emitted an invalid MOVZ shift: {:?}",
            inst.operands
        );
    }
}

#[test]
fn bails_when_array_is_stored() {
    let mut func = build_bytesum_loop(Body::PopcountStore, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: a store makes the loop not read-only"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCntV), 0);
}

#[test]
fn bails_on_signed_byte() {
    let mut func = build_bytesum_loop(Body::SignedByte, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: Sxtb sign-extend is not a byte-local term"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
}

#[test]
fn bails_when_bound_exceeds_overflow_safe_max() {
    // A popcount bound >= 2^28 could overflow the i32 `.4S` partials -> BAIL.
    let mut func = build_bytesum_loop(Body::Popcount, MAX_BOUND_POP);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL at the .4S overflow-safe bound"
    );
}

#[test]
fn detects_64bit_swar_popcount() {
    // The SWAR detector in isolation: build the 17-inst chain and confirm it
    // resolves to the input; a corrupted mask must refute.
    use AArch64Opcode::*;
    let mut func = MachFunction::new("s".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let push = |func: &mut MachFunction, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(bb0, id);
    };
    push(&mut func, Copy, vec![x(65), x(65)]); // the input
    push(&mut func, LsrRI, vec![x(66), x(65), i(1)]);
    push(&mut func, AndRI, vec![x(67), x(66), i(M55)]);
    push(&mut func, SubRR, vec![x(68), x(65), x(67)]);
    push(&mut func, AndRI, vec![x(69), x(68), i(M33)]);
    push(&mut func, LsrRI, vec![x(70), x(68), i(2)]);
    push(&mut func, AndRI, vec![x(71), x(70), i(M33)]);
    push(&mut func, AddRR, vec![x(72), x(69), x(71)]);
    push(&mut func, LsrRI, vec![x(73), x(72), i(4)]);
    push(&mut func, AddRR, vec![x(74), x(72), x(73)]);
    push(&mut func, AndRI, vec![x(75), x(74), i(M0F)]);
    push(&mut func, LsrRI, vec![x(76), x(75), i(8)]);
    push(&mut func, AddRR, vec![x(77), x(75), x(76)]);
    push(&mut func, LsrRI, vec![x(78), x(77), i(16)]);
    push(&mut func, AddRR, vec![x(79), x(77), x(78)]);
    push(&mut func, LsrRI, vec![x(80), x(79), i(32)]);
    push(&mut func, AddRR, vec![x(81), x(79), x(80)]);
    push(&mut func, AndRI, vec![x(82), x(81), i(127)]);
    let def = build_def_map(&func);
    let got = detect_ctpop_swar_i64(&func, &def, VReg::new(82, RegClass::Gpr64));
    assert_eq!(
        got,
        Some(VReg::new(65, RegClass::Gpr64)),
        "SWAR64 -> input v65"
    );
}

// ===========================================================================
// Count-if `== 0` conditional-increment diamond (`PredCountEqZero`).
// ===========================================================================

/// Build the neon-time `while i<N { if a[i]==0 { c+=1 } }` count loop over a
/// `[u8; N]` in the BRANCH-based diamond shape the bridge emits (mirrors
/// p7_sieve): a `LDRB; Uxtb; Cbz` predicate head, a `+1` arm, a `+0` arm, and a
/// phi-merge `c = MovR(merge)` in the latch (both arms write the common vreg
/// `merge`). Register map: v0=base(ptr), v4=N, v47=iv, v49=acc(count).
///
/// * `inc_imm`  — the increment amount (1 fires; anything else must BAIL).
/// * `use_cbnz` — `Cbnz` instead of `Cbz` (increment on the NON-zero arm =
///   `!= 0`; must BAIL under the `== 0` scope).
/// * `signed`   — a signed `Sxtb` byte load (must BAIL).
fn build_countif_loop(inc_imm: i64, use_cbnz: bool, signed: bool, n: i64) -> MachFunction {
    let mut func = MachFunction::new("cif".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let guard = func.create_block();
    let dh = func.create_block(); // diamond head: load + Cbz/Cbnz
    let inc = func.create_block(); // "+inc_imm" arm
    let zero = func.create_block(); // "+0" arm
    let latch = func.create_block(); // join / phi-merge + induction
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader: base, N, iv=0, acc=0.
    push(&mut func, bb0, Copy, vec![x(0), x(0)]);
    push(&mut func, bb0, Movz, vec![x(4), i(n)]);
    push(&mut func, bb0, Movz, vec![x(47), i(0)]);
    push(&mut func, bb0, Movz, vec![x(49), i(0)]);
    push(&mut func, bb0, B, vec![bl(header)]);

    // Header: cmp iv,N (unsigned); enter guard else exit.
    push(&mut func, header, MovR, vec![x(50), x(47)]);
    push(&mut func, header, CmpRR, vec![x(50), x(4)]);
    push(&mut func, header, BCond, vec![i(CC_LO), bl(guard)]);
    push(&mut func, header, B, vec![bl(exit)]);

    // Bounds guard: TrapBoundsCheckExact(iv, iv, N).
    push(&mut func, guard, MovR, vec![x(53), x(47)]);
    push(
        &mut func,
        guard,
        TrapBoundsCheckExact,
        vec![x(53), x(53), i(n)],
    );
    push(&mut func, guard, B, vec![bl(dh)]);

    // Diamond head: addr = base+iv; load byte; extend; branch on == 0.
    push(&mut func, dh, AddRR, vec![x(88), x(0), x(53)]);
    push(&mut func, dh, LdrbRI, vec![w(90), x(88), i(0)]);
    if signed {
        push(&mut func, dh, Sxtb, vec![w(91), w(90)]);
    } else {
        push(&mut func, dh, Uxtb, vec![w(91), w(90)]);
    }
    // Cbz w,inc / B zero  (increment on the byte-zero arm  = `== 0`);
    // Cbnz w,inc / B zero (increment on the NON-zero arm    = `!= 0`, BAIL).
    let br = if use_cbnz { Cbnz } else { Cbz };
    push(&mut func, dh, br, vec![w(91), bl(inc)]);
    push(&mut func, dh, B, vec![bl(zero)]);

    // "+inc_imm" arm: merge = acc + inc_imm.
    push(&mut func, inc, AddRI, vec![x(93), x(49), i(inc_imm)]);
    push(&mut func, inc, MovR, vec![x(94), x(93)]);
    push(&mut func, inc, B, vec![bl(latch)]);

    // "+0" arm: merge = acc.
    push(&mut func, zero, MovR, vec![x(94), x(49)]);
    push(&mut func, zero, B, vec![bl(latch)]);

    // Latch: advance iv; phi-merge writeback acc = merge.
    push(&mut func, latch, AddRI, vec![x(96), x(47), i(1)]);
    push(&mut func, latch, MovR, vec![x(47), x(96)]); // iv writeback
    push(&mut func, latch, MovR, vec![x(49), x(94)]); // acc = merge
    push(&mut func, latch, B, vec![bl(header)]);

    // Exit reads the final count (outside the loop body).
    push(&mut func, exit, AddRR, vec![x(6), x(49), x(49)]);
    push(&mut func, exit, B, vec![bl(exit)]);

    func.add_edge(bb0, header);
    func.add_edge(header, guard);
    func.add_edge(header, exit);
    func.add_edge(guard, dh);
    func.add_edge(dh, inc);
    func.add_edge(dh, zero);
    func.add_edge(inc, latch);
    func.add_edge(zero, latch);
    func.add_edge(latch, header);
    func
}

#[test]
fn fires_on_count_if_eq_zero_u64() {
    let mut func = build_countif_loop(1, false, false, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        pass.run(&mut func),
        "should vectorize count-if `if a[i]==0 {{ c+=1 }}`"
    );
    assert_eq!(pass.fired(), 1);
    // CMEQ.16B (0xFF per zero byte) + AND.16B (collapse to 0x01), one per Q reg.
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmeqV),
        unroll(TermKind::PredCountEqZero),
        "one CMEQ per Q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAndV),
        unroll(TermKind::PredCountEqZero),
        "one AND (0xFF->0x01) per Q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCntV),
        0,
        "no popcount for a count-if"
    );
    // Shared fold: one UDOT-by-ones per acc, 4 zeroed accs + vzero + vone
    // MOVIs, 4 lane extracts, zero-extend each i32 lane to u64.
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        unroll(TermKind::PredCountEqZero),
        "UDOT-by-ones fold"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUaddlpV),
        0,
        "no UADDLP chain (fused into UDOT)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonMovi),
        unroll(TermKind::PredCountEqZero) + 2,
        "4 accs + vzero + vone"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        4,
        "reduce 4 lanes"
    );
    assert!(
        count(&func, AArch64Opcode::Uxtw) >= 4,
        "lane zero-extend to u64"
    );
}

#[test]
fn bails_on_count_if_ne_zero() {
    // Cbnz increments on the NON-zero arm (`!= 0`) — out of the `== 0` scope.
    let mut func = build_countif_loop(1, true, false, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: `!= 0` predicate is not yet supported"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), 0);
}

#[test]
fn bails_on_count_if_plus_two() {
    // The guarded arm adds +2, not +1 — not a count.
    let mut func = build_countif_loop(2, false, false, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: non-+1 increment is not a count"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), 0);
}

#[test]
fn bails_on_count_if_signed_byte() {
    // A signed `Sxtb` byte load is neither whitelisted nor a byte-local term.
    let mut func = build_countif_loop(1, false, true, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(!pass.run(&mut func), "must BAIL: signed byte load");
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), 0);
}

#[test]
fn bails_on_count_if_runtime_bound() {
    // A runtime (non-constant) bound: replace the `Movz N` with a load-like
    // opaque def so the single-N agreement finds no constant.
    let mut func = build_countif_loop(1, false, false, 4096);
    // Rewrite the `Movz v4,#N` to `Uxtw v4, w4` (an opaque, non-constant def).
    for inst in func.insts.iter_mut() {
        if inst.opcode == AArch64Opcode::Movz
            && vreg_of(&inst.operands[0]) == Some(VReg::new(4, RegClass::Gpr64))
        {
            *inst = MachInst::new(
                AArch64Opcode::Uxtw,
                vec![x(4), MachOperand::VReg(VReg::new(400, RegClass::Gpr32))],
            );
        }
    }
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: runtime bound is not `.4S`-overflow-safe"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), 0);
}

#[test]
fn count_if_ones_mask_is_all_lanes() {
    // The `0xFF -> 0x01` collapse mask MUST be 0x01 in ALL 16 byte lanes. We
    // emit it as the byte-form `MOVI` (`NeonMovi #1` == `MOVI Vd.16B, #1`, which
    // the encoder replicates to every byte lane); a low-lane-only scalar `1`
    // would undercount. Assert exactly one `NeonMovi #1` (Fpr128) is emitted and
    // that EVERY `NeonAndV` reads it as its mask operand.
    let mut func = build_countif_loop(1, false, false, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(pass.run(&mut func));

    let ones: Vec<VReg> = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter_map(|id| {
            let inst = func.inst(id);
            (inst.opcode == AArch64Opcode::NeonMovi && imm_of(&inst.operands[1]) == Some(1))
                .then(|| vreg_of(&inst.operands[0]).unwrap())
        })
        .collect();
    assert_eq!(ones.len(), 1, "exactly one all-lanes ones mask (MOVI #1)");
    let vone = ones[0];
    assert_eq!(
        vone.class,
        RegClass::Fpr128,
        "ones mask is a 128-bit vector"
    );

    // A zero comparand (MOVI #0) must also exist for the CMEQ.
    let zeros = count(&func, AArch64Opcode::NeonMovi);
    assert_eq!(
        zeros,
        unroll(TermKind::PredCountEqZero) + 2,
        "MOVIs = 4 accs(#0) + vzero(#0) + vone(#1)"
    );

    // Every AND folds against `vone`.
    let and_reads_vone = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == AArch64Opcode::NeonAndV)
        .all(|id| {
            func.inst(id)
                .operands
                .iter()
                .any(|o| vreg_of(o) == Some(vone))
        });
    assert!(
        and_reads_vone,
        "each AND collapses 0xFF->0x01 against the all-lanes ones mask"
    );
}

// ===========================================================================
// FORWARD bounds-guarded `while i<N` CHAIN shape with a `u32` accumulator —
// the e07_bytesum ground-truth shape (CSet-materialized guards, latch-local
// base/index copy chains, `Gpr32` acc `s = s.wrapping_add(a[i] as u32)`).
// ===========================================================================

/// Build the e07-shaped chain loop, mirroring the bridge's MIR:
///
/// ```text
/// header: iv' = MovR(iv); N = Movz; CmpRR(iv', N); CSet(c, LO); CmpRI(c, 0);
///         BCond(NE, bounds); B(exit)
/// bounds: iv'' = MovR(iv); N' = Movz; CmpRR(iv'', N'); CSet(c', LO);
///         CmpRI(c', 0); BCond(NE, latch); B(panic)
/// latch:  b0 = MovR(base); b1 = MovR(b0); ix = MovR(iv''); addr = AddRR(b1, ix);
///         a = MovR(addr); byte = LdrbRI(a, 0); z = Uxtb(byte);
///         s' = AddRR(acc32, z); s'' = MovR(s'); iv+ = AddRI(iv, 1);
///         acc32 = MovR(s''); iv = MovR(iv+); B(header)
/// ```
///
/// * `early_exit` — insert a data-dependent `Cbz(byte) -> exit` block between
///   `bounds` and `latch` (a `break`); MUST BAIL (the chain gate rejects any
///   in-body branch not controlled by `iv <u N`).
fn build_u32_chain_loop(early_exit: bool, n: i64) -> MachFunction {
    let mut func = MachFunction::new("e07".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let bounds = func.create_block();
    let brk = if early_exit {
        Some(func.create_block())
    } else {
        None
    };
    let latch = func.create_block();
    let exit = func.create_block();
    let panic = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader: base, iv=0, acc32 seeded with a loop-invariant value.
    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base ptr
    push(&mut func, bb0, Movz, vec![x(40), i(0)]); // iv = 0
    push(&mut func, bb0, Movz, vec![w(41), i(7)]); // acc(u32) = seed r
    push(&mut func, bb0, B, vec![bl(header)]);

    // Header: CSet-materialized `iv <u N` continue guard.
    push(&mut func, header, MovR, vec![x(43), x(40)]);
    push(&mut func, header, Movz, vec![x(44), i(n)]);
    push(&mut func, header, CmpRR, vec![x(43), x(44)]);
    push(&mut func, header, CSet, vec![x(45), i(CC_LO)]);
    push(&mut func, header, CmpRI, vec![x(45), i(0)]);
    push(&mut func, header, BCond, vec![i(CC_NE), bl(bounds)]);
    push(&mut func, header, B, vec![bl(exit)]);

    // Bounds diamond: the same CSet-materialized `iv <u N` (panic edge out).
    let bounds_next = brk.unwrap_or(latch);
    push(&mut func, bounds, MovR, vec![x(46), x(40)]);
    push(&mut func, bounds, Movz, vec![x(47), i(n)]);
    push(&mut func, bounds, CmpRR, vec![x(46), x(47)]);
    push(&mut func, bounds, CSet, vec![x(48), i(CC_LO)]);
    push(&mut func, bounds, CmpRI, vec![x(48), i(0)]);
    push(&mut func, bounds, BCond, vec![i(CC_NE), bl(bounds_next)]);
    push(&mut func, bounds, B, vec![bl(panic)]);

    // Optional data-dependent early exit (`break` on a zero byte) — MUST BAIL.
    if let Some(brk) = brk {
        push(&mut func, brk, AddRR, vec![x(98), x(0), x(46)]);
        push(&mut func, brk, LdrbRI, vec![w(99), x(98), i(0)]);
        push(&mut func, brk, Cbz, vec![w(99), bl(exit)]);
        push(&mut func, brk, B, vec![bl(latch)]);
    }

    // Latch (the copy-propagated neon-time shape): direct `base + iv`
    // addressing, byte load, u32 reduce, iv writeback.
    push(&mut func, latch, AddRR, vec![x(52), x(0), x(40)]);
    push(&mut func, latch, LdrbRI, vec![w(54), x(52), i(0)]);
    push(&mut func, latch, Uxtb, vec![w(55), w(54)]);
    push(&mut func, latch, AddRR, vec![w(56), w(41), w(55)]); // acc32 + byte
    push(&mut func, latch, AddRI, vec![x(59), x(40), i(1)]);
    push(&mut func, latch, MovR, vec![w(41), w(56)]); // acc writeback
    push(&mut func, latch, MovR, vec![x(40), x(59)]); // iv writeback
    push(&mut func, latch, B, vec![bl(header)]);

    // Exit / panic.
    push(&mut func, exit, B, vec![bl(exit)]);
    push(&mut func, panic, B, vec![bl(panic)]);

    func.add_edge(bb0, header);
    func.add_edge(header, bounds);
    func.add_edge(header, exit);
    if let Some(brk) = brk {
        func.add_edge(bounds, brk);
        func.add_edge(brk, latch);
        func.add_edge(brk, exit);
    } else {
        func.add_edge(bounds, latch);
    }
    func.add_edge(bounds, panic);
    func.add_edge(latch, header);
    func
}

#[test]
fn fires_on_u32_acc_chain_byte_sum() {
    let mut func = build_u32_chain_loop(false, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        pass.run(&mut func),
        "should vectorize the e07 u32-acc chain byte sum"
    );
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonCntV),
        0,
        "no popcount for a plain sum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        unroll(TermKind::ByteSum),
        "UDOT-by-ones fold (8 accumulators for the plain byte sum)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUaddlpV),
        0,
        "no UADDLP chain (fused into UDOT)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        unroll(TermKind::ByteSum) / 2,
        "4 LDP q,q (128B per iteration)"
    );
    // The u32 fold: the final add into the acc must be the 32-bit `AddRR` whose
    // dst/lhs is the `Gpr32` acc (truncating the u64 partial mod 2^32), and the
    // truncation `MovR Gpr32 <- Gpr64` must exist.
    let acc = VReg::new(41, RegClass::Gpr32);
    let fold_adds = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::AddRR
                && vreg_of(&inst.operands[0]) == Some(acc)
                && vreg_of(&inst.operands[1]) == Some(acc)
        })
        .count();
    assert_eq!(
        fold_adds, 1,
        "exactly one `acc += partial` fold into the u32 acc"
    );
    let trunc = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .any(|id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::MovR
                && inst.operands.len() == 2
                && vreg_of(&inst.operands[0]).is_some_and(|d| d.class == RegClass::Gpr32)
                && vreg_of(&inst.operands[1]).is_some_and(|s| s.class == RegClass::Gpr64)
        });
    assert!(
        trunc,
        "the u64 partial is truncated to u32 (MovR Gpr32 <- Gpr64)"
    );
}

#[test]
fn bails_on_data_early_exit_chain() {
    // A `break`-like data-dependent exit inside the chain: the vector prefix
    // would reduce past the break point -> MUST BAIL (the chain gate rejects
    // the non-`iv<N` branch). Without the gate this shape would MISCOMPILE.
    let mut func = build_u32_chain_loop(true, 4096);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: data-dependent early exit in the chain"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
}

#[test]
fn reconstructs_movz_movk_u32_mask() {
    use AArch64Opcode::*;
    let mut func = MachFunction::new("c".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let id0 = func.push_inst(MachInst::new(Movz, vec![x(64), i(0xFFFF)]));
    func.append_inst(bb0, id0);
    let id1 = func.push_inst(MachInst::new(Movk, vec![x(64), i(0xFFFF), i(16)]));
    func.append_inst(bb0, id1);
    let def = build_def_map(&func);
    assert_eq!(
        const_value(&func, &def, VReg::new(64, RegClass::Gpr64)),
        Some(0xFFFF_FFFF),
        "Movz(0xFFFF)+Movk(0xFFFF,16) == 0xFFFFFFFF"
    );
}

// ===========================================================================
// Per-kind width gate: ByteSum uses 8 accumulators / 128B per iteration, so a
// ByteSum loop with 64 <= N < 128 must stay fully scalar (fail-closed), while
// Popcount / PredCountEqZero keep firing at their unchanged 64B width.
// ===========================================================================

#[test]
fn bytesum_bails_below_its_128b_width() {
    // 64 <= N < 128: too small for one full 8-accumulator iteration -> BAIL.
    for n in [64, 100, 127] {
        let mut func = build_u32_chain_loop(false, n);
        let mut pass = NeonBytesumPass::new();
        assert!(
            !pass.run(&mut func),
            "ByteSum N={} < width 128 must stay scalar",
            n
        );
        assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
    }
    // Same gate on the u64-acc shape.
    let mut func = build_bytesum_loop(Body::Sum, 127);
    let mut pass = NeonBytesumPass::new();
    assert!(!pass.run(&mut func), "u64 ByteSum N=127 must stay scalar");
    assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
}

#[test]
fn bytesum_fires_at_exactly_its_128b_width() {
    let mut func = build_u32_chain_loop(false, 128);
    let mut pass = NeonBytesumPass::new();
    assert!(pass.run(&mut func), "ByteSum N=128 == width must fire");
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        unroll(TermKind::ByteSum)
    );
}

#[test]
fn popcount_still_fires_below_128() {
    // The 4-accumulator kinds keep the original 64B width: N in [64, 128)
    // still fires for popcount (codegen for these kinds is unchanged).
    let mut func = build_bytesum_loop(Body::Popcount, 100);
    let mut pass = NeonBytesumPass::new();
    assert!(pass.run(&mut func), "Popcount N=100 >= width 64 must fire");
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        unroll(TermKind::Popcount)
    );
}

#[test]
fn countif_still_fires_below_128() {
    let mut func = build_countif_loop(1, false, false, 100);
    let mut pass = NeonBytesumPass::new();
    assert!(pass.run(&mut func), "count-if N=100 >= width 64 must fire");
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmeqV),
        unroll(TermKind::PredCountEqZero)
    );
}

// ===========================================================================
// Masked-byte compare (`PredMaskCmp`): `acc(u64) += ((a[i] & MASK) OP CONST)`
// materialized by a `CSet` (STRAIGHT AddRR reduction, NOT a branch diamond).
// The UTF-8 code-point-start count `(b & 0xC0) != 0x80` is this shape.
// ===========================================================================

/// Build the neon-time masked-compare reduction loop over `[u8; N]`, in the
/// 3-block `{header, bounds-guard, body}` shape with an un-eliminated
/// `TrapBoundsCheckExact`. Body chain (mirrors the bridge disasm):
/// `LDRB w60,[base,iv]; AND w61,w60,#MASK; UXTB w62,w61; CMP w62,#CONST;
///  CSET x85,cc; acc += x85`. Register map: v0=base, v4=N, v47=iv, v49=acc.
///
/// * `ne`      — `!=` (CSet NE) vs `==` (CSet EQ).
/// * `acc_u32` — make the accumulator a `Gpr32` (must BAIL: the masked-compare
///   fold is scoped to a `u64` acc).
fn build_maskcmp_loop(mask: i64, cnst: i64, ne: bool, n: i64, acc_u32: bool) -> MachFunction {
    let mut func = MachFunction::new("mc".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let guard = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    let cc = if ne { CC_NE } else { CC_EQ };
    // The accumulator + its reduction operands are `Gpr32` for the u32 variant.
    let acc = |id: u32| if acc_u32 { w(id) } else { x(id) };
    // The CSet boolean term (id 85), read by the reduction at the acc's width.
    let term = |id: u32| if acc_u32 { w(id) } else { x(id) };

    // Preheader: base, N, iv=0, acc=0.
    push(&mut func, bb0, Copy, vec![x(0), x(0)]);
    push(&mut func, bb0, Movz, vec![x(4), i(n)]);
    push(&mut func, bb0, Movz, vec![x(47), i(0)]);
    push(&mut func, bb0, Movz, vec![acc(49), i(0)]);
    push(&mut func, bb0, B, vec![bl(header)]);

    // Header: cmp iv,N (unsigned); enter guard else exit.
    push(&mut func, header, MovR, vec![x(50), x(47)]);
    push(&mut func, header, CmpRR, vec![x(50), x(4)]);
    push(&mut func, header, BCond, vec![i(CC_LO), bl(guard)]);
    push(&mut func, header, B, vec![bl(exit)]);

    // Bounds guard: TrapBoundsCheckExact(iv, iv, N).
    push(&mut func, guard, MovR, vec![x(53), x(47)]);
    push(
        &mut func,
        guard,
        TrapBoundsCheckExact,
        vec![x(53), x(53), i(n)],
    );
    push(&mut func, guard, B, vec![bl(latch)]);

    // Body: LDRB; AND #MASK; UXTB; CMP #CONST; CSET cc; reduce; advance.
    push(&mut func, latch, LdrbRO, vec![w(60), x(0), x(53), i(0)]);
    push(&mut func, latch, AndRI, vec![w(61), w(60), i(mask)]);
    push(&mut func, latch, Uxtb, vec![w(62), w(61)]);
    push(&mut func, latch, CmpRI, vec![w(62), i(cnst)]);
    push(&mut func, latch, CSet, vec![x(85), i(cc)]);
    push(&mut func, latch, AddRR, vec![acc(86), acc(49), term(85)]); // acc + term
    push(&mut func, latch, Movz, vec![x(88), i(1)]);
    push(&mut func, latch, AddRR, vec![x(89), x(47), x(88)]); // iv + 1
    push(&mut func, latch, MovR, vec![acc(49), acc(86)]); // acc writeback
    push(&mut func, latch, MovR, vec![x(47), x(89)]); // iv writeback
    push(&mut func, latch, B, vec![bl(header)]);

    // Exit.
    push(&mut func, exit, B, vec![bl(exit)]);

    func.add_edge(bb0, header);
    func.add_edge(header, guard);
    func.add_edge(header, exit);
    func.add_edge(guard, latch);
    func.add_edge(latch, header);
    func
}

#[test]
fn fires_on_maskcmp_ne_u64() {
    // The UTF-8 code-point-start count `(b & 0xC0) != 0x80`.
    let mut func = build_maskcmp_loop(0xC0, 0x80, true, 1024, false);
    let mut pass = NeonBytesumPass::new();
    assert!(
        pass.run(&mut func),
        "should vectorize acc(u64) += ((a[i] & 0xC0) != 0x80)"
    );
    assert_eq!(pass.fired(), 1);
    let ur = unroll(TermKind::PredMaskCmp {
        mask: 0xC0,
        cnst: 0x80,
        ne: true,
    });
    assert_eq!(ur, 4);
    // One CMEQ (`(b&MASK)==CONST`) per Q reg; one NOT per Q (the `!=` inversion).
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), ur, "one CMEQ per Q");
    assert_eq!(
        count(&func, AArch64Opcode::NeonNotV),
        ur,
        "one NOT per Q (the `!=` inversion)"
    );
    // Two ANDs per Q: `& vmask` (isolate) and `& vone` (0xFF->0x01 collapse).
    assert_eq!(
        count(&func, AArch64Opcode::NeonAndV),
        2 * ur,
        "AND(mask) + AND(collapse) per Q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        ur,
        "UDOT-by-ones fold"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCntV), 0, "no popcount");
    // MOVIs: 4 zeroed accs + vone(#1) + vmask(#0xC0) + vcnst(#0x80). No vzero.
    assert_eq!(
        count(&func, AArch64Opcode::NeonMovi),
        ur + 3,
        "4 accs + vone + vmask + vcnst"
    );
    // The comparand vectors carry the exact byte constants.
    let has_movi = |imm8: i64| {
        func.blocks
            .iter()
            .flat_map(|b| b.insts.iter().copied())
            .any(|id| {
                let inst = func.inst(id);
                inst.opcode == AArch64Opcode::NeonMovi && imm_of(&inst.operands[1]) == Some(imm8)
            })
    };
    assert!(has_movi(0xC0), "vmask broadcasts MASK=0xC0");
    assert!(has_movi(0x80), "vcnst broadcasts CONST=0x80");
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        4,
        "reduce 4 lanes"
    );
}

#[test]
fn fires_on_maskcmp_eq_u64_no_invert() {
    // `== CONST`: same prefix WITHOUT the NOT inversion.
    let mut func = build_maskcmp_loop(0xC0, 0x80, false, 1024, false);
    let mut pass = NeonBytesumPass::new();
    assert!(pass.run(&mut func), "should vectorize the `== CONST` form");
    assert_eq!(pass.fired(), 1);
    let ur = unroll(TermKind::PredMaskCmp {
        mask: 0xC0,
        cnst: 0x80,
        ne: false,
    });
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), ur);
    assert_eq!(
        count(&func, AArch64Opcode::NeonNotV),
        0,
        "no inversion for `==`"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonAndV), 2 * ur);
    assert_eq!(count(&func, AArch64Opcode::NeonUdotV), ur);
}

#[test]
fn bails_on_maskcmp_u32_acc() {
    // The masked-compare fold is scoped to a `u64` acc (the `.4S` lane partials
    // zero-extend to u64). A `u32` acc must BAIL fail-closed.
    let mut func = build_maskcmp_loop(0xC0, 0x80, true, 1024, true);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: maskcmp requires a u64 acc"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), 0);
    assert_eq!(count(&func, AArch64Opcode::NeonNotV), 0);
}

#[test]
fn bails_on_maskcmp_const_out_of_byte_range() {
    // CONST must be a byte (0..=255): a wider compare is not this idiom.
    let mut func = build_maskcmp_loop(0xC0, 300, true, 1024, false);
    let mut pass = NeonBytesumPass::new();
    assert!(!pass.run(&mut func), "must BAIL: CONST out of byte range");
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), 0);
}

#[test]
fn bails_on_maskcmp_mask_out_of_byte_range() {
    // MASK must be a byte (0..=255).
    let mut func = build_maskcmp_loop(0x1C0, 0x80, true, 1024, false);
    let mut pass = NeonBytesumPass::new();
    assert!(!pass.run(&mut func), "must BAIL: MASK out of byte range");
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), 0);
}

#[test]
fn maskcmp_bails_below_64b_width() {
    // 4 accumulators / 64B per iteration: N < 64 stays fully scalar.
    let mut func = build_maskcmp_loop(0xC0, 0x80, true, 48, false);
    let mut pass = NeonBytesumPass::new();
    assert!(!pass.run(&mut func), "N=48 < width 64 must stay scalar");
    assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
}

// ===========================================================================
// Byte-STENCIL count-if diamond (`if a[j] REL a[j-1] { runs += 1 }`,
// PredStencilCmp) — the RLE "count runs" shape.
// ===========================================================================

/// Build the neon-time byte-stencil count-if loop
/// `while j<N { if a[j] REL a[j-1] { runs += 1 } j += 1 }` in the EXACT block
/// shape the bridge emits (verified against the k6_rle_countruns MachIR dump):
/// header guard, a pass-through, a block that loads `a[j]` and bounds-checks
/// `j-delta`, the two-byte-compare diamond head, `+1` / `+0` arms, and a
/// phi-merge latch. Register map: v0=base, v43=const(delta), v46=iv, v47=acc.
///
/// * `ne`        — count `!=` (true) or `==` (false): the head branches to the
///   `+1` arm on that relation.
/// * `iv_init`   — the induction's initial value (MUST be 1 to fire).
/// * `pred_delta`— the predecessor stride: 1 = `a[j-1]` (fires); 2 = `a[j-2]`
///   (non-adjacent, must BAIL).
fn build_stencil_loop(ne: bool, iv_init: i64, n: i64, pred_delta: i64) -> MachFunction {
    let mut func = MachFunction::new("stencil".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let guard = func.create_block(); // pass-through (copies iv)
    let load = func.create_block(); // a[j] load + (j-delta) bounds diamond
    let dh = func.create_block(); // diamond head: a[j-delta] load + two-byte cmp
    let inc = func.create_block(); // "+1" arm
    let zero = func.create_block(); // "+0" arm
    let latch = func.create_block(); // join / phi-merge + induction
    let exit = func.create_block();
    let panic = func.create_block(); // predecessor-bounds-fail (out of body)

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader: base, const delta, iv=iv_init, acc(runs)=1 (seed).
    push(&mut func, bb0, Copy, vec![x(0), x(0)]);
    push(&mut func, bb0, Movz, vec![x(43), i(pred_delta)]);
    push(&mut func, bb0, Movz, vec![x(46), i(iv_init)]);
    push(&mut func, bb0, Movz, vec![x(47), i(1)]);
    push(&mut func, bb0, B, vec![bl(header)]);

    // Header: cmp iv,N (unsigned); enter guard else exit.
    push(&mut func, header, MovR, vec![x(50), x(46)]);
    push(&mut func, header, CmpRI, vec![x(50), i(n)]);
    push(&mut func, header, BCond, vec![i(CC_LO), bl(guard)]);
    push(&mut func, header, B, vec![bl(exit)]);

    // Pass-through: copy iv.
    push(&mut func, guard, MovR, vec![x(53), x(46)]);
    push(&mut func, guard, B, vec![bl(load)]);

    // Load a[j]; compute j-delta; bounds-check it (continue to dh, else panic).
    push(&mut func, load, AddRR, vec![x(59), x(0), x(53)]);
    push(&mut func, load, LdrbRI, vec![w(61), x(59), i(0)]); // a[j]
    push(&mut func, load, MovR, vec![x(62), x(46)]);
    push(&mut func, load, SubRR, vec![x(64), x(62), x(43)]); // j - delta
    push(&mut func, load, CmpRI, vec![x(64), i(n)]);
    push(&mut func, load, BCond, vec![i(CC_LO), bl(dh)]);
    push(&mut func, load, B, vec![bl(panic)]);

    // Diamond head: a[j-delta] load; extend both; two-byte compare; branch.
    push(&mut func, dh, AddRR, vec![x(70), x(0), x(64)]);
    push(&mut func, dh, LdrbRI, vec![w(72), x(70), i(0)]); // a[j-delta]
    push(&mut func, dh, Uxtb, vec![w(73), w(61)]);
    push(&mut func, dh, Uxtb, vec![w(74), w(72)]);
    push(&mut func, dh, CmpRR, vec![w(73), w(74)]);
    let cc = if ne { CC_NE } else { CC_EQ };
    push(&mut func, dh, BCond, vec![i(cc), bl(inc)]);
    push(&mut func, dh, B, vec![bl(zero)]);

    // "+1" arm: merge = acc + 1.
    push(&mut func, inc, AddRI, vec![x(77), x(47), i(1)]);
    push(&mut func, inc, MovR, vec![x(78), x(77)]);
    push(&mut func, inc, B, vec![bl(latch)]);

    // "+0" arm: merge = acc.
    push(&mut func, zero, MovR, vec![x(78), x(47)]);
    push(&mut func, zero, B, vec![bl(latch)]);

    // Latch: advance iv; phi-merge writeback acc = merge.
    push(&mut func, latch, AddRI, vec![x(80), x(46), i(1)]);
    push(&mut func, latch, MovR, vec![x(47), x(78)]);
    push(&mut func, latch, MovR, vec![x(46), x(80)]);
    push(&mut func, latch, B, vec![bl(header)]);

    // Exit + panic (both out of the loop body).
    push(&mut func, exit, AddRR, vec![x(6), x(47), x(47)]);
    push(&mut func, exit, B, vec![bl(exit)]);
    push(&mut func, panic, B, vec![bl(exit)]);

    func.add_edge(bb0, header);
    func.add_edge(header, guard);
    func.add_edge(header, exit);
    func.add_edge(guard, load);
    func.add_edge(load, dh);
    func.add_edge(load, panic);
    func.add_edge(dh, inc);
    func.add_edge(dh, zero);
    func.add_edge(inc, latch);
    func.add_edge(zero, latch);
    func.add_edge(latch, header);
    func.add_edge(panic, exit);
    func
}

#[test]
fn fires_on_stencil_count_runs_ne() {
    // The RLE "count runs" hot loop: `if a[j] != a[j-1] { runs += 1 }`.
    let mut func = build_stencil_loop(true, 1, 1024, 1);
    let mut pass = NeonBytesumPass::new();
    assert!(
        pass.run(&mut func),
        "should vectorize the byte-stencil count-if `a[j] != a[j-1]`"
    );
    assert_eq!(pass.fired(), 1);
    let u = unroll(TermKind::PredStencilCmp { ne: true });
    // One EXT.16B #1 (forward neighbor window), one CMEQ, one NOT (for !=), one
    // AND (0xFF->0x01), one UDOT — per accumulator.
    assert_eq!(
        count(&func, AArch64Opcode::NeonExtV),
        u,
        "one EXT.16B #1 per Q"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), u, "one CMEQ per Q");
    assert_eq!(
        count(&func, AArch64Opcode::NeonNotV),
        u,
        "one NOT per Q (!=)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonAndV), u, "one AND per Q");
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        u,
        "UDOT fold per acc"
    );
    // Every emitted EXT must carry the proven forward-neighbor immediate #1.
    for inst in func.blocks.iter().flat_map(|b| b.insts.iter()) {
        let inst = func.inst(*inst);
        if inst.opcode == AArch64Opcode::NeonExtV {
            assert_eq!(
                imm_of(&inst.operands[3]),
                Some(1),
                "stencil EXT must be the FORWARD #1 window (proof_neon_extv_16b(1))"
            );
        }
    }
}

#[test]
fn fires_on_stencil_count_eq() {
    // The `==` direction (count matching adjacent pairs): no NOT.
    let mut func = build_stencil_loop(false, 1, 1024, 1);
    let mut pass = NeonBytesumPass::new();
    assert!(
        pass.run(&mut func),
        "should vectorize `a[j] == a[j-1]` count"
    );
    let u = unroll(TermKind::PredStencilCmp { ne: false });
    assert_eq!(count(&func, AArch64Opcode::NeonExtV), u);
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), u);
    assert_eq!(count(&func, AArch64Opcode::NeonNotV), 0, "no NOT for `==`");
}

#[test]
fn bails_on_stencil_iv_init_not_one() {
    // iv MUST start at 1: a j=0 start would read a[-1] (predecessor OOB) and the
    // scalar loop would PANIC there, so it MUST NOT be silently vectorized.
    let mut func = build_stencil_loop(true, 0, 1024, 1);
    let mut pass = NeonBytesumPass::new();
    assert!(!pass.run(&mut func), "must BAIL: iv does not start at 1");
    assert_eq!(count(&func, AArch64Opcode::NeonExtV), 0);
}

#[test]
fn bails_on_stencil_non_adjacent_predecessor() {
    // a[j-2] (delta=2) is not the adjacent neighbor the EXT.16B #1 window forms.
    let mut func = build_stencil_loop(true, 1, 1024, 2);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: non-adjacent stencil a[j-2]"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonExtV), 0);
}

#[test]
fn bails_on_stencil_below_floor() {
    // The stencil floor is (unroll+1)*16 + 2 = 66; N=48 stays fully scalar.
    let mut func = build_stencil_loop(true, 1, 48, 1);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "N=48 below the stencil floor must stay scalar"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
}

// ---------------------------------------------------------------------------
// Hex-digit-code REDUCTION (`s += nib(b>>4) + nib(b&15)`, `HexNibbleSum`).
// ---------------------------------------------------------------------------

/// Which deviation (if any) the hex-nibble loop builder injects.
#[derive(Clone, Copy, PartialEq)]
enum Hex {
    /// The exact hex-nibble reduction (must FIRE).
    Fires,
    /// The `>= 10` arm selects 88 instead of 87 (wrong map — must BAIL).
    WrongConst,
    /// The nibble threshold is 11 instead of 10 (must BAIL).
    WrongThreshold,
    /// The loop also STORES to memory (must BAIL — not a pure reduction).
    Stored,
}

/// Build the hex-digit-code reduction `s += nib(b>>4) + nib(b&15)` over `[u8; N]`
/// in the branchy double-CONSTANT-SELECT-DIAMOND shape the bridge emits (if-convert
/// leaves the `nib` selects branchy). Blocks: `bb0 -> header -> guard -> load
/// (diamond-1 head) -> {hi<10 arm, hi>=10 arm} -> merge (diamond-2 head) ->
/// {lo<10 arm, lo>=10 arm} -> latch -> header`, plus `exit`.
fn build_hexnibble_loop(variant: Hex, n: i64) -> MachFunction {
    let mut func = MachFunction::new("hex".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let guard = func.create_block();
    let load = func.create_block(); // diamond-1 head (nib(hi))
    let ahilt = func.create_block(); // hi < 10  -> 48
    let ahige = func.create_block(); // hi >= 10 -> 87
    let merge = func.create_block(); // diamond-2 head (nib(lo))
    let alolt = func.create_block(); // lo < 10  -> 48
    let aloge = func.create_block(); // lo >= 10 -> 87
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // The `>= 10` arms select 87 normally; WrongConst injects 88.
    let hi_const = if variant == Hex::WrongConst { 88 } else { 87 };
    // The nibble threshold is 10 normally; WrongThreshold injects 11.
    let thresh = if variant == Hex::WrongThreshold {
        11
    } else {
        10
    };

    // Preheader: base, N, iv=0, acc=0, the two hoisted ASCII-base constants.
    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base ptr (invariant)
    push(&mut func, bb0, Movz, vec![x(4), i(n)]); // N
    push(&mut func, bb0, Movz, vec![x(47), i(0)]); // iv = 0
    push(&mut func, bb0, Movz, vec![x(49), i(0)]); // acc = 0
    push(&mut func, bb0, Movz, vec![w(10), i(48)]); // '0'..'9' base
    push(&mut func, bb0, Movz, vec![w(11), i(hi_const)]); // 'a'..'f' base
    push(&mut func, bb0, B, vec![bl(header)]);

    // Header: cmp iv,N (unsigned); enter guard else exit.
    push(&mut func, header, MovR, vec![x(50), x(47)]);
    push(&mut func, header, CmpRR, vec![x(50), x(4)]);
    push(&mut func, header, BCond, vec![i(CC_LO), bl(guard)]);
    push(&mut func, header, B, vec![bl(exit)]);

    // Bounds guard (pass-through carrier).
    push(&mut func, guard, MovR, vec![x(53), x(47)]);
    push(
        &mut func,
        guard,
        TrapBoundsCheckExact,
        vec![x(53), x(53), i(n)],
    );
    push(&mut func, guard, B, vec![bl(load)]);

    // Load + nibble split + diamond-1 head (nib(hi)). NOTE: body vregs use ids
    // >= 100 so no id collides with the header/guard/const ids (build_def_map keys
    // on the numeric id, ignoring register class).
    push(&mut func, load, LdrbRO, vec![w(100), x(0), x(53), i(0)]); // b = a[iv]
    push(&mut func, load, Uxtb, vec![w(101), w(100)]);
    push(&mut func, load, LsrRI, vec![w(102), w(101), i(4)]); // hi = b >> 4
    push(&mut func, load, AndRI, vec![w(103), w(101), i(15)]); // lo = b & 15
    push(&mut func, load, CmpRI, vec![w(102), i(thresh)]);
    push(&mut func, load, BCond, vec![i(CC_LO), bl(ahilt)]);
    push(&mut func, load, B, vec![bl(ahige)]);

    // nib(hi) select arms.
    push(&mut func, ahilt, MovR, vec![w(104), w(10)]); // 48
    push(&mut func, ahilt, B, vec![bl(merge)]);
    push(&mut func, ahige, MovR, vec![w(104), w(11)]); // 87
    push(&mut func, ahige, B, vec![bl(merge)]);

    // Merge-1: nib(hi) = hi + sel; sum1 = acc + nib(hi); diamond-2 head (nib(lo)).
    push(&mut func, merge, AddRR, vec![w(105), w(102), w(104)]); // hi + sel_hi
    push(&mut func, merge, Uxtw, vec![x(106), w(105)]);
    push(&mut func, merge, AddRR, vec![x(107), x(49), x(106)]); // sum1 = acc + nib(hi)
    push(&mut func, merge, CmpRI, vec![w(103), i(thresh)]);
    push(&mut func, merge, BCond, vec![i(CC_LO), bl(alolt)]);
    push(&mut func, merge, B, vec![bl(aloge)]);

    // nib(lo) select arms.
    push(&mut func, alolt, MovR, vec![w(108), w(10)]); // 48
    push(&mut func, alolt, B, vec![bl(latch)]);
    push(&mut func, aloge, MovR, vec![w(108), w(11)]); // 87
    push(&mut func, aloge, B, vec![bl(latch)]);

    // Latch: nib(lo) = lo + sel; sum2 = sum1 + nib(lo); writebacks.
    push(&mut func, latch, AddRR, vec![w(109), w(103), w(108)]); // lo + sel_lo
    push(&mut func, latch, Uxtw, vec![x(110), w(109)]);
    push(&mut func, latch, AddRR, vec![x(111), x(107), x(110)]); // sum2 = sum1 + nib(lo)
    if variant == Hex::Stored {
        // A store makes the loop non-read-only -> the whitelist BAILS.
        push(&mut func, latch, StrbRI, vec![w(101), x(0), i(0)]);
    }
    push(&mut func, latch, AddRI, vec![x(112), x(47), i(1)]); // iv + 1
    push(&mut func, latch, MovR, vec![x(49), x(111)]); // acc writeback
    push(&mut func, latch, MovR, vec![x(47), x(112)]); // iv writeback
    push(&mut func, latch, B, vec![bl(header)]);

    push(&mut func, exit, B, vec![bl(exit)]);

    func.add_edge(bb0, header);
    func.add_edge(header, guard);
    func.add_edge(header, exit);
    func.add_edge(guard, load);
    func.add_edge(load, ahilt);
    func.add_edge(load, ahige);
    func.add_edge(ahilt, merge);
    func.add_edge(ahige, merge);
    func.add_edge(merge, alolt);
    func.add_edge(merge, aloge);
    func.add_edge(alolt, latch);
    func.add_edge(aloge, latch);
    func.add_edge(latch, header);
    func
}

#[test]
fn fires_on_hex_nibble_sum() {
    let mut func = build_hexnibble_loop(Hex::Fires, 1024);
    let mut pass = NeonBytesumPass::new();
    assert!(
        pass.run(&mut func),
        "should vectorize s += nib(b>>4) + nib(b&15)"
    );
    assert_eq!(pass.fired(), 1);
    let u = unroll(TermKind::HexNibbleSum);
    // Per block: USHR.16B (hi) + 2x CMHS.16B (hi/lo letter masks).
    assert_eq!(
        count(&func, AArch64Opcode::NeonUshrVImm),
        u,
        "one USHR.16B #4 per block (high nibble)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmhsV),
        2 * u,
        "two CMHS.16B per block (hi/lo hex-letter masks)"
    );
    // Per block: AND.16B for lo-mask + 2x AND.16B for the letter-contrib collapse.
    assert_eq!(
        count(&func, AArch64Opcode::NeonAndV),
        3 * u,
        "lo-mask + 2 letter-contrib ANDs per block"
    );
    // FIVE accumulate UDOTs per block (hi, lo, c_hi, c_lo, #96).
    assert_eq!(
        count(&func, AArch64Opcode::NeonUdotV),
        5 * u,
        "five dot-sum streams per block"
    );
    // No byte-lane ADD emitted (the streams are summed by the accumulate UDOT).
    // The only NeonAddV is the .4S horizontal-combine tree in the exit block.
    assert_eq!(
        count(&func, AArch64Opcode::NeonCntV),
        0,
        "no popcount in the hex kernel"
    );
    // Four hoisted byte constants (#15/#10/#39/#96) + `ones` + the zeroed accs.
    assert_eq!(
        count(&func, AArch64Opcode::NeonMovi),
        u + 1 + 4,
        "accs + ones + {{lomask, thresh, delta, const}}"
    );
}

#[test]
fn bails_on_hex_nibble_wrong_const() {
    // The `>= 10` arm selects 88 (not 87) — an inexact hex map must BAIL.
    let mut func = build_hexnibble_loop(Hex::WrongConst, 1024);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: wrong hex-letter base (88 != 87)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUshrVImm), 0);
    assert_eq!(count(&func, AArch64Opcode::NeonCmhsV), 0);
}

#[test]
fn bails_on_hex_nibble_wrong_threshold() {
    // The nibble boundary is 11 (not 10) — wrong threshold must BAIL.
    let mut func = build_hexnibble_loop(Hex::WrongThreshold, 1024);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "must BAIL: wrong nibble threshold (11 != 10)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
}

#[test]
fn bails_on_hex_nibble_stored() {
    // A store makes the loop non-read-only -> BAIL (not a pure reduction).
    let mut func = build_hexnibble_loop(Hex::Stored, 1024);
    let mut pass = NeonBytesumPass::new();
    assert!(!pass.run(&mut func), "must BAIL: the loop stores to memory");
    assert_eq!(count(&func, AArch64Opcode::NeonUshrVImm), 0);
}

#[test]
fn bails_on_hex_nibble_below_width_floor() {
    // width(HexNibbleSum) = 4*16 = 64; N=48 stays fully scalar.
    let mut func = build_hexnibble_loop(Hex::Fires, 48);
    let mut pass = NeonBytesumPass::new();
    assert!(
        !pass.run(&mut func),
        "N=48 below the width floor must stay scalar"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
}
