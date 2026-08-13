// trust-cg-opt - Scalar ILP unroll tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::Signature;

fn v32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn v64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn vf32(id: u32) -> MachOperand {
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

fn push(func: &mut MachFunction, blk: BlockId, op: AArch64Opcode, ops: Vec<MachOperand>) {
    let id = func.push_inst(MachInst::new(op, ops));
    func.append_inst(blk, id);
}

fn run(func: &mut MachFunction) -> usize {
    let mut pass = ScalarUnrollPass::new();
    pass.run(func);
    pass.fired()
}

/// The ROTATED i64 product-of-array loop — `prod_i64`'s exact post-pipeline
/// shape (guard + body header + bottom-test latch):
///
/// ```text
/// bb0(preheader): v0=base v1=n v10=Movz#8 v3=Movz#1 v5=Movz#0(iv) v6=Movz#1(acc); B guard
/// guard:  CmpRR v5,v1; BCond(LT, header); B exit
/// header: v11=Madd(v5,v10,v0); v12=LdrRI[v11,0]; v13=MulRR(v6,v12);
///         v14=AddRR(v5,v3); B latch
/// latch:  AddRI v5,v14,#0; AddRI v6,v13,#0; CmpRR v5,v1; BCond(LT, header)
/// exit:   ret-ish
/// ```
fn build_prod_i64() -> MachFunction {
    let mut f = MachFunction::new("prod".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let guard = f.create_block();
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    use AArch64Opcode::*;
    push(&mut f, bb0, Movz, vec![v64(10), i(8)]);
    push(&mut f, bb0, Movz, vec![v64(3), i(1)]);
    push(&mut f, bb0, Movz, vec![v64(5), i(0)]);
    push(&mut f, bb0, Movz, vec![v64(6), i(1)]);
    push(&mut f, bb0, B, vec![b(guard)]);
    push(&mut f, guard, CmpRR, vec![v64(5), v64(1)]);
    push(&mut f, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut f, guard, B, vec![b(exit)]);
    push(&mut f, header, Madd, vec![v64(11), v64(5), v64(10), v64(0)]);
    push(&mut f, header, LdrRI, vec![v64(12), v64(11), i(0)]);
    push(&mut f, header, MulRR, vec![v64(13), v64(6), v64(12)]);
    push(&mut f, header, AddRR, vec![v64(14), v64(5), v64(3)]);
    push(&mut f, header, B, vec![b(latch)]);
    push(&mut f, latch, AddRI, vec![v64(5), v64(14), i(0)]);
    push(&mut f, latch, AddRI, vec![v64(6), v64(13), i(0)]);
    push(&mut f, latch, CmpRR, vec![v64(5), v64(1)]);
    push(&mut f, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut f, exit, MovR, vec![v64(20), v64(6)]);
    f.add_edge(bb0, guard);
    f.add_edge(guard, header);
    f.add_edge(guard, exit);
    f.add_edge(header, latch);
    f.add_edge(latch, header);
    f.add_edge(latch, exit);
    f
}

/// The ROTATED i64 gather-xor loop — the CRC-style `acc ^= tbl[b[i]]` shape
/// (byte load feeding a table load's address).
fn build_gather_xor() -> MachFunction {
    let mut f = MachFunction::new("crc".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let guard = f.create_block();
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    use AArch64Opcode::*;
    // v0=data v1=n v2=tbl v13=Movz#8 v4=Movz#1 v5=iv v6=acc
    push(&mut f, bb0, Movz, vec![v64(13), i(8)]);
    push(&mut f, bb0, Movz, vec![v64(4), i(1)]);
    push(&mut f, bb0, Movz, vec![v64(5), i(0)]);
    push(&mut f, bb0, Movz, vec![v64(6), i(0)]);
    push(&mut f, bb0, B, vec![b(guard)]);
    push(&mut f, guard, CmpRR, vec![v64(5), v64(1)]);
    push(&mut f, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut f, guard, B, vec![b(exit)]);
    push(&mut f, header, AddRR, vec![v64(10), v64(0), v64(5)]);
    push(&mut f, header, LdrbRI, vec![v32(11), v64(10), i(0)]);
    push(&mut f, header, Uxtb, vec![v64(12), v32(11)]);
    push(
        &mut f,
        header,
        Madd,
        vec![v64(14), v64(12), v64(13), v64(2)],
    );
    push(&mut f, header, LdrRI, vec![v64(15), v64(14), i(0)]);
    push(&mut f, header, EorRR, vec![v64(16), v64(6), v64(15)]);
    push(&mut f, header, AddRR, vec![v64(17), v64(5), v64(4)]);
    push(&mut f, header, B, vec![b(latch)]);
    push(&mut f, latch, AddRI, vec![v64(5), v64(17), i(0)]);
    push(&mut f, latch, AddRI, vec![v64(6), v64(16), i(0)]);
    push(&mut f, latch, CmpRR, vec![v64(5), v64(1)]);
    push(&mut f, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut f, exit, MovR, vec![v64(20), v64(6)]);
    f.add_edge(bb0, guard);
    f.add_edge(guard, header);
    f.add_edge(guard, exit);
    f.add_edge(header, latch);
    f.add_edge(latch, header);
    f.add_edge(latch, exit);
    f
}

/// The TOP-TESTED f32 sum loop — `fsum`'s exact post-pipeline shape (test in
/// the header, body + writebacks in the latch).
///
/// v0=base(Gpr64) v1=n(Gpr32) v3=Movz#1 v12=Movz#4 iv=v6(Gpr32) acc=v7(Fpr32).
fn build_fsum() -> MachFunction {
    let mut f = MachFunction::new("fsum".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    use AArch64Opcode::*;
    push(&mut f, bb0, Movz, vec![v32(3), i(1)]);
    push(&mut f, bb0, Movz, vec![v64(12), i(4)]);
    push(&mut f, bb0, Movz, vec![v32(6), i(0)]);
    push(&mut f, bb0, FmovFprFpr, vec![vf32(7), vf32(4)]);
    push(&mut f, bb0, B, vec![b(header)]);
    push(&mut f, header, CmpRR, vec![v32(6), v32(1)]);
    push(&mut f, header, BCond, vec![i(CC_LT), b(latch)]);
    push(&mut f, header, B, vec![b(exit)]);
    push(&mut f, latch, Sxtw, vec![v64(11), v32(6)]);
    push(&mut f, latch, Madd, vec![v64(13), v64(11), v64(12), v64(0)]);
    push(&mut f, latch, LdrRI, vec![vf32(14), v64(13), i(0)]);
    push(&mut f, latch, FaddRR, vec![vf32(15), vf32(7), vf32(14)]);
    push(&mut f, latch, AddRR, vec![v32(16), v32(6), v32(3)]);
    push(&mut f, latch, MovR, vec![v32(6), v32(16)]);
    push(&mut f, latch, FmovFprFpr, vec![vf32(7), vf32(15)]);
    push(&mut f, latch, B, vec![b(header)]);
    push(&mut f, exit, MovR, vec![v32(20), v32(6)]);
    f.add_edge(bb0, header);
    f.add_edge(header, latch);
    f.add_edge(header, exit);
    f.add_edge(latch, header);
    f
}

/// The ROTATED i64 FNV loop — compound update `h = (h ^ zext(b[i])) * P`
/// (acc feeds an EOR whose result feeds the MUL: NOT a single assoc root).
fn build_fnv() -> MachFunction {
    let mut f = MachFunction::new("fnv".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let guard = f.create_block();
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    use AArch64Opcode::*;
    // v0=data v1=n v5=prime v3=Movz#1 iv=v6 acc=v7
    push(&mut f, bb0, Movz, vec![v64(5), i(0x1b3)]);
    push(&mut f, bb0, Movz, vec![v64(3), i(1)]);
    push(&mut f, bb0, Movz, vec![v64(6), i(0)]);
    push(&mut f, bb0, Movz, vec![v64(7), i(0)]);
    push(&mut f, bb0, B, vec![b(guard)]);
    push(&mut f, guard, CmpRR, vec![v64(6), v64(1)]);
    push(&mut f, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut f, guard, B, vec![b(exit)]);
    push(&mut f, header, AddRR, vec![v64(11), v64(0), v64(6)]);
    push(&mut f, header, LdrbRI, vec![v32(12), v64(11), i(0)]);
    push(&mut f, header, Uxtb, vec![v64(13), v32(12)]);
    push(&mut f, header, EorRR, vec![v64(14), v64(7), v64(13)]);
    push(&mut f, header, MulRR, vec![v64(15), v64(14), v64(5)]);
    push(&mut f, header, AddRR, vec![v64(16), v64(6), v64(3)]);
    push(&mut f, header, B, vec![b(latch)]);
    push(&mut f, latch, AddRI, vec![v64(6), v64(16), i(0)]);
    push(&mut f, latch, AddRI, vec![v64(7), v64(15), i(0)]);
    push(&mut f, latch, CmpRR, vec![v64(6), v64(1)]);
    push(&mut f, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut f, exit, MovR, vec![v64(20), v64(7)]);
    f.add_edge(bb0, guard);
    f.add_edge(guard, header);
    f.add_edge(guard, exit);
    f.add_edge(header, latch);
    f.add_edge(latch, header);
    f.add_edge(latch, exit);
    f
}

// ---------------------------------------------------------------------------
// SPLIT mode
// ---------------------------------------------------------------------------

#[test]
fn split_fires_on_i64_mul_reduction() {
    let mut f = build_prod_i64();
    let blocks_before = f.block_order.len();
    assert_eq!(run(&mut f), 1);
    // 5 fresh blocks (i64 precheck + header/body/latch/exit).
    assert_eq!(f.block_order.len(), blocks_before + 5);
    // 4 lane MULs + 3 combine MULs + 1 original (tail) = 8.
    assert_eq!(count(&f, AArch64Opcode::MulRR), 8);
    // 4 lane loads + the original.
    assert_eq!(count(&f, AArch64Opcode::LdrRI), 5);
    // 3 identity accumulators seeded with #1.
    let ones = f
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter())
        .filter(|&&id| {
            let inst = f.inst(id);
            inst.opcode == AArch64Opcode::Movz && imm_of(&inst.operands[1]) == Some(1)
        })
        .count();
    assert_eq!(ones, 3 + 2); // 3 seeds + the pre-existing #1 step consts (iv step + acc init)
}

#[test]
fn split_fires_on_gather_xor() {
    let mut f = build_gather_xor();
    assert_eq!(run(&mut f), 1);
    // 4 lane EORs + 3 combine EORs + 1 original = 8.
    assert_eq!(count(&f, AArch64Opcode::EorRR), 8);
    // 4 lane byte loads + 4 lane table loads + originals (1 + 1).
    assert_eq!(count(&f, AArch64Opcode::LdrbRI), 5);
    assert_eq!(count(&f, AArch64Opcode::LdrRI), 5);
}

#[test]
fn split_bails_on_affine_i64_add() {
    // s += a[i] (i64, affine load, AddRR root): neon_array's property — the
    // no-vector-path gate must reject it even though it reaches this pass.
    let mut f = build_prod_i64();
    // Replace the MulRR root with AddRR.
    let root = f
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .find(|&id| f.inst(id).opcode == AArch64Opcode::MulRR)
        .unwrap();
    f.inst_mut(root).opcode = AArch64Opcode::AddRR;
    assert_eq!(run(&mut f), 0);
}

#[test]
fn split_bails_on_i32_mul() {
    // i32 products are neon_minmax's (MUL.4S); only i64 mul has no NEON path.
    // Build an i32 variant of the top-tested loop with a MulRR root.
    let mut f = build_fsum();
    // acc: use a Gpr32 accumulator updated by MulRR instead of the FP chain.
    for blk in 0..f.blocks.len() {
        let ids = f.blocks[blk].insts.clone();
        for id in ids {
            let inst = f.inst_mut(id);
            match inst.opcode {
                AArch64Opcode::LdrRI => inst.operands[0] = v32(14),
                AArch64Opcode::FaddRR => {
                    inst.opcode = AArch64Opcode::MulRR;
                    inst.operands = vec![v32(15), v32(7), v32(14)];
                }
                AArch64Opcode::FmovFprFpr => {
                    inst.opcode = AArch64Opcode::MovR;
                    inst.operands = vec![v32(7), v32(15)];
                }
                _ => {}
            }
        }
    }
    assert_eq!(run(&mut f), 0);
}

// ---------------------------------------------------------------------------
// SERIAL mode
// ---------------------------------------------------------------------------

#[test]
fn serial_fires_on_f32_sum_preserving_order() {
    let mut f = build_fsum();
    let blocks_before = f.block_order.len();
    assert_eq!(run(&mut f), 1);
    // 4 fresh blocks (no i64 precheck for a Gpr32 induction).
    assert_eq!(f.block_order.len(), blocks_before + 4);
    // 4 cloned FADDs + the original = 5; NO identity seeds, NO combine.
    assert_eq!(count(&f, AArch64Opcode::FaddRR), 5);
    // The clones form ONE serial chain: clone k's acc operand is clone k-1's
    // result (strict order — no reassociation).
    let ub = f.block_order[blocks_before]; // entry was last; fresh blocks precede it
    let fadds: Vec<InstId> = {
        // The unrolled body block is the one holding 4 FaddRR.
        let blk = f
            .blocks
            .iter()
            .enumerate()
            .find(|(_, blk)| {
                blk.insts
                    .iter()
                    .filter(|&&id| f.inst(id).opcode == AArch64Opcode::FaddRR)
                    .count()
                    == 4
            })
            .map(|(i, _)| BlockId(i as u32))
            .unwrap();
        let _ = ub;
        f.block(blk)
            .insts
            .iter()
            .copied()
            .filter(|&id| f.inst(id).opcode == AArch64Opcode::FaddRR)
            .collect()
    };
    assert_eq!(fadds.len(), 4);
    // Chain: first reads the live acc (v7); each next reads the previous def.
    let acc_operand = |id: InstId| vreg_of(&f.inst(id).operands[1]).unwrap();
    let def_of = |id: InstId| vreg_of(&f.inst(id).operands[0]).unwrap();
    assert_eq!(acc_operand(fadds[0]).id, 7);
    for k in 1..4 {
        assert_eq!(acc_operand(fadds[k]), def_of(fadds[k - 1]));
    }
    // Exactly one FP writeback of the chained value in the unrolled body.
    assert_eq!(count(&f, AArch64Opcode::FmovFprFpr), 3); // init + original + unrolled
}

#[test]
fn serial_fires_on_invariant_store_reduction() {
    // The FloatMM shape: `*result += a[row][i]*b[i][col]` — clang -O1 leaves a
    // redundant store of the accumulator to a LOOP-INVARIANT address every
    // iteration. SERIAL mode admits it (verbatim per-lane replication is
    // bit-exact) and unrolls; the store is replicated in each lane.
    let mut f = build_fsum();
    let latch = BlockId(2);
    let fadd_pos = f
        .block(latch)
        .insts
        .iter()
        .position(|&id| f.inst(id).opcode == AArch64Opcode::FaddRR)
        .unwrap();
    // `str vf32(15), [v64(0), #0]` — store the FADD result (the accumulator's
    // next value) to the loop-invariant base v64(0), just after the FaddRR.
    let st = f.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![vf32(15), v64(0), i(0)],
    ));
    f.block_mut(latch).insts.insert(fadd_pos + 1, st);
    let stores_before = count(&f, AArch64Opcode::StrRI);
    assert_eq!(
        run(&mut f),
        1,
        "invariant-address accumulator store must FIRE"
    );
    // 4 replicated lane stores added to the (untouched) tail store.
    assert_eq!(count(&f, AArch64Opcode::StrRI), stores_before + 4);
    // The order-preserving FADD chain is intact (4 clones + original).
    assert_eq!(count(&f, AArch64Opcode::FaddRR), 5);
}

#[test]
fn bails_on_loop_variant_store_address() {
    // A store whose ADDRESS is defined in-loop (a scatter `a[i] = ...`, not the
    // reduction-accumulator store to a fixed address) fails closed — those are
    // the memory-MAP vectorizers' territory, and admitting them here is out of
    // scope. Base v64(13) is the in-loop `Madd` result (loop-variant).
    let mut f = build_fsum();
    let latch = BlockId(2);
    let fadd_pos = f
        .block(latch)
        .insts
        .iter()
        .position(|&id| f.inst(id).opcode == AArch64Opcode::FaddRR)
        .unwrap();
    let st = f.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![vf32(15), v64(13), i(0)],
    ));
    f.block_mut(latch).insts.insert(fadd_pos + 1, st);
    assert_eq!(run(&mut f), 0, "loop-variant store address must BAIL");
}

#[test]
fn serial_fires_on_fnv_compound_update() {
    let mut f = build_fnv();
    assert_eq!(run(&mut f), 1);
    // 4 cloned EOR/MUL pairs + originals.
    assert_eq!(count(&f, AArch64Opcode::EorRR), 5);
    assert_eq!(count(&f, AArch64Opcode::MulRR), 5);
    // The 4 cloned MULs chain through the EORs in strict order.
    let blk = f
        .blocks
        .iter()
        .enumerate()
        .find(|(_, blk)| {
            blk.insts
                .iter()
                .filter(|&&id| f.inst(id).opcode == AArch64Opcode::MulRR)
                .count()
                == 4
        })
        .map(|(i, _)| BlockId(i as u32))
        .unwrap();
    let insts = &f.block(blk).insts;
    let eors: Vec<InstId> = insts
        .iter()
        .copied()
        .filter(|&id| f.inst(id).opcode == AArch64Opcode::EorRR)
        .collect();
    let muls: Vec<InstId> = insts
        .iter()
        .copied()
        .filter(|&id| f.inst(id).opcode == AArch64Opcode::MulRR)
        .collect();
    // eor_k reads mul_{k-1}'s def (the chained accumulator); eor_0 reads v7.
    assert_eq!(vreg_of(&f.inst(eors[0]).operands[1]).unwrap().id, 7);
    for k in 1..4 {
        assert_eq!(
            vreg_of(&f.inst(eors[k]).operands[1]).unwrap(),
            vreg_of(&f.inst(muls[k - 1]).operands[0]).unwrap()
        );
    }
}

// ---------------------------------------------------------------------------
// SERIAL mode — k-var recurrences (multiple carried accumulators)
// ---------------------------------------------------------------------------

/// A LOADLESS top-tested i32 `k`-variable shift-register recurrence:
///
/// ```text
/// x0,x1,...,x{k-1} = x1, x2, ..., x{k-1}, (x0 + x1 + ... + x{k-1})
/// ```
///
/// `k=2` is iterative fib (`a,b = b,a+b`); `k=3` is a tribonacci
/// (`a,b,c = b,c,a+b+c`). Carried vars are `iv=v6` plus `x_j = v(7+j)`. Like a
/// real frontend, the parallel shift-copies are broken with temps
/// (`t_j = x_{j+1}`, then `x_j = t_j`), so EVERY carried var's next value is a
/// fresh body def — the recognizer's soundness contract. The sum is a chain of
/// `k-1` adds (`v200..`); the shift temps are `v300..`; the iv step is
/// `v3=Movz#1`. All accumulators are initialized in the preheader.
fn build_shift_recurrence(k: u32) -> MachFunction {
    assert!(k >= 2);
    let mut f = MachFunction::new("shiftrec".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    use AArch64Opcode::*;
    // v1 = n (live-in); v3 = step #1; v6 = iv; accumulators v7..v(7+k-1).
    push(&mut f, bb0, Movz, vec![v32(3), i(1)]);
    push(&mut f, bb0, Movz, vec![v32(6), i(0)]);
    for j in 0..k {
        push(
            &mut f,
            bb0,
            Movz,
            vec![v32(7 + j), i(i64::from(j == k - 1))],
        );
    }
    push(&mut f, bb0, B, vec![b(header)]);
    push(&mut f, header, CmpRR, vec![v32(6), v32(1)]);
    push(&mut f, header, BCond, vec![i(CC_LT), b(latch)]);
    push(&mut f, header, B, vec![b(exit)]);
    // Body: total = x0 + x1 + ... + x{k-1}  (k-1 adds, v200..).
    push(&mut f, latch, AddRR, vec![v32(200), v32(7), v32(8)]);
    for j in 2..k {
        push(
            &mut f,
            latch,
            AddRR,
            vec![v32(200 + j - 1), v32(200 + j - 2), v32(7 + j)],
        );
    }
    let total = 200 + (k - 2);
    // Shift temps t_j = x_{j+1} (breaking the parallel copies → body defs).
    for j in 0..k - 1 {
        push(&mut f, latch, MovR, vec![v32(300 + j), v32(8 + j)]);
    }
    // iv increment (AddRR against the Movz#1 step, like the other kernels).
    push(&mut f, latch, AddRR, vec![v32(100), v32(6), v32(3)]);
    // Writebacks — contiguous, immediately before the branch — each reading a
    // fresh body def: iv, then `x_j = t_j`, then `x_{k-1} = total`.
    push(&mut f, latch, MovR, vec![v32(6), v32(100)]);
    for j in 0..k - 1 {
        push(&mut f, latch, MovR, vec![v32(7 + j), v32(300 + j)]);
    }
    push(&mut f, latch, MovR, vec![v32(7 + (k - 1)), v32(total)]);
    push(&mut f, latch, B, vec![b(header)]);
    push(&mut f, exit, MovR, vec![v32(20), v32(7 + (k - 1))]);
    f.add_edge(bb0, header);
    f.add_edge(header, latch);
    f.add_edge(header, exit);
    f.add_edge(latch, header);
    f
}

/// The unrolled body block (the fresh block holding `4 * per_lane` insts of
/// `op`).
fn unrolled_body_block(f: &MachFunction, op: AArch64Opcode, per_lane: usize) -> BlockId {
    f.blocks
        .iter()
        .enumerate()
        .find(|(_, blk)| {
            blk.insts
                .iter()
                .filter(|&&id| f.inst(id).opcode == op)
                .count()
                == 4 * per_lane
        })
        .map(|(i, _)| BlockId(i as u32))
        .expect("unrolled body block")
}

#[test]
fn serial_fires_on_iterative_fib() {
    // `a,b = b,a+b` — 3 carried vars (iv + 2 accs), LOADLESS. Non-reassociable,
    // no vector path: this pass owns it.
    let mut f = build_shift_recurrence(2);
    let blocks_before = f.block_order.len();
    assert_eq!(run(&mut f), 1);
    // 4 fresh blocks (Gpr32 induction: no i64 precheck).
    assert_eq!(f.block_order.len(), blocks_before + 4);
    // NO identity seeds, NO combine (SERIAL, not SPLIT).
    let seeds = count(&f, AArch64Opcode::Movz);
    assert_eq!(seeds, 4); // only the 4 preheader inits (step + iv + a + b)
    // The unrolled body holds 4 verbatim copies of the 1-add body (loadless:
    // no per-lane index arithmetic — the recurrence never reads `iv`).
    let ub = unrolled_body_block(&f, AArch64Opcode::AddRR, 1);
    let sums: Vec<InstId> = f
        .block(ub)
        .insts
        .iter()
        .copied()
        .filter(|&id| f.inst(id).opcode == AArch64Opcode::AddRR)
        .collect();
    assert_eq!(sums.len(), 4);
    // The 4 sum-adds form ONE serial chain: each reads the previous lane's def
    // (no reassociation). sum_k's `total` operand is derived from sum_{k-1}.
    let def = |id: InstId| vreg_of(&f.inst(id).operands[0]).unwrap();
    for k in 1..4 {
        let ops = &f.inst(sums[k]).operands;
        let reads_prev = ops
            .iter()
            .skip(1)
            .filter_map(vreg_of)
            .any(|v| v == def(sums[k - 1]));
        assert!(reads_prev, "lane {k} sum must chain off lane {}", k - 1);
    }
    // Idempotent: re-running does not re-fire (own-output defense).
    assert_eq!(run(&mut f), 0);
}

#[test]
fn serial_fires_on_tribonacci() {
    // `a,b,c = b,c,a+b+c` — 4 carried vars (iv + 3 accs), LOADLESS, mod 2^32.
    let mut f = build_shift_recurrence(3);
    let blocks_before = f.block_order.len();
    assert_eq!(run(&mut f), 1);
    assert_eq!(f.block_order.len(), blocks_before + 4);
    // Body is 2 adds; unrolled 4x = 8 in the body block.
    let ub = unrolled_body_block(&f, AArch64Opcode::AddRR, 2);
    assert_eq!(
        f.block(ub)
            .insts
            .iter()
            .filter(|&&id| f.inst(id).opcode == AArch64Opcode::AddRR)
            .count(),
        8
    );
    // Idempotent (own-output defense).
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_direct_carried_var_writeback_source() {
    // A writeback whose source is a live carried var (NOT a fresh body-def
    // temp): `a = b` directly. The frontend never emits this (it inserts a
    // temp when the copy is hazardous), and the recognizer BAILS — the
    // body-def-source contract that makes the simultaneous k-var writeback
    // bit-identical to the scalar loop's sequential one (no `a=b;b=a` swap
    // hazard). Repoint fib's `a' = temp` writeback to read `b` (v6) directly.
    let mut f = build_fib_rotated();
    for blk in 0..f.blocks.len() {
        let ids = f.blocks[blk].insts.clone();
        for id in ids {
            let inst = f.inst_mut(id);
            if inst.opcode == AArch64Opcode::AddRI
                && vreg_of(&inst.operands[0]).map(|v| v.id) == Some(7)
                && vreg_of(&inst.operands[1]).map(|v| v.id) == Some(10)
            {
                inst.operands[1] = v32(6); // a' = b (carried source, not a temp)
            }
        }
    }
    assert_eq!(run(&mut f), 0);
}

/// The ROTATED i32 iterative-fib loop — the shape `loop-latch-layout` actually
/// emits (guard + straight-line body header ending `B latch` + bottom-test
/// latch holding the `k+1` carried-var writebacks). LOADLESS. This is the real
/// post-pipeline form; the `serial_fires_on_*` builders above are top-tested.
fn build_fib_rotated() -> MachFunction {
    let mut f = MachFunction::new("fibrot".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let guard = f.create_block();
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    use AArch64Opcode::*;
    // v0=n (live-in); v1=step#1; iv=v5; a=v7; b=v6.
    push(&mut f, bb0, Movz, vec![v32(1), i(1)]);
    push(&mut f, bb0, Movz, vec![v32(5), i(0)]);
    push(&mut f, bb0, Movz, vec![v32(7), i(0)]);
    push(&mut f, bb0, Movz, vec![v32(6), i(1)]);
    push(&mut f, bb0, B, vec![b(guard)]);
    push(&mut f, guard, CmpRR, vec![v32(5), v32(0)]);
    push(&mut f, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut f, guard, B, vec![b(exit)]);
    // body: temp = b; sum = a + b; iv + 1.
    push(&mut f, header, MovR, vec![v32(10), v32(6)]);
    push(&mut f, header, AddRR, vec![v32(12), v32(7), v32(6)]);
    push(&mut f, header, AddRR, vec![v32(13), v32(5), v32(1)]);
    push(&mut f, header, B, vec![b(latch)]);
    // latch: iv=iv+1; b'=sum; a'=old b; bottom test.
    push(&mut f, latch, AddRI, vec![v32(5), v32(13), i(0)]);
    push(&mut f, latch, AddRI, vec![v32(6), v32(12), i(0)]);
    push(&mut f, latch, AddRI, vec![v32(7), v32(10), i(0)]);
    push(&mut f, latch, CmpRR, vec![v32(5), v32(0)]);
    push(&mut f, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut f, exit, MovR, vec![v32(20), v32(6)]);
    f.add_edge(bb0, guard);
    f.add_edge(guard, header);
    f.add_edge(guard, exit);
    f.add_edge(header, latch);
    f.add_edge(latch, header);
    f.add_edge(latch, exit);
    f
}

#[test]
fn serial_fires_on_rotated_fib() {
    // The ROTATED form with 3 carried vars (iv + 2 accs) and 3 latch
    // writebacks — the length-generalized bottom-test recognizer must accept
    // it (the pre-generalization code hardcoded a 4-inst latch = 2 writebacks).
    let mut f = build_fib_rotated();
    let blocks_before = f.block_order.len();
    assert_eq!(run(&mut f), 1);
    // 4 fresh blocks (Gpr32 induction: no i64 precheck).
    assert_eq!(f.block_order.len(), blocks_before + 4);
    // Idempotent (own-output defense).
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_too_many_carried_vars() {
    // k=5 accumulators (iv + 5 = 6 carried vars) exceeds MAX_ACCS: BAIL.
    let mut f = build_shift_recurrence(5);
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_store_in_kvar_body() {
    // A store anywhere in a k-var recurrence loop drops it (memory not
    // invariant) — the same whitelist bail as the single-acc modes.
    let mut f = build_shift_recurrence(3);
    let latch = BlockId(2);
    let id = f.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![v32(200), v64(0), i(0)],
    ));
    f.block_mut(latch).insts.insert(0, id);
    assert_eq!(run(&mut f), 0);
}

// ---------------------------------------------------------------------------
// Fail-closed bails
// ---------------------------------------------------------------------------

#[test]
fn bails_on_store_in_body() {
    let mut f = build_prod_i64();
    let header = BlockId(2);
    let id = f.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![v64(13), v64(11), i(0)],
    ));
    let pos = f.block(header).insts.len() - 1;
    f.block_mut(header).insts.insert(pos, id);
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_call_in_body() {
    let mut f = build_prod_i64();
    let header = BlockId(2);
    let id = f.push_inst(MachInst::new(AArch64Opcode::Bl, vec![]));
    let pos = f.block(header).insts.len() - 1;
    f.block_mut(header).insts.insert(pos, id);
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_unsigned_loop_test() {
    let mut f = build_prod_i64();
    for blk in 0..f.blocks.len() {
        let ids = f.blocks[blk].insts.clone();
        for id in ids {
            let inst = f.inst_mut(id);
            if inst.opcode == AArch64Opcode::BCond {
                inst.operands[0] = i(CC_LO); // unsigned `<`: not the shape
            }
        }
    }
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_step_two() {
    let mut f = build_fsum();
    // iv += 2 (Movz #1 -> #2).
    let bb0 = f.entry;
    let ids = f.block(bb0).insts.clone();
    for id in ids {
        let inst = f.inst_mut(id);
        if inst.opcode == AArch64Opcode::Movz && vreg_of(&inst.operands[0]).map(|v| v.id) == Some(3)
        {
            inst.operands[1] = i(2);
        }
    }
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_loadless_body() {
    // Register-only reductions belong to reduction_split / neon_reduce.
    let mut f = build_prod_i64();
    for blk in 0..f.blocks.len() {
        let ids = f.blocks[blk].insts.clone();
        for id in ids {
            let inst = f.inst_mut(id);
            if inst.opcode == AArch64Opcode::LdrRI {
                // Replace the load with a pure op producing the same def.
                inst.opcode = AArch64Opcode::EorRR;
                inst.operands = vec![v64(12), v64(11), v64(11)];
            }
        }
    }
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_uninitialized_extra_carried_var() {
    // A third carried var that has NO preheader init: the own-output defense
    // (each carried var has EXACTLY ONE outside definition) rejects it, even
    // now that multi-carried-var recurrences are admissible.
    let mut f = build_prod_i64();
    let header = BlockId(2);
    let latch = BlockId(3);
    // v8 += 1 in the body, written back in the latch — but v8 is never
    // initialized outside the loop.
    let id = f.push_inst(MachInst::new(
        AArch64Opcode::AddRR,
        vec![v64(21), v64(8), v64(3)],
    ));
    let pos = f.block(header).insts.len() - 1;
    f.block_mut(header).insts.insert(pos, id);
    let wb = f.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![v64(8), v64(21), i(0)],
    ));
    f.block_mut(latch).insts.insert(2, wb);
    assert_eq!(run(&mut f), 0);
}

#[test]
fn bails_on_multi_pred_entry() {
    // The entry block gaining a second outside predecessor (e.g. a vectorizer
    // guard-skip + main-exit tail) must be rejected — the own-output /
    // NEON-tail defense.
    let mut f = build_prod_i64();
    let guard = BlockId(1);
    let extra = f.create_block();
    push(&mut f, extra, AArch64Opcode::B, vec![b(guard)]);
    f.add_edge(extra, guard);
    assert_eq!(run(&mut f), 0);
}

#[test]
fn transform_is_idempotent() {
    let mut f = build_prod_i64();
    assert_eq!(run(&mut f), 1);
    let insts_after = f.insts.len();
    let blocks_after = f.block_order.len();
    assert_eq!(run(&mut f), 0);
    assert_eq!(f.insts.len(), insts_after);
    assert_eq!(f.block_order.len(), blocks_after);
}

#[test]
fn serial_transform_is_idempotent() {
    let mut f = build_fsum();
    assert_eq!(run(&mut f), 1);
    assert_eq!(run(&mut f), 0);
}

#[test]
fn split_guard_structure_i64() {
    // i64: precheck CmpRI(n, 4) + signed skip; main test iv <u main_bound.
    let mut f = build_prod_i64();
    assert_eq!(run(&mut f), 1);
    assert_eq!(count(&f, AArch64Opcode::CmpRI), 1);
    let lo_bconds = f
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter())
        .filter(|&&id| {
            let inst = f.inst(id);
            inst.opcode == AArch64Opcode::BCond && imm_of(&inst.operands[0]) == Some(CC_LO)
        })
        .count();
    assert_eq!(lo_bconds, 1);
}

#[test]
fn serial_guard_structure_i32() {
    // Gpr32: no precheck; sxtw-based signed guard (2 new Sxtw: bound + iv).
    let mut f = build_fsum();
    let sxtw_before = count(&f, AArch64Opcode::Sxtw);
    assert_eq!(run(&mut f), 1);
    assert_eq!(count(&f, AArch64Opcode::CmpRI), 0);
    // +2 guard Sxtw +4 cloned lane Sxtw.
    assert_eq!(count(&f, AArch64Opcode::Sxtw), sxtw_before + 6);
}

// ---------------------------------------------------------------------------
// FULL-UNROLL (constant-trip, address-folding) — the FloatMM inner product
// ---------------------------------------------------------------------------

/// A CLANG-ROTATED constant-trip FP inner-product loop modelled on FloatMM's
/// `rInnerproduct` (`*r = *r + a[row][i]*b[i][col]`, i = 1..bound-1): a single
/// FP accumulator, two register-offset loads whose offsets are iv-affine, and a
/// loop-invariant store. `bound` sets the constant trip (= `bound - 1`);
/// `bstride` is the b-load's per-iteration stride (its fold coefficient), used
/// to exercise the immediate-range check. v0/v1/v2 (ptrs) and v7/v8 (row/col
/// extended indices) are loop-invariant live-ins.
fn build_floatmm_like(bound: i64, bstride: i64) -> MachFunction {
    let mut f = MachFunction::new("rinner".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let header = f.create_block();
    let exit = f.create_block();
    let latch = f.create_block();
    use AArch64Opcode::*;
    // preheader
    push(&mut f, bb0, Movz, vec![v64(9), i(1)]); // the "+1"
    push(&mut f, bb0, MovR, vec![v64(12), v64(9)]); // iv init = 1
    push(&mut f, bb0, Movz, vec![v32(30), i(0)]);
    push(&mut f, bb0, FmovGprFpr, vec![vf32(13), v32(30)]); // acc init 0.0
    push(&mut f, bb0, Movz, vec![v64(14), i(bstride)]); // b stride / row stride
    push(&mut f, bb0, Movz, vec![v64(15), i(4)]); // a element size
    push(&mut f, bb0, MulRR, vec![v64(22), v64(8), v64(15)]); // colpart = col*4 (invariant)
    push(&mut f, bb0, Movz, vec![v64(29), i(bound)]); // bound
    push(&mut f, bb0, B, vec![b(header)]);
    // header: unconditional body + rotated exit test
    push(&mut f, header, MulRR, vec![v64(16), v64(12), v64(15)]); // iv*4
    push(
        &mut f,
        header,
        Madd,
        vec![v64(17), v64(7), v64(14), v64(16)],
    ); // a off = row*bstride + iv*4
    push(&mut f, header, LdrRO, vec![vf32(19), v64(1), v64(17)]); // a[row][iv]
    push(
        &mut f,
        header,
        Madd,
        vec![v64(23), v64(12), v64(14), v64(22)],
    ); // b off = iv*bstride + col*4
    push(&mut f, header, LdrRO, vec![vf32(25), v64(2), v64(23)]); // b[iv][col]
    push(
        &mut f,
        header,
        FmaddRR,
        vec![vf32(26), vf32(19), vf32(25), vf32(13)],
    ); // acc' = a*b + acc
    push(&mut f, header, StrRI, vec![vf32(26), v64(0), i(0)]); // *result = acc'
    push(&mut f, header, AddRR, vec![v64(28), v64(12), v64(9)]); // iv+1
    push(&mut f, header, CmpRR, vec![v64(28), v64(29)]);
    push(&mut f, header, BCond, vec![i(CC_EQ), b(exit)]);
    push(&mut f, header, B, vec![b(latch)]);
    push(&mut f, exit, Ret, vec![]);
    push(&mut f, latch, MovR, vec![v64(12), v64(28)]);
    push(&mut f, latch, FmovFprFpr, vec![vf32(13), vf32(26)]);
    push(&mut f, latch, B, vec![b(header)]);
    f.add_edge(bb0, header);
    f.add_edge(header, exit);
    f.add_edge(header, latch);
    f.add_edge(latch, header);
    f
}

/// The block holding the straight-line full-unroll fast path (the one carrying
/// the folded `LdrRI` immediate loads), if full-unroll fired.
fn fast_path_block(f: &MachFunction) -> Option<BlockId> {
    f.block_order.iter().copied().find(|&bid| {
        f.block(bid)
            .insts
            .iter()
            .any(|&id| f.inst(id).opcode == AArch64Opcode::LdrRI)
    })
}

#[test]
fn full_unroll_fires_on_constant_trip_10() {
    // Trip 10 (bound 11), both loads foldable: full-unroll must fire and emit
    // base+immediate loads. 9 folded copies × 2 loads = 18 `LdrRI`; the single
    // tail iteration keeps the 2 original `LdrRO`. 10 fmadds total (9 folded + 1
    // tail). No new loop is introduced (idempotent thereafter).
    let mut f = build_floatmm_like(11, 164);
    assert_eq!(run(&mut f), 1);
    assert_eq!(
        count(&f, AArch64Opcode::LdrRI),
        18,
        "9 copies × 2 folded loads"
    );
    assert_eq!(
        count(&f, AArch64Opcode::LdrRO),
        2,
        "only the tail header keeps register-offset loads"
    );
    assert_eq!(
        count(&f, AArch64Opcode::FmaddRR),
        10,
        "9 folded + 1 tail fmadd"
    );
    // The folded immediates are exactly {a: 4·c, b: 164·c} for c = 1..9.
    let ub = fast_path_block(&f).expect("fast path exists");
    let mut imms: Vec<i64> = f
        .block(ub)
        .insts
        .iter()
        .filter(|&&id| f.inst(id).opcode == AArch64Opcode::LdrRI)
        .filter_map(|&id| imm_of(&f.inst(id).operands[2]))
        .collect();
    imms.sort();
    let mut expect: Vec<i64> = (1..=9)
        .map(|c| 4 * c)
        .chain((1..=9).map(|c| 164 * c))
        .collect();
    expect.sort();
    assert_eq!(
        imms, expect,
        "folded immediates are coeff·c for c=1..trip-1"
    );
    // Idempotent: the fast path adds a second outside def of the carried vars.
    assert_eq!(run(&mut f), 0);
}

#[test]
fn full_unroll_preserves_fp_accumulator_chain() {
    // BIT-EXACTNESS: the folded copies must feed ONE accumulator in order — each
    // fmadd's addend is the previous fmadd's result (lane 0 reads the live acc
    // init). No reassociation, no second accumulator.
    let mut f = build_floatmm_like(11, 164);
    assert_eq!(run(&mut f), 1);
    let ub = fast_path_block(&f).expect("fast path exists");
    let fmadds: Vec<InstId> = f
        .block(ub)
        .insts
        .iter()
        .copied()
        .filter(|&id| f.inst(id).opcode == AArch64Opcode::FmaddRR)
        .collect();
    assert_eq!(fmadds.len(), 9);
    for w in fmadds.windows(2) {
        let prev_dst = vreg_of(&f.inst(w[0]).operands[0]).unwrap();
        let next_acc = vreg_of(&f.inst(w[1]).operands[3]).unwrap(); // addend = accumulator
        assert_eq!(
            prev_dst, next_acc,
            "single serial accumulator chain (no reassociation)"
        );
    }
}

#[test]
fn full_unroll_bails_at_trip_65() {
    // Trip 65 > MAX_FULL(64): full-unroll declines; the 4-wide SERIAL path still
    // fires, so no folded immediate loads appear (loads stay register-offset).
    let mut f = build_floatmm_like(66, 164);
    assert_eq!(run(&mut f), 1);
    assert_eq!(
        count(&f, AArch64Opcode::LdrRI),
        0,
        "4-wide clones register-offset loads, no folding"
    );
}

#[test]
fn full_unroll_bails_on_nonconstant_trip() {
    // Bound is a runtime live-in (no in-preheader Movz): the trip is not a
    // compile-time constant, so full-unroll declines and the 4-wide path runs.
    let mut f = build_floatmm_like(11, 164);
    // Repoint the exit compare at a fresh, never-defined live-in (v50): the loop
    // bound is now a runtime value, not a compile-time constant.
    let header = BlockId(1);
    let cmp = *f
        .block(header)
        .insts
        .iter()
        .find(|&&id| f.inst(id).opcode == AArch64Opcode::CmpRR)
        .unwrap();
    f.inst_mut(cmp).operands[1] = MachOperand::VReg(VReg::new(50, RegClass::Gpr64));
    assert_eq!(run(&mut f), 1);
    assert_eq!(
        count(&f, AArch64Opcode::LdrRI),
        0,
        "runtime trip: no full-unroll folding"
    );
}

#[test]
fn full_unroll_bails_on_out_of_range_immediate() {
    // b stride 0x8000: b-load coefficient 32768, so copy c=1's immediate is
    // 32768 (÷4 = 8192 > 4095, the scaled-imm12 ceiling) — full-unroll declines
    // and the 4-wide path runs (no folded loads).
    let mut f = build_floatmm_like(11, 0x8000);
    assert_eq!(run(&mut f), 1);
    assert_eq!(
        count(&f, AArch64Opcode::LdrRI),
        0,
        "out-of-range immediate falls back to 4-wide"
    );
}

// ---------------------------------------------------------------------------
// CmpRI-folded trip guards — ISel (`dc5916e`) folds `icmp iv, C` (C in
// [0,4095]) to `CmpRI iv, #C`, which the recognizer keys on `CmpRR(iv, movz)`
// would otherwise miss; `normalize_const_trip_guards` restores recognition.
// ---------------------------------------------------------------------------

/// `build_floatmm_like` with its header exit compare rewritten from
/// `CmpRR(iv+1, bound)` to the ISel-folded `CmpRI(iv+1, #bound)` (the
/// `select_cmp` fold), modelling exactly the shape that silently defeated the
/// matmul k-loop's full-unroll before `normalize_const_trip_guards`.
fn foldedcmp_floatmm(bound: i64, bstride: i64) -> MachFunction {
    let mut f = build_floatmm_like(bound, bstride);
    let header = BlockId(1);
    let cmp_id = *f
        .block(header)
        .insts
        .iter()
        .find(|&&id| f.inst(id).opcode == AArch64Opcode::CmpRR)
        .expect("header has the exit CmpRR");
    let iv_step = f.inst(cmp_id).operands[0].clone();
    let inst = f.inst_mut(cmp_id);
    inst.opcode = AArch64Opcode::CmpRI;
    inst.operands = vec![iv_step, MachOperand::Imm(bound)];
    f
}

#[test]
fn full_unroll_fires_on_cmpri_folded_trip_guard() {
    // dc5916e folds the constant trip compare to `CmpRI(iv+1, #11)`; the
    // normalizer restores `CmpRR(iv+1, movz)` (movz hoisted into the preheader),
    // so full-unroll fires exactly as the pre-fold `constant_trip_10` case: 9
    // folded copies × 2 loads = 18 `LdrRI`, 10 fmadds. This is the matrix-2x fix.
    let mut f = foldedcmp_floatmm(11, 164);
    assert_eq!(
        run(&mut f),
        1,
        "normalized CmpRI trip guard must full-unroll"
    );
    assert_eq!(
        count(&f, AArch64Opcode::LdrRI),
        18,
        "9 copies × 2 folded loads"
    );
    assert_eq!(
        count(&f, AArch64Opcode::FmaddRR),
        10,
        "9 folded + 1 tail fmadd"
    );
    // Bit-exactness of the restored form is covered by the identical assertions
    // in `full_unroll_preserves_fp_accumulator_chain` (same fast-path shape).
}

#[test]
fn cmpri_trip_guard_below_full_window_is_left_untouched() {
    // imm 3 < MIN_FULL(4): the guard is NOT normalized (dc5916e's CmpRI /
    // CBZ-immediate benefit is preserved for sub-window and `#0` compares) and
    // no unroll happens — the recognizer never sees a `CmpRR` to match.
    let mut f = foldedcmp_floatmm(3, 164);
    assert_eq!(run(&mut f), 0, "sub-window trip: no fire");
    assert_eq!(count(&f, AArch64Opcode::LdrRI), 0, "no folding");
    assert!(
        count(&f, AArch64Opcode::CmpRI) >= 1,
        "sub-window CmpRI guard untouched"
    );
}

#[test]
fn cmpri_large_constant_trip_restores_4wide_unroll() {
    // imm 66 (trip 65 > MAX_FULL) is ABOVE the full-unroll band but still folded
    // to CmpRI by dc5916e — the normalizer (window ceiling = the imm12 range,
    // not MAX_FULL) restores CmpRR so the 4-wide SERIAL path fires, exactly as
    // the CmpRR baseline `full_unroll_bails_at_trip_65`. Without the widened
    // window this loop would strand rolled.
    let mut f = foldedcmp_floatmm(66, 164);
    assert_eq!(
        run(&mut f),
        1,
        "large-constant CmpRI trip must 4-wide unroll"
    );
    assert_eq!(
        count(&f, AArch64Opcode::LdrRI),
        0,
        "4-wide clones register-offset loads, no folding"
    );
}

// ---------------------------------------------------------------------------
// FULL-UNROLL of TWO-LEVEL AFFINE GATHERS — the Shootout `matrix` k-loop
// `val += m1[i][k] * m2[k][j]` (int accumulator, pointer-array matrices).
// ---------------------------------------------------------------------------

/// Options for [`build_matmul_gather`] — each toggles a fail-closed precondition.
#[derive(Clone, Copy, Default)]
struct GatherOpts {
    /// Append a loop-invariant store to the body (must forbid the gather).
    with_store: bool,
    /// Make the ROW load a `Gpr32` (not a full-width 8-byte pointer).
    narrow_row: bool,
    /// Make the ROW load's address non-affine (`iv*iv`).
    nonaffine_row: bool,
    /// Load the ROW pointer through ANOTHER in-loop load (a THIRD level).
    three_level: bool,
}

/// The CLANG-ROTATED constant-trip integer inner product with a TWO-LEVEL
/// pointer-array gather. `m1[i]` (the row pointer, live-in `v1`) is loop-
/// invariant; `m2[k]` is loaded each iteration (the row load, `v19`) off the
/// invariant base `v2` and indexed by the invariant column `v3`. Every address
/// is `Ldr [Madd(idx, #scale, base), #0]` — the shape `AddrModeFormation`
/// leaves when it does not split the index into a register offset.
///
/// ```text
/// header: v16=Madd(k, #4, m1row);  v17=LdrRI[v16,#0]      ; m1[i][k]  (Gpr32)
///         v18=Madd(k, #8, m2base); v19=LdrRI[v18,#0]      ; m2[k]     (Gpr64, ROW)
///         v21=Madd(j, #4, v19);    v22=LdrRI[v21,#0]      ; m2[k][j]  (Gpr32, DEP)
///         v23=Madd(v22, v17, val)                          ; val' = m2·m1 + val
///         v28=AddRR(k, #1); CmpRR(v28,bound); BCond EQ exit; B latch
/// latch:  MovR k=v28; MovR val=v23; B header
/// ```
fn build_matmul_gather(bound: i64, opts: GatherOpts) -> MachFunction {
    let mut f = MachFunction::new("mmult".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let header = f.create_block();
    let exit = f.create_block();
    let latch = f.create_block();
    use AArch64Opcode::*;
    // preheader: constants + carried inits. v1=m1row v2=m2base v3=j (live-ins).
    push(&mut f, bb0, Movz, vec![v64(9), i(1)]); // "+1"
    push(&mut f, bb0, Movz, vec![v64(10), i(0)]);
    push(&mut f, bb0, MovR, vec![v64(12), v64(10)]); // iv (k) init = 0
    push(&mut f, bb0, Movz, vec![v32(20), i(0)]); // val init = 0
    push(&mut f, bb0, Movz, vec![v64(14), i(8)]); // pointer stride
    push(&mut f, bb0, Movz, vec![v64(15), i(4)]); // element size
    push(&mut f, bb0, Movz, vec![v64(29), i(bound)]); // bound
    if opts.three_level {
        push(&mut f, bb0, Movz, vec![v64(7), i(0)]); // extra index #0
    }
    push(&mut f, bb0, B, vec![b(header)]);
    // header: unconditional body + rotated exit test.
    push(
        &mut f,
        header,
        Madd,
        vec![v64(16), v64(12), v64(15), v64(1)],
    ); // &m1[i][k]
    push(&mut f, header, LdrRI, vec![v32(17), v64(16), i(0)]); // m1[i][k]
    // the ROW load's address (default: affine `k*8 + m2base`).
    if opts.nonaffine_row {
        push(
            &mut f,
            header,
            Madd,
            vec![v64(18), v64(12), v64(12), v64(2)],
        ); // k*k + base
    } else if opts.three_level {
        // m2base -> load a row-of-rows pointer first, then the row pointer.
        push(&mut f, header, Madd, vec![v64(4), v64(12), v64(14), v64(2)]); // &m2[k]
        push(&mut f, header, LdrRI, vec![v64(5), v64(4), i(0)]); // m2[k] (ptr-of-ptrs)
        push(&mut f, header, Madd, vec![v64(18), v64(7), v64(14), v64(5)]); // &m2[k][0]
    } else {
        push(
            &mut f,
            header,
            Madd,
            vec![v64(18), v64(12), v64(14), v64(2)],
        ); // &m2[k]
    }
    if opts.narrow_row {
        push(&mut f, header, LdrRI, vec![v32(19), v64(18), i(0)]); // ROW as Gpr32
    } else {
        push(&mut f, header, LdrRI, vec![v64(19), v64(18), i(0)]); // m2[k] (ROW, Gpr64)
    }
    push(
        &mut f,
        header,
        Madd,
        vec![v64(21), v64(3), v64(15), v64(19)],
    ); // &m2[k][j]
    push(&mut f, header, LdrRI, vec![v32(22), v64(21), i(0)]); // m2[k][j] (DEP)
    push(
        &mut f,
        header,
        Madd,
        vec![v32(23), v32(22), v32(17), v32(20)],
    ); // val' = m2·m1 + val
    if opts.with_store {
        push(&mut f, header, StrRI, vec![v32(17), v64(2), i(0)]); // invariant-address store
    }
    push(&mut f, header, AddRR, vec![v64(28), v64(12), v64(9)]); // k+1
    push(&mut f, header, CmpRR, vec![v64(28), v64(29)]);
    push(&mut f, header, BCond, vec![i(CC_EQ), b(exit)]);
    push(&mut f, header, B, vec![b(latch)]);
    push(&mut f, exit, Ret, vec![]);
    push(&mut f, latch, MovR, vec![v64(12), v64(28)]);
    push(&mut f, latch, MovR, vec![v32(20), v32(23)]);
    push(&mut f, latch, B, vec![b(header)]);
    f.add_edge(bb0, header);
    f.add_edge(header, exit);
    f.add_edge(header, latch);
    f.add_edge(latch, header);
    f
}

/// Every `LdrRI` immediate offset in the function. A nonzero value can only come
/// from a fold (the source loads all carry `#0`), so it witnesses full-unroll.
fn ldr_imms(f: &MachFunction) -> Vec<i64> {
    f.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| f.inst(id).opcode == AArch64Opcode::LdrRI)
        .filter_map(|id| imm_of(&f.inst(id).operands[2]))
        .collect()
}

/// True when full-unroll fired on the gather shape: some load folded to a
/// nonzero immediate (the 4-wide path clones the loads verbatim at `#0`).
fn gather_full_unrolled(f: &MachFunction) -> bool {
    ldr_imms(f).iter().any(|&x| x != 0)
}

#[test]
fn full_unroll_fires_on_two_level_gather() {
    // Trip 10 (bound 10, init 0): the m1 element load and the m2 ROW load fold to
    // base+immediate; the dependent m2[k][j] element load and its address Madd
    // clone verbatim, threading the per-copy ROW value. 9 folded copies each emit
    // 3 loads (m1 fold + ROW fold + DEP clone) = 27, plus the tail header's 3
    // original LdrRI = 30.
    let mut f = build_matmul_gather(10, GatherOpts::default());
    assert_eq!(run(&mut f), 1);
    assert!(
        gather_full_unrolled(&f),
        "two-level gather must full-unroll"
    );
    assert_eq!(
        count(&f, AArch64Opcode::LdrRI),
        30,
        "9 copies × 3 loads + 3 tail"
    );

    // The folded ROW loads (Gpr64) carry immediates {0,8,..,64}; the folded m1
    // loads (Gpr32) carry {0,4,..,32}. The dependent loads stay at #0.
    let ub = fast_path_block(&f).expect("fast path exists");
    let mut row_imms: Vec<i64> = Vec::new();
    let mut m1_imms: Vec<i64> = Vec::new();
    for &id in &f.block(ub).insts {
        let inst = f.inst(id);
        if inst.opcode != AArch64Opcode::LdrRI {
            continue;
        }
        let imm = imm_of(&inst.operands[2]).unwrap();
        match vreg_of(&inst.operands[0]).unwrap().class {
            RegClass::Gpr64 => row_imms.push(imm),
            _ => m1_imms.push(imm),
        }
    }
    row_imms.sort();
    assert_eq!(
        row_imms,
        (0..=8).map(|c| 8 * c).collect::<Vec<_>>(),
        "ROW fold #8·c"
    );
    m1_imms.sort();
    // Gpr32 loads = 9 m1 folds {0,4,..,32} + 9 dependent clones {0}.
    let mut expect_m1: Vec<i64> = (0..=8)
        .map(|c| 4 * c)
        .chain(std::iter::repeat_n(0, 9))
        .collect();
    expect_m1.sort();
    assert_eq!(
        m1_imms, expect_m1,
        "m1 fold #4·c plus dependent clones at #0"
    );

    // Idempotent: the fast path adds a second outside def of the carried vars.
    assert_eq!(run(&mut f), 0);
}

#[test]
fn full_unroll_gather_threads_row_load_into_dependent_base() {
    // The two-level chain must be PRESERVED: each dependent element load's base
    // is a `Madd` whose pointer addend is a folded ROW load's result (a Gpr64
    // `LdrRI`), NOT a hoisted invariant base. This is what makes the gather a
    // gather rather than a mis-hoist.
    let mut f = build_matmul_gather(10, GatherOpts::default());
    assert_eq!(run(&mut f), 1);
    let ub = fast_path_block(&f).expect("fast path exists");
    // Map each Gpr64 LdrRI (a folded ROW load) def, and each Madd def.
    let row_defs: std::collections::HashSet<u32> = f
        .block(ub)
        .insts
        .iter()
        .filter(|&&id| f.inst(id).opcode == AArch64Opcode::LdrRI)
        .filter(|&&id| vreg_of(&f.inst(id).operands[0]).unwrap().class == RegClass::Gpr64)
        .map(|&id| vreg_of(&f.inst(id).operands[0]).unwrap().id)
        .collect();
    // Dependent element loads: Gpr32 LdrRI at #0 whose base is a Madd reading a
    // ROW def. There must be exactly 9 (one per folded copy).
    let mut dep_count = 0;
    for &id in &f.block(ub).insts {
        let inst = f.inst(id);
        if inst.opcode != AArch64Opcode::LdrRI
            || vreg_of(&inst.operands[0]).unwrap().class != RegClass::Gpr32
            || imm_of(&inst.operands[2]) != Some(0)
        {
            continue;
        }
        let base = vreg_of(&inst.operands[1]).unwrap();
        let madd = f
            .block(ub)
            .insts
            .iter()
            .map(|&x| f.inst(x))
            .find(|i| i.opcode == AArch64Opcode::Madd && vreg_of(&i.operands[0]) == Some(base));
        if let Some(madd) = madd
            && let Some(addend) = vreg_of(&madd.operands[3])
            && row_defs.contains(&addend.id)
        {
            dep_count += 1;
        }
    }
    assert_eq!(
        dep_count, 9,
        "each dependent load reads a per-copy ROW pointer"
    );
}

#[test]
fn full_unroll_collapses_zero_fold_bases() {
    // `init == 0`: every hoisted fold base is emitted as `Madd(zero, scale, ptr)`
    // = `0*scale + ptr = ptr` (the offset slice cloned with `iv -> 0`). The local
    // zero-fold must remove that redundant multiply-add and address the folded
    // loads off the invariant pointer directly — no fast-path `Madd`/`AddRR` may
    // read a materialised zero, and no dead `Movz #0` may survive. This is what
    // the Shootout `matrix` (i,j)-hot preheader needs so it stops re-deriving the
    // two fold bases on every column iteration.
    let mut f = build_matmul_gather(10, GatherOpts::default());
    assert_eq!(run(&mut f), 1);
    let ub = fast_path_block(&f).expect("fast path exists");

    // The `ub`-local zero registers.
    let zero_defs: std::collections::HashSet<u32> = f
        .block(ub)
        .insts
        .iter()
        .filter(|&&id| {
            let inst = f.inst(id);
            inst.opcode == AArch64Opcode::Movz && imm_of(&inst.operands[1]) == Some(0)
        })
        .filter_map(|&id| vreg_of(&f.inst(id).operands[0]).map(|v| v.id))
        .collect();
    // Every `Movz #0` that remains must still be used (no dead materialised zero).
    let used: std::collections::HashSet<u32> = f
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter())
        .flat_map(|&id| f.inst(id).operands.iter().skip(1))
        .filter_map(vreg_of)
        .map(|v| v.id)
        .collect();
    for z in &zero_defs {
        assert!(used.contains(z), "a dead `Movz #0` survived the collapse");
    }

    // No fast-path multiply-add may still read a materialised zero — the base
    // computations that would have are folded to their invariant pointer.
    for &id in &f.block(ub).insts {
        let inst = f.inst(id);
        if matches!(inst.opcode, AArch64Opcode::Madd | AArch64Opcode::AddRR) {
            for op in inst.operands.iter().skip(1) {
                if let Some(v) = vreg_of(op) {
                    assert!(
                        !zero_defs.contains(&v.id),
                        "fast-path {:?} still combines a materialised zero",
                        inst.opcode
                    );
                }
            }
        }
    }

    // The folded ROW loads (Gpr64 `LdrRI`) now address `m2base` (v2) directly;
    // the folded m1 element loads (Gpr32 `LdrRI`, nonzero imm) address `m1row`
    // (v1) directly. The dependent gather loads (Gpr32 at #0) keep their per-copy
    // ROW-pointer base and are left alone.
    for &id in &f.block(ub).insts {
        let inst = f.inst(id);
        if inst.opcode != AArch64Opcode::LdrRI {
            continue;
        }
        let base = vreg_of(&inst.operands[1]).unwrap().id;
        let imm = imm_of(&inst.operands[2]).unwrap();
        match vreg_of(&inst.operands[0]).unwrap().class {
            RegClass::Gpr64 => assert_eq!(base, 2, "ROW fold addresses m2base directly"),
            RegClass::Gpr32 if imm != 0 => assert_eq!(base, 1, "m1 fold addresses m1row directly"),
            _ => {}
        }
    }

    // Idempotent after the collapse.
    assert_eq!(run(&mut f), 0);
}

#[test]
fn full_unroll_gather_preserves_accumulator_chain() {
    // BIT-EXACTNESS: the folded copies feed ONE integer accumulator in order —
    // each `Madd`'s addend (operand 3) is the previous accumulate's result.
    let mut f = build_matmul_gather(10, GatherOpts::default());
    assert_eq!(run(&mut f), 1);
    let ub = fast_path_block(&f).expect("fast path exists");
    // The accumulate Madds are the Gpr32 Madds (val' = m2·m1 + val).
    let accs: Vec<InstId> = f
        .block(ub)
        .insts
        .iter()
        .copied()
        .filter(|&id| {
            f.inst(id).opcode == AArch64Opcode::Madd
                && vreg_of(&f.inst(id).operands[0]).unwrap().class == RegClass::Gpr32
        })
        .collect();
    assert_eq!(accs.len(), 9);
    for w in accs.windows(2) {
        let prev_dst = vreg_of(&f.inst(w[0]).operands[0]).unwrap();
        let next_acc = vreg_of(&f.inst(w[1]).operands[3]).unwrap();
        assert_eq!(
            prev_dst, next_acc,
            "single serial accumulator chain (no reassociation)"
        );
    }
}

#[test]
fn full_unroll_single_level_ldrri_madd_folds() {
    // The new whole-address affine LdrRI fold must also fire WITHOUT a gather: a
    // single-level `Ldr [Madd(iv, #4, ptr), #0]` reduction `val += a[k]*a[k]`
    // (Madd root ⇒ SERIAL, no gather). The load must fold to base+immediate.
    let mut f = MachFunction::new("dot".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let header = f.create_block();
    let exit = f.create_block();
    let latch = f.create_block();
    use AArch64Opcode::*;
    push(&mut f, bb0, Movz, vec![v64(9), i(1)]);
    push(&mut f, bb0, Movz, vec![v64(10), i(0)]);
    push(&mut f, bb0, MovR, vec![v64(12), v64(10)]); // iv = 0
    push(&mut f, bb0, Movz, vec![v32(20), i(0)]); // acc = 0
    push(&mut f, bb0, Movz, vec![v64(15), i(4)]);
    push(&mut f, bb0, Movz, vec![v64(29), i(10)]); // bound
    push(&mut f, bb0, B, vec![b(header)]);
    push(
        &mut f,
        header,
        Madd,
        vec![v64(16), v64(12), v64(15), v64(1)],
    ); // &a[k]
    push(&mut f, header, LdrRI, vec![v32(17), v64(16), i(0)]); // a[k]
    push(
        &mut f,
        header,
        Madd,
        vec![v32(23), v32(17), v32(17), v32(20)],
    ); // val += a·a
    push(&mut f, header, AddRR, vec![v64(28), v64(12), v64(9)]);
    push(&mut f, header, CmpRR, vec![v64(28), v64(29)]);
    push(&mut f, header, BCond, vec![i(CC_EQ), b(exit)]);
    push(&mut f, header, B, vec![b(latch)]);
    push(&mut f, exit, Ret, vec![]);
    push(&mut f, latch, MovR, vec![v64(12), v64(28)]);
    push(&mut f, latch, MovR, vec![v32(20), v32(23)]);
    push(&mut f, latch, B, vec![b(header)]);
    f.add_edge(bb0, header);
    f.add_edge(header, exit);
    f.add_edge(header, latch);
    f.add_edge(latch, header);
    assert_eq!(run(&mut f), 1);
    assert!(
        gather_full_unrolled(&f),
        "single-level affine LdrRI[Madd] must fold"
    );
    // 9 folded copies × 1 load + 1 tail = 10 LdrRI; folded immediates {0,4,..,32}.
    assert_eq!(count(&f, AArch64Opcode::LdrRI), 10);
}

#[test]
fn full_unroll_gather_bails_on_store_in_loop() {
    // A store anywhere in the loop forbids the gather (it could clobber the
    // row-pointer array): full-unroll declines, the 4-wide path clones verbatim.
    let mut f = build_matmul_gather(
        10,
        GatherOpts {
            with_store: true,
            ..Default::default()
        },
    );
    assert_eq!(run(&mut f), 1);
    assert!(
        !gather_full_unrolled(&f),
        "store present: gather refused, 4-wide"
    );
}

#[test]
fn full_unroll_gather_bails_on_three_levels() {
    // A THREE-level chain (pointer-of-pointers) exceeds the two-level bound: the
    // dependent load's ROW load is itself a gather (non-affine address).
    let mut f = build_matmul_gather(
        10,
        GatherOpts {
            three_level: true,
            ..Default::default()
        },
    );
    assert_eq!(run(&mut f), 1);
    assert!(
        !gather_full_unrolled(&f),
        "three-level gather refused, 4-wide"
    );
}

#[test]
fn full_unroll_gather_bails_on_nonaffine_row_offset() {
    // The ROW load's address is `k*k + base` (not affine in iv): it cannot be
    // materialized to a per-copy pointer, so the gather is refused.
    let mut f = build_matmul_gather(
        10,
        GatherOpts {
            nonaffine_row: true,
            ..Default::default()
        },
    );
    assert_eq!(run(&mut f), 1);
    assert!(!gather_full_unrolled(&f), "non-affine row: refused, 4-wide");
}

#[test]
fn full_unroll_gather_bails_on_narrow_row_load() {
    // The ROW load must be a full-width 8-byte pointer. A Gpr32 row load is
    // rejected as a gather row (fold of the narrow load alone cannot rebuild a
    // dependent pointer).
    let mut f = build_matmul_gather(
        10,
        GatherOpts {
            narrow_row: true,
            ..Default::default()
        },
    );
    assert_eq!(run(&mut f), 1);
    assert!(
        !gather_full_unrolled(&f),
        "narrow row: gather refused, 4-wide"
    );
}
