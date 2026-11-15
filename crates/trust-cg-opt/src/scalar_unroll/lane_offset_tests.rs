// trust-cg-opt - Scalar ILP unroll: lane-offset load tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `lane_offset_loads` rewrites an indexed load `LdrRO [d, base, iv, LSL #3]`
//! into `LdrRI [d', p, #8k]` for lane `k`, from one `p = base + iv*8` per
//! main-loop iteration. These tests check two things the gather fixture in
//! `tests.rs` cannot:
//!
//! * the lane-to-offset pairing in an ORDER-SENSITIVE (SERIAL) chain, where
//!   lanes are not interchangeable, both in emission order and by running
//!   the scalar and unrolled functions on the same inputs;
//! * the loop-invariance guard on `base`: a base defined in the body (or a
//!   copy of one) gets no lane pointer, because `p` is computed at the top of
//!   the main-loop block, before any lane defines that base.
//!
//! The differential runs use [`eval`], a strict evaluator for the opcodes these
//! fixtures and the unroll emit. It is evidence for these shapes and inputs,
//! not a model of the ISA and not a proof of the rewrite.

use super::*;
use trust_cg_ir::Signature;

fn v64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn i(x: i64) -> MachOperand {
    MachOperand::Imm(x)
}
fn b(x: BlockId) -> MachOperand {
    MachOperand::Block(x)
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

fn insts(func: &MachFunction) -> impl Iterator<Item = (BlockId, &MachInst)> {
    func.block_order.iter().flat_map(move |&blk| {
        func.block(blk)
            .insts
            .iter()
            .map(move |&id| (blk, func.inst(id)))
    })
}

// ---------------------------------------------------------------------------
// Strict evaluator
// ---------------------------------------------------------------------------

const STEP_BUDGET: usize = 100_000;

/// Run `func` from its entry with `regs` (register id -> 64-bit value) and
/// 8-byte words `mem` (address -> value) until it reaches `exit`; execute
/// `exit` and return register `result`. Fails on an opcode or operand shape
/// it does not model, a read of an unwritten register, an unmapped or
/// unaligned load, a condition read before any compare, a block that ends
/// without a branch before `exit`, or a run longer than [`STEP_BUDGET`].
fn eval(
    func: &MachFunction,
    regs: &[(u32, u64)],
    mem: &HashMap<u64, u64>,
    exit: BlockId,
    result: u32,
) -> Result<u64, String> {
    let mut regs: HashMap<u32, u64> = regs.iter().copied().collect();
    let mut flags: Option<(bool, bool, bool, bool)> = None; // N, Z, C, V
    let mut blk = func.entry;
    let mut steps = 0usize;
    let width = |v: VReg| -> Result<u32, String> {
        match v.class {
            RegClass::Gpr64 => Ok(64),
            RegClass::Gpr32 => Ok(32),
            other => Err(format!("register class {other:?} is not modeled")),
        }
    };
    let mask = |w: u32, x: u64| if w == 64 { x } else { x & 0xffff_ffff };
    'blocks: loop {
        for &id in &func.block(blk).insts {
            steps += 1;
            if steps > STEP_BUDGET {
                return Err("step budget exhausted".to_string());
            }
            let inst = func.inst(id);
            let ops = inst.operands.as_slice();
            let read = |regs: &HashMap<u32, u64>, op: &MachOperand| -> Result<u64, String> {
                let v = op
                    .as_vreg()
                    .ok_or_else(|| format!("{op:?} is not a register"))?;
                let x = regs
                    .get(&v.id)
                    .copied()
                    .ok_or_else(|| format!("read of unwritten v{}", v.id))?;
                Ok(mask(width(v)?, x))
            };
            let imm = |op: &MachOperand| op.as_imm().ok_or_else(|| format!("{op:?} is not an imm"));
            let load = |addr: u64| -> Result<u64, String> {
                if !addr.is_multiple_of(8) {
                    return Err(format!("unaligned load at {addr:#x}"));
                }
                mem.get(&addr)
                    .copied()
                    .ok_or_else(|| format!("unmapped load at {addr:#x}"))
            };
            use AArch64Opcode::*;
            let def = match (inst.opcode, ops) {
                (MovI | Movz, [_, x]) => Some(imm(x)? as u64),
                (MovR, [_, s]) => Some(read(&regs, s)?),
                (AddRR, [_, a, c]) => Some(read(&regs, a)?.wrapping_add(read(&regs, c)?)),
                (MulRR, [_, a, c]) => Some(read(&regs, a)?.wrapping_mul(read(&regs, c)?)),
                (AddRI, [_, a, x]) => Some(read(&regs, a)?.wrapping_add(imm(x)? as u64)),
                (SubRI, [_, a, x]) => Some(read(&regs, a)?.wrapping_sub(imm(x)? as u64)),
                (AddRRShift, [_, a, c, k]) => {
                    let k = imm(k)?;
                    if !(1..64).contains(&k) {
                        return Err(format!("shift {k} out of range"));
                    }
                    Some(read(&regs, a)?.wrapping_add(read(&regs, c)? << k))
                }
                (Sxtw, [_, s]) => Some(read(&regs, s)? as u32 as i32 as i64 as u64),
                (LdrRI, [d, a, x]) if d.as_vreg().map(|v| v.class) == Some(RegClass::Gpr64) => {
                    Some(load(read(&regs, a)?.wrapping_add(imm(x)? as u64))?)
                }
                (LdrRO, [d, a, x, MachOperand::Imm(7)])
                    if d.as_vreg().map(|v| v.class) == Some(RegClass::Gpr64) =>
                {
                    Some(load(read(&regs, a)?.wrapping_add(read(&regs, x)? << 3))?)
                }
                (CmpRR | CmpRI, [a, c]) => {
                    let w = width(a.as_vreg().ok_or("compare of a non-register")?)?;
                    let x = read(&regs, a)?;
                    let y = if inst.opcode == CmpRR {
                        read(&regs, c)?
                    } else {
                        mask(w, imm(c)? as u64)
                    };
                    let r = mask(w, x.wrapping_sub(y));
                    let sign = 1u64 << (w - 1);
                    flags = Some((r & sign != 0, r == 0, x >= y, (x ^ y) & (x ^ r) & sign != 0));
                    None
                }
                (B, [MachOperand::Block(t)]) => {
                    blk = *t;
                    continue 'blocks;
                }
                (BCond, [cc, MachOperand::Block(t)]) => {
                    let (n, z, c, v) = flags.ok_or("condition read before any compare")?;
                    let taken = match imm(cc)? {
                        CC_EQ => z,
                        CC_LO => !c,
                        CC_GE => n == v,
                        CC_LT => n != v,
                        other => return Err(format!("condition {other} is not modeled")),
                    };
                    if taken {
                        blk = *t;
                        continue 'blocks;
                    }
                    None
                }
                _ => return Err(format!("{:?} {ops:?} is not modeled", inst.opcode)),
            };
            if let Some(x) = def {
                let d = ops[0].as_vreg().ok_or("def is not a register")?;
                regs.insert(d.id, mask(width(d)?, x));
            }
        }
        if blk == exit {
            return regs
                .get(&result)
                .copied()
                .ok_or_else(|| format!("result v{result} unwritten"));
        }
        return Err(format!("block {blk:?} ends without a branch"));
    }
}

/// Run `before` and `after` on the same inputs; both must finish, with equal
/// results.
fn same_result(
    before: &MachFunction,
    after: &MachFunction,
    regs: &[(u32, u64)],
    mem: &HashMap<u64, u64>,
    exit: BlockId,
    what: &str,
) {
    let want = eval(before, regs, mem, exit, 20).unwrap_or_else(|e| panic!("{what}: scalar: {e}"));
    let got = eval(after, regs, mem, exit, 20).unwrap_or_else(|e| panic!("{what}: unrolled: {e}"));
    assert_eq!(got, want, "{what}");
}

/// Distinct, order-revealing element values.
fn element(k: u64) -> u64 {
    (k + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

// ---------------------------------------------------------------------------
// SERIAL: `acc = acc * 31 + a[k]`
// ---------------------------------------------------------------------------

/// TOP-TESTED signed `k < n` loop over a 64-bit array whose step is not
/// commutative across iterations, so the unroll is SERIAL:
///
/// ```text
/// bb0:    v0=a v1=n v5=MovI#0(k) v6=MovI#7(acc) v7=MovI#31; B header
/// header: CmpRR v5,v1 ; BCond(LT, latch) ; B exit
/// latch:  v10=LdrRO[v0,v5,LSL #3] ; v11=MulRR v6,v7 ; v12=AddRR v11,v10 ;
///         v13=AddRI v5,#1 ; v6=MovR v12 ; v5=MovR v13 ; B header
/// exit:   v20=MovR v6
/// ```
fn build_horner() -> MachFunction {
    let mut f = MachFunction::new("horner".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    use AArch64Opcode::*;
    push(&mut f, bb0, MovI, vec![v64(5), i(0)]);
    push(&mut f, bb0, MovI, vec![v64(6), i(7)]);
    push(&mut f, bb0, MovI, vec![v64(7), i(31)]);
    push(&mut f, bb0, B, vec![b(header)]);
    push(&mut f, header, CmpRR, vec![v64(5), v64(1)]);
    push(&mut f, header, BCond, vec![i(CC_LT), b(latch)]);
    push(&mut f, header, B, vec![b(exit)]);
    push(&mut f, latch, LdrRO, vec![v64(10), v64(0), v64(5), i(7)]);
    push(&mut f, latch, MulRR, vec![v64(11), v64(6), v64(7)]);
    push(&mut f, latch, AddRR, vec![v64(12), v64(11), v64(10)]);
    push(&mut f, latch, AddRI, vec![v64(13), v64(5), i(1)]);
    push(&mut f, latch, MovR, vec![v64(6), v64(12)]);
    push(&mut f, latch, MovR, vec![v64(5), v64(13)]);
    push(&mut f, latch, B, vec![b(header)]);
    push(&mut f, exit, MovR, vec![v64(20), v64(6)]);
    f.add_edge(bb0, header);
    f.add_edge(header, latch);
    f.add_edge(header, exit);
    f.add_edge(latch, header);
    f
}

#[test]
fn serial_lane_offsets_follow_lane_order() {
    let scalar = build_horner();
    let mut f = scalar.clone();
    assert_eq!(run(&mut f), 1, "the SERIAL unroll fires");
    // One lane pointer `p = a + k*8`, at the top of the main-loop block.
    let (ub, p) = insts(&f)
        .find(|(_, inst)| inst.opcode == AArch64Opcode::AddRRShift)
        .map(|(blk, inst)| (blk, inst.operands.clone()))
        .expect("a lane pointer");
    assert_eq!(p[1..], [v64(0), v64(5), i(3)]);
    // In emission order, lane k reads `[p, #8k]`: each lane's load feeds the
    // multiply-add of the same lane, and lane k runs after lane k-1.
    let offsets: Vec<i64> = f
        .block(ub)
        .insts
        .iter()
        .map(|&id| f.inst(id))
        .filter(|inst| inst.opcode == AArch64Opcode::LdrRI && inst.operands[1] == p[0])
        .map(|inst| inst.operands[2].as_imm().unwrap())
        .collect();
    assert_eq!(offsets, vec![0, 8, 16, 24]);
    // And the result matches the scalar loop for every trip count around the
    // unroll width, including a negative `n` (the signed loop runs 0 times).
    let base = 0x1000_0000u64;
    let mem: HashMap<u64, u64> = (0..16u64).map(|k| (base + 8 * k, element(k))).collect();
    let exit = BlockId(3);
    for n in (0..=13i64).chain([-1, i64::MIN]) {
        same_result(
            &scalar,
            &f,
            &[(0, base), (1, n as u64)],
            &mem,
            exit,
            &format!("horner n={n}"),
        );
    }
}

// ---------------------------------------------------------------------------
// SPLIT gather: where the indexed load's base comes from
// ---------------------------------------------------------------------------

/// Where the gather's `LdrRO` base comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Base {
    /// The loop-invariant input `v2` itself.
    Invariant,
    /// A body copy `v31 = MovR v2` of the invariant input.
    CopyOfInvariant,
    /// A body load `v30 = LdrRI [v0, #0]` (same value every iteration, but
    /// defined in the loop).
    Loaded,
    /// A body copy `v31 = MovR v30` of that body load.
    CopyOfLoaded,
}

/// `h3_box_leak`'s gather sum (`acc += *a[k]`, widened unsigned header with
/// copies) with the array pointer taken per [`Base`]. `v0` points at a cell
/// holding the array address, `v2` is the array address itself.
fn build_gather(base: Base) -> MachFunction {
    let mut f = MachFunction::new("gather".to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let header = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    use AArch64Opcode::*;
    push(&mut f, bb0, MovI, vec![v64(5), i(0)]);
    push(&mut f, bb0, MovI, vec![v64(6), i(0)]);
    push(&mut f, bb0, B, vec![b(header)]);
    push(&mut f, header, MovR, vec![v64(8), v64(5)]);
    push(&mut f, header, MovR, vec![v64(9), v64(1)]);
    push(&mut f, header, CmpRR, vec![v64(8), v64(9)]);
    push(&mut f, header, BCond, vec![i(CC_LO), b(latch)]);
    push(&mut f, header, B, vec![b(exit)]);
    let arr = match base {
        Base::Invariant => v64(2),
        Base::CopyOfInvariant => {
            push(&mut f, latch, MovR, vec![v64(31), v64(2)]);
            v64(31)
        }
        Base::Loaded => {
            push(&mut f, latch, LdrRI, vec![v64(30), v64(0), i(0)]);
            v64(30)
        }
        Base::CopyOfLoaded => {
            push(&mut f, latch, LdrRI, vec![v64(30), v64(0), i(0)]);
            push(&mut f, latch, MovR, vec![v64(31), v64(30)]);
            v64(31)
        }
    };
    push(&mut f, latch, LdrRO, vec![v64(10), arr, v64(5), i(7)]);
    push(&mut f, latch, LdrRI, vec![v64(11), v64(10), i(0)]);
    push(&mut f, latch, AddRR, vec![v64(12), v64(6), v64(11)]);
    push(&mut f, latch, AddRI, vec![v64(13), v64(5), i(1)]);
    push(&mut f, latch, MovR, vec![v64(6), v64(12)]);
    push(&mut f, latch, MovR, vec![v64(5), v64(13)]);
    push(&mut f, latch, B, vec![b(header)]);
    push(&mut f, exit, MovR, vec![v64(20), v64(6)]);
    f.add_edge(bb0, header);
    f.add_edge(header, latch);
    f.add_edge(header, exit);
    f.add_edge(latch, header);
    f
}

#[test]
fn lane_pointer_base_must_be_loop_invariant() {
    let cell = 0x0800_0000u64;
    let array = 0x1000_0000u64;
    let boxes = 0x2000_0000u64;
    let mut mem: HashMap<u64, u64> = HashMap::default();
    mem.insert(cell, array);
    for k in 0..16u64 {
        mem.insert(array + 8 * k, boxes + 8 * k);
        mem.insert(boxes + 8 * k, element(k));
    }
    let exit = BlockId(3);
    for (base, lane_pointer_base) in [
        (Base::Invariant, Some(v64(2))),
        (Base::CopyOfInvariant, Some(v64(2))),
        // The base is defined in the body: a lane pointer computed at the top
        // of the main-loop block would read it before any lane defines it.
        (Base::Loaded, None),
        (Base::CopyOfLoaded, None),
    ] {
        let scalar = build_gather(base);
        let mut f = scalar.clone();
        assert_eq!(run(&mut f), 1, "{base:?}: the SPLIT unroll fires");
        let pointers: Vec<MachOperand> = insts(&f)
            .filter(|(_, inst)| inst.opcode == AArch64Opcode::AddRRShift)
            .map(|(_, inst)| inst.operands[1].clone())
            .collect();
        assert_eq!(
            pointers,
            lane_pointer_base.into_iter().collect::<Vec<_>>(),
            "{base:?}: lane pointer bases"
        );
        for n in 0..=13u64 {
            same_result(
                &scalar,
                &f,
                &[(0, cell), (1, n), (2, array)],
                &mem,
                exit,
                &format!("{base:?} n={n}"),
            );
        }
    }
}

#[test]
fn evaluator_negative_controls() {
    // Negative controls for the oracle itself: an unwritten register, an
    // unmapped load and a lane pointer read before its base is defined all
    // fail rather than produce a value.
    let mem: HashMap<u64, u64> = HashMap::default();
    let scalar = build_horner();
    let exit = BlockId(3);
    let err = eval(&scalar, &[(1, 2)], &mem, exit, 20).unwrap_err();
    assert!(err.contains("unwritten v0"), "{err}");
    let err = eval(&scalar, &[(0, 0x1000), (1, 2)], &mem, exit, 20).unwrap_err();
    assert!(err.contains("unmapped load"), "{err}");
    // A mis-paired lane (offsets swapped between lanes 1 and 2) changes the
    // SERIAL result, so the differential in
    // `serial_lane_offsets_follow_lane_order` can see it.
    let mut f = scalar.clone();
    assert_eq!(run(&mut f), 1);
    let swapped: Vec<InstId> = f
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| {
            let inst = f.inst(id);
            inst.opcode == AArch64Opcode::LdrRI
                && matches!(inst.operands[2], MachOperand::Imm(8 | 16))
        })
        .collect();
    assert_eq!(swapped.len(), 2);
    for &id in &swapped {
        let off = f.inst(id).operands[2].as_imm().unwrap();
        f.inst_mut(id).operands[2] = i(24 - off);
    }
    let base = 0x1000_0000u64;
    let mem: HashMap<u64, u64> = (0..8u64).map(|k| (base + 8 * k, element(k))).collect();
    let regs = [(0, base), (1, 4)];
    assert_ne!(
        eval(&f, &regs, &mem, exit, 20).unwrap(),
        eval(&scalar, &regs, &mem, exit, 20).unwrap(),
        "a lane permutation must be observable"
    );
    // A lane pointer hoisted from a loop-defined base (what the invariance
    // guard refuses) reads an unwritten register on the first main-loop
    // iteration, so the differential in `lane_pointer_base_must_be_loop_invariant`
    // can see it.
    let mut g = build_gather(Base::Loaded);
    assert_eq!(run(&mut g), 1);
    let ub = g
        .block_order
        .iter()
        .copied()
        .find(|&blk| {
            g.block(blk)
                .insts
                .iter()
                .filter(|&&id| g.inst(id).opcode == AArch64Opcode::LdrRO)
                .count()
                == 4
        })
        .expect("the main-loop block holds the four lanes");
    let hoisted = g.push_inst(MachInst::new(
        AArch64Opcode::AddRRShift,
        vec![v64(900), v64(30), v64(5), i(3)],
    ));
    g.block_mut(ub).insts.insert(0, hoisted);
    let cell = 0x0800_0000u64;
    let array = 0x1000_0000u64;
    let mut mem: HashMap<u64, u64> = HashMap::default();
    mem.insert(cell, array);
    for k in 0..8u64 {
        mem.insert(array + 8 * k, array + 8 * k);
    }
    let err = eval(&g, &[(0, cell), (1, 8), (2, array)], &mem, exit, 20).unwrap_err();
    assert!(err.contains("unwritten v30"), "{err}");
}
