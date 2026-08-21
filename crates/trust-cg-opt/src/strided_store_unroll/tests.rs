// Unit tests for the `strided-store-unroll` counted-strided-store partial-unroll.
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
fn count_op(func: &MachFunction, op: AArch64Opcode) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}
/// Count `BCond` instructions with the given condition-code immediate.
fn count_bcond_cc(func: &MachFunction, cc: i64) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::BCond && imm_of(&inst.operands[0]) == Some(cc)
        })
        .count()
}
/// Count `MovR` whose destination is `reg`.
fn count_movr_to(func: &MachFunction, reg: u32) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::MovR
                && vreg_of(&inst.operands[0]).map(|v| v.id) == Some(reg)
        })
        .count()
}
/// The `BlockId` of the (unique) block containing exactly four `StrbRI` — the
/// unrolled main body `mb`.
fn main_body(func: &MachFunction) -> Option<BlockId> {
    func.blocks
        .iter()
        .enumerate()
        .find(|(_, b)| {
            b.insts
                .iter()
                .filter(|&&id| func.inst(id).opcode == AArch64Opcode::StrbRI)
                .count()
                == 4
        })
        .map(|(idx, _)| BlockId(idx as u32))
}

/// How the loop bound is expressed.
#[derive(Clone, Copy, PartialEq)]
enum BoundK {
    /// `CmpRR iv, Nreg` with `Nreg = Movz #n` — the exact p7 shape.
    ConstReg(i64),
    /// `CmpRI iv, #n`.
    ConstImm(i64),
    /// `CmpRR iv, nreg` with `nreg` a runtime-invariant (non-const) register.
    Runtime,
}

/// Negative-control mutations of the canonical native strided-store loop.
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Good,
    /// stride redefined INSIDE the body (not loop-invariant) -> BAIL.
    StrideInLoop,
    /// iv step is `next = iv + iv` (stride resolves to iv, not invariant) -> BAIL.
    StrideIsSecondIv,
    /// stride is a Gpr32 register (not a single Gpr64) -> BAIL.
    Gpr32Stride,
    /// two stores in the body -> BAIL.
    TwoStores,
    /// a load (LdrbRI) in the body -> BAIL (closed-world reject).
    WithLoad,
    /// a call (Bl) in the body -> BAIL (closed-world reject).
    WithCall,
    /// stored value redefined in the body (loop-variant) -> BAIL.
    ValueInLoop,
    /// rotated do-while: the `iv < N` continue-test is in the LATCH -> BAIL.
    Rotated,
    /// the BOUND register is redefined in the body, so it is loop-carried and
    /// the def map (last-wins over the emitted layout) reports the LATCH value
    /// instead of the one the entry test used -> BAIL.
    BoundInLoop,
    /// stride has a SECOND def OUTSIDE the inner body (an enclosing-IV analog: a
    /// later, non-dominating redef) -> still inner-loop-invariant, must FIRE.
    StrideMultiDef,
}

struct Cfg {
    variant: Variant,
    bound: BoundK,
    /// Initial iv value `q0`.
    q0: i64,
    /// The stride constant baked into the invariant stride register (its runtime
    /// value; the recognizer treats stride as an opaque invariant register).
    stride: i64,
}

impl Default for Cfg {
    fn default() -> Self {
        Cfg {
            variant: Variant::Good,
            bound: BoundK::ConstReg(1024),
            q0: 4,
            stride: 2,
        }
    }
}

/// Build a NATIVE (pre-tested) counted strided-store loop matching the p7 sieve
/// marking loop shape:
/// ```text
/// bb0:     base/stride/value/N/iv setup; B header
/// header:  iv_c = copy iv; cmp iv_c, N; b.lo mid; (fallthrough) exit   // native test
/// mid:     dead = copy iv; B latch
/// latch:   addr = base + iv; *addr = val; next = iv + stride; iv = copy next; B header
/// exit:    ret
/// ```
/// Register map: x0=base, x2=stride(Gpr64 invariant), w3=value, x10=iv,
/// x11=Nreg/runtime-bound, x12=iv-copy, x13=dead-copy, x20=addr, x21=next,
/// w4=gpr32-stride (Gpr32Stride variant only).
fn build_strided(cfg: Cfg) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let mid = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    let rotated = cfg.variant == Variant::Rotated;

    // --- bb0: loop-invariant setup (defs dominate the header preheader).
    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base invariant
    push(&mut func, bb0, Copy, vec![x(2), x(2)]); // stride invariant (opaque runtime)
    push(&mut func, bb0, Movz, vec![w(3), i(1)]); // value = 1
    if cfg.variant == Variant::Gpr32Stride {
        push(&mut func, bb0, Movz, vec![w(4), i(cfg.stride)]); // Gpr32 stride
    }
    match cfg.bound {
        BoundK::ConstReg(n) => {
            push(&mut func, bb0, Movz, vec![x(11), i(n)]);
        }
        BoundK::Runtime => {
            push(&mut func, bb0, Copy, vec![x(11), x(11)]); // runtime-invariant bound
        }
        BoundK::ConstImm(_) => {}
    }
    push(&mut func, bb0, Movz, vec![x(10), i(cfg.q0)]); // iv = q0
    push(&mut func, bb0, B, vec![bl(header)]);

    // The store's stride register (the non-iv addend of the step).
    let stride_reg = if cfg.variant == Variant::Gpr32Stride {
        w(4)
    } else {
        x(2)
    };

    // Emit the loop-body instructions (address, store, step, writeback) into
    // `into`. In the NATIVE shape this is the latch; in ROTATED it is the header.
    let emit_body = |func: &mut MachFunction, into: BlockId| {
        if cfg.variant == Variant::WithLoad {
            push(func, into, LdrbRI, vec![w(30), x(0), i(0)]);
        }
        if cfg.variant == Variant::WithCall {
            push(func, into, Bl, vec![i(0)]);
        }
        push(func, into, AddRR, vec![x(20), x(0), x(10)]); // addr = base + iv
        if cfg.variant == Variant::ValueInLoop {
            push(func, into, Movz, vec![w(3), i(1)]); // redefine value in body
        }
        push(func, into, StrbRI, vec![w(3), x(20), i(0)]); // *addr = val
        if cfg.variant == Variant::TwoStores {
            push(func, into, StrbRI, vec![w(3), x(20), i(0)]);
        }
        if cfg.variant == Variant::StrideInLoop {
            push(func, into, Movz, vec![x(2), i(cfg.stride)]); // redefine stride in body
        }
        if cfg.variant == Variant::BoundInLoop {
            // A SECOND, larger value for the bound register. The entry test used
            // the bb0 `Movz x11, n`; this one wins the def map.
            push(func, into, Movz, vec![x(11), i(4096)]);
        }
        // next = iv + stride.
        match cfg.variant {
            Variant::StrideIsSecondIv => push(func, into, AddRR, vec![x(21), x(10), x(10)]),
            _ => push(func, into, AddRR, vec![x(21), x(10), stride_reg.clone()]),
        }
    };

    if rotated {
        // --- ROTATED do-while: header carries the body + writeback; latch tests.
        emit_body(&mut func, header);
        push(&mut func, header, MovR, vec![x(10), x(21)]); // iv = next (in header)
        push(&mut func, header, B, vec![bl(latch)]);

        push(&mut func, latch, CmpRR, vec![x(10), x(11)]);
        push(&mut func, latch, BCond, vec![i(CC_LO), bl(header)]);
        push(&mut func, latch, B, vec![bl(exit)]);
    } else {
        // --- NATIVE: header pre-tests iv < N.
        push(&mut func, header, MovR, vec![x(12), x(10)]); // iv copy
        match cfg.bound {
            BoundK::ConstReg(_) | BoundK::Runtime => {
                push(&mut func, header, CmpRR, vec![x(12), x(11)]);
            }
            BoundK::ConstImm(n) => {
                push(&mut func, header, CmpRI, vec![x(12), i(n)]);
            }
        }
        push(&mut func, header, BCond, vec![i(CC_LO), bl(mid)]);
        push(&mut func, header, B, vec![bl(exit)]);

        push(&mut func, mid, MovR, vec![x(13), x(10)]); // dead copy of iv
        push(&mut func, mid, B, vec![bl(latch)]);

        emit_body(&mut func, latch);
        push(&mut func, latch, MovR, vec![x(10), x(21)]); // iv = next (writeback)
        push(&mut func, latch, B, vec![bl(header)]);
    }

    if cfg.variant == Variant::StrideMultiDef {
        // A SECOND def of the stride register (x2), OUTSIDE the inner body, that
        // does NOT dominate the preheader — the analog of an enclosing scan
        // loop's outer-latch `stride = stride + 1` writeback. Pushed late so the
        // single-def / last-index-wins `def` map resolves x2 to THIS
        // non-dominating def: exactly the shape that made the pass bail "stride
        // not loop-invariant". The dominating init (`Copy x2,x2` in bb0) still
        // makes x2 available, and no def is in the body, so it IS invariant.
        push(&mut func, exit, AddRI, vec![x(2), x(2), i(1)]);
    }
    push(&mut func, exit, Ret, vec![]);

    // Edges.
    func.add_edge(bb0, header);
    if rotated {
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
    } else {
        func.add_edge(header, mid);
        func.add_edge(header, exit);
        func.add_edge(mid, latch);
        func.add_edge(latch, header);
    }
    func
}

fn run(func: &mut MachFunction) -> (bool, usize) {
    let mut pass = StridedStoreUnroll::new();
    let changed = pass.run(func);
    (changed, pass.fired())
}

// ---------------------------------------------------------------------------
// POSITIVE
// ---------------------------------------------------------------------------

#[test]
fn fires_on_native_sieve_shape() {
    let mut func = build_strided(Cfg {
        bound: BoundK::ConstReg(1024),
        ..Cfg::default()
    });
    let strb_before = count_op(&func, AArch64Opcode::StrbRI);
    assert_eq!(strb_before, 1, "one scalar store before");
    let (changed, fired) = run(&mut func);
    assert!(
        changed && fired == 1,
        "native sieve shape should partially unroll"
    );

    // The scalar store is untouched; the main body adds four more (1 + 4 = 5).
    assert_eq!(
        count_op(&func, AArch64Opcode::StrbRI),
        5,
        "scalar store + 4 unrolled"
    );

    // Exactly one main body block with four stores.
    let mb = main_body(&func).expect("a 4-store main body block exists");

    // Guards: one Cbz (s==0), the HS bails (s>=N, 3s>=N), the LO main-header test.
    assert_eq!(count_op(&func, AArch64Opcode::Cbz), 1, "one s==0 Cbz guard");
    assert_eq!(
        count_bcond_cc(&func, CC_HS),
        2,
        "two HS bail guards (s>=N, 3s>=N)"
    );
    assert!(
        count_bcond_cc(&func, CC_LO) >= 2,
        "main header LO guard (plus scalar's)"
    );
    // lim = N - 3s : one SubRR; 3s : two AddRR in g3 (t2, t3).
    assert_eq!(count_op(&func, AArch64Opcode::SubRR), 1, "one lim = N - 3s");

    // The shared iv (x10) is advanced IN-PLACE inside the main body by an AddRR.
    let iv_advanced_in_mb = func.block(mb).insts.iter().any(|&id| {
        let ins = func.inst(id);
        ins.opcode == AArch64Opcode::AddRR && vreg_of(&ins.operands[0]).map(|v| v.id) == Some(10)
    });
    assert!(
        iv_advanced_in_mb,
        "shared iv (x10) advanced in the main body"
    );
    // The scalar latch's iv writeback is untouched.
    assert_eq!(
        count_movr_to(&func, 10),
        1,
        "scalar latch iv writeback intact"
    );

    // The four main-body stores address base+q, base+q+s, base+q+2s, base+q+3s.
    check_unrolled_addresses(
        &func, mb, /*base=*/ 0, /*iv=*/ 10, /*stride=*/ 2,
    );
}

#[test]
fn fires_on_multidef_invariant_stride() {
    // The stride register x2 has TWO defs: the dominating init in bb0 and a
    // later, NON-dominating redef in the exit block (an enclosing-IV analog).
    // Neither def is in the inner body, so x2 IS inner-loop-invariant; the
    // corrected all-defs availability scan recognizes this and unrolls. The old
    // single-def / last-index-wins dominance check resolved x2 to the exit redef
    // and bailed "stride not loop-invariant".
    let mut func = build_strided(Cfg {
        variant: Variant::StrideMultiDef,
        ..Cfg::default()
    });
    let (changed, fired) = run(&mut func);
    assert!(
        changed && fired == 1,
        "multi-def invariant stride should partially unroll"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::StrbRI),
        5,
        "scalar store + 4 unrolled"
    );
    let mb = main_body(&func).expect("a 4-store main body block exists");
    check_unrolled_addresses(
        &func, mb, /*base=*/ 0, /*iv=*/ 10, /*stride=*/ 2,
    );
}

#[test]
fn fires_on_cmpri_const_bound() {
    let mut func = build_strided(Cfg {
        bound: BoundK::ConstImm(1024),
        ..Cfg::default()
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1, "CmpRI const bound should unroll");
    assert_eq!(count_op(&func, AArch64Opcode::StrbRI), 5);
    // N=1024 is re-materialized in g1 for the runtime s>=N compare.
    assert!(
        count_op(&func, AArch64Opcode::Movz) >= 1,
        "N re-materialized via Movz for the s>=N guard"
    );
    assert!(main_body(&func).is_some());
}

/// Symbolically evaluate a register as `cq*q + cs*stride + cb*base` by walking
/// function-wide `AddRR`/`MovR`/`Copy` defs (so it resolves the precomputed
/// `2s = s+s`, `3s = t2+s` multiples and the running `ptr = base+q` — which live
/// in different blocks). `iv`/`stride`/`base` are treated as leaf symbols.
fn coef(
    func: &MachFunction,
    iv: u32,
    stride: u32,
    base: u32,
    reg: u32,
    depth: u32,
) -> Option<(i64, i64, i64)> {
    if reg == iv {
        return Some((1, 0, 0));
    }
    if reg == stride {
        return Some((0, 1, 0));
    }
    if reg == base {
        return Some((0, 0, 1));
    }
    if depth == 0 {
        return None;
    }
    let d = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .rfind(|&id| {
            let ins = func.inst(id);
            let mut defines = false;
            crate::effects::for_each_inst_def(ins, |v| {
                if v.id == reg {
                    defines = true;
                }
            });
            defines
        })?;
    let inst = func.inst(d);
    match inst.opcode {
        AArch64Opcode::AddRR if inst.operands.len() == 3 => {
            let a = coef(
                func,
                iv,
                stride,
                base,
                vreg_of(&inst.operands[1])?.id,
                depth - 1,
            )?;
            let b = coef(
                func,
                iv,
                stride,
                base,
                vreg_of(&inst.operands[2])?.id,
                depth - 1,
            )?;
            Some((a.0 + b.0, a.1 + b.1, a.2 + b.2))
        }
        AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => coef(
            func,
            iv,
            stride,
            base,
            vreg_of(&inst.operands[1])?.id,
            depth - 1,
        ),
        _ => None,
    }
}

/// Verify the four unrolled stores address `base+q, base+q+s, base+q+2s,
/// base+q+3s`: each store's address resolves symbolically to `base + q + k*s`.
fn check_unrolled_addresses(func: &MachFunction, mb: BlockId, base: u32, iv: u32, stride: u32) {
    let store_addrs: Vec<u32> = func
        .block(mb)
        .insts
        .iter()
        .copied()
        .filter(|&id| func.inst(id).opcode == AArch64Opcode::StrbRI)
        .map(|id| vreg_of(&func.inst(id).operands[1]).unwrap().id)
        .collect();
    assert_eq!(store_addrs.len(), 4, "four unrolled stores");

    for (k, &a) in store_addrs.iter().enumerate() {
        let c = coef(func, iv, stride, base, a, 12).expect("address resolves in (q, stride, base)");
        assert_eq!(
            c,
            (1, k as i64, 1),
            "store {k} address is base + q + {k}*stride (got {c:?})"
        );
    }
}

// ---------------------------------------------------------------------------
// FAIL-SAFE NEGATIVE CONTROLS
// ---------------------------------------------------------------------------

fn assert_bails(cfg: Cfg, why: &str) {
    let mut func = build_strided(cfg);
    let strb_before = count_op(&func, AArch64Opcode::StrbRI);
    let (changed, fired) = run(&mut func);
    assert!(!changed && fired == 0, "must BAIL: {why}");
    // No stores added, no Cbz/guard blocks spliced.
    assert_eq!(
        count_op(&func, AArch64Opcode::StrbRI),
        strb_before,
        "no store added: {why}"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::Cbz),
        0,
        "no guard spliced: {why}"
    );
}

#[test]
fn bails_on_stride_in_loop() {
    assert_bails(
        Cfg {
            variant: Variant::StrideInLoop,
            ..Cfg::default()
        },
        "stride redefined inside the body (not loop-invariant)",
    );
}

#[test]
fn bails_on_second_induction_stride() {
    assert_bails(
        Cfg {
            variant: Variant::StrideIsSecondIv,
            ..Cfg::default()
        },
        "iv step is a second induction var (stride == iv, not invariant)",
    );
}

#[test]
fn bails_on_gpr32_stride() {
    assert_bails(
        Cfg {
            variant: Variant::Gpr32Stride,
            ..Cfg::default()
        },
        "stride is not a single Gpr64 register",
    );
}

#[test]
fn bails_on_two_stores() {
    assert_bails(
        Cfg {
            variant: Variant::TwoStores,
            ..Cfg::default()
        },
        "two stores in the body",
    );
}

#[test]
fn bails_on_load() {
    assert_bails(
        Cfg {
            variant: Variant::WithLoad,
            ..Cfg::default()
        },
        "a load in the body (closed-world reject)",
    );
}

#[test]
fn bails_on_call() {
    assert_bails(
        Cfg {
            variant: Variant::WithCall,
            ..Cfg::default()
        },
        "a call in the body (closed-world reject)",
    );
}

#[test]
fn bails_on_value_in_loop() {
    assert_bails(
        Cfg {
            variant: Variant::ValueInLoop,
            ..Cfg::default()
        },
        "stored value is loop-variant (defined in body)",
    );
}

#[test]
fn bails_on_runtime_bound() {
    assert_bails(
        Cfg {
            bound: BoundK::Runtime,
            ..Cfg::default()
        },
        "non-constant (runtime) bound N",
    );
}

#[test]
fn bails_on_rotated_loop() {
    assert_bails(
        Cfg {
            variant: Variant::Rotated,
            ..Cfg::default()
        },
        "rotated do-while (continue-test in latch, not header)",
    );
}

// ---------------------------------------------------------------------------
// OVERFLOW / ZERO-STRIDE STRUCTURAL GUARDS (compile-time structure; the runtime
// routing of huge/zero strides to the scalar loop is exercised on-host)
// ---------------------------------------------------------------------------

#[test]
fn overflow_and_zero_stride_routed_by_pre_guards() {
    // The pass fires (stride is an opaque register), and the emitted pre-guards
    // route a runtime `s >= N` (which would make a naive q+3s wrap) and a runtime
    // `s == 0` (non-advancing) to the scalar loop BEFORE any main-loop store.
    let mut func = build_strided(Cfg::default());
    let (changed, _) = run(&mut func);
    assert!(
        changed,
        "fires; the guards are runtime, not a compile-time bail"
    );

    // g1: `Cmp s, N; B.HS -> scalar` foreclosing the q+3s wrap for huge s.
    assert!(
        count_bcond_cc(&func, CC_HS) >= 1,
        "s>=N HS pre-guard present (no wrap on huge s)"
    );
    // g2: `Cbz s -> scalar` foreclosing the non-advancing s==0 main loop.
    assert_eq!(
        count_op(&func, AArch64Opcode::Cbz),
        1,
        "s==0 Cbz pre-guard present"
    );
    // The `s < N` guard dominates the `3s`/`lim` compute, so lim is only used on
    // the in-range path: exactly one SubRR (lim = N - 3s).
    assert_eq!(count_op(&func, AArch64Opcode::SubRR), 1);
}

// ---------------------------------------------------------------------------
// GUARD-CORRECTNESS STRUCTURAL: N=1024, s=2, q0=4
// ---------------------------------------------------------------------------

#[test]
fn guard_correctness_structure_n1024_s2_q4() {
    let mut func = build_strided(Cfg {
        bound: BoundK::ConstImm(1024),
        q0: 4,
        stride: 2,
        variant: Variant::Good,
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1);

    // N=1024 materialized once (Movz #1024) for the guards.
    let movz_1024 = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .filter(|&id| {
            let ins = func.inst(id);
            ins.opcode == AArch64Opcode::Movz && imm_of(&ins.operands[1]) == Some(1024)
        })
        .count();
    assert_eq!(movz_1024, 1, "N=1024 re-materialized once in g1");

    // The main-header guard is `Cmp q, lim ; B.LO -> mb`.
    assert!(
        count_bcond_cc(&func, CC_LO) >= 2,
        "main-header LO guard present"
    );
    assert_eq!(count_op(&func, AArch64Opcode::SubRR), 1, "lim = N - 3s");

    // The four store indices are consecutive +s and structurally < N by
    // construction (proven by the emitted `q <u lim = N-3s` guard).
    let mb = main_body(&func).expect("main body exists");
    check_unrolled_addresses(&func, mb, 0, 10, 2);
}

// The compile-time kill switch `TCG_NO_STRIDED_STORE_UNROLL` is NOT unit-tested
// here: `ssu_enabled()` reads the PROCESS-WIDE env var, so a test that mutates it
// races with cargo's parallel test threads (flaking unrelated fire-tests). The
// switch is instead validated on-host — every `bridge pass-OFF` A/B build sets
// `TCG_NO_STRIDED_STORE_UNROLL=1` and is confirmed to emit the un-unrolled scalar
// loop while still MATCHing. The per-pass bisect key
// (`TRUST_CG_DISABLE_PASSES=strided_store_unroll`) IS unit-tested, via the
// thread-local override in `pipeline::tests`.

// ---------------------------------------------------------------------------
// UNCONDITIONAL-STORE GATE (the store's block must dominate the latch)
// ---------------------------------------------------------------------------

/// Build the strided marking loop with an EXTRA in-body conditional in front of
/// the store block:
///
/// ```text
/// bb0:    setup; B header
/// header: iv_c = copy iv; cmp iv_c, Nreg; b.lo chk; B exit
/// chk:    cmp iv, guard; b.lo st; B <side>
/// st:     addr = base + iv; *addr = val; B latch
/// latch:  next = iv + stride; iv = copy next; B header
/// exit:   ret
/// ```
///
/// * `skip_store == true`  -> `<side>` REJOINS the loop at `latch`, i.e.
///   `if c { base[iv] = v; }` — the store does NOT dominate the latch.
/// * `skip_store == false` -> `<side>` LEAVES the loop (the p7 residual
///   bounds-check shape) — the store block still dominates the latch.
fn build_guarded_store(skip_store: bool) -> MachFunction {
    use AArch64Opcode::*;
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let chk = func.create_block();
    let st = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let side = if skip_store { latch } else { exit };

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };

    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base
    push(&mut func, bb0, Copy, vec![x(2), x(2)]); // stride (invariant)
    push(&mut func, bb0, Movz, vec![w(3), i(1)]); // value
    push(&mut func, bb0, Movz, vec![x(11), i(1024)]); // N
    push(&mut func, bb0, Copy, vec![x(14), x(14)]); // opaque guard operand
    push(&mut func, bb0, Movz, vec![x(10), i(4)]); // iv = q0
    push(&mut func, bb0, B, vec![bl(header)]);

    push(&mut func, header, MovR, vec![x(12), x(10)]);
    push(&mut func, header, CmpRR, vec![x(12), x(11)]);
    push(&mut func, header, BCond, vec![i(CC_LO), bl(chk)]);
    push(&mut func, header, B, vec![bl(exit)]);

    push(&mut func, chk, CmpRR, vec![x(10), x(14)]);
    push(&mut func, chk, BCond, vec![i(CC_LO), bl(st)]);
    push(&mut func, chk, B, vec![bl(side)]);

    push(&mut func, st, AddRR, vec![x(20), x(0), x(10)]);
    push(&mut func, st, StrbRI, vec![w(3), x(20), i(0)]);
    push(&mut func, st, B, vec![bl(latch)]);

    push(&mut func, latch, AddRR, vec![x(21), x(10), x(2)]);
    push(&mut func, latch, MovR, vec![x(10), x(21)]);
    push(&mut func, latch, B, vec![bl(header)]);

    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, header);
    func.add_edge(header, chk);
    func.add_edge(header, exit);
    func.add_edge(chk, st);
    func.add_edge(chk, side);
    func.add_edge(st, latch);
    func.add_edge(latch, header);
    func
}

#[test]
fn bails_on_conditional_store_that_rejoins_the_latch() {
    // `while q <u N { if c { base[q] = v; } q += s; }` — the store block does NOT
    // dominate the latch, so unrolling it would perform writes the source skips.
    // This is the shape that miscompiled p7-with-an-inner-`if` end-to-end.
    let mut func = build_guarded_store(true);
    let before = count_op(&func, AArch64Opcode::StrbRI);
    let (changed, fired) = run(&mut func);
    assert!(
        !changed && fired == 0,
        "conditional store must NOT be unrolled"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::StrbRI),
        before,
        "no replicated stores emitted"
    );
}

#[test]
fn fires_when_side_edge_leaves_the_loop_and_store_dominates_latch() {
    // The p7 residual bounds-check shape: the in-body branch's other edge LEAVES
    // the loop, so the store block still dominates the latch and runs on every
    // header->latch path. Must still fire (this is the pass's whole target).
    let mut func = build_guarded_store(false);
    let (changed, fired) = run(&mut func);
    assert!(
        changed && fired == 1,
        "p7 side-edge shape must still unroll"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::StrbRI),
        5,
        "scalar store + 4 unrolled"
    );
}

#[test]
fn bails_when_the_store_sits_in_the_header() {
    // A store in the header also runs on the EXITING pass, where `iv >=u N` puts
    // `base+iv` out of bounds. Reject.
    use AArch64Opcode::*;
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    push(&mut func, bb0, Copy, vec![x(0), x(0)]);
    push(&mut func, bb0, Copy, vec![x(2), x(2)]);
    push(&mut func, bb0, Movz, vec![w(3), i(1)]);
    push(&mut func, bb0, Movz, vec![x(11), i(1024)]);
    push(&mut func, bb0, Movz, vec![x(10), i(4)]);
    push(&mut func, bb0, B, vec![bl(header)]);
    // The store lives in the header, BEFORE the exit test.
    push(&mut func, header, AddRR, vec![x(20), x(0), x(10)]);
    push(&mut func, header, StrbRI, vec![w(3), x(20), i(0)]);
    push(&mut func, header, MovR, vec![x(12), x(10)]);
    push(&mut func, header, CmpRR, vec![x(12), x(11)]);
    push(&mut func, header, BCond, vec![i(CC_LO), bl(latch)]);
    push(&mut func, header, B, vec![bl(exit)]);
    push(&mut func, latch, AddRR, vec![x(21), x(10), x(2)]);
    push(&mut func, latch, MovR, vec![x(10), x(21)]);
    push(&mut func, latch, B, vec![bl(header)]);
    push(&mut func, exit, Ret, vec![]);
    func.add_edge(bb0, header);
    func.add_edge(header, latch);
    func.add_edge(header, exit);
    func.add_edge(latch, header);

    let before = count_op(&func, AArch64Opcode::StrbRI);
    let (changed, fired) = run(&mut func);
    assert!(!changed && fired == 0, "header store must NOT be unrolled");
    assert_eq!(count_op(&func, AArch64Opcode::StrbRI), before);
}

/// The bound register must have exactly ONE live def before its constant is
/// believed. A bound the body REASSIGNS is loop-carried, so the def map — which
/// is last-wins over the emitted layout — reports the LATCH value, not the one
/// the entry test actually compared against.
///
/// Regression (confirmed miscompile, fixed alongside this test):
/// ```ignore
/// let mut lim = 4; let mut q = 8;
/// while q < lim { buf[q] = 1; q += s; lim = 64; }
/// ```
/// `8 < 4` is false, so the loop never runs and the program writes NOTHING. The
/// bound resolved to 64 and the unrolled loop wrote 56 bytes at indices 8..=63,
/// past a 16-byte buffer into a separate allocation. End-to-end cover:
/// `benchmarks/shape-coverage/progs/s16_reassigned_bound.rs`.
#[test]
fn bails_on_bound_redefined_in_body() {
    assert_bails(
        Cfg {
            variant: Variant::BoundInLoop,
            ..Cfg::default()
        },
        "the bound register is loop-carried, so its map entry is the latch value",
    );
}
