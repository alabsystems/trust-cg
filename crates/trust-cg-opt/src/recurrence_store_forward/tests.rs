// Unit tests for the `recurrence-store-forward` loop-carried forwarding pass.
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
    func.block_order
        .iter()
        .flat_map(|&b| func.block(b).insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}

/// How the loop bound is expressed.
#[derive(Clone, Copy, PartialEq)]
enum BoundK {
    /// `CmpRI iv_c, #n` — the post-BCE d02 shape.
    ConstImm(i64),
    /// `CmpRR iv_c, Nreg` with `Nreg = Movz #n` (the consttripnorm shape).
    ConstReg(i64),
    /// `CmpRR iv_c, nreg` with a runtime (non-const) bound register.
    Runtime,
}

/// Negative-control mutations of the canonical d02 recurrence loop.
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Good,
    /// `u64` element recurrence: Gpr64 loads/store, scale 8 -> must FIRE.
    U64,
    /// A load whose index is `iv + 1` (the just-stored cell of THIS traversal,
    /// not the forwardable `iv` cell) -> BAIL.
    LoadAtIvPlus1,
    /// A second store in the body -> BAIL.
    TwoStores,
    /// A call in the body -> BAIL (closed-world reject).
    WithCall,
    /// Madd scale (8) != access width (4) -> BAIL.
    ScaleMismatch,
    /// The stored register is read after the loop -> BAIL.
    VsReadOutside,
    /// A load result is read AFTER the vS def (would observe the NEW value)
    /// -> BAIL.
    DstReadAfterVsDef,
    /// The preheader ends in a CONDITIONAL branch to the header -> BAIL (the
    /// appended load could execute on a path that never enters the loop).
    CondPreheader,
    /// Retained `TrapBoundsCheckExact` guard carriers inside the body (the
    /// certs-on / pre-BCE shape): pure register checks -> must FIRE.
    WithTrapGuards,
}

struct Cfg {
    variant: Variant,
    bound: BoundK,
    /// Initial iv value `i0`.
    i0: i64,
}

impl Default for Cfg {
    fn default() -> Self {
        Cfg {
            variant: Variant::Good,
            bound: BoundK::ConstImm(1023),
            i0: 0,
        }
    }
}

/// Build the post-BCE d02 recurrence loop
/// `while i <u N { a[i+1] = a[i] + (ror32(a[i], 31) ^ i as u32); i += 1 }`:
/// ```text
/// bb0 (preheader): base/scale/iv setup; B header
/// header:  iv_c = MovR iv; cmp iv_c, N; b.lo mid; B exit
/// mid:     c1 = MovR iv; a1 = Madd(c1, scale, base); d1 = Ldr [a1]
///          c2 = MovR iv; B body
/// body:    a2 = Madd(c2, scale, base); d2 = Ldr [a2]; rot = RorRI(d2, 31)
///          c3 = MovR iv; c3w = MovR32(c3); e = Eor(rot, c3w)
///          vS = Add(d1, e); c4 = MovR iv; p1 = AddRI(c4, 1)
///          cmp p1, #1024; b.lo latch; B abortb
/// latch:   a3 = Madd(p1, scale, base); Str vS -> [a3]
///          nx = AddRI(iv, 1); iv = MovR nx; B header
/// abortb:  brk        (outside the loop body)
/// exit:    ret
/// ```
/// Register map: x0=base, x19=scale, x4=iv0 source, x24=iv, x26=header copy,
/// x29/x39/x61/x65=iv copies, x36/x46/x74=addresses, w38/w48=loads, w59=rot,
/// w62=iv retype, w63=eor, w64=vS, x67=iv+1, x78=next, x11=bound reg.
fn build_recurrence(cfg: Cfg) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let mid = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let abortb = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    let u64_elems = cfg.variant == Variant::U64;
    let scale = if cfg.variant == Variant::ScaleMismatch || u64_elems {
        8
    } else {
        4
    };
    // Element-width-matched operand constructors for loads/store values.
    let elem = |id: u32| if u64_elems { x(id) } else { w(id) };

    // --- bb0 (preheader): loop-invariant setup.
    push(&mut func, bb0, Movz, vec![x(0), i(4096)]); // "base"
    push(&mut func, bb0, Movz, vec![x(19), i(scale)]); // scale
    push(&mut func, bb0, Movz, vec![x(4), i(cfg.i0)]); // iv0
    match cfg.bound {
        BoundK::ConstReg(n) => push(&mut func, bb0, Movz, vec![x(11), i(n)]),
        BoundK::Runtime => push(&mut func, bb0, Copy, vec![x(11), x(11)]),
        BoundK::ConstImm(_) => {}
    }
    push(&mut func, bb0, MovR, vec![x(24), x(4)]); // iv init
    if cfg.variant == Variant::CondPreheader {
        push(&mut func, bb0, CmpRI, vec![x(4), i(7)]);
        push(&mut func, bb0, BCond, vec![i(CC_LO), bl(header)]);
        push(&mut func, bb0, B, vec![bl(exit)]);
    } else {
        push(&mut func, bb0, B, vec![bl(header)]);
    }

    // --- header: iv_c = MovR iv; cmp; b.lo mid; B exit.
    push(&mut func, header, MovR, vec![x(26), x(24)]);
    match cfg.bound {
        BoundK::ConstImm(n) => push(&mut func, header, CmpRI, vec![x(26), i(n)]),
        BoundK::ConstReg(_) | BoundK::Runtime => push(&mut func, header, CmpRR, vec![x(26), x(11)]),
    }
    push(&mut func, header, BCond, vec![i(CC_LO), bl(mid)]);
    push(&mut func, header, B, vec![bl(exit)]);

    // --- mid: first load a[iv].
    push(&mut func, mid, MovR, vec![x(29), x(24)]);
    if cfg.variant == Variant::WithTrapGuards {
        push(
            &mut func,
            mid,
            TrapBoundsCheckExact,
            vec![x(29), x(29), i(1024)],
        );
    }
    push(&mut func, mid, Madd, vec![x(36), x(29), x(19), x(0)]);
    push(&mut func, mid, LdrRI, vec![elem(38), x(36), i(0)]);
    if cfg.variant == Variant::WithCall {
        push(&mut func, mid, Bl, vec![i(0)]);
    }
    push(&mut func, mid, MovR, vec![x(39), x(24)]);
    push(&mut func, mid, B, vec![bl(body)]);

    // --- body: second load a[iv] (or a[iv+1] for the negative control),
    // rotate/eor/add recurrence, retained store bounds check.
    if cfg.variant == Variant::LoadAtIvPlus1 {
        push(&mut func, body, AddRI, vec![x(30), x(39), i(1)]);
        push(&mut func, body, Madd, vec![x(46), x(30), x(19), x(0)]);
    } else {
        push(&mut func, body, Madd, vec![x(46), x(39), x(19), x(0)]);
    }
    push(&mut func, body, LdrRI, vec![elem(48), x(46), i(0)]);
    push(&mut func, body, RorRI, vec![elem(59), elem(48), i(31)]);
    push(&mut func, body, MovR, vec![x(61), x(24)]);
    if u64_elems {
        push(&mut func, body, EorRR, vec![x(63), x(59), x(61)]);
        push(&mut func, body, AddRR, vec![x(64), x(38), x(63)]); // vS def
    } else {
        push(&mut func, body, MovR, vec![w(62), x(61)]); // Gpr64 -> Gpr32 retype
        push(&mut func, body, EorRR, vec![w(63), w(59), w(62)]);
        push(&mut func, body, AddRR, vec![w(64), w(38), w(63)]); // vS def
    }
    if cfg.variant == Variant::DstReadAfterVsDef {
        // Reads the first load's result AFTER the vS def -> must BAIL.
        push(&mut func, body, EorRR, vec![elem(70), elem(38), elem(38)]);
    }
    push(&mut func, body, MovR, vec![x(65), x(24)]);
    push(&mut func, body, AddRI, vec![x(67), x(65), i(1)]);
    push(&mut func, body, CmpRI, vec![x(67), i(1024)]);
    push(&mut func, body, BCond, vec![i(CC_LO), bl(latch)]);
    push(&mut func, body, B, vec![bl(abortb)]);

    // --- latch: the store a[iv+1] = vS and the iv writeback.
    push(&mut func, latch, Madd, vec![x(74), x(67), x(19), x(0)]);
    push(&mut func, latch, StrRI, vec![elem(64), x(74), i(0)]);
    if cfg.variant == Variant::TwoStores {
        push(&mut func, latch, StrRI, vec![elem(64), x(74), i(0)]);
    }
    push(&mut func, latch, AddRI, vec![x(78), x(24), i(1)]);
    push(&mut func, latch, MovR, vec![x(24), x(78)]);
    push(&mut func, latch, B, vec![bl(header)]);

    // --- abortb (outside the loop body): trap.
    push(&mut func, abortb, Brk, vec![]);

    // --- exit.
    if cfg.variant == Variant::VsReadOutside {
        push(&mut func, exit, MovR, vec![elem(90), elem(64)]);
    }
    push(&mut func, exit, Ret, vec![]);

    // Edges.
    func.add_edge(bb0, header);
    if cfg.variant == Variant::CondPreheader {
        func.add_edge(bb0, exit);
    }
    func.add_edge(header, mid);
    func.add_edge(header, exit);
    func.add_edge(mid, body);
    func.add_edge(body, latch);
    func.add_edge(body, abortb);
    func.add_edge(latch, header);
    func
}

fn run(func: &mut MachFunction) -> bool {
    RecurrenceStoreForward::new().run(func)
}

#[test]
fn canonical_d02_shape_fires() {
    let mut func = build_recurrence(Cfg::default());
    assert!(run(&mut func));

    // Both in-loop loads (and their private address Madds) are gone; the
    // preheader gained exactly one Madd + LdrRI pair.
    assert_eq!(count_op(&func, AArch64Opcode::LdrRI), 1);
    assert_eq!(count_op(&func, AArch64Opcode::Madd), 2); // preheader + store addr
    let ph = &func.block(func.entry).insts;
    let n = ph.len();
    assert_eq!(func.inst(ph[n - 1]).opcode, AArch64Opcode::B); // terminator last
    let ldr = func.inst(ph[n - 2]);
    assert_eq!(ldr.opcode, AArch64Opcode::LdrRI);
    assert_eq!(ldr.operands[0], w(64)); // loads straight into vS
    let madd = func.inst(ph[n - 3]);
    assert_eq!(madd.opcode, AArch64Opcode::Madd);
    assert_eq!(madd.operands[1], x(24)); // index = iv
    assert_eq!(madd.operands[2], x(19)); // scale
    assert_eq!(madd.operands[3], x(0)); // base

    // The recurrence is register-carried: the rotate and the accumulate read
    // vS in place of the deleted load results.
    let all: Vec<&MachInst> = func
        .block_order
        .iter()
        .flat_map(|&b| func.block(b).insts.iter())
        .map(|&id| func.inst(id))
        .collect();
    let rot = all
        .iter()
        .find(|inst| inst.opcode == AArch64Opcode::RorRI)
        .unwrap();
    assert_eq!(rot.operands[1], w(64));
    let add = all
        .iter()
        .find(|inst| inst.opcode == AArch64Opcode::AddRR && inst.operands[0] == w(64))
        .unwrap();
    assert_eq!(add.operands[1], w(64)); // AddRR(vS, vS, e) — in place

    // The store is byte-for-byte untouched.
    let st = all
        .iter()
        .find(|inst| inst.opcode == AArch64Opcode::StrRI)
        .unwrap();
    assert_eq!(st.operands, vec![w(64), x(74), i(0)]);
}

#[test]
fn fires_once_then_idempotent() {
    let mut func = build_recurrence(Cfg::default());
    assert!(run(&mut func));
    assert!(
        !run(&mut func),
        "no loads left to forward on the second run"
    );
}

#[test]
fn u64_recurrence_fires() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::U64,
        ..Cfg::default()
    });
    assert!(run(&mut func));
    assert_eq!(count_op(&func, AArch64Opcode::LdrRI), 1);
    let ph = &func.block(func.entry).insts;
    let ldr = func.inst(ph[ph.len() - 2]);
    assert_eq!(ldr.operands[0], x(64)); // Gpr64 vS
}

#[test]
fn const_reg_bound_fires() {
    let mut func = build_recurrence(Cfg {
        bound: BoundK::ConstReg(1023),
        ..Cfg::default()
    });
    assert!(run(&mut func));
}

#[test]
fn retained_trap_guard_carriers_fire() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::WithTrapGuards,
        ..Cfg::default()
    });
    assert!(run(&mut func));
    // The guard carrier is untouched.
    assert_eq!(count_op(&func, AArch64Opcode::TrapBoundsCheckExact), 1);
}

#[test]
fn runtime_bound_bails() {
    let mut func = build_recurrence(Cfg {
        bound: BoundK::Runtime,
        ..Cfg::default()
    });
    assert!(!run(&mut func), "runtime bound: trip >= 1 unprovable");
}

#[test]
fn trip_zero_bails() {
    // iv0 == N: the guard fails on entry, the loop never runs, and the
    // preheader load would touch an address the original program never
    // dereferences.
    let mut func = build_recurrence(Cfg {
        i0: 1023,
        ..Cfg::default()
    });
    assert!(!run(&mut func), "iv0 >= N: trip 0");
}

#[test]
fn load_at_iv_plus_1_bails() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::LoadAtIvPlus1,
        ..Cfg::default()
    });
    assert!(!run(&mut func), "a[iv+1] load is not the forwarded cell");
}

#[test]
fn second_store_bails() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::TwoStores,
        ..Cfg::default()
    });
    assert!(!run(&mut func));
}

#[test]
fn call_in_body_bails() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::WithCall,
        ..Cfg::default()
    });
    assert!(!run(&mut func), "a call may write the forwarded cell");
}

#[test]
fn scale_width_mismatch_bails() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::ScaleMismatch,
        ..Cfg::default()
    });
    assert!(!run(&mut func), "scale 8 with 4-byte accesses");
}

#[test]
fn vs_read_outside_loop_bails() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::VsReadOutside,
        ..Cfg::default()
    });
    assert!(!run(&mut func));
}

#[test]
fn load_dst_read_after_vs_def_bails() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::DstReadAfterVsDef,
        ..Cfg::default()
    });
    assert!(
        !run(&mut func),
        "a read after the vS def would see the NEW value"
    );
}

#[test]
fn reaches_avoiding_admits_reset_rejects_unreset_nested() {
    // The `iv == iv0`-at-preheader guard, tested on the two nested-loop CFG
    // topologies directly. Shared spine:
    //   entry -> outer_header -> [init ->] preheader -> inner_header
    //   inner_header -> {inner_latch(redef), outer_latch}
    //   inner_latch -> inner_header ;  outer_latch -> outer_header
    // REJECT (un-reset): `init` is in `entry`, before the outer loop; the outer
    // back-edge re-enters the preheader without re-running init, so the redef
    // reaches the preheader avoiding init -> guard must fire (true).
    {
        let mut f = MachFunction::new("t".to_string(), Signature::new(vec![], vec![]));
        let entry = f.entry; // init lives here
        let outer_header = f.create_block();
        let preheader = f.create_block();
        let inner_header = f.create_block();
        let inner_latch = f.create_block(); // redef here
        let outer_latch = f.create_block();
        f.add_edge(entry, outer_header);
        f.add_edge(outer_header, preheader);
        f.add_edge(preheader, inner_header);
        f.add_edge(inner_header, inner_latch);
        f.add_edge(inner_header, outer_latch);
        f.add_edge(inner_latch, inner_header);
        f.add_edge(outer_latch, outer_header);
        assert!(
            reaches_avoiding(&f, inner_latch, preheader, entry),
            "un-reset outer loop: redef reaches preheader avoiding init"
        );
    }
    // ADMIT (reset): `init` sits between the outer header and the preheader, so
    // it re-runs every outer iteration; every redef -> preheader path passes
    // through init -> guard stays silent (false). This is d02's own shape (the
    // prefix loop nested in the `reps` loop, `let mut i = 0` each rep).
    {
        let mut f = MachFunction::new("t".to_string(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let outer_header = f.create_block();
        let init = f.create_block(); // init lives here (re-run each outer iter)
        let preheader = f.create_block();
        let inner_header = f.create_block();
        let inner_latch = f.create_block();
        let outer_latch = f.create_block();
        f.add_edge(entry, outer_header);
        f.add_edge(outer_header, init);
        f.add_edge(init, preheader);
        f.add_edge(preheader, inner_header);
        f.add_edge(inner_header, inner_latch);
        f.add_edge(inner_header, outer_latch);
        f.add_edge(inner_latch, inner_header);
        f.add_edge(outer_latch, outer_header);
        assert!(
            !reaches_avoiding(&f, inner_latch, preheader, init),
            "reset outer loop: every redef -> preheader path re-passes init"
        );
        // Degenerate reset: init IS the preheader (barrier == target) -> silent.
        assert!(
            !reaches_avoiding(&f, inner_latch, preheader, preheader),
            "init inside the preheader re-runs on every entry"
        );
    }
}

#[test]
fn conditional_preheader_terminator_bails() {
    let mut func = build_recurrence(Cfg {
        variant: Variant::CondPreheader,
        ..Cfg::default()
    });
    assert!(
        !run(&mut func),
        "appended load must not run on a loop-skipping path"
    );
}

// The compile-time kill switch `TCG_NO_RECURRENCE_STORE_FWD` is NOT unit-tested
// here: mutating process environment races with concurrently-running tests that
// build pipelines (the same reason `TCG_NO_STRIDED_STORE_UNROLL` has no unit
// test). It is exercised end-to-end: the d02 A/B lanes compile with and without
// the variable and are confirmed to emit the forwarded / un-forwarded loop
// respectively. The `TRUST_CG_DISABLE_PASSES=recurrence_store_fwd` bisect switch
// IS unit-tested (thread-scoped override) in `pipeline.rs`.
