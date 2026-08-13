// Unit tests for the `mac-row-unroll` RMW-MAC row-loop partial-unroll.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::Signature;

fn x(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
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
fn has_movz_imm(func: &MachFunction, v: i64) -> bool {
    func.blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .any(|id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::Movz && imm_of(&inst.operands[1]) == Some(v)
        })
}
/// The (unique) block that contains exactly four `StrRI` — the unrolled main
/// body `mb`.
fn main_body(func: &MachFunction) -> Option<BlockId> {
    func.blocks
        .iter()
        .enumerate()
        .find(|(_, b)| {
            b.insts
                .iter()
                .filter(|&&id| func.inst(id).opcode == AArch64Opcode::StrRI)
                .count()
                == 4
        })
        .map(|(idx, _)| BlockId(idx as u32))
}
/// Count `AddRI` in `blk` whose immediate is `v`.
fn count_addri_imm_in(func: &MachFunction, blk: BlockId, v: i64) -> usize {
    func.block(blk)
        .insts
        .iter()
        .filter(|&&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::AddRI && imm_of(&inst.operands[2]) == Some(v)
        })
        .count()
}

/// How the loop bound / array length are expressed and various fault injections.
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Good,
    /// iv step is `+2` (non-unit stride) -> BAIL.
    Step2,
    /// bound `N` is a runtime (non-const) register -> BAIL.
    RuntimeN,
    /// the b-index bounds check compares against a DIFFERENT length -> BAIL.
    InconsistentL,
    /// `aik` is redefined inside the body (loop-variant) -> BAIL.
    AikInLoop,
    /// the store writes through `b_base` (not the c-load's base): not an RMW of
    /// the loaded address -> BAIL.
    StoreWrongBase,
    /// a second `StrRI` in the body -> BAIL.
    TwoStores,
    /// a call (`Bl`) in the body -> BAIL (closed-world reject).
    WithCall,
    /// rotated do-while: the `j < N` continue-test is in the LATCH -> BAIL.
    Rotated,
}

struct Cfg {
    variant: Variant,
    n: i64,
    l: i64,
    scale: i64,
}

impl Default for Cfg {
    fn default() -> Self {
        Cfg {
            variant: Variant::Good,
            n: 24,
            l: 576,
            scale: 8,
        }
    }
}

// Register map (Gpr64 throughout):
//   j=100 (iv), N=83, L=6, i=50, k=51, c_base=2, b_base=1, scale=103, aik=60,
//   L2=7 (InconsistentL only). Temporaries: jc_h=101, jc_1=111, jc_2=112,
//   jc_3=113, jn=114, cidx=120, caddr=121, cval=122, bidx=123, baddr=124,
//   bval=125, mac=126, cidx2=127, caddr2=128, junk=130.
fn build_mac(cfg: Cfg) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let b1 = func.create_block();
    let b2 = func.create_block();
    let b3 = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let abort = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    let rotated = cfg.variant == Variant::Rotated;

    // --- bb0: loop-invariant setup (defs dominate the header preheader).
    push(&mut func, bb0, Copy, vec![x(2), x(2)]); // c_base invariant
    push(&mut func, bb0, Copy, vec![x(1), x(1)]); // b_base invariant
    push(&mut func, bb0, Copy, vec![x(50), x(50)]); // i invariant
    push(&mut func, bb0, Copy, vec![x(51), x(51)]); // k invariant
    push(&mut func, bb0, Copy, vec![x(60), x(60)]); // aik invariant
    push(&mut func, bb0, Movz, vec![x(103), i(cfg.scale)]); // element scale
    match cfg.variant {
        Variant::RuntimeN => push(&mut func, bb0, Copy, vec![x(83), x(83)]), // runtime N
        _ => push(&mut func, bb0, Movz, vec![x(83), i(cfg.n)]),              // const N
    }
    push(&mut func, bb0, Movz, vec![x(6), i(cfg.l)]); // const L
    if cfg.variant == Variant::InconsistentL {
        push(&mut func, bb0, Movz, vec![x(7), i(cfg.l + 1)]); // a different length
    }
    push(&mut func, bb0, Movz, vec![x(100), i(0)]); // j = 0
    push(&mut func, bb0, B, vec![bl(header)]);

    let step = if cfg.variant == Variant::Step2 { 2 } else { 1 };

    // Emit the loop body chain (b1,b2,b3,latch). In the ROTATED variant the
    // continue-test lives in the latch instead of the header.
    let emit_body = |func: &mut MachFunction| {
        // b1: cidx = i*N + j ; bounds-check cidx < L.
        push(func, b1, MovR, vec![x(111), x(100)]);
        push(func, b1, Madd, vec![x(120), x(50), x(83), x(111)]); // i*N + j
        push(func, b1, CmpRR, vec![x(120), x(6)]);
        push(func, b1, BCond, vec![i(CC_LO), bl(b2)]);
        push(func, b1, B, vec![bl(abort)]);

        // b2: caddr = cidx*scale + c_base ; cval = c[cidx] ; bidx = k*N + j ;
        //     bounds-check bidx < L.
        push(func, b2, Madd, vec![x(121), x(120), x(103), x(2)]);
        push(func, b2, LdrRI, vec![x(122), x(121), i(0)]);
        push(func, b2, MovR, vec![x(112), x(100)]);
        push(func, b2, Madd, vec![x(123), x(51), x(83), x(112)]); // k*N + j
        let bcheck = if cfg.variant == Variant::InconsistentL {
            7
        } else {
            6
        };
        push(func, b2, CmpRR, vec![x(123), x(bcheck)]);
        push(func, b2, BCond, vec![i(CC_LO), bl(b3)]);
        push(func, b2, B, vec![bl(abort)]);

        // b3: baddr = bidx*scale + b_base ; bval = b[bidx] ;
        //     mac = aik*bval + cval ; cidx2 = i*N + j ; bounds-check cidx2 < L.
        push(func, b3, Madd, vec![x(124), x(123), x(103), x(1)]);
        push(func, b3, LdrRI, vec![x(125), x(124), i(0)]);
        if cfg.variant == Variant::AikInLoop {
            push(func, b3, Copy, vec![x(60), x(60)]); // redefine aik in body
        }
        push(func, b3, Madd, vec![x(126), x(60), x(125), x(122)]); // aik*bval + cval
        push(func, b3, MovR, vec![x(113), x(100)]);
        push(func, b3, Madd, vec![x(127), x(50), x(83), x(113)]); // i*N + j
        push(func, b3, CmpRR, vec![x(127), x(6)]);
        push(func, b3, BCond, vec![i(CC_LO), bl(latch)]);
        push(func, b3, B, vec![bl(abort)]);

        // latch: caddr2 = cidx2*scale + c_base ; c[cidx2] = mac ; j += step.
        let store_base = if cfg.variant == Variant::StoreWrongBase {
            1
        } else {
            2
        };
        push(
            func,
            latch,
            Madd,
            vec![x(128), x(127), x(103), x(store_base)],
        );
        push(func, latch, StrRI, vec![x(126), x(128), i(0)]);
        if cfg.variant == Variant::TwoStores {
            push(func, latch, StrRI, vec![x(126), x(128), i(0)]);
        }
        if cfg.variant == Variant::WithCall {
            push(func, latch, Bl, vec![i(0)]);
        }
        push(func, latch, AddRI, vec![x(114), x(100), i(step)]);
        push(func, latch, MovR, vec![x(100), x(114)]);
    };

    if rotated {
        // ROTATED: the body/writeback are in the header, the test is in latch.
        // header carries the body chain start; simplest form: put the native
        // test in the latch. We keep the chain but move the `j<N` test out of
        // the header.
        push(&mut func, header, MovR, vec![x(101), x(100)]);
        push(&mut func, header, B, vec![bl(b1)]); // no test in header
        emit_body(&mut func);
        // latch continue-test:
        push(&mut func, latch, CmpRR, vec![x(100), x(83)]);
        push(&mut func, latch, BCond, vec![i(CC_LO), bl(header)]);
        push(&mut func, latch, B, vec![bl(exit)]);
    } else {
        // NATIVE: header pre-tests j < N.
        push(&mut func, header, MovR, vec![x(101), x(100)]);
        push(&mut func, header, CmpRR, vec![x(101), x(83)]);
        push(&mut func, header, BCond, vec![i(CC_LO), bl(b1)]);
        push(&mut func, header, B, vec![bl(exit)]);
        emit_body(&mut func);
        push(&mut func, latch, B, vec![bl(header)]);
    }

    push(&mut func, exit, Ret, vec![]);
    push(&mut func, abort, Brk, vec![]);

    // Edges.
    func.add_edge(bb0, header);
    if rotated {
        func.add_edge(header, b1);
        func.add_edge(b1, b2);
        func.add_edge(b1, abort);
        func.add_edge(b2, b3);
        func.add_edge(b2, abort);
        func.add_edge(b3, latch);
        func.add_edge(b3, abort);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
    } else {
        func.add_edge(header, b1);
        func.add_edge(header, exit);
        func.add_edge(b1, b2);
        func.add_edge(b1, abort);
        func.add_edge(b2, b3);
        func.add_edge(b2, abort);
        func.add_edge(b3, latch);
        func.add_edge(b3, abort);
        func.add_edge(latch, header);
    }
    func
}

fn run(func: &mut MachFunction) -> (bool, usize) {
    let mut pass = MacRowUnroll::new();
    let changed = pass.run(func);
    (changed, pass.fired())
}

// ---------------------------------------------------------------------------
// POSITIVE
// ---------------------------------------------------------------------------

#[test]
fn fires_on_matmul_mac_shape() {
    let mut func = build_mac(Cfg::default());
    assert_eq!(
        count_op(&func, AArch64Opcode::StrRI),
        1,
        "one scalar store before"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::LdrRI),
        2,
        "two scalar loads before"
    );

    let (changed, fired) = run(&mut func);
    assert!(
        changed && fired == 1,
        "matmul MAC shape should partially unroll"
    );

    // Scalar store/loads untouched; the main body adds 4 stores + 8 loads.
    assert_eq!(
        count_op(&func, AArch64Opcode::StrRI),
        5,
        "scalar store + 4 unrolled"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::LdrRI),
        10,
        "scalar 2 + 8 unrolled"
    );

    // Exactly one main body with four stores.
    let mb = main_body(&func).expect("a 4-store main body block exists");

    // Three per-block HS guard bails (j<N-3, cidx<L-3, bidx<L-3).
    assert_eq!(count_bcond_cc(&func, CC_HS), 3, "three HS guard bails");

    // The loop constants N-3=21 and L-3=573 are materialized once.
    assert!(has_movz_imm(&func, 21), "N-3 materialized");
    assert!(has_movz_imm(&func, 573), "L-3 materialized");

    // The lanes use the immediate-offset addressing mode directly
    // (`LdrRI/StrRI [base, #m*scale]`), so there are NO per-lane +8/+16/+24
    // address `AddRI`s. The main body's `AddRI`s are the running-IV advances:
    // the two byte pointers `pc`/`pb` by UNROLL*scale = 32, and the two index
    // IVs `cidx_iv`/`bidx_iv` plus the shared iv `j` by UNROLL = 4.
    assert_eq!(count_addri_imm_in(&func, mb, 8), 0, "no lane +8 AddRI");
    assert_eq!(count_addri_imm_in(&func, mb, 16), 0, "no lane +16 AddRI");
    assert_eq!(count_addri_imm_in(&func, mb, 24), 0, "no lane +24 AddRI");
    assert_eq!(count_addri_imm_in(&func, mb, 32), 2, "pc/pb advance +32");
    assert_eq!(
        count_addri_imm_in(&func, mb, 4),
        3,
        "cidx_iv/bidx_iv/j advance +4"
    );

    // The four main-body stores address the single running pointer `pc` with
    // immediate offsets {0,8,16,24}; likewise the loads.
    check_unrolled_addresses(&func, mb);
}

/// Verify the four unrolled stores address a single running pointer `pc` with
/// immediate byte offsets {0,8,16,24} carried on the `StrRI` itself.
fn check_unrolled_addresses(func: &MachFunction, mb: BlockId) {
    let stores: Vec<InstId> = func
        .block(mb)
        .insts
        .iter()
        .copied()
        .filter(|&id| func.inst(id).opcode == AArch64Opcode::StrRI)
        .collect();
    assert_eq!(stores.len(), 4, "four unrolled stores");

    // Each store is `StrRI [val, base, #off]`: the base register is identical
    // (the running caddr0) and the immediate offsets are exactly {0,8,16,24}.
    let base0 = vreg_of(&func.inst(stores[0]).operands[1]).unwrap().id;
    let mut offs: Vec<i64> = stores
        .iter()
        .map(|&id| {
            let inst = func.inst(id);
            assert_eq!(
                vreg_of(&inst.operands[1]).unwrap().id,
                base0,
                "all lanes share the running pointer pc"
            );
            imm_of(&inst.operands[2]).unwrap()
        })
        .collect();
    offs.sort_unstable();
    assert_eq!(offs, vec![0, 8, 16, 24], "lane byte offsets 0/8/16/24");
}

#[test]
fn idempotent_second_run_is_noop() {
    let mut func = build_mac(Cfg::default());
    let (c1, f1) = run(&mut func);
    assert!(c1 && f1 == 1);
    let strri_after_first = count_op(&func, AArch64Opcode::StrRI);
    // Second run: the scalar remainder now has multiple guard predecessors, so
    // it has no unique preheader -> not re-recognized.
    let (c2, f2) = run(&mut func);
    assert!(!c2 && f2 == 0, "second run must be a no-op");
    assert_eq!(
        count_op(&func, AArch64Opcode::StrRI),
        strri_after_first,
        "no new stores"
    );
}

// ---------------------------------------------------------------------------
// FAIL-SAFE NEGATIVE CONTROLS
// ---------------------------------------------------------------------------

fn assert_bails(cfg: Cfg, why: &str) {
    let mut func = build_mac(cfg);
    let str_before = count_op(&func, AArch64Opcode::StrRI);
    let ldr_before = count_op(&func, AArch64Opcode::LdrRI);
    let (changed, fired) = run(&mut func);
    assert!(!changed && fired == 0, "must BAIL: {why}");
    assert_eq!(
        count_op(&func, AArch64Opcode::StrRI),
        str_before,
        "no store added: {why}"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::LdrRI),
        ldr_before,
        "no load added: {why}"
    );
    assert_eq!(count_bcond_cc(&func, CC_HS), 0, "no guard spliced: {why}");
}

#[test]
fn bails_on_non_unit_stride() {
    assert_bails(
        Cfg {
            variant: Variant::Step2,
            ..Cfg::default()
        },
        "iv step is +2, not +1",
    );
}

#[test]
fn bails_on_runtime_bound() {
    assert_bails(
        Cfg {
            variant: Variant::RuntimeN,
            ..Cfg::default()
        },
        "N is runtime, not const",
    );
}

#[test]
fn bails_on_inconsistent_array_length() {
    assert_bails(
        Cfg {
            variant: Variant::InconsistentL,
            ..Cfg::default()
        },
        "b bounds-check length differs from c",
    );
}

#[test]
fn bails_on_variant_aik() {
    assert_bails(
        Cfg {
            variant: Variant::AikInLoop,
            ..Cfg::default()
        },
        "aik redefined inside the body (loop-variant)",
    );
}

#[test]
fn bails_on_store_to_wrong_base() {
    assert_bails(
        Cfg {
            variant: Variant::StoreWrongBase,
            ..Cfg::default()
        },
        "store base differs from the c-load base (not an RMW of that address)",
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
fn bails_on_call_in_body() {
    assert_bails(
        Cfg {
            variant: Variant::WithCall,
            ..Cfg::default()
        },
        "a call in the body",
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
// REMAINDER / TRIP SHAPES: N not a multiple of 4 still fires (the scalar loop is
// the untouched `trip mod 4` remainder) and small N (< 4) bails.
// ---------------------------------------------------------------------------

#[test]
fn fires_on_non_multiple_of_four_trip() {
    for n in [5i64, 6, 7, 25, 26] {
        let l = n * n;
        let mut func = build_mac(Cfg {
            n,
            l,
            ..Cfg::default()
        });
        let (changed, fired) = run(&mut func);
        assert!(
            changed && fired == 1,
            "N={n} should still unroll (scalar handles the tail)"
        );
        assert!(has_movz_imm(&func, n - 3), "N-3 materialized for N={n}");
        assert!(has_movz_imm(&func, l - 3), "L-3 materialized for N={n}");
    }
}

#[test]
fn bails_when_n_below_unroll_factor() {
    for n in [1i64, 2, 3] {
        let mut func = build_mac(Cfg {
            n,
            l: 576,
            ..Cfg::default()
        });
        let (changed, fired) = run(&mut func);
        assert!(
            !changed && fired == 0,
            "N={n} < 4 must bail (no room for a block of four)"
        );
    }
}

#[test]
fn bails_when_length_below_unroll_factor() {
    let mut func = build_mac(Cfg {
        n: 24,
        l: 3,
        ..Cfg::default()
    });
    let (changed, fired) = run(&mut func);
    assert!(!changed && fired == 0, "L < 4 must bail");
}
