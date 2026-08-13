// Unit tests for the `neon-iota-fill` affine iota-fill store vectorizer.
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

/// How the stored value is produced from `trunc32(iv)`.
#[derive(Clone, Copy, PartialEq)]
enum Add {
    /// `+ w14` where `w14` is a runtime-invariant `Gpr32`.
    Invariant,
    /// `+ #k` immediate.
    ConstImm(i64),
    /// Bare `trunc32(iv)`.
    Bare,
}

/// The loop bound.
#[derive(Clone, Copy, PartialEq)]
enum BoundK {
    Runtime,
    Const(i64),
}

/// Negative-control mutations of the canonical iota-fill loop.
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Good,
    /// A load in the body -> BAIL.
    WithLoad,
    /// The trunc reads the POST-INCREMENT `iv+1` value -> BAIL (strict walk).
    TruncOfNext,
    /// The addend is defined inside the loop -> BAIL.
    AddendInLoop,
    /// The stored value is a `Gpr64` (8-byte store) -> BAIL.
    WideStore,
    /// A loop-defined vreg is used after the loop -> BAIL.
    EscapingDef,
    /// A second store -> BAIL.
    SecondStore,
    /// ROTATED do-while (test in the latch, none in the header) -> BAIL.
    Rotated,
    /// A conditional side exit out of the body (abort-diamond class) -> BAIL.
    SideExit,
    /// The header compares a Gpr32 TRUNCATION of the iv -> BAIL (the scalar
    /// test would be mod 2^32; the vector guard is 64-bit).
    Cmp32,
    /// A second, non-iv compare between the iv compare and the `BCond` -> BAIL
    /// (the branch would consume the WRONG flags).
    StrayCmp,
    /// Store via `StrRO [base, Xiv, LSL #2]` -> FIRE (positive control).
    StoreRoLsl,
    /// Store via `StrRO [base, Wtrunc(iv), UXTW #2]` -> BAIL (32-bit index).
    StoreRoUxtw,
}

struct Cfg {
    bound: BoundK,
    addv: Add,
    variant: Variant,
}

/// Build the NATIVE 3-block iota-fill loop mirroring the bridge lowering of
/// `while i < N { a[i] = (i as u32) + r; i += 1 }`:
/// ```text
/// bb0:    base=x0 (invariant); r=w14 (invariant); es4=Movz 4; iv=Movz 0; B header
/// header: v15 = MovR iv; CmpRI/CmpRR v15, bound; BCond LO body; B exit
/// body:   v18 = MovR iv; w19 = MovR v18 (trunc); w21 = w19 (+r/+k);
///         v29 = Madd iv, es4, base; StrRI w21,[v29,#0]; B latch
/// latch:  v33 = AddRI iv,1; iv = MovR v33; B header
/// exit:   (empty terminator-less tail; only reads invariants)
/// ```
fn build_iota(cfg: Cfg) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    let rotated = cfg.variant == Variant::Rotated;

    // --- bb0: invariant setup.
    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base
    push(&mut func, bb0, Copy, vec![x(2), x(2)]); // runtime bound
    push(&mut func, bb0, Uxtb, vec![w(14), w(1)]); // invariant addend r
    push(&mut func, bb0, Movz, vec![x(28), i(4)]); // elem-size const
    push(&mut func, bb0, Movz, vec![x(40), i(0)]); // iv init source
    push(&mut func, bb0, MovR, vec![x(13), x(40)]); // iv = 0
    push(&mut func, bb0, B, vec![bl(header)]);
    func.add_edge(bb0, header);

    // --- header.
    if rotated {
        // Body ops live in the header; no header test.
        push(&mut func, header, MovR, vec![x(18), x(13)]);
        push(&mut func, header, MovR, vec![w(19), x(18)]); // trunc
        push(&mut func, header, AddRR, vec![w(21), w(19), w(14)]);
        push(&mut func, header, Madd, vec![x(29), x(13), x(28), x(0)]);
        push(&mut func, header, StrRI, vec![w(21), x(29), i(0)]);
        push(&mut func, header, B, vec![bl(latch)]);
        func.add_edge(header, latch);
        // latch: iv += 1; test; back-edge.
        push(&mut func, latch, AddRI, vec![x(33), x(13), i(1)]);
        push(&mut func, latch, MovR, vec![x(13), x(33)]);
        match cfg.bound {
            BoundK::Const(n) => push(&mut func, latch, CmpRI, vec![x(13), i(n)]),
            BoundK::Runtime => push(&mut func, latch, CmpRR, vec![x(13), x(2)]),
        }
        push(&mut func, latch, BCond, vec![i(3), bl(header)]);
        push(&mut func, latch, B, vec![bl(exit)]);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        return func;
    }

    if cfg.variant == Variant::Cmp32 {
        // Truncating copy of the iv feeding a 32-bit compare.
        push(&mut func, header, MovR, vec![w(15), x(13)]);
        match cfg.bound {
            BoundK::Const(n) => push(&mut func, header, CmpRI, vec![w(15), i(n)]),
            BoundK::Runtime => push(&mut func, header, CmpRR, vec![w(15), w(2)]),
        }
    } else {
        push(&mut func, header, MovR, vec![x(15), x(13)]);
        match cfg.bound {
            BoundK::Const(n) => push(&mut func, header, CmpRI, vec![x(15), i(n)]),
            BoundK::Runtime => push(&mut func, header, CmpRR, vec![x(15), x(2)]),
        }
    }
    if cfg.variant == Variant::StrayCmp {
        // A second compare on an invariant CLOBBERS the flags the BCond reads.
        push(&mut func, header, CmpRI, vec![x(0), i(0)]);
    }
    push(&mut func, header, BCond, vec![i(3), bl(body)]);
    push(&mut func, header, B, vec![bl(exit)]);
    func.add_edge(header, body);
    func.add_edge(header, exit);

    // --- body.
    push(&mut func, body, MovR, vec![x(18), x(13)]);
    if cfg.variant == Variant::TruncOfNext {
        // Trunc of the incremented value (defined in the latch) — the strict
        // walk must refuse this.
        push(&mut func, body, MovR, vec![w(19), x(33)]);
    } else {
        push(&mut func, body, MovR, vec![w(19), x(18)]); // trunc32(iv)
    }
    if cfg.variant == Variant::AddendInLoop {
        push(&mut func, body, AddRI, vec![w(50), w(19), i(1)]); // in-loop addend
        push(&mut func, body, AddRR, vec![w(21), w(19), w(50)]);
    } else {
        match cfg.addv {
            Add::Invariant => push(&mut func, body, AddRR, vec![w(21), w(19), w(14)]),
            Add::ConstImm(k) => push(&mut func, body, AddRI, vec![w(21), w(19), i(k)]),
            Add::Bare => push(&mut func, body, MovR, vec![w(21), w(19)]),
        }
    }
    if cfg.variant == Variant::WithLoad {
        push(&mut func, body, LdrRI, vec![w(60), x(0), i(0)]);
    }
    match cfg.variant {
        Variant::StoreRoLsl => {
            // `StrRO w21, [x0, x13, LSL #2]` — packed extend (0b011<<1)|1.
            push(&mut func, body, StrRO, vec![w(21), x(0), x(13), i(0b0111)]);
        }
        Variant::StoreRoUxtw => {
            // `StrRO w21, [x0, w19, UXTW #2]` — packed extend (0b010<<1)|1;
            // w19 is the truncating copy of the iv made above.
            push(&mut func, body, StrRO, vec![w(21), x(0), w(19), i(0b0101)]);
        }
        Variant::WideStore => {
            push(&mut func, body, Madd, vec![x(29), x(13), x(28), x(0)]);
            push(&mut func, body, StrRI, vec![x(61), x(29), i(0)]);
        }
        _ => {
            push(&mut func, body, Madd, vec![x(29), x(13), x(28), x(0)]);
            push(&mut func, body, StrRI, vec![w(21), x(29), i(0)]);
        }
    }
    if cfg.variant == Variant::SecondStore {
        push(&mut func, body, StrRI, vec![w(21), x(29), i(0)]);
    }
    if cfg.variant == Variant::SideExit {
        push(&mut func, body, CmpRI, vec![x(18), i(5)]);
        push(&mut func, body, BCond, vec![i(3), bl(exit)]);
        func.add_edge(body, exit);
    }
    push(&mut func, body, B, vec![bl(latch)]);
    func.add_edge(body, latch);

    // --- latch (phi-copy induction).
    push(&mut func, latch, AddRI, vec![x(33), x(13), i(1)]);
    push(&mut func, latch, MovR, vec![x(13), x(33)]);
    push(&mut func, latch, B, vec![bl(header)]);
    func.add_edge(latch, header);

    // --- exit.
    if cfg.variant == Variant::EscapingDef {
        // Reads a loop-defined vreg after the loop.
        push(&mut func, exit, MovR, vec![x(70), x(29)]);
    }
    push(&mut func, exit, MovR, vec![x(71), x(0)]);

    func
}

fn run(cfg: Cfg) -> (MachFunction, bool) {
    let mut func = build_iota(cfg);
    let changed = NeonIotaFillPass::new().run(&mut func);
    (func, changed)
}

// ---------------------------------------------------------------------------
// Positive cases
// ---------------------------------------------------------------------------

#[test]
fn fires_on_const_bound_invariant_addend() {
    let (func, changed) = run(Cfg {
        bound: BoundK::Const(1024),
        addv: Add::Invariant,
        variant: Variant::Good,
    });
    assert!(changed, "canonical d08 iota-fill must vectorize");
    // 2 paired-Q stores (64B/iter), 1 iota load, 5 lane adds (v0 seed + 3
    // offsets + step), 5 DUPs (base + c4/c8/c12/c16).
    assert_eq!(count_op(&func, AArch64Opcode::NeonStpQPost), 2);
    assert_eq!(count_op(&func, AArch64Opcode::NeonLd1Post), 1);
    assert_eq!(count_op(&func, AArch64Opcode::NeonAddV), 5);
    assert_eq!(count_op(&func, AArch64Opcode::NeonDupGen), 5);
    // The scalar loop is untouched: original store + the two 8-byte iota
    // literal stores.
    assert_eq!(count_op(&func, AArch64Opcode::StrRI), 3);
    // One fresh 16-byte literal slot.
    assert_eq!(func.stack_slots.len(), 1);
}

#[test]
fn fires_on_const_addend_and_bare_trunc() {
    for addv in [Add::ConstImm(7), Add::Bare] {
        let (func, changed) = run(Cfg {
            bound: BoundK::Const(64),
            addv,
            variant: Variant::Good,
        });
        assert!(
            changed,
            "const-addend / bare-trunc iota fills must vectorize"
        );
        assert_eq!(count_op(&func, AArch64Opcode::NeonStpQPost), 2);
    }
}

#[test]
fn fires_on_runtime_bound_with_precheck() {
    let (func, changed) = run(Cfg {
        bound: BoundK::Runtime,
        addv: Add::Invariant,
        variant: Variant::Good,
    });
    assert!(changed, "runtime-bound iota fill must vectorize");
    // The `n <s 16` precheck: SubRI(main_bound) + CmpRI(n, 16).
    assert_eq!(count_op(&func, AArch64Opcode::SubRI), 1);
    assert!(
        func.blocks.iter().flat_map(|b| b.insts.iter()).any(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::CmpRI && imm_of(&inst.operands[1]) == Some(16)
        }),
        "runtime bound needs the n<16 precheck"
    );
}

// ---------------------------------------------------------------------------
// Negative controls (every one must BAIL and leave the function unchanged)
// ---------------------------------------------------------------------------

fn assert_bails(cfg: Cfg, why: &str) {
    let (func, changed) = run(cfg);
    assert!(!changed, "must BAIL: {why}");
    assert_eq!(count_op(&func, AArch64Opcode::NeonStpQPost), 0, "{why}");
    assert_eq!(func.stack_slots.len(), 0, "{why}");
}

#[test]
fn bails_on_load_in_body() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::WithLoad,
        },
        "a load in the body",
    );
}

#[test]
fn bails_on_trunc_of_incremented_iv() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::TruncOfNext,
        },
        "value reads iv+1 (post-increment) — the strict walk must refuse",
    );
}

#[test]
fn bails_on_in_loop_addend() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::AddendInLoop,
        },
        "addend defined inside the loop",
    );
}

#[test]
fn bails_on_wide_store() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::WideStore,
        },
        "8-byte store (i32 lanes only)",
    );
}

#[test]
fn bails_on_escaping_loop_def() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::EscapingDef,
        },
        "loop-defined vreg used after the loop",
    );
}

#[test]
fn bails_on_second_store() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::SecondStore,
        },
        "two stores",
    );
}

#[test]
fn bails_on_rotated_loop() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::Rotated,
        },
        "rotated do-while (no NATIVE header test)",
    );
}

#[test]
fn bails_on_body_side_exit() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::SideExit,
        },
        "conditional side exit from the body (its test would be skipped)",
    );
}

#[test]
fn fires_on_strro_lsl_store() {
    let (func, changed) = run(Cfg {
        bound: BoundK::Const(1024),
        addv: Add::Invariant,
        variant: Variant::StoreRoLsl,
    });
    assert!(changed, "StrRO [base, Xiv, LSL #2] must vectorize");
    assert_eq!(count_op(&func, AArch64Opcode::NeonStpQPost), 2);
}

#[test]
fn bails_on_strro_uxtw_store() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::StoreRoUxtw,
        },
        "StrRO UXTW (32-bit index) — address is base + zext(trunc32(iv))*4",
    );
}

#[test]
fn bails_on_32bit_header_compare() {
    for bound in [BoundK::Const(1024), BoundK::Runtime] {
        assert_bails(
            Cfg {
                bound,
                addv: Add::Invariant,
                variant: Variant::Cmp32,
            },
            "header compares trunc32(iv) — 32-bit loop semantics",
        );
    }
}

#[test]
fn bails_on_stray_cmp_before_bcond() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(1024),
            addv: Add::Invariant,
            variant: Variant::StrayCmp,
        },
        "a non-iv compare clobbers the flags the BCond consumes",
    );
}

#[test]
fn bails_on_small_const_bound() {
    assert_bails(
        Cfg {
            bound: BoundK::Const(15),
            addv: Add::Invariant,
            variant: Variant::Good,
        },
        "const bound below one full vector block",
    );
}
