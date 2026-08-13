// Unit tests for the `neon-fill` array-fill store vectorizer.
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

/// How the stored value is produced.
#[derive(Clone, Copy, PartialEq)]
enum Val {
    /// A runtime-invariant register (the `__trustcg_array_fill` helper's `elem`).
    Invariant,
    /// A byte-replicable constant (every element byte equal) -> `MOVI`.
    ConstByte(i64),
    /// A general (non-byte-replicable) constant -> `Movz/Movk + DUP`.
    ConstGeneral(i64),
    /// The stored value is defined INSIDE the loop (must BAIL).
    InLoop,
}

/// The loop bound.
#[derive(Clone, Copy, PartialEq)]
enum BoundK {
    Runtime,
    Const(i64),
}

/// Negative-control mutations of the canonical fill loop.
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Good,
    /// A load in the body (read+fill) -> BAIL.
    WithLoad,
    /// Store stride != store width (byte store at base+iv*2) -> BAIL.
    WrongStride,
    /// Base defined inside the loop -> BAIL.
    BaseInLoop,
    /// A second store -> BAIL.
    SecondStore,
    /// A call in the body -> BAIL.
    WithCall,
    /// Reversed / non-forward header/latch compare -> BAIL.
    Reversed,
}

struct Cfg {
    elem_size: i64,
    bound: BoundK,
    val: Val,
    variant: Variant,
}

/// Build a ROTATED (do-while) fill loop matching the `__trustcg_array_fill_iN`
/// helper shape:
/// ```text
/// bb0:   setup; B guard
/// guard: cmp iv,bound; b.lt body; (fallthrough) exit      // entry guard
/// body:  addr = base + iv*es; *addr = val; iv1 = iv+1; B latch
/// latch: iv = iv1; cmp iv,bound; b.lt body; (fallthrough) exit
/// exit:  ret
/// ```
/// Register map: v0=base, v2=bound(runtime), v3/w3=value, v8=elem-size const,
/// v10=iv, v11=iv1, v20=addr.
fn build_fill(cfg: Cfg) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    let es = cfg.elem_size;
    // The transfer register class matches the store width.
    let val_is_x = es == 8;
    let vreg_val = |id: u32| if val_is_x { x(id) } else { w(id) };

    // --- bb0: setup (all loop-invariant, defs dominate the guard).
    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base (self-copy: invariant def)
    push(&mut func, bb0, Copy, vec![x(2), x(2)]); // runtime bound
    push(&mut func, bb0, Movz, vec![x(8), i(es)]); // elem-size constant
    // The stored value.
    match cfg.val {
        Val::Invariant => {
            // A non-const invariant (models `elem = trunc(value)`).
            push(&mut func, bb0, Uxtb, vec![vreg_val(3), w(1)]);
        }
        Val::ConstByte(k) | Val::ConstGeneral(k) => {
            push(&mut func, bb0, Movz, vec![vreg_val(3), i(k & 0xFFFF)]);
            if k > 0xFFFF {
                push(
                    &mut func,
                    bb0,
                    Movk,
                    vec![vreg_val(3), i((k >> 16) & 0xFFFF), i(16)],
                );
            }
        }
        Val::InLoop => { /* defined in the body below */ }
    }
    push(&mut func, bb0, Movz, vec![x(10), i(0)]); // iv = 0
    push(&mut func, bb0, B, vec![bl(guard)]);

    // --- guard: entry pre-test.
    let bound_rhs = match cfg.bound {
        BoundK::Runtime => x(2),
        BoundK::Const(_) => x(2), // v2 will be Movz'd below for the const case
    };
    if let BoundK::Const(n) = cfg.bound {
        // Materialize the const bound into v2 in bb0 so both compares agree.
        // (Insert right after the base/bound copies — simplest: overwrite via a
        // fresh Movz at block start of guard is not invariant-safe, so define in
        // bb0.) We instead use CmpRI against the immediate directly.
        let _ = n;
    }
    match cfg.bound {
        BoundK::Runtime => {
            push(&mut func, guard, CmpRR, vec![x(10), bound_rhs.clone()]);
        }
        BoundK::Const(n) => {
            push(&mut func, guard, CmpRI, vec![x(10), i(n)]);
        }
    }
    if cfg.variant == Variant::Reversed {
        // Reversed polarity: exit on `iv < bound` (b.lt -> exit), enter on ge.
        push(&mut func, guard, BCond, vec![i(CC_LT), bl(exit)]);
        push(&mut func, guard, B, vec![bl(body)]);
    } else {
        push(&mut func, guard, BCond, vec![i(CC_LT), bl(body)]);
        push(&mut func, guard, B, vec![bl(exit)]);
    }

    // --- body (header): address, store, iv+1.
    let store_stride = if cfg.variant == Variant::WrongStride {
        2
    } else {
        es
    };
    if cfg.variant == Variant::WithLoad {
        // A load in the body -> BAIL (read+fill).
        push(&mut func, body, LdrbRI, vec![w(30), x(0), i(0)]);
    }
    if cfg.variant == Variant::WithCall {
        push(&mut func, body, Bl, vec![i(0)]);
    }
    // addr = base + iv*store_stride.
    if store_stride == 1 && cfg.variant != Variant::WrongStride {
        push(&mut func, body, AddRR, vec![x(20), x(0), x(10)]);
    } else {
        push(&mut func, body, Movz, vec![x(21), i(store_stride)]);
        push(&mut func, body, Madd, vec![x(20), x(10), x(21), x(0)]);
    }
    // The stored value register.
    let val_reg = match cfg.val {
        Val::InLoop => {
            // iv-dependent value defined in the loop.
            push(&mut func, body, AddRI, vec![vreg_val(3), x(10), i(7)]);
            vreg_val(3)
        }
        _ => vreg_val(3),
    };
    // Base defined inside loop -> overwrite v0 in the body (BAIL control).
    if cfg.variant == Variant::BaseInLoop {
        push(&mut func, body, AddRI, vec![x(0), x(0), i(0)]);
    }
    let store_op = match es {
        1 => StrbRI,
        2 => StrhRI,
        _ => StrRI,
    };
    push(
        &mut func,
        body,
        store_op,
        vec![val_reg.clone(), x(20), i(0)],
    );
    if cfg.variant == Variant::SecondStore {
        push(&mut func, body, store_op, vec![val_reg, x(20), i(0)]);
    }
    push(&mut func, body, AddRI, vec![x(11), x(10), i(1)]); // iv1 = iv + 1
    push(&mut func, body, B, vec![bl(latch)]);

    // --- latch: iv = iv1; continue-test.
    push(&mut func, latch, AddRI, vec![x(10), x(11), i(0)]); // iv = copy(iv1)
    match cfg.bound {
        BoundK::Runtime => {
            push(&mut func, latch, CmpRR, vec![x(10), x(2)]);
        }
        BoundK::Const(n) => {
            push(&mut func, latch, CmpRI, vec![x(10), i(n)]);
        }
    }
    if cfg.variant == Variant::Reversed {
        push(&mut func, latch, BCond, vec![i(CC_LT), bl(exit)]);
    } else {
        push(&mut func, latch, BCond, vec![i(CC_LT), bl(body)]);
    }

    // --- exit.
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, guard);
    func.add_edge(guard, body);
    func.add_edge(guard, exit);
    func.add_edge(body, latch);
    if cfg.variant == Variant::Reversed {
        func.add_edge(latch, exit);
        func.add_edge(latch, body); // keep it a loop so LoopAnalysis sees it
    } else {
        func.add_edge(latch, body);
        func.add_edge(latch, exit);
    }
    func
}

fn run(func: &mut MachFunction) -> (bool, usize) {
    let mut pass = NeonFillPass::new();
    let changed = pass.run(func);
    (changed, pass.fired())
}

// ---------------------------------------------------------------------------
// POSITIVE
// ---------------------------------------------------------------------------

#[test]
fn fires_on_byte_fill_helper_shape() {
    let mut func = build_fill(Cfg {
        elem_size: 1,
        bound: BoundK::Runtime,
        val: Val::Invariant,
        variant: Variant::Good,
    });
    let strb_before = count_op(&func, AArch64Opcode::StrbRI);
    let (changed, fired) = run(&mut func);
    assert!(
        changed && fired == 1,
        "byte fill helper shape should vectorize"
    );
    // One DUP broadcast (element-size code 1 = B).
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonDupGen),
        1,
        "one DUP broadcast"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonMovi),
        0,
        "invariant value uses DUP not MOVI"
    );
    // One paired store; qb stored twice (both operands the same broadcast Q).
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonStpQPost),
        1,
        "one STP q,q store"
    );
    let stp = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .find(|&id| func.inst(id).opcode == AArch64Opcode::NeonStpQPost)
        .unwrap();
    let ops = &func.inst(stp).operands;
    assert_eq!(
        vreg_of(&ops[0]),
        vreg_of(&ops[1]),
        "STP stores the SAME broadcast Q twice"
    );
    assert_eq!(imm_of(&ops[3]), Some(32), "post-index is 32 bytes");
    // The scalar store is UNCHANGED (still present).
    assert_eq!(
        count_op(&func, AArch64Opcode::StrbRI),
        strb_before,
        "scalar store untouched"
    );
    // Rotated shape: an unsigned `iv>=bound` exit guard (b.hs) and a `n<W`
    // precheck (b.lt) were emitted.
    let hs = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == AArch64Opcode::BCond)
        .any(|id| imm_of(&func.inst(id).operands[0]) == Some(CC_HS));
    assert!(hs, "rotated do-while must emit the iv>=bound HS exit guard");
}

#[test]
fn fires_widths_h_s_d() {
    for (es, code) in [(2i64, 2i64), (4, 4), (8, 8)] {
        let mut func = build_fill(Cfg {
            elem_size: es,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::Good,
        });
        let (changed, fired) = run(&mut func);
        assert!(changed && fired == 1, "width {es} fill should vectorize");
        assert_eq!(count_op(&func, AArch64Opcode::NeonDupGen), 1, "one DUP");
        // The DUP element-size code equals the element size (2/4/8 = H/S/D).
        let dup = func
            .blocks
            .iter()
            .flat_map(|b| b.insts.iter().copied())
            .find(|&id| func.inst(id).opcode == AArch64Opcode::NeonDupGen)
            .unwrap();
        assert_eq!(
            imm_of(&func.inst(dup).operands[2]),
            Some(code),
            "DUP element-size code"
        );
        // StpQPost imm is 32 in every case.
        let stp = func
            .blocks
            .iter()
            .flat_map(|b| b.insts.iter().copied())
            .find(|&id| func.inst(id).opcode == AArch64Opcode::NeonStpQPost)
            .unwrap();
        assert_eq!(
            imm_of(&func.inst(stp).operands[3]),
            Some(32),
            "STP imm 32 for width {es}"
        );
    }
}

#[test]
fn const_byte_fill_uses_movi() {
    // Inline const byte-fill: a byte-replicable value -> MOVI Vd.16B (no DUP).
    let mut func = build_fill(Cfg {
        elem_size: 1,
        bound: BoundK::Const(1024),
        val: Val::ConstByte(0x41),
        variant: Variant::Good,
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1, "const byte fill should vectorize");
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonMovi),
        1,
        "byte-replicable const uses MOVI"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonDupGen),
        0,
        "no DUP for a MOVI const"
    );
    let movi = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .find(|&id| func.inst(id).opcode == AArch64Opcode::NeonMovi)
        .unwrap();
    assert_eq!(
        imm_of(&func.inst(movi).operands[1]),
        Some(0x41),
        "MOVI immediate is the byte"
    );
}

#[test]
fn const_general_u32_uses_movz_dup() {
    // A non-byte-replicable u32 const -> Movz/Movk + NeonDupGen (NOT MOVI).
    let mut func = build_fill(Cfg {
        elem_size: 4,
        bound: BoundK::Const(1024),
        val: Val::ConstGeneral(0x1234_5678),
        variant: Variant::Good,
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1, "general const fill should vectorize");
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonMovi),
        0,
        "non-byte-replicable const must NOT use MOVI"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonDupGen),
        1,
        "general const broadcasts via DUP"
    );
}

#[test]
fn const_byte_replicable_wide_uses_movi() {
    // A u16 const whose two bytes are equal (0x0101) IS byte-replicable -> MOVI.
    let mut func = build_fill(Cfg {
        elem_size: 2,
        bound: BoundK::Const(512),
        val: Val::ConstByte(0x0101),
        variant: Variant::Good,
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1);
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonMovi),
        1,
        "0x0101 is byte-replicable -> MOVI"
    );
    assert_eq!(count_op(&func, AArch64Opcode::NeonDupGen), 0);
}

// ---------------------------------------------------------------------------
// KEEP (fail-safe negative controls)
// ---------------------------------------------------------------------------

fn assert_bails(cfg: Cfg, why: &str) {
    let mut func = build_fill(cfg);
    let (changed, fired) = run(&mut func);
    assert!(!changed && fired == 0, "must BAIL: {why}");
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonStpQPost),
        0,
        "no NEON store emitted: {why}"
    );
}

#[test]
fn bails_on_load() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::WithLoad,
        },
        "a load in the body (read+fill)",
    );
}

#[test]
fn bails_on_wrong_stride() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::WrongStride,
        },
        "byte store at base+iv*2 (stride != width)",
    );
}

#[test]
fn bails_on_value_in_loop() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::InLoop,
            variant: Variant::Good,
        },
        "stored value defined inside the loop / iv-dependent",
    );
}

#[test]
fn bails_on_base_in_loop() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::BaseInLoop,
        },
        "base defined inside the loop (not invariant)",
    );
}

#[test]
fn bails_on_second_store() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::SecondStore,
        },
        "a second store",
    );
}

#[test]
fn bails_on_call() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::WithCall,
        },
        "a call in the body",
    );
}

#[test]
fn bails_on_reversed_compare() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::Reversed,
        },
        "reversed / non-forward loop compare",
    );
}

#[test]
fn bails_on_small_const_bound() {
    // Const bound < WIDTH_ELEMS (32 for bytes) leaves the loop entirely scalar.
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Const(16),
            val: Val::ConstByte(0),
            variant: Variant::Good,
        },
        "const bound below one full 32-byte block",
    );
}

// ---------------------------------------------------------------------------
// Helper unit checks
// ---------------------------------------------------------------------------

#[test]
fn byte_replicable_predicate() {
    assert!(byte_replicable(0x00, 1));
    assert!(byte_replicable(0x41, 1));
    assert!(byte_replicable(0x0101, 2));
    assert!(byte_replicable(0x0101_0101, 4));
    assert!(!byte_replicable(0x1234, 2));
    assert!(!byte_replicable(0x1234_5678, 4));
    assert_eq!(low_byte(0x1234_5678), 0x78);
}
