// Unit tests for alias-versioned load hoisting.
//
// Each test builds a small machine function and checks whether the pass fires
// (transforms the CFG) or fails closed. The canonical firing shape is a counted
// inner loop carrying a loop-invariant plain load and an indexed store whose
// index is a `[0, bound)` induction variable — the matrix j-loop in miniature.

use super::*;
use crate::pass_manager::MachinePass;
use trust_cg_ir::{
    AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, RegClass, Signature, VReg,
};

const PACKED_LSL_SCALED: i64 = 7; // (OPTION_LSL << 1) | 1

fn g64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn i(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn blk(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn push(func: &mut MachFunction, b: BlockId, op: AArch64Opcode, ops: Vec<MachOperand>) {
    let id = func.push_inst(MachInst::new(op, ops));
    func.append_inst(b, id);
}
fn nblocks(func: &MachFunction) -> usize {
    func.block_order.len()
}

/// Knobs to derive the canonical firing shape and its fail-closed variants.
struct Shape {
    conditional_preheader: bool,
    plain_load: bool,
    opaque_writer: bool,
    counted_store: bool,
}

/// Build a counted inner loop (self-loop header==latch) with:
///  * an invariant plain load `v20 = ldr [v0, #0]`  (base v0 defined in preheader)
///  * an indexed store `str v20, [v1, v10, lsl #3]`  (base v1 invariant, idx v10)
///  * idx `v10`: init 0 in the preheader, step `v11 = v10 + 1`, `v10 = v11`
///  * exit test `cmp v11, v2(=bound 4); b.eq exit`
fn build(shape: Shape) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry; // preheader
    let hdr = func.create_block(); // header == latch (self-loop)
    let exit = func.create_block();

    // Preheader: invariant bases + bound + idx init.
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(0), i(4096)]); // load base
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(1), i(65536)]); // store base
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(2), i(4)]); // bound
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(10), i(0)]); // idx init = 0
    if shape.conditional_preheader {
        push(&mut func, ph, AArch64Opcode::CmpRR, vec![g64(2), g64(10)]);
        push(&mut func, ph, AArch64Opcode::BCond, vec![i(1), blk(hdr)]);
        push(&mut func, ph, AArch64Opcode::B, vec![blk(exit)]);
        func.add_edge(ph, hdr);
        func.add_edge(ph, exit);
    } else {
        push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
        func.add_edge(ph, hdr);
    }

    // Header/latch body.
    if shape.plain_load {
        push(
            &mut func,
            hdr,
            AArch64Opcode::LdrRI,
            vec![g64(20), g64(0), i(0)],
        );
    } else {
        // register-offset load — not a plain hoistable load.
        push(
            &mut func,
            hdr,
            AArch64Opcode::LdrRO,
            vec![g64(20), g64(0), g64(10), i(PACKED_LSL_SCALED)],
        );
    }
    if shape.opaque_writer {
        push(
            &mut func,
            hdr,
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("f".to_string())],
        );
    }
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRO,
        vec![g64(20), g64(1), g64(10), i(PACKED_LSL_SCALED)],
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::AddRI,
        vec![g64(11), g64(10), i(1)],
    ); // step
    push(&mut func, hdr, AArch64Opcode::MovR, vec![g64(10), g64(11)]); // idx <- step
    if shape.counted_store {
        push(&mut func, hdr, AArch64Opcode::CmpRR, vec![g64(11), g64(2)]);
        push(&mut func, hdr, AArch64Opcode::BCond, vec![i(0), blk(exit)]); // b.eq exit
        push(&mut func, hdr, AArch64Opcode::B, vec![blk(hdr)]);
    } else {
        // Exit predicate that never references the step: the index is unbounded.
        push(&mut func, hdr, AArch64Opcode::CmpRR, vec![g64(20), g64(2)]);
        push(&mut func, hdr, AArch64Opcode::BCond, vec![i(0), blk(exit)]);
        push(&mut func, hdr, AArch64Opcode::B, vec![blk(hdr)]);
    }
    func.add_edge(hdr, exit);
    func.add_edge(hdr, hdr);

    push(&mut func, exit, AArch64Opcode::Ret, vec![]);
    func
}

fn ok() -> Shape {
    Shape {
        conditional_preheader: false,
        plain_load: true,
        opaque_writer: false,
        counted_store: true,
    }
}

#[test]
fn fires_on_counted_invariant_load_store_shape() {
    let mut func = build(ok());
    let before = nblocks(&func);
    let mut pass = AliasVersionedLoadHoist;
    assert!(pass.run(&mut func), "should fire on the matrix-like shape");
    assert!(
        nblocks(&func) > before,
        "firing must add the version-check diamond + clone blocks"
    );
    // An unsigned-LS disjointness branch (b.ls) must be emitted.
    let has_ls = func.block_order.iter().any(|&b| {
        func.block(b).insts.iter().any(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::BCond
                && matches!(inst.operands.first(), Some(MachOperand::Imm(9)))
        })
    });
    assert!(has_ls, "an unsigned-LS disjointness branch must be emitted");
}

#[test]
fn refuses_conditional_preheader() {
    let mut func = build(Shape {
        conditional_preheader: true,
        ..ok()
    });
    let before = nblocks(&func);
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "must refuse a non-unconditional preheader"
    );
    assert_eq!(nblocks(&func), before);
}

#[test]
fn refuses_non_plain_load() {
    let mut func = build(Shape {
        plain_load: false,
        ..ok()
    });
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "no plain LdrRI load => no hoist candidate"
    );
}

#[test]
fn refuses_opaque_writer() {
    let mut func = build(Shape {
        opaque_writer: true,
        ..ok()
    });
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "a call in the loop is an unbounded writer"
    );
}

#[test]
fn refuses_unbounded_store_index() {
    let mut func = build(Shape {
        counted_store: false,
        ..ok()
    });
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "store index without a [0,bound) counted-IV test must fail closed"
    );
}

/// A load base produced by a CSEL is NOT loop-invariant: `CSEL` consumes NZCV,
/// which is not in its operand list, so the flag writer in the body changes the
/// selected pointer every iteration.
///
/// The operand-only invariance test admitted it (both explicit sources are
/// invariant) and `MemoryEffect::Pure` let it through the purity gate, so the
/// pass hoisted `ldr [csel_result]` into the fast preheader AND
/// re-materialized the CSEL in the preamble, where NO compare has run — it
/// then selects on the CALLER's leftover NZCV. Reproduced end-to-end: a raw
/// pointer kernel `p = if s & 1 == 0 { a } else { b }; s += *p; *out = s;`
/// returned 30 under trust-cg vs 39 under LLVM and under
/// `TRUST_CG_DISABLE_PASSES=aliashoist`.
#[test]
fn refuses_flag_reading_load_base() {
    let mut func = MachFunction::new("csel_base".to_string(), Signature::new(vec![], vec![]));
    let ph = func.entry;
    let hdr = func.create_block();
    let exit = func.create_block();

    // Preheader: two candidate load bases, a store base, the bound, idx init.
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(0), i(4096)]); // cand A
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(1), i(8192)]); // cand B
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(3), i(65536)]); // store base
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(2), i(4)]); // bound
    push(&mut func, ph, AArch64Opcode::Movz, vec![g64(10), i(0)]); // idx init
    push(&mut func, ph, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(ph, hdr);

    // Body: a LOOP-VARIANT compare feeding a CSEL that picks the load base.
    push(&mut func, hdr, AArch64Opcode::CmpRI, vec![g64(10), i(2)]);
    push(
        &mut func,
        hdr,
        AArch64Opcode::Csel,
        vec![g64(4), g64(0), g64(1), i(0)], // v4 = (idx == 2) ? v0 : v1
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::LdrRI,
        vec![g64(20), g64(4), i(0)], // ldr v20, [v4] -- base is the CSEL result
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::StrRI,
        vec![g64(20), g64(3), i(0)], // boundable fixed store
    );
    push(
        &mut func,
        hdr,
        AArch64Opcode::AddRI,
        vec![g64(11), g64(10), i(1)],
    );
    push(&mut func, hdr, AArch64Opcode::MovR, vec![g64(10), g64(11)]);
    push(&mut func, hdr, AArch64Opcode::CmpRR, vec![g64(11), g64(2)]);
    push(&mut func, hdr, AArch64Opcode::BCond, vec![i(0), blk(exit)]);
    push(&mut func, hdr, AArch64Opcode::B, vec![blk(hdr)]);
    func.add_edge(hdr, exit);
    func.add_edge(hdr, hdr);
    push(&mut func, exit, AArch64Opcode::Ret, vec![]);

    let before = nblocks(&func);
    let mut pass = AliasVersionedLoadHoist;
    assert!(
        !pass.run(&mut func),
        "a CSEL result is not loop-invariant: NZCV is an unmodelled input"
    );
    assert_eq!(nblocks(&func), before);
}

/// The movement contract itself: every flag READER that `opcode_effect`
/// classifies as memory-pure must still be refused, so a future opcode cannot
/// silently re-open the hole above.
#[test]
fn flag_readers_are_never_invariance_movable() {
    for op in [
        AArch64Opcode::Csel,
        AArch64Opcode::CSet,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csinv,
        AArch64Opcode::Csneg,
        AArch64Opcode::FcselRR,
        AArch64Opcode::Adc,
        AArch64Opcode::Sbc,
    ] {
        assert!(
            crate::effects::opcode_effect(op).is_pure(),
            "{op:?} is memory-pure, which is exactly why the weaker gate let it through"
        );
        let inst = MachInst::new(op, vec![]);
        assert!(
            !super::is_invariance_movable(&inst),
            "{op:?} reads NZCV and must fail the invariance movement contract"
        );
    }
    // A genuinely movable pure op still passes.
    let add = MachInst::new(AArch64Opcode::AddRR, vec![]);
    assert!(super::is_invariance_movable(&add));
}

#[test]
fn no_loops_is_noop() {
    let mut func = MachFunction::new("flat".to_string(), Signature::new(vec![], vec![]));
    let e = func.entry;
    push(&mut func, e, AArch64Opcode::Ret, vec![]);
    let mut pass = AliasVersionedLoadHoist;
    assert!(!pass.run(&mut func));
}

/// The clobber/read range of a 128-bit access must be 16 bytes.
///
/// This number is the ONLY thing standing between the runtime disjointness
/// check and an unsound hoist: it is used both as a load range's width and as
/// the SCALE of an indexed store's range (`[base, base + bound*scale)`), so an
/// under-estimate shrinks the region the check proves disjoint while the
/// hardware still writes the full width. The pass previously reached `Fpr128`
/// through a `_ => 8` catch-all and credited a 16-byte `STR Q` / `LDR Q` with 8
/// bytes — half of every vector access invisible to the check.
///
/// Errors in the other direction are safe (a too-wide range can only fail the
/// check and take the untouched slow loop), which is why the narrow classes may
/// keep the conservative 8; only "never smaller than the true width" is
/// asserted here.
#[test]
fn class_byte_ranges_never_understate_the_access_width() {
    let true_width = |c: RegClass| -> i64 {
        match c {
            RegClass::Fpr128 => 16,
            RegClass::Gpr64 | RegClass::Fpr64 | RegClass::System => 8,
            RegClass::Gpr32 | RegClass::Fpr32 => 4,
            RegClass::Fpr16 => 2,
            RegClass::Fpr8 => 1,
        }
    };
    for c in [
        RegClass::Fpr128,
        RegClass::Gpr64,
        RegClass::Fpr64,
        RegClass::System,
        RegClass::Gpr32,
        RegClass::Fpr32,
        RegClass::Fpr16,
        RegClass::Fpr8,
    ] {
        assert!(
            class_bytes(c) >= true_width(c),
            "{c:?}: range {} understates a {}-byte access",
            class_bytes(c),
            true_width(c)
        );
    }
    assert_eq!(class_bytes(RegClass::Fpr128), 16, "Q access is 16 bytes");
}
