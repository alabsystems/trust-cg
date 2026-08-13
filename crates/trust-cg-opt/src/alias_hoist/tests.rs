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

#[test]
fn no_loops_is_noop() {
    let mut func = MachFunction::new("flat".to_string(), Signature::new(vec![], vec![]));
    let e = func.entry;
    push(&mut func, e, AArch64Opcode::Ret, vec![]);
    let mut pass = AliasVersionedLoadHoist;
    assert!(!pass.run(&mut func));
}
