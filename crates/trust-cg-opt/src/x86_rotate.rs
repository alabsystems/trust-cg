// trust-cg-opt - x86-64 Loop Rotation (jump threading through pure-test blocks)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Loop rotation for x86-64 ISel-output functions, implemented as jump
//! threading through PURE-TEST blocks (task #72 pass 1 — the largest scalar
//! per-iteration tax; see the b09 decomposition in the sweep memory).
//!
//! The top-tested loops the frontend emits pay, per iteration, the header's
//! compare chain PLUS a conditional branch PLUS the latch's unconditional
//! `jmp` back to the header. LLVM rotates such loops so the body ends with a
//! single bottom-test branch. This pass gets the same effect as a peephole:
//!
//! For a block `L` ending `Jmp H` where `H` consists solely of pure,
//! register-only, PReg-free compute (the Setcc-materialized compare idiom:
//! copies / extends / adds / masks / compares) ending `Jcc cc, T; Jmp F`,
//! replace L's terminator with a FRESH-VREG-renamed copy of H's instructions
//! followed by the same two terminators, and set L's successors to `[T, F]`.
//!
//! SOUNDNESS is local and unconditional — no loop or dominance analysis is
//! needed: control that flowed `L → H → (T|F)` executed exactly H's pure
//! compute on register state unchanged since the end of L (H reads no memory,
//! calls nothing, and traps nothing), so executing a renamed copy of that
//! compute at the end of L reaches the identical successor with identical
//! observable state (the copy leaves the same EFLAGS the original H left,
//! and its fresh defs are dead outside the copied chain). When `L → H` is a
//! loop back edge this IS loop rotation (H remains as the guard for the
//! first entry); when it is not, it is plain profitable jump threading of a
//! small test block. The regalloc validator and TV-5 gate the final stream
//! as with every pass.
//!
//! Kill switch: DEFAULT-ON at O2/O3 (flipped after the staged gate: 18/18
//! suite differential + 12/12 generated loop-shape corpus at O0/O2/O3, with
//! the liveness-safety fix the b07 gate run caught — headers whose defs are
//! live into the body are refused). `TCG_NO_X86_ROTATE` opts out for
//! forensic rollback / A-B comparison.

use std::collections::HashMap;

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::x86_pass_manager::X86MachinePass;

/// Mint a fresh vreg of `class` (the same discipline as the vectorizer's
/// helpers: bump `next_vreg`, record nominal width by class).
fn fresh_vreg(func: &mut X86ISelFunction, class: RegClass) -> VReg {
    let id = func.next_vreg;
    func.next_vreg += 1;
    let v = VReg::new(id, class);
    let width = match class {
        RegClass::Gpr32 => 32,
        _ => 64,
    };
    func.vreg_nominal_widths.insert(v, width);
    v
}

/// Maximum instruction count (excluding the two terminators) of a header we
/// are willing to replicate into each predecessor latch. The Setcc compare
/// idiom is 6-9 instructions; 12 leaves headroom without bloating code.
const MAX_THREADED_HEADER_INSTS: usize = 12;

/// Loop rotation / pure-test jump threading for x86-64 ISel functions.
pub struct X86LoopRotate;

impl X86MachinePass for X86LoopRotate {
    fn name(&self) -> &str {
        "x86-loop-rotate"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        if std::env::var_os("TCG_NO_X86_ROTATE").is_some() {
            return false;
        }
        run_impl(func)
    }
}

/// Opcodes allowed in a threadable pure-test header: register-only compute
/// with no memory access, no calls, no traps, and no implicit fixed-register
/// behavior. Flag WRITES are fine (the copy re-creates the exact flag state
/// the original header produced on the taken path); flag READS other than the
/// final `Jcc` are confined to `Setcc`, which reads the flags the copied
/// chain itself just computed.
fn is_threadable_opcode(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::MovRR
            | X86Opcode::MovRR32
            | X86Opcode::MovRI
            | X86Opcode::Movzx
            | X86Opcode::MovzxW
            | X86Opcode::MovsxB
            | X86Opcode::MovsxW
            | X86Opcode::Movsx
            | X86Opcode::AddRR
            | X86Opcode::SubRR
            | X86Opcode::AndRI
            | X86Opcode::CmpRR
            | X86Opcode::CmpRI
            | X86Opcode::CmpRI8
            | X86Opcode::TestRR
            | X86Opcode::TestRI
            | X86Opcode::Setcc
    )
}

/// A header eligible for threading: `insts[..n-2]` all threadable pure
/// compute over VReg/Imm/CondCode operands only, terminated by exactly
/// `Jcc cc, T` then `Jmp F`.
fn threadable_header(func: &X86ISelFunction, h: Block) -> Option<Vec<X86ISelInst>> {
    let block = func.blocks.get(&h)?;
    let n = block.insts.len();
    if n < 2 || n - 2 > MAX_THREADED_HEADER_INSTS {
        return None;
    }
    let jcc = &block.insts[n - 2];
    let jmp = &block.insts[n - 1];
    if jcc.opcode != X86Opcode::Jcc || jmp.opcode != X86Opcode::Jmp {
        return None;
    }
    for inst in &block.insts[..n - 2] {
        if !is_threadable_opcode(inst.opcode) {
            return None;
        }
        for op in &inst.operands {
            match op {
                X86ISelOperand::VReg(_) | X86ISelOperand::Imm(_) | X86ISelOperand::CondCode(_) => {}
                // PRegs (ABI state), memory, blocks, slots: refuse.
                _ => return None,
            }
        }
    }
    // LIVENESS SAFETY (the b07 gate catch): the threaded path BYPASSES H, so
    // any value H defines must be consumed entirely WITHIN H — a def that is
    // (a) read by any other block, or (b) also defined elsewhere (a
    // loop-carried vreg being updated in the header), would be stale or
    // skipped on the threaded path. Refuse such headers.
    let mut h_defs: Vec<VReg> = Vec::new();
    for inst in &block.insts[..n - 2] {
        if crate::effects::x86_produces_value(inst.opcode)
            && let Some(X86ISelOperand::VReg(d)) = inst.operands.first()
        {
            h_defs.push(*d);
        }
    }
    if !h_defs.is_empty() {
        for (bid, other) in func.blocks.iter() {
            for inst in &other.insts {
                let in_header = *bid == h;
                for (idx, op) in inst.operands.iter().enumerate() {
                    let refs = |v: &VReg| h_defs.contains(v);
                    let hit = match op {
                        X86ISelOperand::VReg(v) => refs(v),
                        X86ISelOperand::MemAddr { base, .. } => {
                            matches!(base.as_ref(), X86ISelOperand::VReg(v) if refs(v))
                        }
                        X86ISelOperand::SibMemAddr { base, index, .. } => {
                            matches!(base.as_ref(), X86ISelOperand::VReg(v) if refs(v))
                                || matches!(index.as_ref(), X86ISelOperand::VReg(v) if refs(v))
                        }
                        _ => false,
                    };
                    if !hit {
                        continue;
                    }
                    if !in_header {
                        return None; // used or defined outside H
                    }
                    // Inside H a hit is fine UNLESS it is a SECOND def of the
                    // same vreg... multiple defs within H are handled by the
                    // sequential rename; only external references matter.
                    let _ = idx;
                }
            }
        }
    }
    Some(block.insts.clone())
}

/// Copy the header instruction sequence, renaming every DEF to a fresh vreg
/// (sequentially, so intra-copy uses of a renamed def pick up the new name).
/// Uses of vregs not defined inside the copy keep their names — they read the
/// same live values the original header would have read.
fn rename_copy(func: &mut X86ISelFunction, insts: &[X86ISelInst]) -> Vec<X86ISelInst> {
    let mut map: HashMap<VReg, VReg> = HashMap::new();
    let mut out = Vec::with_capacity(insts.len());
    for inst in insts {
        let mut cloned = inst.clone();
        // Rewrite USES first (operands beyond the def position, and the def
        // position too when the opcode reads it — conservatively rewrite all
        // operand vregs through the current map), then mint the def.
        for op in cloned.operands.iter_mut() {
            if let X86ISelOperand::VReg(v) = op
                && let Some(nv) = map.get(v)
            {
                *v = *nv;
            }
        }
        if crate::effects::x86_produces_value(cloned.opcode)
            && let Some(X86ISelOperand::VReg(d)) = cloned.operands.first().cloned()
        {
            let fresh = fresh_vreg(func, d.class);
            map.insert(d, fresh);
            if let Some(X86ISelOperand::VReg(slot)) = cloned.operands.first_mut() {
                *slot = fresh;
            }
        }
        out.push(cloned);
    }
    out
}

fn run_impl(func: &mut X86ISelFunction) -> bool {
    let mut changed = false;
    let order = func.block_order.clone();
    for l in order {
        // L must end with an unconditional `Jmp H` and have no other
        // terminator ambiguity (exactly one successor).
        let (h,) = {
            let Some(lb) = func.blocks.get(&l) else {
                continue;
            };
            let Some(last) = lb.insts.last() else {
                continue;
            };
            if last.opcode != X86Opcode::Jmp {
                continue;
            }
            let Some(X86ISelOperand::Block(h)) = last.operands.first() else {
                continue;
            };
            if lb.successors.len() != 1 || lb.successors[0] != *h || *h == l {
                continue;
            }
            (*h,)
        };
        // Thread only BACK edges (H already laid out before L): this is the
        // loop-rotation profile. Forward threading is left to cfg_simplify.
        let pos = |b: Block| func.block_order.iter().position(|x| *x == b);
        match (pos(h), pos(l)) {
            (Some(hp), Some(lp)) if hp < lp => {}
            _ => continue,
        }
        let Some(header_insts) = threadable_header(func, h) else {
            continue;
        };
        let n = header_insts.len();
        let (taken, fall, cc) = {
            let jcc = &header_insts[n - 2];
            let jmp = &header_insts[n - 1];
            let (Some(X86ISelOperand::CondCode(cc)), Some(X86ISelOperand::Block(t))) =
                (jcc.operands.first(), jcc.operands.get(1))
            else {
                continue;
            };
            let Some(X86ISelOperand::Block(f)) = jmp.operands.first() else {
                continue;
            };
            (*t, *f, *cc)
        };
        // `taken == l` is the CANONICAL rotated form: the single-block loop
        // body becomes a self-looping bottom test (`Jcc cc, L`), replaying
        // exactly the original L -> H -> L execution sequence. `fall == l`
        // is the same argument on the exit edge. Neither needs exclusion.
        let mut copy = rename_copy(func, &header_insts[..n - 2]);
        copy.push(X86ISelInst::new(
            X86Opcode::Jcc,
            vec![X86ISelOperand::CondCode(cc), X86ISelOperand::Block(taken)],
        ));
        copy.push(X86ISelInst::new(
            X86Opcode::Jmp,
            vec![X86ISelOperand::Block(fall)],
        ));
        let Some(lb) = func.blocks.get_mut(&l) else {
            continue;
        };
        lb.insts.pop(); // the old `Jmp H`
        lb.insts.extend(copy);
        lb.successors = vec![taken, fall];
        changed = true;
    }
    changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::X86ISelBlock;
    use trust_cg_lower::function::Signature;

    fn empty_func(name: &str) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut f = X86ISelFunction::new(name.to_string(), sig);
        for b in 0..4u32 {
            f.blocks.insert(
                Block(b),
                X86ISelBlock {
                    insts: vec![],
                    successors: vec![],
                },
            );
        }
        f.block_order = vec![Block(0), Block(1), Block(2), Block(3)];
        f
    }

    fn vr(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg {
            id,
            class: RegClass::Gpr64,
        })
    }

    /// A top-tested loop: preheader(0) -> header(1){test: Jcc->body(2),
    /// Jmp->exit(3)}; body(2) is the latch ending `Jmp header`. Rotation must
    /// replace the latch terminator with a renamed copy of the test + the two
    /// branches, retargeting the latch to {body, exit} directly.
    #[test]
    fn rotates_top_tested_loop_latch() {
        let mut func = empty_func("rot");
        // preheader: jmp header
        func.push_inst(
            Block(0),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
        );
        func.blocks.get_mut(&Block(0)).unwrap().successors = vec![Block(1)];
        // header: cmp v0, 7; jcc NE -> body; jmp exit
        func.push_inst(
            Block(1),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vr(0), X86ISelOperand::Imm(7)]),
        );
        func.push_inst(
            Block(1),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::NE),
                    X86ISelOperand::Block(Block(2)),
                ],
            ),
        );
        func.push_inst(
            Block(1),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(3))]),
        );
        func.blocks.get_mut(&Block(1)).unwrap().successors = vec![Block(2), Block(3)];
        // body/latch: v0 = v0 + v1 ; jmp header
        func.push_inst(
            Block(2),
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(0), vr(0), vr(1)]),
        );
        func.push_inst(
            Block(2),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
        );
        func.blocks.get_mut(&Block(2)).unwrap().successors = vec![Block(1)];
        // exit: ret
        func.push_inst(Block(3), X86ISelInst::new(X86Opcode::Ret, vec![]));

        let changed = run_impl(&mut func);
        assert!(changed, "back edge through a pure-test header must thread");
        let latch = func.blocks.get(&Block(2)).unwrap();
        assert_eq!(latch.successors, vec![Block(2), Block(3)]);
        let k = latch.insts.len();
        assert_eq!(latch.insts[k - 3].opcode, X86Opcode::CmpRI);
        assert_eq!(latch.insts[k - 2].opcode, X86Opcode::Jcc);
        assert_eq!(latch.insts[k - 1].opcode, X86Opcode::Jmp);
        // The copied CmpRI reads the SAME vreg (v0 — not defined in the copy).
        assert_eq!(latch.insts[k - 3].operands[0], vr(0));
    }

    /// A header containing a memory load must NOT be threaded.
    #[test]
    fn refuses_header_with_memory() {
        let mut func = empty_func("rot_mem");
        func.push_inst(
            Block(1),
            X86ISelInst::new(
                X86Opcode::MovRM,
                vec![
                    vr(0),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vr(9)),
                        disp: 0,
                    },
                ],
            ),
        );
        func.push_inst(
            Block(1),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vr(0), X86ISelOperand::Imm(0)]),
        );
        func.push_inst(
            Block(1),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::NE),
                    X86ISelOperand::Block(Block(2)),
                ],
            ),
        );
        func.push_inst(
            Block(1),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(3))]),
        );
        func.blocks.get_mut(&Block(1)).unwrap().successors = vec![Block(2), Block(3)];
        func.push_inst(
            Block(2),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
        );
        func.blocks.get_mut(&Block(2)).unwrap().successors = vec![Block(1)];
        func.push_inst(Block(3), X86ISelInst::new(X86Opcode::Ret, vec![]));

        assert!(!run_impl(&mut func), "memory-reading header must refuse");
    }
}
