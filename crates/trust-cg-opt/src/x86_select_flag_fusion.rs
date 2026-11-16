// trust-cg-opt - x86-64 select-on-compare flag fusion
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `Cmp + Setcc + Movzx [+ Movzx + AndRI 1] + zero-test + Cmovcc` becomes
//! `Cmp + Cmovcc`.
//!
//! trust_ir lowers `select(a <cc> b, t, f)` as an `ICmp` that materializes a
//! boolean (`Cmp a,b; Setcc %D,cc; Movzx %D,%D`) and a `Select` that re-tests
//! it (`MovRR dst,f; Movzx %D2,%D; AndRI %D2,%D2,1; CmpRI %D2,0;
//! Cmovcc dst,t,NE`). When the boolean feeds only that select, the round trip
//! through `%D` puts five dependent instructions between the comparison and
//! the conditional move. The `Cmovcc` can read the comparison's flags
//! directly, which is the form LLVM emits.
//!
//! Measured cause: `h4_vec_dropper`'s `Vec::push` grow path computes
//! `max(2*cap, len+1)` and `max(4, ..)` with two such selects, back to back, on
//! the path to the allocator call. Hand-editing the linked O2 binary to the
//! fused form moved its runtime from 1.098 to 1.039 of LLVM with both loops
//! pinned at their original addresses (layout-only control: 1.095;
//! `reports/2026-11-15-x86-runtime-2/`).
//!
//! # Pattern, all in one block
//!
//! ```text
//! [c]   flag_writer                ; full RFLAGS overwrite, pure
//! [c+1] Setcc %D, cc                ; standard compare cc
//! [c+2] Movzx %D, %D
//!       W*                          ; flag-neutral moves (see `is_window_move`)
//!       [Movzx %D2, %D ; AndRI %D2, %D2, 1]
//! [z]   CmpRI %T, 0 | TestRR %T, %T ; %T = %D2 if normalized, else %D
//! [z+1] Cmovcc{,32} dst, src, NE|E
//! ```
//!
//! becomes `flag_writer; W*; Cmovcc{,32} dst, src, cc` (`cc.invert()` for an
//! `E` move).
//!
//! # Hand proof
//!
//! `Setcc` makes `%D` exactly `cc ? 1 : 0` from flag_writer's RFLAGS, the
//! `Movzx`/`AndRI 1` normalization keeps that value, and the zero-test sets
//! ZF to `!cc`, so `Cmovcc NE` moves exactly when `cc` held (`E` exactly when
//! it did not). After the rewrite the same RFLAGS reach the `Cmovcc`: nothing
//! between flag_writer and the move writes RFLAGS (the window holds only
//! register moves, which leave RFLAGS untouched), so `Cmovcc cc` moves on the
//! same executions. The erased instructions write only the boolean chain and
//! RFLAGS; no chain register is read anywhere else in the function (checked
//! by register id, class-blind), and the only RFLAGS reader they fed is the
//! rewritten move: the RFLAGS live after the `Cmovcc` (the zero-test's before
//! the rewrite, flag_writer's after it) must be dead there, which
//! [`X86FlagLiveness`] decides across blocks and fails closed on a call, a
//! return, a conditional branch or an unknown exit.
//!
//! # Evidence boundary
//!
//! A code-changing rewrite with no proof-lane run: it is withheld from every
//! compile that keeps proof certificates and from every driver that installs
//! no policy (`x86_select_flag_fusion_enabled`), the
//! `x86_rowreg_memory_rmw_withheld` contract.

use trust_cg_ir::regs::VReg;
use trust_cg_ir::{X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{FlagOverwrite, condition_flag_overwrite, x86_reads_flags, x86_writes_flags};
use crate::x86_flag_liveness::X86FlagLiveness;

static SELECT_FLAG_FUSION_DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Whether a compile withholds the select flag fusion: when it was opted out
/// of, or when the compile keeps proof certificates (see the module's
/// evidence boundary).
pub fn x86_select_flag_fusion_withheld(opted_out: bool, proof_certificates: bool) -> bool {
    opted_out || proof_certificates
}

/// Install the select flag fusion's policy from a TRACKED compiler option,
/// once (`-Ztrust-ir-cg-args=no-x86-select-flag-fusion`, or a compile that
/// keeps proof certificates; [`x86_select_flag_fusion_withheld`]). Returns
/// whether the installed value agrees with `disabled`.
pub fn set_x86_select_flag_fusion_disabled(disabled: bool) -> bool {
    match SELECT_FLAG_FUSION_DISABLED.set(disabled) {
        Ok(()) => true,
        Err(requested) => SELECT_FLAG_FUSION_DISABLED.get() == Some(&requested),
    }
}

/// Only an installed `false` enables the fusion. A driver that installs no
/// policy may keep proof certificates, so the fusion is withheld there.
fn enabled_from(installed_disabled: Option<bool>) -> bool {
    installed_disabled.is_some_and(|disabled| !disabled)
}

pub(crate) fn x86_select_flag_fusion_enabled() -> bool {
    enabled_from(SELECT_FLAG_FUSION_DISABLED.get().copied())
}

/// The register moves the window between the boolean and its zero-test may
/// hold: they neither read nor write RFLAGS. ISel places the select's
/// false-value copy (`MovRR dst, f`) there.
fn is_window_move(inst: &X86ISelInst) -> bool {
    matches!(
        inst.opcode,
        X86Opcode::MovRR | X86Opcode::MovRR32 | X86Opcode::MovRI
    ) && inst.flags == inst.opcode.default_flags()
        && !x86_reads_flags(inst.opcode)
        && !x86_writes_flags(inst.opcode)
        && inst
            .operands
            .iter()
            .all(|op| matches!(op, X86ISelOperand::VReg(_) | X86ISelOperand::Imm(_)))
}

fn mentions_id(inst: &X86ISelInst, id: u32) -> bool {
    inst.operands.iter().any(|op| operand_mentions_id(op, id))
}

fn operand_mentions_id(op: &X86ISelOperand, id: u32) -> bool {
    match op {
        X86ISelOperand::VReg(v) => v.id == id,
        X86ISelOperand::MemAddr { base, .. } => operand_mentions_id(base, id),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_mentions_id(base, id) || operand_mentions_id(index, id)
        }
        _ => false,
    }
}

fn is_standard_compare_cc(cc: X86CondCode) -> bool {
    use X86CondCode::*;
    matches!(cc, B | AE | BE | A | E | NE | L | GE | LE | G)
}

fn is_zero_test_of(inst: &X86ISelInst, v: VReg) -> bool {
    match inst.opcode {
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(r), X86ISelOperand::Imm(0)] if *r == v
        ),
        X86Opcode::TestRR => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)] if *a == v && *b == v
        ),
        _ => false,
    }
}

/// One matched window: the instruction indices to erase, the `Cmovcc` to
/// rewrite and its new condition.
#[derive(Debug, PartialEq, Eq)]
struct Fusion {
    erase: Vec<usize>,
    cmov_idx: usize,
    new_cc: X86CondCode,
    chain_ids: Vec<u32>,
}

fn match_at(insts: &[X86ISelInst], c: usize) -> Option<Fusion> {
    let flag_writer = insts.get(c)?;
    if condition_flag_overwrite(flag_writer) != FlagOverwrite::Full {
        return None;
    }
    let fw = flag_writer.flags;
    if fw.is_call()
        || fw.is_branch()
        || fw.is_terminator()
        || fw.is_return()
        || fw.reads_memory()
        || fw.writes_memory()
        || fw.is_pseudo()
    {
        return None;
    }

    let setcc = insts.get(c + 1)?;
    if setcc.opcode != X86Opcode::Setcc || setcc.flags != X86Opcode::Setcc.default_flags() {
        return None;
    }
    let (d, cc) = match setcc.operands.as_slice() {
        [X86ISelOperand::VReg(d), X86ISelOperand::CondCode(cc)] => (*d, *cc),
        _ => return None,
    };
    if !is_standard_compare_cc(cc) || mentions_id(flag_writer, d.id) {
        return None;
    }
    let movzx = insts.get(c + 2)?;
    if movzx.opcode != X86Opcode::Movzx
        || movzx.flags != X86Opcode::Movzx.default_flags()
        || movzx.operands.as_slice() != [X86ISelOperand::VReg(d), X86ISelOperand::VReg(d)]
    {
        return None;
    }

    let mut chain_ids = vec![d.id];
    let mut erase = vec![c + 1, c + 2];
    let mut i = c + 3;
    while insts
        .get(i)
        .is_some_and(|w| is_window_move(w) && !mentions_id(w, d.id))
    {
        i += 1;
    }

    // Optional normalization of the boolean before its zero-test.
    let mut tail = d;
    if let (Some(nz), Some(am)) = (insts.get(i), insts.get(i + 1))
        && nz.opcode == X86Opcode::Movzx
        && nz.flags == X86Opcode::Movzx.default_flags()
        && let [X86ISelOperand::VReg(d2), X86ISelOperand::VReg(src)] = nz.operands.as_slice()
        && *src == d
        && d2.id != d.id
        && am.opcode == X86Opcode::AndRI
        && am.flags == X86Opcode::AndRI.default_flags()
        && am.operands.as_slice()
            == [
                X86ISelOperand::VReg(*d2),
                X86ISelOperand::VReg(*d2),
                X86ISelOperand::Imm(1),
            ]
    {
        chain_ids.push(d2.id);
        erase.extend([i, i + 1]);
        tail = *d2;
        i += 2;
    }

    let zero_test = insts.get(i)?;
    if !is_zero_test_of(zero_test, tail) || zero_test.flags != zero_test.opcode.default_flags() {
        return None;
    }
    erase.push(i);

    let cmov_idx = i + 1;
    let cmov = insts.get(cmov_idx)?;
    if !matches!(cmov.opcode, X86Opcode::Cmovcc | X86Opcode::Cmovcc32)
        || cmov.flags != cmov.opcode.default_flags()
    {
        return None;
    }
    let new_cc = match cmov.operands.as_slice() {
        [
            X86ISelOperand::VReg(_),
            X86ISelOperand::VReg(_),
            X86ISelOperand::CondCode(m),
        ] => match m {
            X86CondCode::NE => cc,
            X86CondCode::E => cc.invert(),
            _ => return None,
        },
        _ => return None,
    };

    // No chain register is mentioned in this block outside the erased
    // instructions (the setcc, its movzx, the normalization, the zero-test),
    // the cmov included.
    for (k, inst) in insts.iter().enumerate() {
        if erase.contains(&k) {
            continue;
        }
        if chain_ids.iter().any(|id| mentions_id(inst, *id)) {
            return None;
        }
    }

    Some(Fusion {
        erase,
        cmov_idx,
        new_cc,
        chain_ids,
    })
}

/// Fuse every matching window of `func`. Returns whether it changed. The
/// RFLAGS liveness snapshot is recomputed after every block that changed.
pub(crate) fn select_flag_fusion_run(func: &mut X86ISelFunction) -> bool {
    let mut changed = false;
    let mut flags = X86FlagLiveness::analyze(func);
    for block_id in func.block_order.clone() {
        if select_flag_fusion_run_on_block(func, block_id, &flags) {
            changed = true;
            flags = X86FlagLiveness::analyze(func);
        }
    }
    changed
}

/// Fuse every matching window of `block_id`. Returns whether it changed.
/// `flags` is an RFLAGS liveness snapshot of `func` as it stands.
fn select_flag_fusion_run_on_block(
    func: &mut X86ISelFunction,
    block_id: Block,
    flags: &X86FlagLiveness,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let mut fusions = Vec::new();
    let mut c = 0;
    while c < block.insts.len() {
        match match_at(&block.insts, c) {
            Some(fusion) => {
                // No chain register in any other block (no live-out, no
                // second definition elsewhere), by id.
                let escapes = func.blocks.iter().any(|(other, b)| {
                    *other != block_id
                        && b.insts
                            .iter()
                            .any(|inst| fusion.chain_ids.iter().any(|id| mentions_id(inst, *id)))
                });
                // The RFLAGS after the `Cmovcc` change from the zero-test's to
                // flag_writer's: nothing may read them.
                let flags_live_after =
                    !flags.flags_dead_after(&block.insts, block_id, fusion.cmov_idx);
                if escapes || flags_live_after {
                    c += 1;
                } else {
                    c = fusion.cmov_idx + 1;
                    fusions.push(fusion);
                }
            }
            None => c += 1,
        }
    }
    if fusions.is_empty() {
        return false;
    }
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for fusion in fusions.into_iter().rev() {
        if let Some(X86ISelOperand::CondCode(m)) = block.insts[fusion.cmov_idx].operands.get_mut(2)
        {
            *m = fusion.new_cc;
        }
        for idx in fusion.erase.into_iter().rev() {
            block.insts.remove(idx);
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::InstFlags;
    use trust_cg_ir::regs::RegClass;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::types::Type;

    fn g(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }
    fn g32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }
    fn i(op: X86Opcode, ops: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(op, ops)
    }
    fn cc(c: X86CondCode) -> X86ISelOperand {
        X86ISelOperand::CondCode(c)
    }

    /// `h4_vec_dropper`'s grow-path select, as ISel emits it:
    /// `new_cap = (doubled <u new_len) ? new_len : doubled`.
    fn h4_select(cmov_cc: X86CondCode) -> Vec<X86ISelInst> {
        vec![
            i(X86Opcode::CmpRR, vec![g(17), g(7)]),
            i(X86Opcode::Setcc, vec![g32(18), cc(X86CondCode::B)]),
            i(X86Opcode::Movzx, vec![g32(18), g32(18)]),
            i(X86Opcode::MovRR, vec![g(19), g(17)]),
            i(X86Opcode::Movzx, vec![g(20), g32(18)]),
            i(X86Opcode::AndRI, vec![g(20), g(20), X86ISelOperand::Imm(1)]),
            i(X86Opcode::CmpRI, vec![g(20), X86ISelOperand::Imm(0)]),
            i(X86Opcode::Cmovcc, vec![g(19), g(7), cc(cmov_cc)]),
            i(X86Opcode::MovRR, vec![g(21), g(19)]),
            // The next comparison overwrites every flag: RFLAGS are dead
            // after the select.
            i(X86Opcode::CmpRI, vec![g(21), X86ISelOperand::Imm(4)]),
        ]
    }

    fn func_of(blocks: Vec<Vec<X86ISelInst>>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("select_flag_fusion_test".to_string(), sig);
        func.next_vreg = 64;
        for (n, insts) in blocks.into_iter().enumerate() {
            let b = Block(n as u32);
            func.ensure_block(b);
            for inst in insts {
                func.push_inst(b, inst);
            }
        }
        func
    }

    fn run(insts: Vec<X86ISelInst>) -> (bool, Vec<X86ISelInst>) {
        let mut func = func_of(vec![insts]);
        let changed = select_flag_fusion_run(&mut func);
        (changed, func.blocks[&Block(0)].insts.clone())
    }

    #[test]
    fn fuses_the_h4_grow_path_select() {
        let (changed, out) = run(h4_select(X86CondCode::NE));
        assert!(changed);
        let ops: Vec<_> = out.iter().map(|x| x.opcode).collect();
        assert_eq!(
            ops,
            vec![
                X86Opcode::CmpRR,
                X86Opcode::MovRR,
                X86Opcode::Cmovcc,
                X86Opcode::MovRR,
                X86Opcode::CmpRI
            ]
        );
        assert_eq!(out[2].operands, vec![g(19), g(7), cc(X86CondCode::B)]);
    }

    #[test]
    fn a_move_on_equal_takes_the_inverted_condition() {
        let (changed, out) = run(h4_select(X86CondCode::E));
        assert!(changed);
        assert_eq!(out[2].operands[2], cc(X86CondCode::AE));
    }

    #[test]
    fn fuses_without_the_normalization_pair() {
        let insts = vec![
            i(X86Opcode::CmpRR, vec![g(2), g(3)]),
            i(X86Opcode::Setcc, vec![g32(5), cc(X86CondCode::L)]),
            i(X86Opcode::Movzx, vec![g32(5), g32(5)]),
            i(X86Opcode::TestRR, vec![g32(5), g32(5)]),
            i(
                X86Opcode::Cmovcc32,
                vec![g32(6), g32(7), cc(X86CondCode::NE)],
            ),
            i(X86Opcode::TestRR, vec![g32(6), g32(6)]),
        ];
        let (changed, out) = run(insts);
        assert!(changed);
        assert_eq!(out.len(), 3);
        assert_eq!(out[1].operands, vec![g32(6), g32(7), cc(X86CondCode::L)]);
    }

    #[test]
    fn declines_a_partial_flag_writer() {
        let mut insts = h4_select(X86CondCode::NE);
        insts[0] = i(X86Opcode::ImulRR, vec![g(17), g(17), g(7)]);
        assert!(!run(insts).0);
    }

    #[test]
    fn declines_a_flag_writer_that_touches_memory() {
        let mut insts = h4_select(X86CondCode::NE);
        insts[0] = X86ISelInst::with_flags(
            X86Opcode::CmpRR,
            vec![g(17), g(7)],
            X86Opcode::CmpRR
                .default_flags()
                .union(InstFlags::READS_MEMORY),
        );
        assert!(!run(insts).0);
    }

    #[test]
    fn declines_a_non_compare_condition() {
        let mut insts = h4_select(X86CondCode::NE);
        insts[1] = i(X86Opcode::Setcc, vec![g32(18), cc(X86CondCode::S)]);
        assert!(!run(insts).0);
    }

    #[test]
    fn declines_a_flag_writer_in_the_window() {
        let mut insts = h4_select(X86CondCode::NE);
        insts[3] = i(X86Opcode::AddRR, vec![g(19), g(17), g(17)]);
        assert!(!run(insts).0);
    }

    #[test]
    fn declines_a_window_move_that_reads_the_boolean() {
        let mut insts = h4_select(X86CondCode::NE);
        insts[3] = i(X86Opcode::MovRR, vec![g(19), g(18)]);
        assert!(!run(insts).0);
    }

    #[test]
    fn declines_a_cmov_on_another_condition() {
        assert!(!run(h4_select(X86CondCode::B)).0);
    }

    #[test]
    fn declines_a_gap_between_the_zero_test_and_the_cmov() {
        let mut insts = h4_select(X86CondCode::NE);
        insts.insert(7, i(X86Opcode::MovRR, vec![g(30), g(31)]));
        assert!(!run(insts).0);
    }

    #[test]
    fn declines_a_boolean_read_later_in_the_block() {
        let mut insts = h4_select(X86CondCode::NE);
        insts.push(i(X86Opcode::MovRR, vec![g(22), g(20)]));
        assert!(!run(insts).0);
    }

    #[test]
    fn declines_a_boolean_named_in_another_width_later_in_the_block() {
        // Class-blind: a Gpr32 view of the normalized boolean's id still reads it.
        let mut insts = h4_select(X86CondCode::NE);
        insts.push(i(X86Opcode::MovRR32, vec![g32(22), g32(20)]));
        assert!(!run(insts).0);
    }

    #[test]
    fn declines_a_boolean_read_in_another_block() {
        let mut func = func_of(vec![
            h4_select(X86CondCode::NE),
            vec![i(X86Opcode::MovRR, vec![g(23), g(18)])],
        ]);
        assert!(!select_flag_fusion_run(&mut func));
    }

    /// The zero-test's RFLAGS are still read after the `Cmovcc` (here by a
    /// second conditional move): fusing would hand that reader flag_writer's
    /// flags instead.
    #[test]
    fn declines_when_the_zero_tests_flags_are_read_after_the_cmov() {
        let mut insts = h4_select(X86CondCode::NE);
        insts.insert(
            8,
            i(X86Opcode::Cmovcc, vec![g(24), g(25), cc(X86CondCode::E)]),
        );
        assert!(!run(insts).0);
    }

    /// RFLAGS may be live out of the block: the block ends without a full
    /// overwrite and falls through into a block that reads them first.
    #[test]
    fn declines_when_the_flags_are_live_out_of_the_block() {
        let mut first = h4_select(X86CondCode::NE);
        first.pop(); // the trailing `CmpRI`
        let mut func = func_of(vec![
            first,
            vec![i(X86Opcode::Setcc, vec![g32(26), cc(X86CondCode::E)])],
        ]);
        assert!(!select_flag_fusion_run(&mut func));
        // ... and fuses once the successor overwrites them first.
        let mut first = h4_select(X86CondCode::NE);
        first.pop();
        let mut func = func_of(vec![
            first,
            vec![i(X86Opcode::CmpRI, vec![g(21), X86ISelOperand::Imm(0)])],
        ]);
        assert!(select_flag_fusion_run(&mut func));
    }

    #[test]
    fn declines_a_cmov_that_reads_the_boolean() {
        let mut insts = h4_select(X86CondCode::NE);
        insts[7] = i(X86Opcode::Cmovcc, vec![g(19), g(20), cc(X86CondCode::NE)]);
        assert!(!run(insts).0);
    }

    #[test]
    fn policy_enables_only_an_installed_false() {
        assert!(!enabled_from(None));
        assert!(!enabled_from(Some(true)));
        assert!(enabled_from(Some(false)));
        assert!(x86_select_flag_fusion_withheld(true, false));
        assert!(x86_select_flag_fusion_withheld(false, true));
        assert!(x86_select_flag_fusion_withheld(true, true));
        assert!(!x86_select_flag_fusion_withheld(false, false));
    }

    #[test]
    fn the_peephole_pass_withholds_the_fusion_without_an_installed_policy() {
        // No test in this crate installs the policy.
        assert!(SELECT_FLAG_FUSION_DISABLED.get().is_none());
        let mut func = func_of(vec![h4_select(X86CondCode::NE)]);
        crate::x86_peephole::X86Peephole::default().run_on_function(&mut func);
        assert!(
            func.blocks[&Block(0)]
                .insts
                .iter()
                .any(|x| x.opcode == X86Opcode::Setcc)
        );
    }
}
