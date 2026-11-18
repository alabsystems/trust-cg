// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Target-side guard for the AArch64 unsigned-remainder slice. This checks the
//! final layout's local transfers and the register read at each guard. Source
//! reachability, source-to-register binding and actual byte checks belong to
//! the caller. A direct call either leaves this function or returns to its
//! continuation under the calling convention. Unwinding and indirect local
//! transfers are outside the admitted shape.

use std::collections::HashSet;

use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId};
use trust_cg_ir::regs::{X30, regs_overlap};
use trust_cg_ir::{
    AArch64Opcode as Op, InstFlags, InstId, MachFunction, MachInst, MachOperand as O,
};

use trust_cg_opt::effects::aarch64_for_each_def_position;

#[path = "../../../formal/lean/Trust/A64/EuclideanRemainder.lean"]
clean mod euclidean_remainder;

type SourceStamp = (SourceInstId, SourceInstDigest);

/// Immutable attachment to one final machine layout. All paths into the
/// identified divide test its actual X-register divisor as nonzero immediately
/// before entering, either directly or through the checked loop backedge.
pub(crate) struct GuardedRemainder<'a> {
    _function: &'a MachFunction,
    source_rows: [InstId; 3],
    loop_back: Option<RemainderBackedge>,
}

pub(crate) struct RemainderBackedge {
    pub(crate) from: usize,
    pub(crate) to: usize,
    pub(crate) zero: usize,
    #[cfg(test)]
    latch: InstId,
}

impl GuardedRemainder<'_> {
    pub(crate) fn euclidean_loop(&self) -> Option<(&RemainderBackedge, [InstId; 3])> {
        Some((self.loop_back.as_ref()?, self.source_rows))
    }
}

#[cfg(test)]
impl GuardedRemainder<'_> {
    /// The original switch guard, the division and the multiply-subtract, plus
    /// the synthesized zero test of the next divisor if there is a loop.
    pub(crate) fn rows(&self) -> ([InstId; 3], Option<InstId>) {
        (
            self.source_rows,
            self.loop_back.as_ref().map(|edge| edge.latch),
        )
    }
}

pub(crate) fn bind_guarded_remainder(
    func: &MachFunction,
    switch: SourceStamp,
    remainder: SourceStamp,
) -> Option<GuardedRemainder<'_>> {
    let rows = laid_out_words(func)?;
    let incoming = local_incoming_edges(&rows)?;
    let mut remainder_rows = rows
        .iter()
        .enumerate()
        .filter(|(_, row)| source_stamp(func, row.0).is_some_and(|(id, _)| id == remainder.0));
    let (divide_at, &(divide_id, divide)) = remainder_rows.next()?;
    let (msub_at, &(msub_id, msub)) = remainder_rows.next()?;
    if divide_at == 0
        || msub_at != divide_at + 1
        || incoming[msub_at].as_slice() != [divide_at]
        || remainder_rows.next().is_some()
        || source_stamp(func, divide_id) != Some(remainder)
        || source_stamp(func, msub_id) != Some(remainder)
    {
        return None;
    }
    let [q, a, b] = x_operands(divide, Op::UDiv)?;
    let [r, mul_q, mul_b, accum_a] = x_operands(msub, Op::Msub)?;
    if [mul_q, mul_b, accum_a] != [q, b, a]
        || q == a
        || q == b
        || a == b
        || r == a
        || r == b
        || r == q
    {
        return None;
    }

    let mut switch_guards = rows.iter().enumerate().filter(|(_, (id, inst))| {
        matches!(inst.opcode, Op::Cbz | Op::Cbnz)
            && source_stamp(func, *id).is_some_and(|(id, _)| id == switch.0)
    });
    let (entry_at, &(entry_id, entry)) = switch_guards.next()?;
    if switch_guards.next().is_some()
        || source_stamp(func, entry_id) != Some(switch)
        || entry_at >= divide_at
        || zero_test_register(entry)? != b
    {
        return None;
    }
    let taken = resolved_target(entry_at, entry.operands[1].as_imm()?, 19, rows.len())?;
    let (nonzero, zero) = if entry.opcode == Op::Cbnz {
        (taken, entry_at + 1)
    } else {
        (entry_at + 1, taken)
    };
    if nonzero != divide_at || zero == divide_at {
        return None;
    }

    let loop_back = match incoming[divide_at].as_slice() {
        [only] if *only == entry_at => None,
        [first, back] if *first == entry_at && *back == divide_at + 5 => Some(guarded_backedge(
            &rows, &incoming, divide_at, zero, a, b, r,
        )?),
        _ => return None,
    };
    Some(GuardedRemainder {
        _function: func,
        source_rows: [entry_id, divide_id, msub_id],
        loop_back,
    })
}

fn source_stamp(func: &MachFunction, id: InstId) -> Option<SourceStamp> {
    match func.inst_lowering_provenance(id) {
        LoweringProvenance::SourceInst { id, digest, .. } => Some((id, digest)),
        _ => None,
    }
}

fn x_register(op: &O) -> Option<u16> {
    let O::PReg(reg) = op else { return None };
    let encoding = reg.encoding();
    (encoding <= 30).then_some(encoding)
}

fn x_operands<const N: usize>(inst: &MachInst, opcode: Op) -> Option<[u16; N]> {
    if inst.opcode != opcode || !inst.implicit_defs.is_empty() || inst.operands.len() != N {
        return None;
    }
    let mut registers = [0; N];
    for (slot, operand) in registers.iter_mut().zip(&inst.operands) {
        *slot = x_register(operand)?;
    }
    Some(registers)
}

fn zero_test_register(inst: &MachInst) -> Option<u16> {
    let [register, O::Imm(_)] = inst.operands.as_slice() else {
        return None;
    };
    inst.implicit_defs.is_empty().then_some(())?;
    x_register(register)
}

type Word<'a> = (InstId, &'a MachInst);

fn guarded_backedge(
    rows: &[Word<'_>],
    incoming: &[Vec<usize>],
    divide: usize,
    zero: usize,
    a: u16,
    b: u16,
    r: u16,
) -> Option<RemainderBackedge> {
    // UDIV; MSUB; MOV Xa,Xb; MOV Xb,Xr; CBZ Xb,exit; B remainder.
    // Each intervening word is reachable only by falling through its exact
    // predecessor, including the back branch itself.
    let [(_, next_a), (_, next_b), (_latch_id, cbz), (_, back)] =
        rows.get(divide + 2..=divide + 5)?
    else {
        return None;
    };
    for at in divide + 2..=divide + 5 {
        if incoming[at].as_slice() != [at - 1] {
            return None;
        }
    }
    if !matches!(next_a.opcode, Op::MOVXrr | Op::MovR)
        || !matches!(next_b.opcode, Op::MOVXrr | Op::MovR)
        || cbz.opcode != Op::Cbz
        || zero_test_register(cbz)? != b
        || resolved_target(divide + 4, cbz.operands[1].as_imm()?, 19, rows.len())? != zero
        || back.opcode != Op::B
        || !back.implicit_defs.is_empty()
    {
        return None;
    }
    let [dst_a, src_a] = x_operands(next_a, next_a.opcode)?;
    let [dst_b, src_b] = x_operands(next_b, next_b.opcode)?;
    if dst_a != a
        || dst_b != b
        || trust_cg_a64_euclidean_register_update(
            u32::from(b),
            u32::from(r),
            u32::from(src_a),
            u32::from(src_b),
        ) != 0
    {
        return None;
    }
    Some(RemainderBackedge {
        from: divide + 5,
        to: divide,
        zero,
        #[cfg(test)]
        latch: *_latch_id,
    })
}

fn laid_out_words(func: &MachFunction) -> Option<Vec<Word<'_>>> {
    if func.block_order.first() != Some(&func.entry)
        || func.eh_metadata.has_eh_info()
        || func.stack_limit_overflow_block.is_some()
        || !func.jump_tables.is_empty()
    {
        return None;
    }
    let mut blocks = HashSet::new();
    let mut ids = HashSet::new();
    let mut words = Vec::new();
    for block in &func.block_order {
        if !blocks.insert(*block) {
            return None;
        }
        for id in &func.blocks.get(block.0 as usize)?.insts {
            if !ids.insert(*id) {
                return None;
            }
            let inst = func.insts.get(id.0 as usize)?;
            // Match the shared AArch64 encode/layout convention: every
            // non-pseudo instruction occupies one word, and no pseudo does.
            if !inst.is_pseudo() {
                words.push((*id, inst));
            }
        }
    }
    Some(words)
}

fn resolved_target(at: usize, displacement: i64, bits: u32, words: usize) -> Option<usize> {
    let limit = 1i64 << (bits - 1);
    if !(-limit..limit).contains(&displacement) {
        return None;
    }
    let target = at.checked_add_signed(isize::try_from(displacement).ok()?)?;
    (target < words).then_some(target)
}

fn local_incoming_edges(rows: &[Word<'_>]) -> Option<Vec<Vec<usize>>> {
    // RET exits through the caller's link only while that link is intact.
    // A call or a write to either LR view requires its own return proof.
    if rows.iter().any(|(_, inst)| inst.opcode == Op::Ret)
        && rows.iter().any(|(_, inst)| {
            (inst.flags | inst.opcode.default_flags()).is_call() || writes_link_register(inst)
        })
    {
        return None;
    }
    let mut incoming = vec![Vec::new(); rows.len()];
    let control = InstFlags::IS_BRANCH | InstFlags::IS_CALL | InstFlags::IS_TERMINATOR;
    for (at, (_, inst)) in rows.iter().enumerate() {
        let mut fallthrough = true;
        let target = match (inst.opcode, inst.operands.as_slice()) {
            (Op::B, [O::Imm(d)]) => {
                fallthrough = false;
                Some(resolved_target(at, *d, 26, rows.len())?)
            }
            (Op::BCond | Op::Bcc | Op::Cbz | Op::Cbnz, [_, O::Imm(d)]) => {
                Some(resolved_target(at, *d, 19, rows.len())?)
            }
            (Op::Tbz | Op::Tbnz, [_, O::Imm(_), O::Imm(d)]) => {
                Some(resolved_target(at, *d, 14, rows.len())?)
            }
            (Op::Bl | Op::BL, [O::Symbol(_)]) => None,
            (Op::Ret, []) | (Op::Brk, [] | [O::Imm(0..=0xffff)]) => {
                fallthrough = false;
                None
            }
            (Op::Ret, [reg]) if x_register(reg) == Some(30) => {
                fallthrough = false;
                None
            }
            (Op::Brk | Op::Ret, _) => return None,
            _ if ((inst.flags | inst.opcode.default_flags()) & control) != InstFlags::EMPTY => {
                return None;
            }
            _ => None,
        };
        if let Some(target) = target {
            incoming[target].push(at);
        }
        if fallthrough {
            incoming.get_mut(at + 1)?.push(at);
        }
    }
    Some(incoming)
}

fn writes_link_register(inst: &MachInst) -> bool {
    let mut writes_link = inst.implicit_defs.iter().any(|&reg| regs_overlap(reg, X30));
    aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |position| {
        if let O::PReg(reg) | O::MemOp { base: reg, .. } = inst.operands[position] {
            writes_link |= regs_overlap(reg, X30);
        }
    });
    writes_link
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{BlockId, PReg, Signature};

    const SWITCH: SourceStamp = (
        SourceInstId {
            block: 10,
            index: 1,
        },
        SourceInstDigest(76),
    );
    const UREM: SourceStamp = (
        SourceInstId {
            block: 14,
            index: 0,
        },
        SourceInstDigest(94),
    );

    fn x(reg: u16) -> O {
        O::PReg(PReg::new(reg))
    }

    fn emit(func: &mut MachFunction, block: BlockId, opcode: Op, operands: Vec<O>) -> InstId {
        let id = func.push_inst(MachInst::new(opcode, operands));
        func.append_inst(block, id);
        id
    }

    fn stamp(func: &mut MachFunction, row: InstId, (id, digest): SourceStamp) {
        func.set_inst_lowering_provenance(
            row,
            LoweringProvenance::SourceInst {
                id,
                digest,
                trust_ir_inst: None,
            },
        );
    }

    struct Fixture {
        func: MachFunction,
        prelude: InstId,
        guard: InstId,
        divide: InstId,
        msub: InstId,
        latch: Option<(InstId, InstId, InstId)>,
    }

    fn fixture(rotated: bool) -> Fixture {
        let mut func = MachFunction::new("remainder".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let exit = func.create_block();
        let body = func.create_block();
        // The prelude occupies a word that a control can retarget to break
        // the otherwise guarded entry. Its recorded CFG does not change.
        let prelude = emit(&mut func, entry, Op::BCond, vec![O::Imm(0), O::Imm(1)]);
        let guard = emit(&mut func, entry, Op::Cbnz, vec![x(2), O::Imm(2)]);
        emit(&mut func, exit, Op::Ret, vec![]);
        let divide = emit(&mut func, body, Op::UDiv, vec![x(0), x(3), x(2)]);
        let msub = emit(&mut func, body, Op::Msub, vec![x(1), x(0), x(2), x(3)]);
        let latch = if rotated {
            emit(&mut func, body, Op::MOVXrr, vec![x(3), x(2)]);
            let update = emit(&mut func, body, Op::MOVXrr, vec![x(2), x(1)]);
            let cbz = emit(&mut func, body, Op::Cbz, vec![x(2), O::Imm(-5)]);
            let back = emit(&mut func, body, Op::B, vec![O::Imm(-5)]);
            Some((update, cbz, back))
        } else {
            emit(&mut func, body, Op::Ret, vec![]);
            None
        };
        stamp(&mut func, guard, SWITCH);
        stamp(&mut func, divide, UREM);
        stamp(&mut func, msub, UREM);
        Fixture {
            func,
            prelude,
            guard,
            divide,
            msub,
            latch,
        }
    }

    #[test]
    fn binds_guarded_remainder_and_rotated_latch() {
        for rotated in [false, true] {
            let f = fixture(rotated);
            let witness = bind_guarded_remainder(&f.func, SWITCH, UREM).unwrap();
            assert_eq!(
                witness.rows(),
                ([f.guard, f.divide, f.msub], f.latch.map(|(_, cbz, _)| cbz))
            );
        }
    }

    #[test]
    fn refuses_an_actual_edge_bypassing_any_guard_or_the_divide() {
        let f = fixture(true);
        // Targets are UDIV, MSUB, the update of X2, and the back branch.
        for target in [3, 4, 6, 8] {
            let mut changed = f.func.clone();
            changed.inst_mut(f.prelude).operands[1] = O::Imm(target);
            assert!(bind_guarded_remainder(&changed, SWITCH, UREM).is_none());
        }
    }

    #[test]
    fn refuses_retargeted_returns_that_can_bypass_the_guard() {
        let f = fixture(false);
        let indirect_entries = [
            MachInst::new(Op::Adr, vec![x(30), O::Imm(12)]),
            MachInst::new(Op::MOVWrr, vec![x(62), x(34)]),
            MachInst::new(Op::LdpRI, vec![x(13), x(30), x(4), O::Imm(0)]),
            MachInst::new(
                Op::LdpPostIndex,
                vec![
                    x(13),
                    x(14),
                    O::MemOp {
                        base: X30,
                        offset: 16,
                    },
                ],
            ),
            // A laid-out NOP exercises hidden definitions. The default NOP
            // is a pseudo and consumes no word or architectural state.
            MachInst::with_flags(Op::Nop, vec![], InstFlags::EMPTY).with_implicit_defs(&[X30]),
            MachInst::with_flags(Op::BL, vec![O::Symbol("callee".into())], InstFlags::EMPTY),
        ];
        for inst in indirect_entries {
            let mut changed = f.func.clone();
            let opcode = inst.opcode;
            *changed.inst_mut(f.prelude) = inst;
            assert!(
                bind_guarded_remainder(&changed, SWITCH, UREM).is_none(),
                "{opcode:?} undermines the return-link premise"
            );
        }
    }

    #[test]
    fn refuses_inverted_guards_wrong_polarity_targets_and_wrong_registers() {
        let f = fixture(true);
        let (update, cbz, back) = f.latch.unwrap();
        for (id, index, operand) in [
            (f.guard, 0, x(34)), // W2 does not test all of the I64 divisor.
            (f.guard, 0, x(3)),
            (f.guard, 1, O::Imm(1)),
            (f.divide, 2, x(4)),
            (f.msub, 2, x(5)),
            (update, 1, x(0)),
            (cbz, 0, x(3)),
            (cbz, 1, O::Imm(-4)),
            (back, 0, O::Imm(-4)),
        ] {
            let mut changed = f.func.clone();
            changed.inst_mut(id).operands[index] = operand;
            assert!(bind_guarded_remainder(&changed, SWITCH, UREM).is_none());
        }
        for (id, opcode) in [(f.guard, Op::Cbz), (cbz, Op::Cbnz)] {
            let mut changed = f.func.clone();
            changed.inst_mut(id).opcode = opcode;
            assert!(bind_guarded_remainder(&changed, SWITCH, UREM).is_none());
        }
    }

    #[test]
    fn refuses_stale_source_digests_and_cloned_remainder_rows() {
        let f = fixture(true);
        assert!(bind_guarded_remainder(&f.func, (SWITCH.0, SourceInstDigest(0)), UREM).is_none());
        assert!(bind_guarded_remainder(&f.func, SWITCH, (UREM.0, SourceInstDigest(0))).is_none());
        let mut changed = f.func.clone();
        stamp(&mut changed, f.msub, (UREM.0, SourceInstDigest(0)));
        assert!(bind_guarded_remainder(&changed, SWITCH, UREM).is_none());
        let mut changed = f.func.clone();
        *changed.inst_mut(f.prelude) = f.func.inst(f.divide).clone();
        stamp(&mut changed, f.prelude, UREM);
        assert!(bind_guarded_remainder(&changed, SWITCH, UREM).is_none());
    }
}
