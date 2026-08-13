// trust-cg-opt - x86-64 Dead Code Elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Conservative dead code elimination for x86-64 ISel-output functions.
//!
//! This pass is intentionally scoped to the x86 pass-manager surface. It is not
//! part of the default x86 codegen pipeline.

use std::collections::HashSet;

use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{
    x86_inst_effect, x86_is_removable, x86_produces_value, x86_reads_flags, x86_writes_flags,
};
use crate::x86_pass_manager::X86MachinePass;

/// Dead Code Elimination for x86-64 ISel-output machine functions.
pub struct X86DeadCodeElimination;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FlagOverwrite {
    None,
    Partial,
    Full,
}

impl X86DeadCodeElimination {
    /// Run x86 DCE directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86DeadCodeElimination {
    fn name(&self) -> &str {
        "x86-dce"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

fn run_impl(func: &mut X86ISelFunction) -> bool {
    let mut changed = false;
    let local_tier = local_dce_enabled();

    loop {
        let used_vregs = collect_used_vregs(func);
        let mut iteration_changed = false;

        for block_id in func.block_order.clone() {
            let Some(block) = func.blocks.get_mut(&block_id) else {
                continue;
            };

            let old_len = block.insts.len();
            let remove: Vec<bool> = block
                .insts
                .iter()
                .enumerate()
                .map(|(index, inst)| {
                    is_dead_instruction(inst, &used_vregs)
                        || is_dead_flag_only_instruction(&block.insts, index)
                })
                .collect();
            let mut next_insts = Vec::with_capacity(block.insts.len());
            for (inst, remove) in block.insts.drain(..).zip(remove) {
                if !remove {
                    next_insts.push(inst);
                }
            }
            block.insts = next_insts;
            if local_tier && local_per_def_dce_on_block(&mut block.insts) {
                iteration_changed = true;
            }
            iteration_changed |= block.insts.len() != old_len;
        }

        if !iteration_changed {
            break;
        }
        changed = true;
    }

    changed
}

// ---------------------------------------------------------------------------
// Per-def local deadness tier (DEFAULT-ON; `TCG_NO_X86_DCE_LOCAL` opts out)
//
// The function-wide `used_vregs` model above keeps EVERY def of a vreg id
// alive as long as ANY use of that id exists anywhere — sound, but blind in a
// post-unroll body where verbatim clones REUSE vreg ids (24 defs of one id,
// each dead except where locally consumed). This tier deletes a def that
// provably cannot reach any use:
//
//   the SAME block contains a LATER def of the same vreg, and in the window
//   between the two there is NO use of the vreg, NO branch / call /
//   terminator / return (no path leaves the window carrying the value), and
//   NO pseudo (trap carriers etc. are opaque: fail closed).
//
// SOUNDNESS. The value the candidate def writes can only be observed through
// a later read of the vreg. Reads inside the window: excluded by the use
// scan (which over-approximates: any operand mention, including addressing
// regs, and the tied first operand). Reads after the window: see the LATER
// def's value, not the candidate's (same vreg, straight-line between). Reads
// on another path: impossible — no control flow leaves the window. The
// redefining instruction itself must not READ the vreg (tied forms): checked
// via `first_operand_is_def_and_use` + an operand scan of its non-def
// operands.
//
// What may be deleted (each fail-closed beyond the window proof):
//   - the pure no-flag set `x86_is_removable` (MovRR/MovRI/Lea/…);
//   - pure flag-WRITING ALU from a closed allowlist (AddRR/AddRI/SubRR/
//     SubRI/ImulRR/ImulRRI/AndRR/AndRI/OrRR/OrRI/XorRR/XorRI/ShlRI/ShrRI/
//     SarRI), additionally requiring `flags_written_here_are_dead` — the
//     same obligation the flag-only deletion above discharges;
//   - direct stack-slot loads `MovRM [StackSlot + d]` (never trap: frame
//     slots are mapped for the function's lifetime; deleting a dead
//     non-faulting load is unobservable), requiring no proof_origin (an
//     atomic/volatile load carries one and is never deleted).
// No operand may be a PReg (fixed-register contracts are ABI-observable).
// ---------------------------------------------------------------------------

/// DEFAULT-ON after the 2026-07-20 record (the Cmovcc/tied-shadow classes
/// are excluded by the closed `full_unconditional_overwrite` allowlist and
/// pinned by teeth); `TCG_NO_X86_DCE_LOCAL` is the forensic opt-out.
fn local_dce_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_DCE_LOCAL").is_none()
}

/// Pure flag-writing ALU allowlist for the per-def local tier. Closed set:
/// every member writes RFLAGS as its only effect beyond the operand-0 def.
fn local_dce_pure_flag_alu(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        AddRR
            | AddRI
            | SubRR
            | SubRI
            | ImulRR
            | ImulRRI
            | AndRR
            | AndRI
            | OrRR
            | OrRI
            | XorRR
            | XorRI
            | ShlRI
            | ShrRI
            | SarRI
    )
}

/// Deletability class of a candidate instruction, before the window proof.
/// (A slot-load class was considered and REJECTED in adversarial review:
/// its "frame loads never fault" obligation is not discharged by any
/// analysis here — memory reads stay out of scope entirely.)
enum LocalDceClass {
    /// Pure, no flag write (the `x86_is_removable` set).
    PureNoFlags,
    /// Pure ALU that writes flags: needs `local_flags_dead`.
    PureFlags,
}

fn local_dce_class(inst: &X86ISelInst) -> Option<LocalDceClass> {
    if inst.proof_origin.is_some() || inst_touches_fixed_register(inst) {
        return None;
    }
    if inst.flags != inst.opcode.default_flags() {
        return None;
    }
    let effect = x86_inst_effect(inst);
    if x86_is_removable(inst.opcode) && effect.is_pure() {
        return Some(LocalDceClass::PureNoFlags);
    }
    if local_dce_pure_flag_alu(inst.opcode) && effect.is_pure() {
        return Some(LocalDceClass::PureFlags);
    }
    None
}

/// Closed allowlist of opcodes whose operand-0 write is FULL-WIDTH and
/// UNCONDITIONAL — the only opcodes eligible as shadowing redefs in the
/// per-def local tier. Notably EXCLUDED: `Cmovcc`/`Cmovcc32` (conditional
/// write — the not-taken path preserves the old value), `Setcc` (writes
/// only the low byte), and everything unrecognized (fail-closed).
pub(crate) fn full_unconditional_overwrite(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        MovRI
            | MovRR
            | MovRR32
            | MovRM
            | MovRM32
            | MovRMSib
            | Lea
            | LeaSib
            | Movzx
            | MovzxW
            | MovsxB
            | MovsxW
            | Movsx
            | AddRR
            | AddRI
            | SubRR
            | SubRI
            | ImulRR
            | ImulRRI
            | AndRR
            | AndRI
            | OrRR
            | OrRI
            | XorRR
            | XorRI
            | ShlRI
            | ShrRI
            | SarRI
    )
}

/// Whether a value-producing instruction READS its operand-0 (the tied-form
/// question, answered per FORM rather than per opcode). The blanket
/// `first_operand_is_def_and_use` returns true for the whole immediate ALU
/// family, but the THREE-operand forms (`AddRI d, s, imm`) do not read `d` —
/// only the 2-operand tied forms do. Used by the shadow-redef acceptance;
/// anything unrecognized answers `true` (fail-closed: treated as tied).
pub(crate) fn redef_reads_operand0(inst: &X86ISelInst) -> bool {
    use X86Opcode::*;
    if !first_operand_is_def_and_use(inst) {
        // 2-operand tied RR ALU forms (`AddRR d, s`) read operand 0 too;
        // the 3-operand forms do not.
        return matches!(inst.opcode, AddRR | SubRR | ImulRR | AndRR | OrRR | XorRR)
            && inst.operands.len() == 2;
    }
    match inst.opcode {
        // Immediate / shift-immediate families: tied iff 2 operands
        // ([d, imm]); the 3-operand form is [d, s, imm].
        AddRI | SubRI | AndRI | OrRI | XorRI | ShlRI | ShrRI | SarRI => inst.operands.len() == 2,
        // Register-count shifts: tied iff 2 operands ([d, count]).
        ShlRR | ShrRR | SarRR => inst.operands.len() == 2,
        // Neg/Not/Inc/Dec ([d]) and the RM ALU forms ([d, mem]) always
        // read their destination.
        _ => true,
    }
}

/// Per-inst use collection mirroring `collect_used_vregs` (tied first
/// operands count as uses; addressing regs inside memory operands count) —
/// PLUS one strictly-more-conservative extension: a two-operand RR ALU form
/// (`AddRR d, s` = d := d OP s) reads its operand 0, but the RR family is not
/// in `first_operand_is_def_and_use` (the pre-RA dialect is three-operand).
/// If a tied two-operand RR form ever appears, treating operand 0 as a use is
/// required for soundness here (it only ever blocks deletions, never enables
/// them).
fn local_dce_inst_uses(inst: &X86ISelInst, used: &mut HashSet<VReg>) {
    let has_def = x86_produces_value(inst.opcode);
    let tied_rr_two_operand = matches!(
        inst.opcode,
        X86Opcode::AddRR
            | X86Opcode::SubRR
            | X86Opcode::ImulRR
            | X86Opcode::AndRR
            | X86Opcode::OrRR
            | X86Opcode::XorRR
    ) && inst.operands.len() == 2;
    let first_operand_is_use = first_operand_is_def_and_use(inst) || tied_rr_two_operand;
    for (index, operand) in inst.operands.iter().enumerate() {
        if index == 0 && has_def && !first_operand_is_use {
            continue;
        }
        collect_operand_vregs(operand, used);
    }
}

/// One sweep of the per-def local tier over a block. Deletes at most many
/// instructions per call; the caller's fixpoint loop handles cascades (a
/// chain's upper links become locally dead only after the lower links go).
fn local_per_def_dce_on_block(insts: &mut Vec<X86ISelInst>) -> bool {
    let mut changed = false;
    let mut i = 0usize;
    'outer: while i < insts.len() {
        let Some(class) = local_dce_class(&insts[i]) else {
            i += 1;
            continue;
        };
        let Some(v) = get_def_vreg(&insts[i]) else {
            i += 1;
            continue;
        };
        // Find the next def of `v` after i; scan the window as we go.
        let mut j = i + 1;
        let redef_at = loop {
            if j >= insts.len() {
                // No later redef in this block: the value may be live-out.
                i += 1;
                continue 'outer;
            }
            let w = &insts[j];
            // Window barriers: any control flow, opaque pseudo, or the
            // exchange family (hidden defs beyond operand 0 — an
            // `Xchg v, x` both reads AND writes v, which the operand-0
            // redef model below cannot represent; fail closed).
            let f = w.flags;
            if f.is_branch() || f.is_call() || f.is_terminator() || f.is_return() || f.is_pseudo() {
                i += 1;
                continue 'outer;
            }
            if matches!(
                w.opcode,
                X86Opcode::Xchg
                    | X86Opcode::Cmpxchg
                    | X86Opcode::Cmpxchg8
                    | X86Opcode::Cmpxchg16
                    | X86Opcode::AtomicRmwCasLoop
                    | X86Opcode::AtomicRmwCasLoop8
                    | X86Opcode::AtomicRmwCasLoop16
            ) {
                i += 1;
                continue 'outer;
            }
            // Narrow-view aliasing (the dirty-high-bits class): a VReg with
            // the SAME id but a DIFFERENT class is an aliased width view of
            // the same underlying register. Any such mention in the window —
            // def OR use — makes per-def reasoning on `v` unsound here; bail.
            let mut mentions = HashSet::new();
            for op in &w.operands {
                collect_operand_vregs(op, &mut mentions);
            }
            if mentions.iter().any(|m| m.id == v.id && m.class != v.class) {
                i += 1;
                continue 'outer;
            }
            // A use of v anywhere in the window keeps the def.
            let mut uses = HashSet::new();
            local_dce_inst_uses(w, &mut uses);
            let redefines = x86_produces_value(w.opcode)
                && matches!(w.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == v);
            if redefines {
                // The shadow must be a FULL, UNCONDITIONAL overwrite. A
                // closed allowlist is the only sound shape here: Cmovcc
                // writes its destination CONDITIONALLY (the not-taken path
                // keeps the candidate's value alive), Setcc writes only the
                // low byte — treating either as a shadow deletes a live def
                // (the select false-arm miscompile class). Anything not on
                // the list refuses, including future opcodes.
                if !full_unconditional_overwrite(w.opcode) {
                    i += 1;
                    continue 'outer;
                }
                // The redefining inst must not itself READ v. Tied FORMS do
                // (e.g. 2-operand `AddRI d, imm`); the 3-operand forms
                // (`AddRI d, s, imm`) do not — `redef_reads_operand0` is the
                // per-form precise answer, and any read of v through a
                // NON-first operand (e.g. `AddRI v, v, 8` three-op) is caught
                // by the explicit scan of operands[1..].
                let mut src_uses = HashSet::new();
                for operand in w.operands.iter().skip(1) {
                    collect_operand_vregs(operand, &mut src_uses);
                }
                if redef_reads_operand0(w) || src_uses.contains(&v) {
                    i += 1;
                    continue 'outer;
                }
                break j;
            }
            if uses.contains(&v) {
                i += 1;
                continue 'outer;
            }
            // Hidden multi-defs (xchg family) both read and write: the use
            // scan above already caught them via their operand mentions.
            j += 1;
        };
        let _ = redef_at;
        // Flag obligation for flag-writing ALU.
        if matches!(class, LocalDceClass::PureFlags) && !local_flags_dead(insts, i) {
            i += 1;
            continue;
        }
        insts.remove(i);
        changed = true;
        // Do not advance i: the next inst shifted into position i.
    }
    changed
}

/// Flags-deadness for the per-def local tier — the PARTIAL-TRANSPARENT
/// variant (mirrors the peephole's `sib_fold_flags_dead`, not the strict
/// `flags_written_here_are_dead` above). What must be proven is that no
/// instruction ever OBSERVES the deleted writer's flag output. Observation
/// happens only through a flag reader (caught by `x86_reads_flags`) or past
/// a control-flow / ABI boundary (call/branch/terminator/return — caught
/// below). A PARTIAL overwriter (imul/shl/...) neither reads flags nor
/// forwards our bits to a reader as-is: any reader after it either sits
/// before the next FULL overwrite (still caught by this scan, refusing) or
/// after it (observes only that overwriter). Loads and plain stores neither
/// read nor write RFLAGS and are transparent. Falling off the block end
/// without a FULL overwrite refuses (flags may be live-out).
fn local_flags_dead(insts: &[X86ISelInst], index: usize) -> bool {
    for inst in &insts[index + 1..] {
        if x86_reads_flags(inst.opcode) {
            return false;
        }
        let flags = inst.flags;
        if flags.is_call() || flags.is_branch() || flags.is_terminator() || flags.is_return() {
            return false;
        }
        match condition_flag_overwrite(inst) {
            FlagOverwrite::None | FlagOverwrite::Partial => {}
            FlagOverwrite::Full => return true,
        }
    }
    false
}

fn is_dead_instruction(inst: &X86ISelInst, used_vregs: &HashSet<VReg>) -> bool {
    if has_observable_effects(inst) {
        return false;
    }

    match get_def_vreg(inst) {
        Some(vreg) => !used_vregs.contains(&vreg),
        None => inst.opcode == X86Opcode::Nop,
    }
}

fn is_dead_flag_only_instruction(insts: &[X86ISelInst], index: usize) -> bool {
    let inst = &insts[index];

    is_removable_flag_only_candidate(inst) && flags_written_here_are_dead(insts, index)
}

fn is_removable_flag_only_candidate(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    is_supported_flag_only_opcode(inst.opcode)
        && has_supported_flag_only_operands(inst)
        && x86_inst_effect(inst).is_pure()
        && !inst_touches_fixed_register(inst)
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !flags.reads_memory()
        && !flags.writes_memory()
        && !flags.is_pseudo()
}

fn is_supported_flag_only_opcode(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::CmpRR
            | X86Opcode::CmpRI
            | X86Opcode::CmpRI8
            | X86Opcode::TestRR
            | X86Opcode::TestRI
            // FP compares (UCOMISD/UCOMISS) only set RFLAGS; they produce no
            // register or memory result. The register-register form reads two
            // XMM registers and is memory-pure, so it is removable on the same
            // terms as the integer CMP/TEST register forms. The register-memory
            // form is excluded by `has_supported_flag_only_operands` (and by the
            // `reads_memory` guard) — see the soundness note there.
            | X86Opcode::Ucomisd
            | X86Opcode::Ucomiss
    )
}

fn has_supported_flag_only_operands(inst: &X86ISelInst) -> bool {
    match inst.opcode {
        X86Opcode::CmpRR | X86Opcode::TestRR => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(_), X86ISelOperand::VReg(_)]
        ),
        X86Opcode::CmpRI | X86Opcode::CmpRI8 | X86Opcode::TestRI => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(_), X86ISelOperand::Imm(_)]
        ),
        // Only the register-register form of the FP compares is removable. Both
        // operands must be plain registers: a `MemAddr`/`SibMemAddr` operand
        // means the instruction loads from memory (see the
        // CmpRM/TestRM/Ucomi-RM soundness note below), which we never remove.
        X86Opcode::Ucomisd | X86Opcode::Ucomiss => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(_), X86ISelOperand::VReg(_)]
        ),
        _ => false,
    }
}

// SOUNDNESS NOTE — memory-form flag-only ops (CmpRM, TestRM, and the
// register-memory forms of Ucomisd/Ucomiss) are intentionally NOT removable:
//
//   * They READ memory. The memory effects model classifies CmpRM/TestRM as
//     `Load`, and a memory-operand Ucomisd/Ucomiss carries `READS_MEMORY`.
//     `is_removable_flag_only_candidate` already rejects anything whose
//     `x86_inst_effect` is non-pure or whose flags report `reads_memory`.
//
//   * Removing a memory read is observationally visible whenever the access
//     could FAULT (e.g. an unmapped/guard page) or where the address could
//     ALIAS a volatile/MMIO location. We cannot prove non-faulting,
//     non-aliasing memory operands at this layer, so eliminating the load —
//     even when its RFLAGS result is dead — could erase a trap that the source
//     program is entitled to observe. Per the conservative DCE contract we
//     keep these instructions.
//
// Only the pure register-register FP-compare forms are added above, where the
// instruction touches no memory and its sole effect is RFLAGS.

fn flags_written_here_are_dead(insts: &[X86ISelInst], index: usize) -> bool {
    for inst in &insts[index + 1..] {
        if x86_reads_flags(inst.opcode) {
            return false;
        }

        match condition_flag_overwrite(inst) {
            FlagOverwrite::None => {}
            FlagOverwrite::Partial => return false,
            FlagOverwrite::Full => return true,
        }

        if instruction_may_export_flags(inst) {
            return false;
        }
    }

    false
}

fn condition_flag_overwrite(inst: &X86ISelInst) -> FlagOverwrite {
    use FlagOverwrite::*;
    use X86Opcode::*;

    match inst.opcode {
        Not => None,
        ShlRI | ShrRI | SarRI if shift_immediate_is_zero(inst) => None,

        AddRR | AddRI | AddRM | SubRR | SubRI | SubRM | Neg | AndRR | AndRI | OrRR | OrRI
        | XorRR | XorRI | CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM | Ucomisd
        | Ucomiss | Popcnt => Full,

        Inc | Dec | ImulRR | ImulRRI | ImulRM | ImulRMSib | Idiv | Div | Mul | ShlRR | ShlRI
        | ShrRR | ShrRI | SarRR | SarRI | Bsf | Bsr | Tzcnt | Lzcnt | BtRI | Cmpxchg => Partial,

        _ if x86_writes_flags(inst.opcode) => Partial,
        _ => None,
    }
}

fn shift_immediate_is_zero(inst: &X86ISelInst) -> bool {
    matches!(
        inst.operands.as_slice(),
        [X86ISelOperand::VReg(_), X86ISelOperand::Imm(0)]
            | [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(_),
                X86ISelOperand::Imm(0),
            ]
    )
}

fn instruction_may_export_flags(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.has_side_effects()
}

fn collect_used_vregs(func: &X86ISelFunction) -> HashSet<VReg> {
    let mut used = HashSet::new();

    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };

        for inst in &block.insts {
            let has_def = x86_produces_value(inst.opcode);
            let first_operand_is_use = first_operand_is_def_and_use(inst);

            for (index, operand) in inst.operands.iter().enumerate() {
                if index == 0 && has_def && !first_operand_is_use {
                    continue;
                }
                collect_operand_vregs(operand, &mut used);
            }
        }
    }

    used
}

fn get_def_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }

    match inst.operands.first() {
        Some(X86ISelOperand::VReg(vreg)) => Some(*vreg),
        _ => None,
    }
}

fn collect_operand_vregs(operand: &X86ISelOperand, used: &mut HashSet<VReg>) {
    match operand {
        X86ISelOperand::VReg(vreg) => {
            used.insert(*vreg);
        }
        X86ISelOperand::MemAddr { base, .. } => collect_operand_vregs(base, used),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_vregs(base, used);
            collect_operand_vregs(index, used);
        }
        _ => {}
    }
}

fn has_observable_effects(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    !x86_is_removable(inst.opcode)
        || inst_touches_fixed_register(inst)
        || flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.has_side_effects()
        || flags.reads_memory()
        || flags.writes_memory()
}

fn inst_touches_fixed_register(inst: &X86ISelInst) -> bool {
    inst.operands.iter().any(operand_touches_fixed_register)
}

fn operand_touches_fixed_register(operand: &X86ISelOperand) -> bool {
    match operand {
        X86ISelOperand::PReg(_) => true,
        X86ISelOperand::MemAddr { base, .. } => operand_touches_fixed_register(base),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_touches_fixed_register(base) || operand_touches_fixed_register(index)
        }
        _ => false,
    }
}

fn first_operand_is_def_and_use(inst: &X86ISelInst) -> bool {
    use X86Opcode::*;

    matches!(
        inst.opcode,
        Neg | Not
            | Inc
            | Dec
            | AddRI
            | SubRI
            | AndRI
            | OrRI
            | XorRI
            | AddRM
            | SubRM
            | ImulRM
            | ImulRMSib
            | ShlRI
            | ShrRI
            | SarRI
            | ShlRR
            | ShrRR
            | SarRR
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::x86_64_regs::{RAX, RDI};
    use trust_cg_ir::{InstFlags, X86CondCode};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;

    use crate::X86PassManager;

    fn vreg(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg_class(id: u32, class: RegClass) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, class))
    }

    fn make_func(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_dce_test".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 8;
        for inst in insts {
            func.push_inst(entry, inst);
        }
        func
    }

    fn entry_opcodes(func: &X86ISelFunction) -> Vec<X86Opcode> {
        func.blocks
            .get(&Block(0))
            .unwrap()
            .insts
            .iter()
            .map(|inst| inst.opcode)
            .collect()
    }

    fn entry_insts(func: &X86ISelFunction) -> &[X86ISelInst] {
        &func.blocks.get(&Block(0)).unwrap().insts
    }

    #[test]
    fn x86_dce_removes_dead_cmp_before_full_flag_overwrite() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(42)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::NE)],
            ),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(3)),
                        disp: 0,
                    },
                    vreg(2),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::TestRI,
                X86Opcode::Setcc,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_removes_dead_test_rr_before_full_flag_overwrite() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::CmpRI8, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(3), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(4)),
                        disp: 0,
                    },
                    vreg(3),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI8,
                X86Opcode::Setcc,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_keeps_cmp_when_flags_are_read_before_overwrite() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(1), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg(2), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(3)),
                        disp: 0,
                    },
                    vreg(1),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::Setcc,
                X86Opcode::TestRI,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_keeps_cmp_across_partial_flag_overwrite() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Inc, vec![vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(3)),
                        disp: 0,
                    },
                    vreg(2),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::Inc,
                X86Opcode::Setcc,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_keeps_flag_writer_without_later_full_overwrite() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::CmpRI, X86Opcode::Ret]);
    }

    #[test]
    fn x86_dce_preserves_unsupported_flag_writer_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::TestRM,
                vec![
                    vreg(0),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::with_flags(
                X86Opcode::TestRI,
                vec![vreg(2), X86ISelOperand::Imm(1)],
                InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::READS_MEMORY),
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(4), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(5)),
                        disp: 0,
                    },
                    vreg(4),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::TestRM,
                X86Opcode::TestRI,
                X86Opcode::CmpRI,
                X86Opcode::Setcc,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            entry_insts(&func)[2].flags,
            InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::READS_MEMORY)
        );
    }

    #[test]
    fn x86_dce_removes_dead_pure_virtual_register_def() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(42)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86DeadCodeElimination));

        assert!(pm.run_once(&mut func));

        let block = func.blocks.get(&Block(0)).unwrap();
        assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
        assert_eq!(block.insts[0].flags, X86Opcode::Ret.default_flags());
    }

    #[test]
    fn x86_dce_removes_dead_same_id_different_class_def() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(42)]),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 0,
                    },
                    vreg_class(0, RegClass::Fpr64),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(dce.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::MovMR, X86Opcode::Ret]);
        assert_eq!(
            entry_insts(&func)[0].operands[1],
            vreg_class(0, RegClass::Fpr64)
        );
    }

    #[test]
    fn x86_dce_removes_dead_def_when_same_id_other_class_is_memory_base() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(42)]),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg_class(0, RegClass::Fpr64)),
                        disp: 0,
                    },
                    vreg(2),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(dce.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::MovMR, X86Opcode::Ret]);
        assert_eq!(
            entry_insts(&func)[0].operands[0],
            X86ISelOperand::MemAddr {
                base: Box::new(vreg_class(0, RegClass::Fpr64)),
                disp: 0,
            }
        );
    }

    #[test]
    fn x86_dce_keeps_defs_used_by_observable_later_instructions() {
        let store_addr = X86ISelOperand::MemAddr {
            base: Box::new(vreg(2)),
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![store_addr, vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRR,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_removes_transitive_dead_vreg_chain_in_one_run() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(dce.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
    }

    #[test]
    fn x86_dce_keeps_defs_used_by_sib_address_operands() {
        let sib_addr = X86ISelOperand::SibMemAddr {
            base: Box::new(vreg(0)),
            index: Box::new(vreg(1)),
            scale: 4,
            disp: 16,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(2), sib_addr]),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(3)),
                        disp: 0,
                    },
                    vreg(2),
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(4), X86ISelOperand::Imm(99)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::LeaSib,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            entry_insts(&func)[2].operands,
            vec![
                vreg(2),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(0)),
                    index: Box::new(vreg(1)),
                    scale: 4,
                    disp: 16,
                },
            ]
        );
    }

    #[test]
    fn x86_dce_preserves_memory_calls_and_terminators() {
        let store_addr = X86ISelOperand::MemAddr {
            base: Box::new(vreg(2)),
            disp: 16,
        };
        let load_addr = X86ISelOperand::MemAddr {
            base: Box::new(vreg(3)),
            disp: 24,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovMR, vec![store_addr, vreg(4)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(5), load_addr]),
            X86ISelInst::new(
                X86Opcode::Call,
                vec![X86ISelOperand::Symbol("callee".to_string())],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovMR,
                X86Opcode::MovRM,
                X86Opcode::Call,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_preserves_sib_fixed_physical_register_glue() {
        let sib_addr = X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::PReg(RAX)),
            index: Box::new(vreg(1)),
            scale: 2,
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(0), sib_addr]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::LeaSib, X86Opcode::Ret]
        );
        assert_eq!(
            entry_insts(&func)[0].operands,
            vec![
                vreg(0),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(X86ISelOperand::PReg(RAX)),
                    index: Box::new(vreg(1)),
                    scale: 2,
                    disp: 0,
                },
            ]
        );
    }

    #[test]
    fn x86_dce_preserves_fixed_physical_register_glue() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(0), X86ISelOperand::PReg(RDI)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RAX), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRR, X86Opcode::MovRR, X86Opcode::Ret]
        );
    }

    fn fpr(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr64))
    }

    #[test]
    fn x86_dce_removes_dead_ucomisd_rr_before_full_flag_overwrite() {
        // UCOMISD (register-register) only sets RFLAGS. With the flags fully
        // overwritten by a later CMP before any reader, the dead FP compare is
        // removable on the same terms as a dead integer CMP/TEST.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::Ucomisd, vec![fpr(0), fpr(1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(3), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(4)),
                        disp: 0,
                    },
                    vreg(3),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::Setcc,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_removes_dead_ucomiss_rr_before_another_fp_compare() {
        // A later UCOMISS fully overwrites RFLAGS, so the first (dead) UCOMISS
        // is removable.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::Ucomiss, vec![fpr(0), fpr(1)]),
            X86ISelInst::new(X86Opcode::Ucomiss, vec![fpr(2), fpr(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(4), X86ISelOperand::CondCode(X86CondCode::A)],
            ),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(5)),
                        disp: 0,
                    },
                    vreg(4),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Ucomiss,
                X86Opcode::Setcc,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_keeps_ucomisd_rr_when_flags_are_read() {
        // The UCOMISD result is consumed by the following Setcc, so it must be
        // kept.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::Ucomisd, vec![fpr(0), fpr(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(3)),
                        disp: 0,
                    },
                    vreg(2),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Ucomisd,
                X86Opcode::Setcc,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_preserves_memory_form_flag_only_ops_even_when_flags_dead() {
        // CmpRM / TestRM read memory; the register-memory UCOMISD likewise. Even
        // though the RFLAGS they write are fully overwritten by the trailing
        // CmpRI before any reader, removing them would erase a memory read that
        // could fault or alias volatile/MMIO storage. They must be preserved.
        let mem = |base: u32, disp: i32| X86ISelOperand::MemAddr {
            base: Box::new(vreg(base)),
            disp,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRM, vec![vreg(0), mem(1, 0)]),
            X86ISelInst::new(X86Opcode::TestRM, vec![vreg(2), mem(3, 8)]),
            X86ISelInst::new(X86Opcode::Ucomisd, vec![fpr(4), mem(5, 0)]),
            // Full flag overwrite with no intervening flag reader: the flags of
            // all three above are dead, yet the memory reads must stay.
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(7), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem(0, 16), vreg(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRM,
                X86Opcode::TestRM,
                X86Opcode::Ucomisd,
                X86Opcode::CmpRI,
                X86Opcode::Setcc,
                X86Opcode::MovMR,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_dce_preserves_ucomisd_rr_marked_reads_memory() {
        // Defense in depth: even a register-shaped UCOMISD that is flagged as
        // reading memory (e.g. an aliased folded load) must not be removed.
        let mut func = make_func(vec![
            X86ISelInst::with_flags(
                X86Opcode::Ucomisd,
                vec![fpr(0), fpr(1)],
                X86Opcode::Ucomisd
                    .default_flags()
                    .union(InstFlags::READS_MEMORY),
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(3), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(4)),
                        disp: 0,
                    },
                    vreg(3),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut dce = X86DeadCodeElimination;

        assert!(!dce.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func)[0], X86Opcode::Ucomisd);
    }

    // -----------------------------------------------------------------------
    // Per-def local deadness tier — the block helper is
    // called directly, bypassing the env gate.
    // -----------------------------------------------------------------------

    fn local_tier(insts: Vec<X86ISelInst>) -> (bool, Vec<X86Opcode>) {
        let mut func = make_func(insts);
        let block = func.blocks.get_mut(&Block(0)).unwrap();
        let changed = {
            let mut c = false;
            // Mirror the pass's fixpoint: cascade until stable.
            loop {
                let round = local_per_def_dce_on_block(&mut block.insts);
                c |= round;
                if !round {
                    break;
                }
            }
            c
        };
        let ops = block.insts.iter().map(|i| i.opcode).collect();
        (changed, ops)
    }

    #[test]
    fn local_dce_removes_shadowed_movri() {
        // MovRI v1,5 shadowed by MovRI v1,6 with no use between: the first
        // def dies even though the ID is used later (multi-def clone shape).
        let (changed, ops) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(changed);
        assert_eq!(
            ops,
            vec![X86Opcode::MovRI, X86Opcode::MovRR, X86Opcode::Ret]
        );
    }

    #[test]
    fn local_dce_keeps_def_with_use_in_window() {
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_keeps_def_across_branch() {
        // A mid-block Jcc is a legal side exit on this surface: the value
        // may be live on the taken edge. Must keep.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_keeps_def_across_trap_carrier_pseudo() {
        // Trap carriers are opaque pseudos: fail closed.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(
                X86Opcode::TrapBoundsCheckExact,
                vec![vreg(4), vreg(5), X86ISelOperand::Imm(24)],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_removes_dead_alu_when_flags_dead() {
        // AddRR v1 shadowed by MovRI v1; its flags are overwritten by the
        // AddRR v4 def before any reader: both window and flags obligations
        // hold, the dead AddRR goes.
        let (changed, ops) = local_tier(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(1), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(6), vreg(4)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(changed);
        assert_eq!(ops[0], X86Opcode::MovRI);
    }

    #[test]
    fn local_dce_keeps_dead_alu_when_flags_read() {
        // Window passes (shadowing MovRI right after) but a Jcc reads the
        // AddRR's flags before any full overwrite: must keep.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(1), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::AE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_keeps_dead_slot_load() {
        // Slot loads are OUT of the tier's scope (never-faults obligation
        // deliberately not claimed): a dead shadowed slot load stays.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(
                X86Opcode::MovRM,
                vec![
                    vreg(1),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(3)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_cmovcc_is_not_a_shadow() {
        // Cmovcc writes CONDITIONALLY: the not-taken path reads the prior
        // def, so it must never count as a shadowing overwrite (the select
        // false-arm miscompile class from adversarial review).
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(2), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Cmovcc,
                vec![vreg(1), vreg(2), X86ISelOperand::CondCode(X86CondCode::AE)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_keeps_dead_pointer_load() {
        // A load through a computed pointer may fault: never removed.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(
                X86Opcode::MovRM,
                vec![
                    vreg(1),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(9)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_keeps_def_with_narrow_alias_in_window() {
        // A Gpr32 mention of the same id inside the window is an aliased
        // width view (dirty-high-bits class): fail closed.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg_class(1, RegClass::Gpr32), X86ISelOperand::Imm(9)],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_keeps_tied_redef() {
        // The "redef" is a tied AddRI (reads its operand 0): NOT a clean
        // shadow — the candidate's value is consumed by it.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_cascades_chain_deletion() {
        // Post-fold chain shape: once the mem op no longer reads the chain,
        // the whole chain dies bottom-up across fixpoint rounds. A later
        // full flag overwrite (the next step's ALU, as in the real unrolled
        // body) discharges the AddRI's flag obligation.
        //   MovRR v6, v5          (copy hop, dead once AddRI goes)
        //   AddRI v6, 16 (tied)   (dead once nothing reads v6)
        //   MovRI v6, 0           (shadowing def)
        //   AddRR v8, v2, v3      (full flag overwrite, live)
        //   MovRR v7, v6 ; MovRR v9, v8
        let (changed, ops) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(6), vreg(5)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(6), X86ISelOperand::Imm(16)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(8), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(7), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(8)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(changed);
        assert_eq!(
            ops,
            vec![
                X86Opcode::MovRI,
                X86Opcode::AddRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::Ret
            ]
        );
    }

    #[test]
    fn local_dce_three_op_addri_is_clean_shadow() {
        // The unrolled-body shape: a 3-operand `AddRI d, s, imm` redefines d
        // WITHOUT reading it — it must count as a clean shadow (this was the
        // exact miss that kept every dead chain alive on real b05).
        let (changed, ops) = local_tier(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(5), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(5), X86ISelOperand::Imm(16)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(7), vreg(6)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(changed);
        assert_eq!(ops[0], X86Opcode::AddRI);
        assert_eq!(
            ops,
            vec![
                X86Opcode::AddRI,
                X86Opcode::AddRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::Ret
            ]
        );
    }

    #[test]
    fn local_dce_three_op_addri_reading_v_is_not_a_shadow() {
        // `AddRI v, v, imm` (3-op with s == d) READS v: not a clean shadow.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }

    #[test]
    fn local_dce_real_b05_window_replication() {
        // Byte-exact replication of the post-fold b05 k-step window (dump2
        // indices 19..30): the dead a-side AddRI at [0] must delete against
        // its shadow at [11].
        fn sib(base: u32, index: u32, disp: i32) -> X86ISelOperand {
            X86ISelOperand::SibMemAddr {
                base: Box::new(vreg(base)),
                index: Box::new(vreg(index)),
                scale: 1,
                disp,
            }
        }
        let (changed, ops) = local_tier(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(162), vreg(158), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(164), sib(151, 154, 8)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(176), vreg(172), X86ISelOperand::Imm(192)],
            ),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(185), sib(172, 182, 192)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(186), vreg(164), vreg(185)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(187), vreg(136), vreg(186)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(188), vreg(187)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(136), vreg(188)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(155), vreg(151), vreg(154)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(156), vreg(155)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(158), vreg(156)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(162), vreg(158), X86ISelOperand::Imm(16)],
            ),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(164), sib(151, 154, 16)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(changed, "the dead AddRI must delete");
        assert!(
            !ops.iter().take(3).any(|o| *o == X86Opcode::AddRI) || ops[0] != X86Opcode::AddRI,
            "first AddRI should be gone: {ops:?}"
        );
    }

    #[test]
    fn local_dce_keeps_dead_alu_before_return_boundary() {
        // No full flag overwrite before Ret: the ABI boundary may observe
        // RFLAGS — fail closed even though the value window is clean.
        let (changed, _) = local_tier(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(1), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!changed);
    }
}
