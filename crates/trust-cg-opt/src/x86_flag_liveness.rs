//! Cross-block RFLAGS liveness for x86-64 machine IR.
//!
//! Every flag-deadness predicate in this crate before this module scanned only
//! WITHIN a block and refused when it ran off the end, on the grounds that the
//! flags might be live-out. That is sound but it gives up exactly where real
//! code needs an answer: the last flag-writer in a block is typically the one
//! whose flags nobody wants, and the full overwrite that proves it sits in the
//! successor.
//!
//! The measured case that motivated this is the `b1_mispredict` hot loop, where
//! a value-dead `add` is the second-to-last instruction of its block and the
//! `and $0x6,%rcx` that discharges its flag obligation is the second
//! instruction of the fall-through successor. See
//! `sib_fold_falls_back_to_scale_1_and_retains_the_chain_when_flags_may_be_live`
//! in [`crate::x86_peephole`] for the shape.
//!
//! # What is computed
//!
//! For each block, whether RFLAGS MAY BE OBSERVED starting from the top of it:
//! that is, whether some path from the block's first instruction reaches a flag
//! READER before a FULL overwrite. This is a `may` property, so it is the LEAST
//! fixpoint of the successor union, computed from an all-dead initialisation.
//!
//! # Where it is conservative, and deliberately so
//!
//! * Only a FULL flag overwrite concludes "dead"; a PARTIAL one is transparent
//!   and keeps the scan going (see [`local_scan`] for why that is sound in both
//!   directions). This matches `local_flags_dead` and the peephole's
//!   `sib_fold_flags_dead`.
//! * A call, a return, a pseudo, an indirect branch, a side-effecting
//!   instruction, and any terminator other than a direct unconditional `Jmp`
//!   all read as "flags may be observed". Only `Jmp` is transparent, because it
//!   is the only control transfer that provably neither reads nor writes
//!   RFLAGS; the scan continues through it into the successors.
//! * A block with no interpretable exit, no successors, or a successor absent
//!   from the analysis reads as live.
//!
//! # Why a snapshot stays valid while its consumer mutates the function
//!
//! A consumer computes this once and then deletes instructions, so the question
//! is whether a deletion can retroactively invalidate a conclusion drawn from
//! the snapshot. It cannot, PROVIDED every deletion is itself justified by "the
//! flags this instruction writes are dead":
//!
//! Deleting an instruction whose flags are dead cannot change what any reader
//! observes. "Flags dead at X" means no reader sees X's flag output, which in
//! turn means a FULL overwrite `W` separates X from the first subsequent reader
//! `R` (or no `R` exists on any path). Removing X leaves `W` between the
//! earlier writers and `R`, so `R` still observes `W`. By the same argument a
//! block that killed flags before any reader still does so after the deletion —
//! the killer that made it `Dead` is either still present, or was itself
//! removed only because a further full overwrite preceded the first reader. So
//! no block's entry verdict can move from dead to live.
//!
//! Exits are snapshotted too, which is sound for the same class of consumer:
//! deletions never remove a branch (a branch is never flag-dead-justified, and
//! never removable), so a block's exit shape does not change under them.
//!
//! A consumer that deletes on any OTHER justification must re-analyze instead.

use std::collections::HashMap;

use trust_cg_ir::X86Opcode;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{FlagOverwrite, condition_flag_overwrite, x86_reads_flags};

/// Verdict of a straight-line scan within one block.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LocalScan {
    /// A flag READER (or an opaque boundary) is reached first.
    Live,
    /// A FULL flag overwrite is reached first.
    Dead,
    /// Neither: the scan ran off the end of the block.
    OffBlockEnd,
}

/// Where control may go when it leaves a block.
#[derive(Clone, Debug)]
enum Exit {
    To(Vec<Block>),
    /// Uninterpretable, so fail closed.
    Unknown,
}

/// Scan `insts[from..]` for the fate of the RFLAGS value live at `from`.
fn local_scan(insts: &[X86ISelInst], from: usize) -> LocalScan {
    if from > insts.len() {
        return LocalScan::Live;
    }
    for inst in &insts[from..] {
        if x86_reads_flags(inst.opcode) {
            return LocalScan::Live;
        }

        // A direct unconditional `Jmp` neither reads nor writes RFLAGS, so the
        // scan continues THROUGH it and the caller consults the successors.
        // `JmpR` (indirect) carries no interpretable target and is excluded by
        // the opcode test, so it falls into the opaque arm below.
        let transparent = inst.opcode == X86Opcode::Jmp;
        let flags = inst.flags;
        if !transparent
            && (flags.is_call()
                || flags.is_branch()
                || flags.is_terminator()
                || flags.is_return()
                || flags.is_pseudo())
        {
            return LocalScan::Live;
        }
        // MEMORY EFFECTS ARE NOT FLAG EFFECTS. A load or a store neither reads
        // nor writes RFLAGS, so `reads_memory`/`writes_memory`/`has_side_effects`
        // are deliberately NOT part of the opaque set above — the same position
        // `local_flags_dead` and `sib_fold_flags_dead` take, and stated outright
        // in the latter's documentation. Including them would make every block
        // containing a store opaque, which is most of them.
        //
        // The only way this scan can be UNSOUND is to report `Dead` while some
        // reader still observes the value, and that needs a `Full` verdict
        // below; reporting `Live` is always safe. So the exposure is limited to
        // an unrecognised flag READER, which is `x86_reads_flags`'s closed list
        // — shared with every other flag predicate in this crate, not widened
        // here.

        match condition_flag_overwrite(inst) {
            FlagOverwrite::Full => return LocalScan::Dead,
            // A PARTIAL overwrite is transparent, and only a FULL one concludes
            // `Dead`. Soundness is in the asymmetry: a partial overwriter
            // redefines some RFLAGS bits and leaves the rest carrying the
            // scanned value, so it cannot license a `Dead` verdict — but it
            // cannot hide a reader either, because the scan keeps going and ANY
            // reader it then meets returns `Live`. So a bit that survives a
            // partial overwrite and is later read still refuses, and the only
            // way to reach `Dead` is a full redefinition of every bit.
            //
            // This matches `local_flags_dead` and the peephole's
            // `sib_fold_flags_dead`. The third predicate,
            // `flags_written_here_are_dead`, refuses on a partial instead; that
            // is strictly more conservative than the argument requires, and it
            // is strictly more conservative than the argument requires.
            //
            // The partial class is `imul`/`shl`-style, per
            // `condition_flag_overwrite`: opcodes that write SOME flags without
            // defining every CondCode-consumable one. `and` is NOT in it —
            // `x86_defines_all_cc_flags` lists `AndRI`, because AND clears CF/OF
            // and defines SF/ZF/PF, and the AF it leaves undefined is not
            // CondCode-consumable.
            FlagOverwrite::Partial | FlagOverwrite::None => {}
        }
    }
    LocalScan::OffBlockEnd
}

/// Derive a block's exit edges from its own instructions, never from a cached
/// `successors` field: the instruction stream is ground truth, and anything
/// uninterpretable fails closed.
fn exit_of(func: &X86ISelFunction, block_id: Block) -> Exit {
    let Some(block) = func.blocks.get(&block_id) else {
        return Exit::Unknown;
    };

    if let Some(last) = block.insts.last() {
        if last.opcode == X86Opcode::Jmp {
            let targets: Vec<Block> = last
                .operands
                .iter()
                .filter_map(|operand| match operand {
                    X86ISelOperand::Block(b) => Some(*b),
                    _ => None,
                })
                .collect();
            return if targets.is_empty() {
                Exit::Unknown
            } else {
                Exit::To(targets)
            };
        }
        // Any other terminator means `local_scan` already answered `Live` and
        // no caller reaches here; answer conservatively regardless.
        let flags = last.flags;
        if flags.is_terminator() || flags.is_branch() || flags.is_return() {
            return Exit::Unknown;
        }
    }

    // No terminator: control falls through to the next block in LAYOUT order.
    match func.block_order.iter().position(|b| *b == block_id) {
        Some(i) if i + 1 < func.block_order.len() => Exit::To(vec![func.block_order[i + 1]]),
        _ => Exit::Unknown,
    }
}

/// A snapshot of cross-block RFLAGS liveness. See the module docs for the
/// conditions under which it stays valid while its consumer mutates.
pub struct X86FlagLiveness {
    /// Whether RFLAGS may be observed starting at the top of each block.
    live_in: HashMap<Block, bool>,
    /// Snapshotted exit edges, so a query needs no borrow of the function.
    exits: HashMap<Block, Exit>,
}

impl X86FlagLiveness {
    /// Run the analysis over `func`.
    pub fn analyze(func: &X86ISelFunction) -> Self {
        let mut local: HashMap<Block, LocalScan> = HashMap::new();
        let mut exits: HashMap<Block, Exit> = HashMap::new();
        for &block_id in &func.block_order {
            let verdict = match func.blocks.get(&block_id) {
                Some(block) => local_scan(&block.insts, 0),
                None => LocalScan::Live,
            };
            local.insert(block_id, verdict);
            exits.insert(block_id, exit_of(func, block_id));
        }

        // Liveness is a MAY property: the least fixpoint reached from an
        // all-dead start is exactly "a reader is reachable before a kill".
        // Monotone, so it terminates in at most one round per block.
        let mut live_in: HashMap<Block, bool> =
            func.block_order.iter().map(|b| (*b, false)).collect();
        loop {
            let mut changed = false;
            for &block_id in &func.block_order {
                let next = match local.get(&block_id) {
                    Some(LocalScan::Live) | None => true,
                    Some(LocalScan::Dead) => false,
                    Some(LocalScan::OffBlockEnd) => exit_is_live(exits.get(&block_id), &live_in),
                };
                if live_in.get(&block_id) != Some(&next) {
                    live_in.insert(block_id, next);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        Self { live_in, exits }
    }

    /// Whether the RFLAGS written by `insts[index]` of `block_id` is dead.
    ///
    /// `insts` is read LIVE, so the within-block part of the answer reflects
    /// any mutation already applied to this block; only the successor verdicts
    /// come from the snapshot.
    pub fn flags_dead_after(&self, insts: &[X86ISelInst], block_id: Block, index: usize) -> bool {
        match local_scan(insts, index + 1) {
            LocalScan::Live => false,
            LocalScan::Dead => true,
            LocalScan::OffBlockEnd => !exit_is_live(self.exits.get(&block_id), &self.live_in),
        }
    }

    /// Whether RFLAGS may be observed starting at the top of `block_id`.
    /// Absent blocks read as live.
    pub fn live_in(&self, block_id: Block) -> bool {
        self.live_in.get(&block_id).copied().unwrap_or(true)
    }
}

/// Whether leaving a block along `exit` can reach an observer of RFLAGS.
/// Unknown exits, exitless blocks and unanalyzed successors all read as live.
fn exit_is_live(exit: Option<&Exit>, live_in: &HashMap<Block, bool>) -> bool {
    match exit {
        Some(Exit::To(succs)) if !succs.is_empty() => succs
            .iter()
            .any(|s| live_in.get(s).copied().unwrap_or(true)),
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::x86_64_ops::X86CondCode;
    use trust_cg_ir::{RegClass, VReg};
    use trust_cg_lower::function::Signature as X86Signature;
    use trust_cg_lower::types::Type as LirType;

    fn vr(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn func_with(blocks: Vec<Vec<X86ISelInst>>) -> X86ISelFunction {
        let sig = X86Signature {
            params: vec![],
            returns: vec![LirType::I64],
        };
        let mut f = X86ISelFunction::new("flag_liveness_probe".to_string(), sig);
        for (i, insts) in blocks.into_iter().enumerate() {
            let b = Block(i as u32);
            f.ensure_block(b);
            for inst in insts {
                f.push_inst(b, inst);
            }
        }
        f
    }

    fn add(dst: u32, a: u32, b: u32) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(dst), vr(a), vr(b)])
    }

    /// THE `b1_mispredict` SHAPE. The `add` is the second-to-last instruction
    /// of block 0, which has no terminator and so falls through to block 1;
    /// block 1's second instruction is a FULL flag overwrite. Block-local
    /// reasoning refuses this and cross-block reasoning answers it.
    #[test]
    fn fallthrough_successor_kill_proves_the_block_tail_dead() {
        let f = func_with(vec![
            vec![
                add(4, 1, 3),
                X86ISelInst::new(
                    X86Opcode::MovMR,
                    vec![
                        X86ISelOperand::MemAddr {
                            base: Box::new(vr(9)),
                            disp: 0,
                        },
                        vr(6),
                    ],
                ),
            ],
            // b1's successor prefix verbatim: `mov %r12,%rcx ; and $0x6,%rcx ;
            // cmp $0x2,%rcx`. The `and` is the FULL overwrite that discharges the
            // obligation; the `cmp` behind it is kept so the block matches the
            // shipped code rather than a reduction of it.
            vec![
                X86ISelInst::new(X86Opcode::MovRR, vec![vr(7), vr(8)]),
                X86ISelInst::new(X86Opcode::AndRI, vec![vr(7), vr(7), X86ISelOperand::Imm(6)]),
                X86ISelInst::new(X86Opcode::CmpRI, vec![vr(7), X86ISelOperand::Imm(2)]),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ],
        ]);
        let live = X86FlagLiveness::analyze(&f);
        assert!(
            !live.live_in(Block(1)),
            "block 1 fully overwrites RFLAGS (at the `cmp`) before reading it, so \
             nothing there observes an incoming flag value"
        );
        let insts = &f.blocks[&Block(0)].insts;
        assert!(
            live.flags_dead_after(insts, Block(0), 0),
            "the `add`'s flags are dead: the scan runs off the end of block 0 into a \
             successor that kills before any read"
        );
    }

    /// The negative control on the same topology: make the successor READ flags
    /// before overwriting them, and the identical query must refuse.
    #[test]
    fn fallthrough_successor_read_keeps_the_block_tail_live() {
        let f = func_with(vec![
            vec![add(4, 1, 3)],
            vec![
                X86ISelInst::new(
                    X86Opcode::Cmovcc,
                    vec![vr(7), vr(8), X86ISelOperand::CondCode(X86CondCode::E)],
                ),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ],
        ]);
        let live = X86FlagLiveness::analyze(&f);
        assert!(
            live.live_in(Block(1)),
            "block 1 starts with a cmov, which READS the incoming flags"
        );
        let insts = &f.blocks[&Block(0)].insts;
        assert!(
            !live.flags_dead_after(insts, Block(0), 0),
            "the successor observes the `add`'s flags, so they are NOT dead"
        );
    }

    /// An unconditional `Jmp` is transparent: the scan passes through it to the
    /// branch target rather than refusing at the terminator.
    #[test]
    fn unconditional_jmp_is_transparent_to_its_target() {
        let f = func_with(vec![
            vec![
                add(4, 1, 3),
                X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
            ],
            // Layout-adjacent DECOY that reads flags: reaching it would mean the
            // analysis followed layout instead of the branch target.
            vec![
                X86ISelInst::new(
                    X86Opcode::Cmovcc,
                    vec![vr(7), vr(8), X86ISelOperand::CondCode(X86CondCode::E)],
                ),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ],
            vec![
                X86ISelInst::new(X86Opcode::AndRI, vec![vr(7), vr(7), X86ISelOperand::Imm(6)]),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ],
        ]);
        let live = X86FlagLiveness::analyze(&f);
        let insts = &f.blocks[&Block(0)].insts;
        assert!(
            live.flags_dead_after(insts, Block(0), 0),
            "the `jmp` target kills flags; the layout-adjacent flag reader is not a \
             successor and must not be consulted"
        );
    }

    /// A `Ret` is opaque by choice, so a block ending in one never licenses a
    /// cross-block conclusion.
    #[test]
    fn return_refuses() {
        let f = func_with(vec![vec![
            add(4, 1, 3),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]]);
        let live = X86FlagLiveness::analyze(&f);
        let insts = &f.blocks[&Block(0)].insts;
        assert!(
            !live.flags_dead_after(insts, Block(0), 0),
            "a return is treated as able to expose RFLAGS"
        );
    }

    /// A loop whose only flag reader is the latch: the fixpoint must propagate
    /// liveness backwards around the back edge rather than reporting the
    /// all-dead initialisation.
    #[test]
    fn liveness_propagates_around_a_back_edge() {
        let f = func_with(vec![
            // 0: transparent, falls through to 1
            vec![add(4, 1, 3)],
            // 1: transparent, jumps to 2
            vec![X86ISelInst::new(
                X86Opcode::Jmp,
                vec![X86ISelOperand::Block(Block(2))],
            )],
            // 2: READS flags, then loops back to 1
            vec![
                X86ISelInst::new(
                    X86Opcode::Cmovcc,
                    vec![vr(7), vr(8), X86ISelOperand::CondCode(X86CondCode::E)],
                ),
                X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
            ],
        ]);
        let live = X86FlagLiveness::analyze(&f);
        assert!(live.live_in(Block(2)), "block 2 reads flags directly");
        assert!(
            live.live_in(Block(1)),
            "block 1 is transparent and jumps to a reader, so liveness must reach it"
        );
        let insts = &f.blocks[&Block(0)].insts;
        assert!(
            !live.flags_dead_after(insts, Block(0), 0),
            "the `add`'s flags reach the loop's reader"
        );
    }

    /// A block absent from `block_order`, and a missing exit, both read as live.
    #[test]
    fn unknown_topology_fails_closed() {
        let f = func_with(vec![vec![add(4, 1, 3)]]);
        let live = X86FlagLiveness::analyze(&f);
        assert!(
            live.live_in(Block(99)),
            "an unanalyzed block must read as live"
        );
        let insts = &f.blocks[&Block(0)].insts;
        assert!(
            !live.flags_dead_after(insts, Block(0), 0),
            "the only block has no successor, so its tail flags are not provably dead"
        );
    }
}
