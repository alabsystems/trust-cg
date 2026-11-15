// trust-cg-opt - publication review bar for the mac-reg-block recognizer
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # The publication review bar (ledger L10-P4)
//!
//! Release review of the v0.1.0 candidate found that the `mac-reg-block`
//! recognizer did not prove four conditions the register-blocked fast path
//! relies on, and excluded the pass until they were fail-closed
//! (`publish/DECISIONS.md`):
//!
//! 1. **Data width.** `apply` emits 64-bit `LDR`/`LDP`/`STR` lanes and a 64-bit
//!    `MADD`. The element STRIDE (`scale == 8`) is checked by the recognizer;
//!    [`check_data_width`] also requires every transferred and multiplied
//!    VALUE to be a 64-bit GPR, so `i32` data kept in 8-byte cells (stride 8,
//!    `ldr w`) is refused instead of widened into its neighbour's bytes.
//! 2. **All array bounds.** The fast path accesses every index in
//!    `[0, N*N)` of `a`, `b` and `c` with no check. [`check_slots`] requires
//!    each backing stack slot to hold at least `N*N` elements, and
//!    [`check_mandatory_control_flow`] requires EVERY bounds check in the nest
//!    (including the `a[i*N+k]` check in the k-loop, which the shape
//!    recognizer never inspected) to compare a recognized index, computed in
//!    the current iteration of its own loop and dominating the check, against
//!    a length of at least `N*N`. A check may also arrive as the proof-only
//!    carrier `TrapBoundsCheckExact [base, index, #len]`, which traps iff
//!    `!(index <u len)` and has no CFG edge of its own. It is what the rustc
//!    bridge's constant-length checks lowered to before TrustIR v52 (a
//!    `const` + `icmp ult` + `assert` triple, which the shared admission
//!    floor now refuses as a kindless source `assert`); the current bridge
//!    emits a compare and branch to a block that calls `panic_bounds_check`.
//!    [`check_bounds_carrier`] holds every carrier in the nest to the same
//!    index, placement and length conditions, and refuses any other carrier
//!    by name ([`NestReject::UnprovenBoundsCarrier`]).
//! 3. **Mandatory control flow.** The fast path replays only the straight-line
//!    nest. [`check_mandatory_control_flow`] classifies every conditional
//!    branch and every loop exit in the nest: the three counted-loop header
//!    tests, each exiting to exactly its parent loop (the i-loop to the nest
//!    exit), and bounds checks proven to pass. Any other branch — an early
//!    exit, a data-dependent `break`, an internal diamond that makes the store
//!    conditional — is refused. A header runs once more than its body, with
//!    the counter at `N`, so [`check_header_work`] admits only copies, the
//!    counter compare and the branches there, and [`check_placement`] puts
//!    every recognized index, address, load, multiply-add and the store in a
//!    non-header block of its own loop. [`check_dominated_uses`] requires
//!    every single-definition value the nest reads to be defined on every
//!    path before the read, so no read sees a previous iteration's value.
//!    [`check_counter_reads`] refuses a read of a loop counter after its latch
//!    step or outside its own loop, and [`check_counter_inits`] requires each
//!    counter to be reset once per iteration of its parent loop.
//! 4. **Bypassed loop live-outs.** The fast path defines only fresh vregs and
//!    leaves the nest straight to its exit. [`check_no_bypassed_live_out`]
//!    asks the crate's one loop-state contract ([`crate::loop_contract`]),
//!    handing off only at that exit, which refuses the nest when any register
//!    the nest writes (the flags included) is live into it, because on the
//!    fast path it would still hold its pre-nest value. The one exception is
//!    a pass-through carrier the nest only copies out and back (the rustc
//!    bridge threads outer-loop values through inner loops as block
//!    parameters): its exit value is its pre-nest value on both paths, so it
//!    counts as reproduced.
//!
//! Every constant these checks rely on — a bounds-check length or loop bound
//! held in a register, and the element-scale register — must be a
//! [`nest_constant`]: one `Movz` (plus `Movk` chunks) in one block outside
//! the nest. The recognizer's last-wins definition map names whichever
//! definition comes last in the layout, which need not be the one reaching
//! the nest.
//!
//! The condition flags are one of the registers the contract checks. Both the
//! scalar nest and the fast path leave through a final `cmp N, N` of the i
//! counter, so NZCV at the exit would agree; the contract still refuses a nest
//! whose exit reads NZCV before writing it (fail closed, never measured).
//!
//! This is recognition-side evidence plus the native on/off/reference
//! differential in `trust-cg-codegen/tests/e2e_aarch64_mac_reg_block_differential.rs`;
//! it is not a proof that the rewrite preserves semantics.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::fmt;

use trust_cg_ir::function::StackSlotAllocationKind;
use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, RegClass, StackSlotId, VReg};

use super::{
    CC_LO, CC_LT, block_of_inst, bounds_carrier, branch_targets, copied_const, copy_like,
    find_all_defs, resolve_to_carried, same_as, strip_copies,
};
use crate::dom::DomTree;
use crate::effects::{for_each_inst_def, for_each_inst_use, live_def_count, writes_flags};
use crate::loop_contract::{ExitPlan, Handoff, LoopExit, LoopLocality, LoopStateEscape, StateReg};

/// Why the recognizer declined a candidate nest.
///
/// The named variants are the fail-closed guards the unit tests pin; every
/// other structural mismatch (the nest is simply not the modeled matmul
/// shape) is [`NestReject::Shape`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NestReject {
    /// Not the modeled three-deep square matmul nest.
    Shape,
    /// An `a`/`b`/`c` base is not the exact start of a single-definition
    /// fixed stack slot (a pointer parameter, a derived address).
    ArrayBaseNotStackSlot,
    /// Two of `a`/`b`/`c` are the same stack slot.
    AliasedArrays,
    /// An instruction, operand or memory access outside the modeled set.
    OpenWorld,
    /// `N` is not a positive multiple of a 12- or 8-lane tile.
    NotTileMultiple,
    /// The element stride is not the 8 bytes the kernel's lanes transfer.
    ElementScale,
    /// A loaded, multiplied or stored value is not a 64-bit GPR.
    DataWidth,
    /// One of the nest's index, address or data values has more than one
    /// definition, so no single reaching definition is known.
    MultiDefValue,
    /// A backing stack slot holds fewer than `N*N` elements, or is not a
    /// fixed-size slot.
    SlotTooSmall,
    /// A bounds check compares against a length below `N*N`, so it can fail
    /// on an index the fast path would access unchecked.
    BoundsCheckMayFail,
    /// A conditional branch that is neither a counted-loop test nor a bounds
    /// check proven to pass (an early exit, a data-dependent branch).
    UnprovenConditionalBranch,
    /// A loop exit edge other than the header test leaving to the parent loop
    /// (or, for the i-loop, to the nest exit).
    UnmodeledLoopExit,
    /// A loop counter is read after its latch step.
    CounterReadAfterStep,
    /// A value the nest defines is live into the nest exit.
    BypassedLiveOut,
    /// A loop header holds an instruction other than a copy, the counter
    /// compare and the branches. A header runs once more than the body, with
    /// the counter at `N`, so any work there is an extra iteration the fast
    /// path does not replay.
    HeaderWork,
    /// A recognized index, address, load, multiply-add or the store is not
    /// in a non-header block of the loop whose iteration it belongs to.
    MisplacedAccess,
    /// A single-definition value is read where its definition does not
    /// dominate the read, so the read can see another iteration's value.
    UseNotDominated,
    /// A loop counter is read outside its own loop body.
    CounterReadOutsideLoop,
    /// A loop counter's `= 0` definition is not in its parent loop (outside
    /// the nest, for the i-loop) dominating the loop header, so the counter is
    /// not reset once per parent iteration.
    CounterInitOutsideParent,
    /// A `TrapBoundsCheckExact` carrier in the nest is not proven to pass: it
    /// is malformed, compares a length register rather than a constant, or
    /// checks a value that is not a recognized index of the current
    /// iteration. The fast path would skip a trap the scalar nest can take.
    UnprovenBoundsCarrier,
}

impl fmt::Display for NestReject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Shape => "not the modeled matmul nest shape",
            Self::ArrayBaseNotStackSlot => {
                "an array base is not the start of a single-definition stack slot"
            }
            Self::AliasedArrays => "a/b/c are not three distinct stack slots",
            Self::OpenWorld => "an instruction or operand outside the modeled nest",
            Self::NotTileMultiple => "N is not a positive multiple of a 12- or 8-lane tile",
            Self::ElementScale => "element stride is not the 8 bytes the kernel lanes transfer",
            Self::DataWidth => "a transferred or multiplied value is not a 64-bit GPR lane",
            Self::MultiDefValue => "a nest index, address or data value has several definitions",
            Self::SlotTooSmall => "a backing stack slot holds fewer than N*N elements",
            Self::BoundsCheckMayFail => {
                "a bounds check in the nest compares against a length below N*N"
            }
            Self::UnprovenConditionalBranch => {
                "a conditional branch in the nest is neither a counted-loop test nor a passing bounds check"
            }
            Self::UnmodeledLoopExit => {
                "a loop in the nest has an exit edge other than its header test"
            }
            Self::CounterReadAfterStep => "a loop counter is read after its latch step",
            Self::BypassedLiveOut => "a value defined in the nest is live into the nest exit",
            Self::HeaderWork => "a loop header holds work other than copies and its counter test",
            Self::MisplacedAccess => {
                "a recognized index, access or multiply-add is outside the body of its own loop"
            }
            Self::UseNotDominated => {
                "a single-definition value is read where its definition does not dominate the read"
            }
            Self::CounterReadOutsideLoop => "a loop counter is read outside its own loop",
            Self::CounterInitOutsideParent => {
                "a loop counter is not reset once per iteration of its parent loop"
            }
            Self::UnprovenBoundsCarrier => {
                "a bounds-check trap carrier in the nest is not a constant-length check of a current index"
            }
        };
        f.write_str(text)
    }
}

/// A verified `for counter in 0..N` loop: its latch step and its reset.
#[derive(Debug, Clone, Copy)]
pub(super) struct CountedLoop {
    /// The loop-carried counter register.
    pub(super) counter: VReg,
    /// The loop's single latch.
    pub(super) latch: BlockId,
    /// The `+1` step definition of `counter` in `latch`.
    pub(super) step: InstId,
    /// The single `counter = 0` definition outside the loop body.
    pub(super) init: InstId,
}

/// Everything the review bar needs about a shape-recognized nest.
pub(super) struct NestFacts<'a> {
    pub(super) i_body: &'a HashSet<BlockId>,
    pub(super) k_body: &'a HashSet<BlockId>,
    pub(super) j_body: &'a HashSet<BlockId>,
    /// Loop headers, outermost first: `[i, k, j]`.
    pub(super) headers: [BlockId; 3],
    /// Counted loops, outermost first: `[i, k, j]`.
    pub(super) counters: [CountedLoop; 3],
    /// The i-header's unique out-of-nest successor.
    pub(super) exit_target: BlockId,
    /// The recognized indices `a[i*N+k]`, `c[i*N+j]` (load), `b[k*N+j]`,
    /// `c[i*N+j]` (store). Each is `Madd(x, N, y)` of loop counters.
    pub(super) indices: [VReg; 4],
    /// Values the kernel moves through 64-bit lanes: the loaded `a` element
    /// and the operand the `madd` multiplies, the loaded `b` and `c`
    /// elements, and the stored sum.
    pub(super) lane_values: [VReg; 5],
    /// The `a[i*N+k]` chain, one per k iteration: index, address, value.
    pub(super) k_level_values: [VReg; 3],
    /// The j-loop chain, one per j iteration: the `c` load's index, address
    /// and value, the `b` load's, and the store's index, address and value
    /// (the multiply-add).
    pub(super) j_level_values: [VReg; 9],
    /// The single `c` store.
    pub(super) store: InstId,
    /// Backing slots of `a`, `b`, `c`.
    pub(super) slots: [StackSlotId; 3],
    /// The register the address `madd`s scale every index by.
    pub(super) scale_reg: VReg,
    pub(super) n: i64,
    pub(super) scale: i64,
}

impl NestFacts<'_> {
    /// The recognized values whose single reaching definition the shape
    /// match relied on.
    fn recognized_values(&self) -> impl Iterator<Item = VReg> + '_ {
        self.k_level_values
            .iter()
            .chain(&self.j_level_values)
            .copied()
    }

    /// The body of the loop at `level` (`0` = i, `1` = k, `2` = j).
    fn body(&self, level: usize) -> &HashSet<BlockId> {
        [self.i_body, self.k_body, self.j_body][level]
    }
}

/// Run every review-bar guard; the first refusal wins. The last guard is the
/// loop-state contract, whose token the plan carries.
pub(super) fn check(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    facts: &NestFacts<'_>,
) -> Result<LoopLocality, NestReject> {
    check_data_width(facts)?;
    check_scale_register(func, def, facts)?;
    check_single_defs(func, facts)?;
    check_slots(func, facts)?;
    check_header_work(func, facts)?;
    check_placement(func, facts)?;
    check_dominated_uses(func, dom, facts)?;
    check_counter_reads(func, facts)?;
    check_counter_inits(func, dom, facts)?;
    let proven_checks = check_mandatory_control_flow(func, dom, def, facts)?;
    check_no_bypassed_live_out(func, dom, facts, &proven_checks)
}

/// Review item 1: every lane value is a 64-bit GPR, so the emitted 64-bit
/// loads, stores and `madd` transfer and compute exactly the modeled width.
pub(super) fn check_data_width(facts: &NestFacts<'_>) -> Result<(), NestReject> {
    if facts
        .lane_values
        .iter()
        .all(|value| value.class == RegClass::Gpr64)
    {
        Ok(())
    } else {
        Err(NestReject::DataWidth)
    }
}

/// Every index/address/data value the shape match resolved through the
/// last-wins definition map has exactly one definition.
pub(super) fn check_single_defs(
    func: &MachFunction,
    facts: &NestFacts<'_>,
) -> Result<(), NestReject> {
    if facts
        .recognized_values()
        .all(|value| live_def_count(func, value.id) == 1)
    {
        Ok(())
    } else {
        Err(NestReject::MultiDefValue)
    }
}

/// Review item 2 (storage): each backing slot is fixed-size and holds at
/// least `N*N` elements of `scale` bytes, so every unchecked fast-path access
/// stays inside its own slot.
pub(super) fn check_slots(func: &MachFunction, facts: &NestFacts<'_>) -> Result<(), NestReject> {
    let needed = i128::from(facts.n) * i128::from(facts.n) * i128::from(facts.scale);
    for slot in facts.slots {
        let Some(slot) = func.stack_slots.get(slot.0 as usize) else {
            return Err(NestReject::SlotTooSmall);
        };
        if slot.allocation != StackSlotAllocationKind::Fixed || i128::from(slot.size) < needed {
            return Err(NestReject::SlotTooSmall);
        }
    }
    Ok(())
}

/// The nest level of `block`: `2` in the j-loop, `1` in the k-loop outside
/// it, `0` elsewhere in the i-loop.
fn level_of(facts: &NestFacts<'_>, block: BlockId) -> usize {
    if facts.j_body.contains(&block) {
        2
    } else if facts.k_body.contains(&block) {
        1
    } else {
        0
    }
}

/// `(block, position)` of every instruction in the emitted layout.
fn inst_positions(func: &MachFunction) -> HashMap<InstId, (BlockId, usize)> {
    let mut positions = HashMap::default();
    for &block in &func.block_order {
        for (pos, &id) in func.block(block).insts.iter().enumerate() {
            positions.insert(id, (block, pos));
        }
    }
    positions
}

/// Whether the instruction at `def` runs before the one at `read` on every
/// path to `read`.
fn runs_before(dom: &DomTree, def: (BlockId, usize), read: (BlockId, usize)) -> bool {
    if def.0 == read.0 {
        def.1 < read.1
    } else {
        dom.dominates(def.0, read.0)
    }
}

/// Mandatory control flow (headers): a loop header runs once more than the
/// loop body, with the counter already at `N`. The fast path replays only
/// the iterations that reach the body, so a header may hold only copies, the
/// counter compare and its branches; an index, load, multiply-add or store
/// there would run an extra time in the scalar nest.
pub(super) fn check_header_work(
    func: &MachFunction,
    facts: &NestFacts<'_>,
) -> Result<(), NestReject> {
    for header in facts.headers {
        for &id in &func.block(header).insts {
            let inst = func.inst(id);
            let admitted = copy_like(inst).is_some()
                || matches!(
                    inst.opcode,
                    AArch64Opcode::CmpRR
                        | AArch64Opcode::CmpRI
                        | AArch64Opcode::BCond
                        | AArch64Opcode::B
                );
            if !admitted {
                return Err(NestReject::HeaderWork);
            }
        }
    }
    Ok(())
}

/// Mandatory control flow (placement): the `a[i*N+k]` chain is defined in a
/// non-header block of the k-loop outside the j-loop, and the j-loop chain
/// and the store in a non-header block of the j-loop. Such a block is
/// reached only after its header's `counter < N` test passed in the current
/// iteration, so each recognized index is `x*N + y` of counters in `[0, N)`
/// and each access runs exactly once per iteration the fast path replays.
pub(super) fn check_placement(
    func: &MachFunction,
    facts: &NestFacts<'_>,
) -> Result<(), NestReject> {
    let at_level = |id: InstId, level: usize| {
        block_of_inst(func, id)
            .is_some_and(|block| block != facts.headers[level] && level_of(facts, block) == level)
    };
    let defined_at_level = |value: VReg, level: usize| {
        find_all_defs(func, value)
            .first()
            .is_some_and(|&id| at_level(id, level))
    };
    let placed = facts
        .k_level_values
        .iter()
        .all(|&value| defined_at_level(value, 1))
        && facts
            .j_level_values
            .iter()
            .all(|&value| defined_at_level(value, 2))
        && at_level(facts.store, 2);
    if placed {
        Ok(())
    } else {
        Err(NestReject::MisplacedAccess)
    }
}

/// Mandatory control flow (reaching values): every vreg with exactly one
/// definition that the nest reads is defined on every path before the read.
/// Otherwise the read sees a previous iteration's value, or no value at all
/// on the first iteration. Multi-definition vregs (the loop counters and
/// other block parameters) are covered by the counted-loop checks instead.
pub(super) fn check_dominated_uses(
    func: &MachFunction,
    dom: &DomTree,
    facts: &NestFacts<'_>,
) -> Result<(), NestReject> {
    let positions = inst_positions(func);
    let mut defs: HashMap<u32, Vec<InstId>> = HashMap::default();
    for &block in &func.block_order {
        for &id in &func.block(block).insts {
            for_each_inst_def(func.inst(id), |value| {
                let ids = defs.entry(value.id).or_default();
                if ids.last() != Some(&id) {
                    ids.push(id);
                }
            });
        }
    }
    for &block in facts.i_body {
        for (pos, &id) in func.block(block).insts.iter().enumerate() {
            let mut dominated = true;
            for_each_inst_use(func.inst(id), |value| {
                if let Some(&[single]) = defs.get(&value.id).map(Vec::as_slice)
                    && let Some(&at) = positions.get(&single)
                    && !runs_before(dom, at, (block, pos))
                {
                    dominated = false;
                }
            });
            if !dominated {
                return Err(NestReject::UseNotDominated);
            }
        }
    }
    Ok(())
}

/// Induction (reset): each counter's `= 0` definition lies in its parent
/// loop's body outside the loop itself (for the i-loop, outside the nest)
/// and dominates the loop header, so every parent iteration starts the loop
/// from 0, as the fast path does.
pub(super) fn check_counter_inits(
    func: &MachFunction,
    dom: &DomTree,
    facts: &NestFacts<'_>,
) -> Result<(), NestReject> {
    for (level, counted) in facts.counters.iter().enumerate() {
        let Some(block) = block_of_inst(func, counted.init) else {
            return Err(NestReject::CounterInitOutsideParent);
        };
        let in_parent = match level {
            0 => !facts.i_body.contains(&block),
            _ => facts.body(level - 1).contains(&block) && !facts.body(level).contains(&block),
        };
        if !in_parent || !dom.dominates(block, facts.headers[level]) {
            return Err(NestReject::CounterInitOutsideParent);
        }
    }
    Ok(())
}

/// Review items 2 and 3: classify every conditional branch and every loop
/// exit in the nest.
///
/// For each block of the i-loop body, with `own` the innermost of the three
/// loop bodies containing it:
///
/// * a loop header carries exactly one conditional branch, a forward `LT`/`LO`
///   into `own`, and its other successor leaves exactly that loop: into the
///   parent loop's body, or for the i-loop to the nest exit;
/// * a block without a conditional branch has every successor in `own`;
/// * a block with one conditional branch must be a bounds check: `LT`/`LO`
///   into `own`, the other successor outside the whole nest, and flags from a
///   compare of a recognized index against a constant length `>= N*N`. The
///   index's definition must lie in a non-header block of its own loop, run
///   before the compare on every path, and the check must lie in that same
///   loop, so the compared value is `x*N + y` of the current iteration's
///   counters, both in `[0, N)`. The check then always passes and its
///   failure edge is dead on the fast path.
///
/// Every `TrapBoundsCheckExact` carrier in any block of the nest (it traps
/// without a CFG edge, so the successor rules above cannot see it) must pass
/// [`check_bounds_carrier`]. Carriers in a loop header were already refused
/// by [`check_header_work`].
///
/// Anything else is refused. Returns the checks it proved cannot fail, as the
/// i-loop exits they are (a bounds check's failure edge, a carrier), for the
/// loop-state contract's exit plan ([`check_no_bypassed_live_out`]).
pub(super) fn check_mandatory_control_flow(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    facts: &NestFacts<'_>,
) -> Result<Vec<LoopExit<BlockId>>, NestReject> {
    let min_len = facts.n.checked_mul(facts.n).ok_or(NestReject::Shape)?;
    let mut proven: Vec<LoopExit<BlockId>> = Vec::new();
    let mut blocks: Vec<BlockId> = facts.i_body.iter().copied().collect();
    blocks.sort_unstable();
    for block_id in blocks {
        let level = level_of(facts, block_id);
        let own = facts.body(level);
        let block = func.block(block_id);
        for (pos, &id) in block.insts.iter().enumerate() {
            if func.inst(id).opcode == AArch64Opcode::TrapBoundsCheckExact {
                check_bounds_carrier(func, dom, def, facts, (block_id, pos), min_len)?;
                proven.push(LoopExit::Stop {
                    block: block_id,
                    index: pos,
                });
            }
        }
        let mut succs = block.succs.clone();
        succs.sort_unstable();
        succs.dedup();
        let bconds: Vec<usize> = block
            .insts
            .iter()
            .enumerate()
            .filter(|(_, id)| func.inst(**id).opcode == AArch64Opcode::BCond)
            .map(|(pos, _)| pos)
            .collect();

        if block_id == facts.headers[level] {
            let &[pos] = bconds.as_slice() else {
                return Err(NestReject::UnprovenConditionalBranch);
            };
            let Some((cc, target)) = forward_branch(func, block.insts[pos]) else {
                return Err(NestReject::UnprovenConditionalBranch);
            };
            if !(cc == CC_LT || cc == CC_LO) || !own.contains(&target) {
                return Err(NestReject::UnprovenConditionalBranch);
            }
            // The branch's flags compare this loop's counter against `N`,
            // with `N` a nest constant (not a register another path may
            // define differently).
            let counted = &facts.counters[level];
            let Some((compared, bound)) = flag_compare(func, def, facts.i_body, block_id, pos)
            else {
                return Err(NestReject::UnprovenConditionalBranch);
            };
            if bound != facts.n
                || resolve_to_carried(func, compared, counted.latch) != Some(counted.counter)
            {
                return Err(NestReject::UnprovenConditionalBranch);
            }
            let &[first, second] = succs.as_slice() else {
                return Err(NestReject::UnmodeledLoopExit);
            };
            let exit = if first == target { second } else { first };
            if own.contains(&exit) {
                return Err(NestReject::UnprovenConditionalBranch);
            }
            let exits_to_parent = match level {
                0 => exit == facts.exit_target,
                _ => facts.body(level - 1).contains(&exit),
            };
            if !exits_to_parent {
                return Err(NestReject::UnmodeledLoopExit);
            }
            continue;
        }

        match bconds.as_slice() {
            [] => {
                if succs.iter().any(|succ| !own.contains(succ)) {
                    return Err(NestReject::UnmodeledLoopExit);
                }
            }
            &[pos] => {
                let fail =
                    check_bounds_check(func, dom, def, facts, own, block_id, pos, &succs, min_len)?;
                proven.push(LoopExit::Edge {
                    from: block_id,
                    to: fail,
                });
            }
            _ => return Err(NestReject::UnprovenConditionalBranch),
        }
    }
    Ok(proven)
}

/// `(condition code, target)` of a well-formed `BCond cc, target`.
fn forward_branch(func: &MachFunction, id: InstId) -> Option<(i64, BlockId)> {
    let inst = func.inst(id);
    if inst.opcode != AArch64Opcode::BCond || inst.operands.len() != 2 {
        return None;
    }
    let cc = inst.operands[0].as_imm()?;
    let target = *branch_targets(inst).first()?;
    Some((cc, target))
}

/// `(compared register, constant)` of the compare whose flags the `BCond` at
/// `bcond_pos` reads: the last flag writer before it in the same block (a
/// producer in another block is not modeled), `CmpRI x, #c` or `CmpRR x, r`
/// with `r` a [`nest_constant`].
fn flag_compare(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    nest: &HashSet<BlockId>,
    block_id: BlockId,
    bcond_pos: usize,
) -> Option<(VReg, i64)> {
    // A bounds carrier expands to its own `CMP` after optimization, so one
    // between the compare and the branch would supply the branch's flags:
    // it counts as the last flag writer here and is refused below.
    let cmp = func.block(block_id).insts[..bcond_pos]
        .iter()
        .rev()
        .map(|&id| func.inst(id))
        .find(|inst| {
            writes_flags(inst.opcode) || inst.opcode == AArch64Opcode::TrapBoundsCheckExact
        })?;
    match cmp.opcode {
        AArch64Opcode::CmpRI if cmp.operands.len() == 2 => {
            Some((cmp.operands[0].as_vreg()?, cmp.operands[1].as_imm()?))
        }
        AArch64Opcode::CmpRR if cmp.operands.len() == 2 => Some((
            cmp.operands[0].as_vreg()?,
            nest_constant(func, def, nest, cmp.operands[1].as_vreg()?)?,
        )),
        _ => None,
    }
}

/// The value of a constant register that every read inside `nest` sees.
///
/// The shape match's `copied_const` already folds a register only when every
/// definition of it materializes the same constant. This is the review bar's
/// own re-proof, stricter and independent of that: every definition of the
/// register (through single-definition copies) must lie in ONE block outside
/// the nest and be exactly one `Movz` plus `Movk` chunks, so the materialized
/// value is the same on every path into the nest.
pub(super) fn nest_constant(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    nest: &HashSet<BlockId>,
    value: VReg,
) -> Option<i64> {
    let value = strip_copies(func, def, value);
    let defs = find_all_defs(func, value);
    let block = block_of_inst(func, *defs.first()?)?;
    if nest.contains(&block) {
        return None;
    }
    let mut movz = 0usize;
    for &id in &defs {
        if block_of_inst(func, id) != Some(block) {
            return None;
        }
        match func.inst(id).opcode {
            AArch64Opcode::Movz => movz += 1,
            AArch64Opcode::Movk => {}
            _ => return None,
        }
    }
    if movz != 1 {
        return None;
    }
    copied_const(func, def, value)
}

/// Review item 2 (stride): the element-scale register the index `madd`s
/// multiply by is the recognized 8 on every path into the nest.
pub(super) fn check_scale_register(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    facts: &NestFacts<'_>,
) -> Result<(), NestReject> {
    if nest_constant(func, def, facts.i_body, facts.scale_reg) == Some(facts.scale) {
        Ok(())
    } else {
        Err(NestReject::ElementScale)
    }
}

/// A non-header conditional branch must be a bounds check that cannot fail.
/// Returns its failure target.
#[allow(clippy::too_many_arguments)]
fn check_bounds_check(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    facts: &NestFacts<'_>,
    own: &HashSet<BlockId>,
    block_id: BlockId,
    bcond_pos: usize,
    succs: &[BlockId],
    min_len: i64,
) -> Result<BlockId, NestReject> {
    let insts = &func.block(block_id).insts;
    let Some((cc, ok)) = forward_branch(func, insts[bcond_pos]) else {
        return Err(NestReject::UnprovenConditionalBranch);
    };
    if !(cc == CC_LO || cc == CC_LT) || !own.contains(&ok) {
        return Err(NestReject::UnprovenConditionalBranch);
    }
    let &[first, second] = succs else {
        return Err(NestReject::UnmodeledLoopExit);
    };
    let fail = if first == ok { second } else { first };
    if facts.i_body.contains(&fail) {
        // Both edges stay in the nest: a data-dependent branch, not a check.
        return Err(NestReject::UnprovenConditionalBranch);
    }
    let Some((index, len)) = flag_compare(func, def, facts.i_body, block_id, bcond_pos) else {
        return Err(NestReject::UnprovenConditionalBranch);
    };
    let Some(known) = facts
        .indices
        .iter()
        .copied()
        .find(|&known| same_as(func, def, index, known))
    else {
        return Err(NestReject::UnprovenConditionalBranch);
    };
    if !index_is_current_at(func, dom, facts, known, (block_id, bcond_pos)) {
        return Err(NestReject::UnprovenConditionalBranch);
    }
    if len < min_len {
        return Err(NestReject::BoundsCheckMayFail);
    }
    Ok(fail)
}

/// A `TrapBoundsCheckExact [base, index, #len]` carrier in the nest must be a
/// check that cannot trap: a constant `len >= N*N` compared with a recognized
/// index that holds the current iteration's value at the carrier (see
/// [`index_is_current_at`]). The index is then `x*N + y` with both counters
/// in `[0, N)`, so `index <= N*N - 1 < len`. The base operand is proof
/// identity only and plays no part in the runtime check.
pub(super) fn check_bounds_carrier(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    facts: &NestFacts<'_>,
    at: (BlockId, usize),
    min_len: i64,
) -> Result<(), NestReject> {
    let inst = func.inst(func.block(at.0).insts[at.1]);
    let Some((index, len)) = bounds_carrier(inst) else {
        return Err(NestReject::UnprovenBoundsCarrier);
    };
    let Some(known) = facts
        .indices
        .iter()
        .copied()
        .find(|&known| same_as(func, def, index, known))
    else {
        return Err(NestReject::UnprovenBoundsCarrier);
    };
    if !index_is_current_at(func, dom, facts, known, at) {
        return Err(NestReject::UnprovenBoundsCarrier);
    }
    if len < min_len {
        return Err(NestReject::BoundsCheckMayFail);
    }
    Ok(())
}

/// Whether the recognized index `known` holds the current iteration's value
/// at `check`: its single definition lies in a non-header block of its own
/// loop, runs before `check` on every path, and `check` lies in that loop.
/// An index defined in a header, or read after its loop exits, can hold
/// `x*N + N`.
fn index_is_current_at(
    func: &MachFunction,
    dom: &DomTree,
    facts: &NestFacts<'_>,
    known: VReg,
    check: (BlockId, usize),
) -> bool {
    let defs = find_all_defs(func, known);
    let &[single] = defs.as_slice() else {
        return false;
    };
    let Some(def_block) = block_of_inst(func, single) else {
        return false;
    };
    let Some(def_pos) = func
        .block(def_block)
        .insts
        .iter()
        .position(|&id| id == single)
    else {
        return false;
    };
    let level = level_of(facts, def_block);
    level > 0
        && def_block != facts.headers[level]
        && facts.body(level).contains(&check.0)
        && runs_before(dom, (def_block, def_pos), check)
}

/// Review item 3 (induction): after a counter's latch step the register holds
/// the next iteration's value, so no instruction after the step in the latch
/// may read it (a degenerate self-copy excepted, as the counted-loop check
/// also ignores it). Outside its own loop body the register holds `N` (after
/// the loop) or a previous parent iteration's value (before the reset), so no
/// instruction anywhere else in the function may read it either.
pub(super) fn check_counter_reads(
    func: &MachFunction,
    facts: &NestFacts<'_>,
) -> Result<(), NestReject> {
    for (level, counted) in facts.counters.iter().enumerate() {
        let body = facts.body(level);
        for &block in func
            .block_order
            .iter()
            .filter(|block| !body.contains(block))
        {
            for &id in &func.block(block).insts {
                let mut reads_counter = false;
                for_each_inst_use(func.inst(id), |used| {
                    if used.id == counted.counter.id {
                        reads_counter = true;
                    }
                });
                if reads_counter {
                    return Err(NestReject::CounterReadOutsideLoop);
                }
            }
        }
    }
    for counted in &facts.counters {
        let insts = &func.block(counted.latch).insts;
        let Some(step_pos) = insts.iter().position(|&id| id == counted.step) else {
            return Err(NestReject::Shape);
        };
        for &id in &insts[step_pos + 1..] {
            let inst = func.inst(id);
            if let Some((dst, src)) = copy_like(inst)
                && dst == counted.counter
                && src == counted.counter
            {
                continue;
            }
            let mut reads_counter = false;
            for_each_inst_use(inst, |used| {
                if used.id == counted.counter.id {
                    reads_counter = true;
                }
            });
            if reads_counter {
                return Err(NestReject::CounterReadAfterStep);
            }
        }
    }
    Ok(())
}

/// Review item 4: no vreg written anywhere in the nest is live into the nest
/// exit (a backward liveness fixpoint over the emitted layout, restricted to
/// the nest's definitions), unless it is a pass-through carrier whose value
/// at the exit is provably its value before the nest
/// ([`is_pass_through_carrier`]).
pub(super) fn check_no_bypassed_live_out(
    func: &MachFunction,
    dom: &DomTree,
    facts: &NestFacts<'_>,
    proven_checks: &[LoopExit<BlockId>],
) -> Result<LoopLocality, NestReject> {
    // The crate's one loop-state contract (`crate::loop_contract`), for a
    // rewrite that replaces the whole i-loop and hands off only at the nest's
    // exit target (never the i-header, never an abort path whose check the
    // review bar proved cannot fire). Its exits are the i-header's `i <u N`
    // test and the checks [`check_mandatory_control_flow`] proved cannot fail
    // (`proven_checks`); any other exit is refused. The fast path writes only
    // fresh vregs, so the only registers it reproduces are the pass-through
    // carriers the nest also leaves holding their entry value: each one the
    // contract names as live is admitted only when `is_pass_through_carrier`
    // proves it.
    let positions = inst_positions(func);
    let exit = [facts.exit_target];
    let exits = proven_checks.iter().fold(
        ExitPlan::loop_test(facts.headers[0], facts.exit_target),
        |plan, &check| plan.and_proved_not_taken(check),
    );
    let mut carriers: Vec<VReg> = Vec::new();
    loop {
        match LoopLocality::check(
            func,
            facts.i_body.iter().copied(),
            facts.headers[0],
            &exits,
            Handoff::Only(&exit),
            &carriers,
        ) {
            Ok(locality) => return Ok(locality),
            Err(LoopStateEscape::Live {
                reg: StateReg::Virtual(value),
                ..
            }) if !carriers.contains(&value)
                && is_pass_through_carrier(func, dom, &positions, facts.i_body, value.id) =>
            {
                carriers.push(value);
            }
            Err(LoopStateEscape::Exit(_) | LoopStateEscape::NotAnExit(_)) => {
                return Err(NestReject::UnmodeledLoopExit);
            }
            Err(_) => return Err(NestReject::BypassedLiveOut),
        }
    }
}

/// Whether the nest only copies vreg `id` around, so on every scalar path it
/// leaves the nest holding the value `X` it entered with, the value the fast
/// path (which never writes it) also leaves it holding.
///
/// The rustc bridge threads every value that is live across an inner loop
/// through that loop's block parameters: an outer loop's counter, bound and
/// accumulator reach the nest exit through `w = copy(v)` at the top of the
/// i-loop body and `v = copy(w)` in its latch. Such a `v` is admitted when
/// every definition of it in the nest is a same-class copy `v = copy(w)`
/// (or a self-copy), where `w` has exactly one definition in the function,
/// that definition is the same-class copy `w = copy(v)` inside the nest, and
/// it runs before the `v = copy(w)` on every path. By induction over the
/// nest's execution, `v` holds `X` at every point: each `w` is assigned `X`
/// from `v` and is assigned within the same pass through its dominating
/// block before `v` reads it back. A `w` read at the exit is refused
/// separately (its only definition is in the nest, so the fast path leaves
/// it stale, and it is not a pass-through carrier itself).
fn is_pass_through_carrier(
    func: &MachFunction,
    dom: &DomTree,
    positions: &HashMap<InstId, (BlockId, usize)>,
    nest: &HashSet<BlockId>,
    id: u32,
) -> bool {
    let mut blocks: Vec<BlockId> = nest.iter().copied().collect();
    blocks.sort_unstable();
    let mut defined = false;
    for block in blocks {
        for (pos, &inst_id) in func.block(block).insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            let mut defines = false;
            for_each_inst_def(inst, |value| defines |= value.id == id);
            if !defines {
                continue;
            }
            defined = true;
            let Some((dst, src)) = copy_like(inst) else {
                return false;
            };
            if dst.id != id || src.class != dst.class {
                return false;
            }
            if src == dst {
                continue;
            }
            let src_defs = find_all_defs(func, src);
            let &[src_def] = src_defs.as_slice() else {
                return false;
            };
            let Some(&src_at) = positions.get(&src_def) else {
                return false;
            };
            if !nest.contains(&src_at.0)
                || copy_like(func.inst(src_def)) != Some((src, dst))
                || !runs_before(dom, src_at, (block, pos))
            {
                return false;
            }
        }
    }
    defined
}
