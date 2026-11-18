// trust-cg-opt - x86-64 frame-slot value forwarding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Value forwarding through FIXED frame slots for x86-64 ISel-output
//! functions: satisfy a slot load from a register that already provably holds
//! that slot range's contents, within a block and across a forward edge into
//! a block with exactly one predecessor (see "Cross-block propagation"
//! below).
//!
//! Two shapes, both textbook and both absent from this backend before now:
//!
//! ```text
//!   (A) store-to-load forward      (B) load-to-load reuse
//!       mov [slot+d], v                v1 = mov [slot+d]
//!       ...                            ...
//!       v2 = mov [slot+d]              v2 = mov [slot+d]
//!   =>  v2 = mov v                 =>  v2 = mov v1
//! ```
//!
//! The emitted `MovRR`/`MovRR32` is then consumed by `X86CopyPropagation` and
//! deleted by `X86DeadCodeElimination`, so the net effect is one fewer memory
//! operation. A load whose value is already in its OWN destination register is
//! deleted outright rather than rewritten to a self-copy.
//!
//! # Why this pass exists and SROA does not cover it
//!
//! [`crate::x86_sroa`] promotes a non-escaped slot to vregs outright, which is
//! strictly better wherever it applies. It does not apply to these: its
//! recogniser is ROOTED at a materialized slot address
//! (`root = lea dst, [StackSlot(N)+0]`) and rewrites the loads and stores
//! derived from that root. A slot the ISel addresses DIRECTLY as
//! `[StackSlot(N)+d]` has no root vreg, so it is not a SROA candidate at all —
//! and a memory-backed scalar local is exactly that shape. Those slots kept
//! every load and store they were lowered with, including the provably
//! redundant ones.
//!
//! # Soundness
//!
//! An entry maps `(slot, displacement, width)` to a vreg that holds that byte
//! range's current contents. Admitted only when:
//!
//! 1. The address is `MemAddr { base, disp }` where `base` either IS
//!    `StackSlot(s)` or is a vreg [`build_frame_addresses`] resolves to a frame
//!    address. No index register, no arithmetic other than `Lea` displacements.
//!
//!    The resolver is not a convenience — without it this pass cannot fire AT
//!    ALL. x86 ISel never emits a direct `[StackSlot(s)+d]` load or store: every
//!    frame access is `Lea root, [StackSlot(s)+0]` followed by `[root + d]`, and
//!    the only direct-slot addressing in the stream is the register allocator's
//!    own spill code, which is materialized long after this pass runs. The first
//!    version of this pass matched only the direct form and was byte-identical on
//!    all 18 runtime programs for exactly that reason.
//! 2. `s` is a `Fixed` allocation and `[disp, disp+width)` lies wholly inside
//!    it, so the access can neither cross into a neighbouring slot nor depend on
//!    a runtime size.
//! 3. Load and source agree on width EXACTLY and on register class EXACTLY, and
//!    both are GPR (`Gpr64` via `MovRM`/`MovMR`, `Gpr32` via
//!    `MovRM32`/`MovMR32`). A 4-byte store does not satisfy an 8-byte load, and
//!    a narrow or SSE form is refused rather than modelled. The width is part of
//!    the key, so a partial-overlap read can never hit.
//! 4. Neither the load nor the instruction that established the entry carries
//!    `proof_origin`: this pass cannot transfer operand-bound proof custody to a
//!    new copy. Same rule as [`crate::x86_cse`].
//! 5. A def of an entry's VALUE vreg kills that entry, compared CLASS-BLIND by
//!    `VReg::id` — a same-id vreg at another class is an aliased width view of
//!    the same storage, not an unrelated register.
//!
//! and killed by exactly two rules, which together are the whole aliasing
//! argument:
//!
//! 6. A **precisely resolved** store — an allowlisted plain-store opcode whose
//!    operand 0 satisfies rules 1 and 2 and whose other operands name no frame
//!    address — kills every entry of that slot whose byte range it intersects,
//!    and nothing else.
//! 7. **Anything else that could write memory clears the WHOLE map**, as does
//!    every call, pseudo, terminator, atomic/exchange, side-effecting or
//!    proof-carrying instruction. A SIB-addressed store, a store through a
//!    register, a memory-destination RMW and `Push` are all in this class.
//!
//! Rule 7 is why this pass needs NO escape analysis: the only instructions
//! treated as harmless either cannot write memory at all, only read it, or write
//! a statically known slot range. Nothing that might name a frame slot through a
//! pointer is ever allowed to leave an entry standing — in particular a store
//! through a register the resolver could not ground clears the map, so an
//! escaped slot written through an aliased pointer is covered without the pass
//! ever asking which slots escape.
//!
//! # Cross-block propagation, restricted to the sound single-predecessor case
//!
//! Block-local alone is not enough here: `h2_vec_grow`'s `main` has 35 blocks and
//! ~20 candidate loads, so most candidates are the only access of their slot in
//! their block, and the pair this pass most wants — a `Vec` length stored at the
//! end of one block and reloaded at the start of the next — straddles the
//! boundary.
//!
//! So a block with EXACTLY ONE predecessor, reached by a FORWARD edge, seeds its
//! entry state from that predecessor's exit state. This is the same restricted
//! form of global availability [`crate::x86_cse::single_pred_source`] implements,
//! with the same argument: one predecessor means every execution reaching the
//! block came directly from it, edges in this IR carry no instructions, and the
//! forward-edge requirement rules out loop back-edges (a loop header has ≥ 2
//! predecessors) while guaranteeing the predecessor's exit state is already
//! final. A predecessor's exit state is snapshotted immediately before its first
//! PURE control-flow terminator, which clobbers no register and writes no
//! memory; a block whose tail contains a call or a memory barrier correctly
//! exports nothing.
//!
//! Merge points and back-edges get nothing. A full version would need a meet over
//! predecessors and fixpoint iteration — the same design note
//! [`crate::x86_cse`]'s module docs set out for global CSE.
//!
//! Nothing is reordered and nothing is hoisted. A rewrite replaces one
//! instruction in place with a copy reading a register already live at that
//! point; a deletion removes an instruction whose destination already holds the
//! value it would load.
//!
//! Opt-out: `-Ztrust-ir-cg-args=no-x86-slot-forward`. Trace:
//! `-Ztrust-ir-cg-args=trace-x86-slot-forward` (a TRACKED option — `trustc`
//! refuses every `TCG_*` environment variable, so an env-only instrument does
//! not exist under the Trust driver).
//!
//! # Known INCOMPLETENESS, deliberately left
//!
//! Rule 7 discards a non-escaped slot's entries at an unrelated heap store,
//! although a slot whose address is never materialized cannot be aliased by any
//! pointer — [`crate::x86_licm`]'s load tier proves exactly that and uses it.
//! Wiring that here would let an entry survive `y[i] = ...`. It is NOT done
//! because it buys nothing on the programs this pass was measured against (in
//! both of them every forwarded pair is already store/load-adjacent) and it
//! would make the kill rule depend on a whole-function analysis instead of the
//! instruction in front of it.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use trust_cg_ir::X86Opcode;
use trust_cg_ir::function::StackSlotAllocationKind;
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_lower::function::StackSlotInfo;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::x86_inst_effect;
use crate::x86_pass_manager::X86MachinePass;

/// A tracked frame-slot byte range: slot index, displacement, byte width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SlotRange {
    slot: u32,
    disp: i64,
    width: i64,
}

impl SlotRange {
    /// Byte-range intersection. Two ranges of the same slot conflict iff their
    /// `[disp, disp + width)` intervals overlap.
    fn overlaps(&self, other: &SlotRange) -> bool {
        self.slot == other.slot
            && self.disp < other.disp + other.width
            && other.disp < self.disp + self.width
    }
}

/// Block-local frame-slot value forwarding.
#[derive(Debug, Default)]
pub struct X86SlotForward {
    /// `None` reads the policy default ([`slot_forward_enabled_default`]).
    /// `Some` overrides it for this instance only.
    enabled: Option<bool>,
    last_run_rewrites: usize,
    last_run_deletions: usize,
}

impl X86SlotForward {
    pub fn new() -> Self {
        Self::default()
    }

    /// Override the policy default for this instance. Exists so a test can
    /// exercise BOTH arms in one process: [`set_slot_forward_disabled`] installs
    /// into a process-global `OnceLock`, so a test that called it would decide
    /// the default for every other test in the binary.
    pub fn with_enabled(mut self, enabled: bool) -> Self {
        self.enabled = Some(enabled);
        self
    }

    /// Loads rewritten to register copies by the most recent `run`. Diagnostic,
    /// not a performance metric.
    pub fn last_run_rewrites(&self) -> usize {
        self.last_run_rewrites
    }

    /// Loads DELETED by the most recent `run` (the value was already in the
    /// load's own destination register).
    pub fn last_run_deletions(&self) -> usize {
        self.last_run_deletions
    }
}

impl X86MachinePass for X86SlotForward {
    fn name(&self) -> &str {
        "x86-slot-forward"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        self.last_run_rewrites = 0;
        self.last_run_deletions = 0;
        if !self.enabled.unwrap_or_else(slot_forward_enabled_default) {
            return false;
        }
        run_impl(
            func,
            &mut self.last_run_rewrites,
            &mut self.last_run_deletions,
        )
    }
}

static SLOT_FORWARD_DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
static SLOT_FORWARD_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install this pass's OPT-OUT from a TRACKED compiler option, once
/// (`-Ztrust-ir-cg-args=no-x86-slot-forward`). DEFAULT ON.
pub fn set_slot_forward_disabled(disabled: bool) -> bool {
    match SLOT_FORWARD_DISABLED.set(disabled) {
        Ok(()) => true,
        Err(requested) => SLOT_FORWARD_DISABLED.get() == Some(&requested),
    }
}

/// Install the decision trace from a TRACKED compiler option, once
/// (`-Ztrust-ir-cg-args=trace-x86-slot-forward`).
pub fn set_slot_forward_trace_enabled(enabled: bool) -> bool {
    match SLOT_FORWARD_TRACE.set(enabled) {
        Ok(()) => true,
        Err(requested) => SLOT_FORWARD_TRACE.get() == Some(&requested),
    }
}

/// Whether the pass runs when its instance states no preference. DEFAULT TRUE.
pub fn slot_forward_enabled_default() -> bool {
    !SLOT_FORWARD_DISABLED.get().copied().unwrap_or(false)
        && !crate::tcg_env_flag("TCG_NO_X86_SLOT_FORWARD")
}

fn trace_enabled() -> bool {
    SLOT_FORWARD_TRACE.get().copied().unwrap_or(false)
        || crate::tcg_env_flag("TCG_TRACE_X86_SLOT_FORWARD")
}

macro_rules! trace {
    ($($arg:tt)*) => {
        if trace_enabled() {
            eprintln!("[x86-slot-forward] {}", format!($($arg)*));
        }
    };
}

/// Loads this pass can satisfy from a register. GPR only and width-exact; an
/// SSE or narrow form is refused rather than modelled (rule 3).
fn tracked_load(opcode: X86Opcode) -> Option<(i64, RegClass)> {
    match opcode {
        X86Opcode::MovRM => Some((8, RegClass::Gpr64)),
        X86Opcode::MovRM32 => Some((4, RegClass::Gpr32)),
        _ => None,
    }
}

/// Stores this pass can use as the SOURCE of a forwarded value. Same width and
/// class vocabulary as [`tracked_load`].
fn tracked_store(opcode: X86Opcode) -> Option<(i64, RegClass)> {
    match opcode {
        X86Opcode::MovMR => Some((8, RegClass::Gpr64)),
        X86Opcode::MovMR32 => Some((4, RegClass::Gpr32)),
        _ => None,
    }
}

/// Plain stores whose operand 0 IS the memory destination and which write
/// exactly this many bytes there. Wider than [`tracked_store`] on purpose: a
/// `MovMR8` cannot supply a value but it certainly invalidates one. This is the
/// same allowlist, for the same reason, as `x86_licm::plain_store_width`.
fn plain_store_width(opcode: X86Opcode) -> Option<i64> {
    use X86Opcode::*;
    match opcode {
        MovMR8 => Some(1),
        MovMR16 => Some(2),
        MovMR32 => Some(4),
        MovMR => Some(8),
        MovssMR => Some(4),
        MovsdMR => Some(8),
        MovdquMR | MovdqaMR => Some(16),
        _ => None,
    }
}

fn movrr_opcode_for_class(class: RegClass) -> X86Opcode {
    match class {
        RegClass::Gpr32 => X86Opcode::MovRR32,
        _ => X86Opcode::MovRR,
    }
}

/// Fixpoint bound for the frame-address resolver. A `Lea`/`MovRR` chain from a
/// slot root is a handful of links in practice; this only stops a pathological
/// input from making the pass quadratic.
const FRAME_RESOLVE_ROUNDS: usize = 8;

/// Vreg id -> `(slot, byte offset)` for every vreg with EXACTLY ONE definition
/// in the whole function whose def chain grounds in `Lea [StackSlot(s) + k]`.
///
/// # Why this is sound
///
/// A frame address is a pure function of the frame pointer, which is invariant
/// for the whole body. With exactly one static definition, the vreg therefore
/// holds that same address at every program point where it is live — including
/// inside a loop, and on every path. This is the same argument
/// `x86_64::pipeline`'s `X86SpillRemat::FrameAddr` uses to recompute a spilled
/// frame address at an arbitrary later point, and the same one
/// `x86_licm::resolve_frame_address` uses.
///
/// Multi-def vregs are EXCLUDED: a second definition makes the vreg a
/// path-sensitive carrier rather than a value, and this pass has no dataflow
/// with which to tell the paths apart. `MovRR32` is excluded because a 32-bit
/// copy truncates an address, and any instruction carrying `proof_origin` or
/// non-default flags is excluded because its semantics are not this pass's to
/// assume.
fn build_frame_addresses(func: &X86ISelFunction) -> HashMap<u32, (u32, i64)> {
    let mut def_counts: HashMap<u32, usize> = HashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            for def in crate::effects::x86_may_defined_vregs(inst) {
                *def_counts.entry(def.id).or_insert(0) += 1;
            }
        }
    }

    let clean = |inst: &X86ISelInst| {
        inst.proof_origin.is_none() && inst.flags == inst.opcode.default_flags()
    };
    let single_def = |v: &VReg| def_counts.get(&v.id).copied().unwrap_or(0) == 1;

    let mut frame: HashMap<u32, (u32, i64)> = HashMap::default();
    for _ in 0..FRAME_RESOLVE_ROUNDS {
        let before = frame.len();
        for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for inst in &block.insts {
                if !clean(inst) {
                    continue;
                }
                match (inst.opcode, inst.operands.as_slice()) {
                    (
                        X86Opcode::Lea,
                        [
                            X86ISelOperand::VReg(dst),
                            X86ISelOperand::MemAddr { base, disp },
                        ],
                    ) if single_def(dst) => {
                        let resolved = match base.as_ref() {
                            X86ISelOperand::StackSlot(slot) => Some((*slot, 0i64)),
                            X86ISelOperand::VReg(src) => frame.get(&src.id).copied(),
                            _ => None,
                        };
                        if let Some((slot, off)) = resolved
                            && let Some(off) = off.checked_add(i64::from(*disp))
                        {
                            frame.insert(dst.id, (slot, off));
                        }
                    }
                    (X86Opcode::MovRR, [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)])
                        if single_def(dst) =>
                    {
                        if let Some(addr) = frame.get(&src.id).copied() {
                            frame.insert(dst.id, addr);
                        }
                    }
                    _ => {}
                }
            }
        }
        if frame.len() == before {
            break;
        }
    }
    frame
}

/// `Some(range)` iff `operand` addresses a known `Fixed` frame slot at a
/// constant displacement and `[disp, disp+width)` lies wholly inside it (rules 1
/// and 2). The base may be a bare `StackSlot` or a vreg `frame` grounds.
fn direct_slot_range(
    func: &X86ISelFunction,
    frame: &HashMap<u32, (u32, i64)>,
    operand: &X86ISelOperand,
    width: i64,
) -> Option<SlotRange> {
    let X86ISelOperand::MemAddr { base, disp } = operand else {
        return None;
    };
    let (slot, base_off) = match base.as_ref() {
        X86ISelOperand::StackSlot(slot) => (*slot, 0i64),
        X86ISelOperand::VReg(r) => *frame.get(&r.id)?,
        _ => return None,
    };
    let slot = &slot;
    let info: &StackSlotInfo = func.stack_slots.get(*slot as usize)?;
    if info.allocation != StackSlotAllocationKind::Fixed {
        return None;
    }
    let disp = base_off.checked_add(i64::from(*disp))?;
    if disp < 0 || disp.checked_add(width)? > i64::from(info.size) {
        return None;
    }
    Some(SlotRange {
        slot: *slot,
        disp,
        width,
    })
}

/// Whether any operand other than operand 0 names a frame ADDRESS through a
/// memory operand. Rule 6 admits a precise kill only when the instruction's only
/// frame memory reference is the destination it is storing to.
///
/// A bare `VReg` operand holding a frame address does NOT count: that is the
/// stored VALUE, and storing a pointer does not write what it points at.
fn mentions_frame_memory_outside_operand0(
    inst: &X86ISelInst,
    frame: &HashMap<u32, (u32, i64)>,
) -> bool {
    inst.operands
        .iter()
        .skip(1)
        .any(|op| operand_names_frame_memory(op, frame))
}

fn operand_names_frame_memory(operand: &X86ISelOperand, frame: &HashMap<u32, (u32, i64)>) -> bool {
    let grounds = |op: &X86ISelOperand| match op {
        X86ISelOperand::StackSlot(_) => true,
        X86ISelOperand::VReg(r) => frame.contains_key(&r.id),
        _ => false,
    };
    match operand {
        X86ISelOperand::StackSlot(_) => true,
        X86ISelOperand::MemAddr { base, .. } => grounds(base),
        X86ISelOperand::SibMemAddr { base, index, .. } => grounds(base) || grounds(index),
        _ => false,
    }
}

/// Whether `inst` forces the whole map to be discarded (rule 7's non-memory
/// half).
///
/// ⚑ `InstFlags::HAS_SIDE_EFFECTS` is deliberately NOT in this test, and that is
/// the one subtle thing here. On x86 every plain store carries it (so DCE cannot
/// elide a store whose value looks dead), and so does every `Cmp`/`Test` (so a
/// flag write is not treated as pure). Using it as a barrier would make this
/// pass clear its map at exactly the store it is supposed to forward FROM, and
/// again at every compare, which is how the first version of this function
/// managed to be sound and completely inert. What this pass needs to know about
/// an instruction is whether it WRITES MEMORY, and `x86_inst_effect` answers
/// that; a write is then handled by rules 6 and 7 rather than here.
fn is_barrier(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;
    if inst.proof_origin.is_some() {
        return true;
    }
    // The atomics and `Mfence` also set WRITES_MEMORY, so rule 7 would catch
    // them; they are named anyway because their register effects are modelled
    // nowhere in this pass.
    if matches!(
        inst.opcode,
        X86Opcode::Phi
            | X86Opcode::StackAlloc
            | X86Opcode::Mfence
            | X86Opcode::Xchg
            | X86Opcode::Cmpxchg
            | X86Opcode::Cmpxchg8
            | X86Opcode::Cmpxchg16
            | X86Opcode::AtomicLoadCmpxchg16b
            | X86Opcode::AtomicRmwCasLoop
            | X86Opcode::AtomicRmwCasLoop8
            | X86Opcode::AtomicRmwCasLoop16
    ) {
        return true;
    }
    flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.is_pseudo()
}

/// One admitted change. Positions refer to the block's PRE-edit instruction
/// list; rewrites are applied in place and deletions afterwards in a single
/// `retain`, so no position goes stale mid-application.
enum Action {
    Rewrite {
        index: usize,
        dst: VReg,
        source: VReg,
    },
    Delete {
        index: usize,
    },
}

/// Whether `inst` transfers control without clobbering any register or touching
/// memory, so the state accumulated before it is exactly what a
/// single-predecessor successor sees on entry. Mirrors
/// `x86_cse::is_pure_control_flow_terminator`.
fn is_pure_control_flow_terminator(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;
    if flags.is_call() || flags.reads_memory() || flags.writes_memory() || flags.has_side_effects()
    {
        return false;
    }
    matches!(
        inst.opcode,
        X86Opcode::Jmp | X86Opcode::Jcc | X86Opcode::Ret
    )
}

/// The unique predecessor to seed `block` from, when cross-block propagation is
/// provably sound for it. A direct port of `x86_cse::single_pred_source`; its doc
/// comment carries the full soundness argument.
fn single_pred_source(
    block: &Block,
    predecessors: &crate::fast_hash::FxHashMap<Block, Vec<Block>>,
    order_index: &HashMap<Block, usize>,
) -> Option<Block> {
    let preds = predecessors.get(block)?;
    if preds.len() != 1 {
        return None;
    }
    let pred = preds[0];
    if pred == *block {
        return None;
    }
    let (Some(&pred_pos), Some(&block_pos)) = (order_index.get(&pred), order_index.get(block))
    else {
        return None;
    };
    (pred_pos < block_pos).then_some(pred)
}

fn run_impl(func: &mut X86ISelFunction, rewrites: &mut usize, deletions: &mut usize) -> bool {
    let mut changed = false;
    let mut census = BlockCensus::default();
    let frame = build_frame_addresses(func);
    census.frame_addresses = frame.len();
    let block_ids: Vec<_> = func.block_order.clone();
    let order_index: HashMap<Block, usize> =
        block_ids.iter().enumerate().map(|(i, b)| (*b, i)).collect();
    let predecessors = crate::mach_view::predecessor_map(func);

    // PLAN every block first, in `block_order`, carrying each block's exit state
    // forward. Planning reads `func` immutably and the applied edits never change
    // what the planner recorded (a rewrite still defines the load's destination;
    // a deletion removes a load whose destination already held the value), so
    // planning ahead of applying is consistent with applying as we go.
    let mut plans: Vec<(Block, Vec<Action>)> = Vec::new();
    let mut block_exit: HashMap<Block, HashMap<SlotRange, VReg>> = HashMap::default();
    for block_id in &block_ids {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        let entry = single_pred_source(block_id, &predecessors, &order_index)
            .and_then(|pred| block_exit.get(&pred).cloned())
            .unwrap_or_default();
        let (plan, exit) = plan_block(func, &frame, &block.insts, entry, &mut census);
        block_exit.insert(*block_id, exit);
        if !plan.is_empty() {
            plans.push((*block_id, plan));
        }
    }

    for (block_id, plan) in plans {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };
        let mut doomed: HashSet<usize> = HashSet::default();
        for action in plan {
            match action {
                Action::Rewrite { index, dst, source } => {
                    block.insts[index] = X86ISelInst::new(
                        movrr_opcode_for_class(dst.class),
                        vec![X86ISelOperand::VReg(dst), X86ISelOperand::VReg(source)],
                    );
                    *rewrites += 1;
                    changed = true;
                }
                Action::Delete { index } => {
                    doomed.insert(index);
                    *deletions += 1;
                    changed = true;
                }
            }
        }
        if !doomed.is_empty() {
            let mut idx = 0usize;
            block.insts.retain(|_| {
                let keep = !doomed.contains(&idx);
                idx += 1;
                keep
            });
        }
    }

    if trace_enabled() {
        trace!(
            "{}: {} rewritten, {} deleted | tracked-load opcodes {} of which {} resolve to a slot; \
             store opcodes {} of which {} resolve; barriers {}; unresolved writes {}; \
             frame addresses resolved {}",
            func.name,
            rewrites,
            deletions,
            census.tracked_load_opcodes,
            census.loads_resolving_to_a_slot,
            census.store_opcodes,
            census.stores_resolving_to_a_slot,
            census.barriers,
            census.unresolved_writes,
            census.frame_addresses,
        );
    }
    changed
}

/// What a block offered this pass, whether or not anything was rewritten. The
/// pass's first version fired on NOTHING across the whole runtime corpus, and no
/// per-hit trace could say why — a census of the shapes actually present is the
/// instrument that answers it.
#[derive(Debug, Default, Clone, Copy)]
struct BlockCensus {
    tracked_load_opcodes: usize,
    loads_resolving_to_a_slot: usize,
    store_opcodes: usize,
    stores_resolving_to_a_slot: usize,
    barriers: usize,
    unresolved_writes: usize,
    /// How many vregs the frame-address resolver grounded. Zero here with a
    /// nonzero load count is the exact signature of the pass's first, inert
    /// version.
    frame_addresses: usize,
}

/// Plan one block and return its exit state for a single-predecessor successor.
fn plan_block(
    func: &X86ISelFunction,
    frame: &HashMap<u32, (u32, i64)>,
    insts: &[X86ISelInst],
    entry: HashMap<SlotRange, VReg>,
    census: &mut BlockCensus,
) -> (Vec<Action>, HashMap<SlotRange, VReg>) {
    let mut available = entry;
    let mut plan: Vec<Action> = Vec::new();
    // Snapshotted immediately before the FIRST pure control-flow terminator,
    // which `is_barrier` is about to clear the map at. A later terminator sees a
    // cleared map and must not overwrite the snapshot.
    let mut exit: Option<HashMap<SlotRange, VReg>> = None;

    for (index, inst) in insts.iter().enumerate() {
        if is_barrier(inst) {
            census.barriers += 1;
            if exit.is_none() && is_pure_control_flow_terminator(inst) {
                exit = Some(available.clone());
            }
            available.clear();
            continue;
        }

        if tracked_load(inst.opcode).is_some() {
            census.tracked_load_opcodes += 1;
        }
        if plain_store_width(inst.opcode).is_some() {
            census.store_opcodes += 1;
        }

        // A LOAD this pass understands. The lookup must happen before this
        // instruction's own definition kills anything, because the value it
        // wants is the one available on ENTRY to it.
        if let Some((width, class)) = tracked_load(inst.opcode)
            && let Some(mem) = inst.operands.get(1)
            && let Some(range) = direct_slot_range(func, frame, mem, width)
            && let Some(X86ISelOperand::VReg(dst)) = inst.operands.first()
            && dst.class == class
            && inst.operands.len() == 2
        {
            census.loads_resolving_to_a_slot += 1;
            if let Some(source) = available.get(&range).copied()
                && source.class == class
            {
                if source.id == dst.id {
                    trace!(
                        "delete {index}: slot {}+{} ({}B) already in v{}",
                        range.slot, range.disp, range.width, dst.id
                    );
                    plan.push(Action::Delete { index });
                    // The destination keeps the value it already held, so the
                    // entry stays valid and no def kill is owed.
                    continue;
                }
                trace!(
                    "forward {index}: slot {}+{} ({}B) v{} <- v{}",
                    range.slot, range.disp, range.width, dst.id, source.id
                );
                plan.push(Action::Rewrite {
                    index,
                    dst: *dst,
                    source,
                });
                // The replacement copy still defines `dst`.
                kill_value_defs(&mut available, *dst);
                available.insert(range, *dst);
                continue;
            }
            kill_value_defs(&mut available, *dst);
            available.insert(range, *dst);
            continue;
        }

        if x86_inst_effect(inst).writes_memory() {
            let precise = plain_store_width(inst.opcode)
                .filter(|_| !mentions_frame_memory_outside_operand0(inst, frame))
                .and_then(|width| {
                    inst.operands
                        .first()
                        .and_then(|mem| direct_slot_range(func, frame, mem, width))
                });
            match precise {
                // Rule 6: kill exactly the overlapping entries of this slot.
                Some(range) => {
                    census.stores_resolving_to_a_slot += 1;
                    available.retain(|tracked, _| !tracked.overlaps(&range));
                    if let Some((store_width, store_class)) = tracked_store(inst.opcode)
                        && store_width == range.width
                        && inst.operands.len() == 2
                        && let Some(X86ISelOperand::VReg(src)) = inst.operands.get(1)
                        && src.class == store_class
                    {
                        available.insert(range, *src);
                    }
                }
                // Rule 7: anything else that writes memory clears everything.
                None => {
                    census.unresolved_writes += 1;
                    available.clear();
                }
            }
        }

        for def in crate::effects::x86_may_defined_vregs(inst) {
            kill_value_defs(&mut available, def);
        }
    }

    // A block with no terminator at all (the planner is also used on synthetic
    // single-block functions in tests) exports whatever it ended holding.
    (plan, exit.unwrap_or(available))
}

/// Rule 5: a def of an entry's VALUE register kills that entry. The comparison
/// is CLASS-BLIND — a same-id vreg at another class is an aliased width view of
/// the same storage.
fn kill_value_defs(available: &mut HashMap<SlotRange, VReg>, def: VReg) {
    available.retain(|_, value| value.id != def.id);
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::types::Type;

    fn v(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn v32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn slot(slot: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(X86ISelOperand::StackSlot(slot)),
            disp,
        }
    }

    fn thru(id: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(v(id)),
            disp,
        }
    }

    fn load(dst: u32, mem: X86ISelOperand) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::MovRM, vec![v(dst), mem])
    }

    fn store(mem: X86ISelOperand, src: u32) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::MovMR, vec![mem, v(src)])
    }

    /// One block holding `insts`, plus the given fixed-slot sizes.
    fn one_block(insts: Vec<X86ISelInst>, slot_sizes: &[u32]) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("f".to_string(), sig);
        func.ensure_block(Block(0));
        func.next_vreg = 128;
        func.stack_slots = slot_sizes
            .iter()
            .map(|size| StackSlotInfo::new(*size, 8))
            .collect();
        let block = func.blocks.get_mut(&Block(0)).unwrap();
        block.insts = insts;
        func
    }

    fn insts(func: &X86ISelFunction) -> &[X86ISelInst] {
        &func.blocks.get(&Block(0)).unwrap().insts
    }

    fn opcodes(func: &X86ISelFunction) -> Vec<X86Opcode> {
        insts(func).iter().map(|i| i.opcode).collect()
    }

    /// (B) load-to-load reuse: the second load of the same slot range becomes a
    /// register copy.
    #[test]
    fn second_load_of_the_same_slot_range_becomes_a_copy() {
        // The shift writes a COPY of the loaded value, exactly as the xorshift
        // sequence this was written for does. Shifting v10 in place would kill
        // the entry under rule 5, which the width-view test covers separately.
        let mut func = one_block(
            vec![
                load(10, slot(0, 0)),
                X86ISelInst::new(X86Opcode::MovRR, vec![v(20), v(10)]),
                X86ISelInst::new(X86Opcode::ShlRI, vec![v(20), X86ISelOperand::Imm(13)]),
                load(11, slot(0, 0)),
            ],
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(
            pass.run(&mut func),
            "the redundant reload must be rewritten"
        );
        assert_eq!(pass.last_run_rewrites(), 1);
        assert_eq!(pass.last_run_deletions(), 0);
        assert_eq!(
            opcodes(&func),
            vec![
                X86Opcode::MovRM,
                X86Opcode::MovRR,
                X86Opcode::ShlRI,
                X86Opcode::MovRR
            ]
        );
        assert_eq!(insts(&func)[3].operands, vec![v(11), v(10)]);
    }

    /// (A) store-to-load forward: the load after a store of the same range reads
    /// the stored register instead of memory.
    #[test]
    fn load_after_a_store_of_the_same_range_reads_the_stored_register() {
        let mut func = one_block(vec![store(slot(0, 0), 7), load(11, slot(0, 0))], &[8]);
        let mut pass = X86SlotForward::new();
        assert!(pass.run(&mut func));
        assert_eq!(pass.last_run_rewrites(), 1);
        assert_eq!(
            opcodes(&func),
            vec![X86Opcode::MovMR, X86Opcode::MovRR],
            "{:?}",
            insts(&func)
        );
        assert_eq!(insts(&func)[1].operands, vec![v(11), v(7)]);
    }

    /// A load whose value is already in its OWN destination is deleted, not
    /// rewritten to a self-copy.
    #[test]
    fn a_reload_into_the_same_register_is_deleted() {
        let mut func = one_block(
            vec![
                load(10, slot(0, 0)),
                X86ISelInst::new(X86Opcode::MovRR, vec![v(20), v(10)]),
                load(10, slot(0, 0)),
            ],
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(pass.run(&mut func));
        assert_eq!(pass.last_run_deletions(), 1);
        assert_eq!(pass.last_run_rewrites(), 0);
        assert_eq!(opcodes(&func), vec![X86Opcode::MovRM, X86Opcode::MovRR]);
    }

    /// Rule 6: an overlapping store to the same slot kills the entry. A 4-byte
    /// store at +0 must defeat an 8-byte entry at +0.
    #[test]
    fn an_overlapping_narrower_store_kills_the_entry() {
        let mut func = one_block(
            vec![
                load(10, slot(0, 0)),
                X86ISelInst::new(X86Opcode::MovMR32, vec![slot(0, 0), v32(9)]),
                load(11, slot(0, 0)),
            ],
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func), "the reload must survive");
        assert_eq!(
            opcodes(&func),
            vec![X86Opcode::MovRM, X86Opcode::MovMR32, X86Opcode::MovRM]
        );
    }

    /// Rule 6 the other way: a store to a DISJOINT range of the same slot does
    /// NOT kill the entry. Without this the pass would be sound but useless on
    /// any multi-field slot, and the `overlaps` arithmetic would be untested in
    /// the negative direction.
    #[test]
    fn a_disjoint_store_to_the_same_slot_leaves_the_entry_alive() {
        let mut func = one_block(
            vec![
                load(10, slot(0, 0)),
                store(slot(0, 8), 9),
                load(11, slot(0, 0)),
            ],
            &[16],
        );
        let mut pass = X86SlotForward::new();
        assert!(pass.run(&mut func));
        assert_eq!(pass.last_run_rewrites(), 1);
        assert_eq!(insts(&func)[2].operands, vec![v(11), v(10)]);
    }

    /// Rule 7: a store through a REGISTER could name this slot for all this pass
    /// knows, so it clears everything.
    #[test]
    fn a_store_through_a_register_clears_the_map() {
        let mut func = one_block(
            vec![
                load(10, slot(0, 0)),
                store(thru(5, 0), 9),
                load(11, slot(0, 0)),
            ],
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func), "an unresolved write must clear");
        assert_eq!(
            opcodes(&func),
            vec![X86Opcode::MovRM, X86Opcode::MovMR, X86Opcode::MovRM]
        );
    }

    /// Rule 7: a SIB-addressed store is unresolvable even with a slot base,
    /// because the index is a runtime value.
    #[test]
    fn a_sib_store_off_the_same_slot_clears_the_map() {
        let sib = X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::StackSlot(0)),
            index: Box::new(v(4)),
            scale: 8,
            disp: 0,
        };
        let mut func = one_block(
            vec![
                load(10, slot(0, 0)),
                X86ISelInst::new(X86Opcode::MovMRSib, vec![sib, v(9)]),
                load(11, slot(0, 0)),
            ],
            &[64],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func));
        assert_eq!(
            opcodes(&func),
            vec![X86Opcode::MovRM, X86Opcode::MovMRSib, X86Opcode::MovRM]
        );
    }

    /// Rule 7: a call clears everything (a callee can write any slot whose
    /// address it was handed, and this pass does not track which those are).
    #[test]
    fn a_call_clears_the_map() {
        let mut func = one_block(
            vec![
                load(10, slot(0, 0)),
                X86ISelInst::new(
                    X86Opcode::Call,
                    vec![X86ISelOperand::Symbol("callee".to_string())],
                ),
                load(11, slot(0, 0)),
            ],
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func));
        assert_eq!(opcodes(&func)[2], X86Opcode::MovRM);
    }

    /// Rule 5: redefining the register that holds the value kills the entry,
    /// and the kill is CLASS-BLIND — the redefinition here is of the SAME id at
    /// `Gpr32`, an aliased width view of the same storage.
    #[test]
    fn a_narrow_width_view_redefinition_kills_the_entry() {
        let mut func = one_block(
            vec![
                load(10, slot(0, 0)),
                X86ISelInst::new(X86Opcode::MovRR32, vec![v32(10), v32(3)]),
                load(11, slot(0, 0)),
            ],
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(
            !pass.run(&mut func),
            "v10's low half was rewritten, so v10 no longer holds the slot"
        );
        assert_eq!(opcodes(&func)[2], X86Opcode::MovRM);
    }

    /// Rule 3: a 4-byte store does not satisfy an 8-byte load. The width is part
    /// of the key, so this is a MISS rather than a bad forward.
    #[test]
    fn a_narrow_store_does_not_satisfy_a_wide_load() {
        let mut func = one_block(
            vec![
                X86ISelInst::new(X86Opcode::MovMR32, vec![slot(0, 0), v32(9)]),
                load(11, slot(0, 0)),
            ],
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func));
        assert_eq!(opcodes(&func)[1], X86Opcode::MovRM);
    }

    /// Rule 2: an access that would run past the end of its slot is not tracked
    /// at all, so nothing is forwarded through it.
    #[test]
    fn an_out_of_bounds_access_is_not_tracked() {
        let mut func = one_block(
            vec![load(10, slot(0, 4)), load(11, slot(0, 4))],
            // 8-byte slot, 8-byte load at +4 runs 4 bytes past the end.
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func));
        assert_eq!(opcodes(&func), vec![X86Opcode::MovRM, X86Opcode::MovRM]);
    }

    /// Rule 2: a runtime-sized slot is refused (its bound is not a constant, so
    /// the in-bounds argument cannot be made).
    #[test]
    fn a_runtime_sized_slot_is_refused() {
        let mut func = one_block(vec![load(10, slot(0, 0)), load(11, slot(0, 0))], &[8]);
        func.stack_slots = vec![StackSlotInfo::new_dynamic(
            trust_cg_ir::function::StackSlotSizeSource::Unknown,
            8,
        )];
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func));
        assert_eq!(opcodes(&func), vec![X86Opcode::MovRM, X86Opcode::MovRM]);
    }

    /// Wire a two-or-three block function: bb0 -> bb_last, plus optionally a
    /// second predecessor bb2 -> bb_last so the last block is a MERGE point.
    fn linear_blocks(
        head: Vec<X86ISelInst>,
        tail: Vec<X86ISelInst>,
        second_pred: bool,
        slot_sizes: &[u32],
    ) -> X86ISelFunction {
        let last = if second_pred { Block(2) } else { Block(1) };
        let mut func = one_block(head, slot_sizes);
        {
            let bb0 = func.blocks.get_mut(&Block(0)).unwrap();
            bb0.insts.push(X86ISelInst::new(
                X86Opcode::Jmp,
                vec![X86ISelOperand::Block(last)],
            ));
            bb0.successors = vec![last];
        }
        if second_pred {
            func.ensure_block(Block(1));
            let bb1 = func.blocks.get_mut(&Block(1)).unwrap();
            bb1.insts = vec![X86ISelInst::new(
                X86Opcode::Jmp,
                vec![X86ISelOperand::Block(last)],
            )];
            bb1.successors = vec![last];
        }
        func.ensure_block(last);
        let bb = func.blocks.get_mut(&last).unwrap();
        bb.insts = tail;
        bb.insts.push(X86ISelInst::new(X86Opcode::Ret, vec![]));
        func
    }

    /// A block with exactly ONE forward predecessor is seeded from that
    /// predecessor's exit state: the store at the end of bb0 satisfies the load
    /// at the start of bb1. This is the shape the corpus actually needs — a `Vec`
    /// length stored in one block and reloaded in the next.
    #[test]
    fn a_single_forward_predecessor_seeds_the_successor() {
        let mut func = linear_blocks(
            vec![store(slot(0, 0), 7)],
            vec![load(11, slot(0, 0))],
            false,
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(pass.run(&mut func));
        assert_eq!(pass.last_run_rewrites(), 1);
        let tail = &func.blocks.get(&Block(1)).unwrap().insts;
        assert_eq!(tail[0].opcode, X86Opcode::MovRR);
        assert_eq!(tail[0].operands, vec![v(11), v(7)]);
    }

    /// A MERGE point is seeded from nothing. Only one of its predecessors stored
    /// to the slot, so the value is not available on every path and forwarding
    /// would miscompile the other one. This is the single most important negative
    /// in the pass: the positive above and this share one code path.
    #[test]
    fn a_merge_point_is_seeded_from_nothing() {
        let mut func = linear_blocks(
            vec![store(slot(0, 0), 7)],
            vec![load(11, slot(0, 0))],
            true,
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(
            !pass.run(&mut func),
            "a two-predecessor block must not be seeded"
        );
        assert_eq!(
            func.blocks.get(&Block(2)).unwrap().insts[0].opcode,
            X86Opcode::MovRM
        );
    }

    /// A block whose tail contains a CALL exports nothing, even though its
    /// terminator is a pure jump: the call is a barrier and clears the map before
    /// the snapshot is taken.
    #[test]
    fn a_call_in_the_predecessor_tail_exports_nothing() {
        let mut func = linear_blocks(
            vec![
                store(slot(0, 0), 7),
                X86ISelInst::new(
                    X86Opcode::Call,
                    vec![X86ISelOperand::Symbol("callee".to_string())],
                ),
            ],
            vec![load(11, slot(0, 0))],
            false,
            &[8],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func));
        assert_eq!(
            func.blocks.get(&Block(1)).unwrap().insts[0].opcode,
            X86Opcode::MovRM
        );
    }

    /// The shape that actually occurs in x86 ISel output: the frame address is
    /// materialized by a `Lea` root and every access goes through it, so both the
    /// store and the two loads name `[root + 8]` rather than `[StackSlot+8]`.
    /// Without [`build_frame_addresses`] this whole pass is inert, and this is
    /// the test that says so — it is the corpus shape reduced to five
    /// instructions.
    #[test]
    fn a_lea_rooted_access_resolves_and_forwards() {
        let mut func = one_block(
            vec![
                X86ISelInst::new(X86Opcode::Lea, vec![v(1), slot(0, 0)]),
                store(thru(1, 8), 7),
                load(11, thru(1, 8)),
                X86ISelInst::new(X86Opcode::MovRR, vec![v(21), v(11)]),
                load(12, thru(1, 8)),
            ],
            &[16],
        );
        let mut pass = X86SlotForward::new();
        assert!(pass.run(&mut func));
        assert_eq!(pass.last_run_rewrites(), 2, "both loads must be satisfied");
        assert_eq!(
            opcodes(&func),
            vec![
                X86Opcode::Lea,
                X86Opcode::MovMR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR
            ]
        );
        // The store's source satisfies the first load; the first load's
        // destination then satisfies the second.
        assert_eq!(insts(&func)[2].operands, vec![v(11), v(7)]);
        assert_eq!(insts(&func)[4].operands, vec![v(12), v(11)]);
    }

    /// A `Lea` chain and a full-width copy both carry a frame address; the
    /// resolver must follow them, and the displacements must ADD.
    #[test]
    fn a_lea_chain_and_a_copy_both_carry_the_frame_address() {
        let mut func = one_block(
            vec![
                X86ISelInst::new(X86Opcode::Lea, vec![v(1), slot(0, 0)]),
                X86ISelInst::new(X86Opcode::Lea, vec![v(2), thru(1, 8)]),
                X86ISelInst::new(X86Opcode::MovRR, vec![v(3), v(2)]),
                store(thru(3, 0), 7),
                // [slot0 + 8] via the chain == [slot0 + 8] via the root.
                load(11, thru(1, 8)),
            ],
            &[16],
        );
        let mut pass = X86SlotForward::new();
        assert!(pass.run(&mut func));
        assert_eq!(pass.last_run_rewrites(), 1);
        assert_eq!(insts(&func)[4].operands, vec![v(11), v(7)]);
    }

    /// A MULTI-def base is a path-sensitive carrier, not a value: the resolver
    /// must refuse it even though one of its definitions is a frame address.
    /// Without this the pass would forward across a conditional reassignment of
    /// the base and miscompile.
    #[test]
    fn a_multi_def_base_is_refused() {
        let mut func = one_block(
            vec![
                X86ISelInst::new(X86Opcode::Lea, vec![v(1), slot(0, 0)]),
                store(thru(1, 0), 7),
                // A second definition of the base, to something unknown.
                X86ISelInst::new(X86Opcode::MovRR, vec![v(1), v(9)]),
                load(11, thru(1, 0)),
            ],
            &[16],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func), "a multi-def base must not resolve");
        assert_eq!(opcodes(&func)[3], X86Opcode::MovRM);
    }

    /// A 32-bit copy TRUNCATES an address, so it does not carry one.
    #[test]
    fn a_narrow_copy_does_not_carry_the_frame_address() {
        let mut func = one_block(
            vec![
                X86ISelInst::new(X86Opcode::Lea, vec![v(1), slot(0, 0)]),
                X86ISelInst::new(X86Opcode::MovRR32, vec![v32(2), v32(1)]),
                store(thru(2, 0), 7),
                load(11, thru(2, 0)),
            ],
            &[16],
        );
        let mut pass = X86SlotForward::new();
        assert!(!pass.run(&mut func));
        assert_eq!(opcodes(&func)[3], X86Opcode::MovRM);
    }

    /// The pass is DEFAULT ON. Falsifiability arm: the SAME input under the
    /// opt-out must keep the load, so a function this pass silently failed to
    /// touch cannot satisfy the first half vacuously.
    ///
    /// The opt-out is spelled through the BUILDER, not through
    /// [`set_slot_forward_disabled`]: that installer writes a process-global
    /// `OnceLock`, so a test using it would decide the default for every other
    /// test in this binary and the suite's outcome would depend on thread
    /// scheduling.
    #[test]
    fn default_on_and_the_opt_out_restores_the_load() {
        let build = || one_block(vec![store(slot(0, 0), 7), load(11, slot(0, 0))], &[8]);

        let mut on = build();
        assert!(
            X86SlotForward::new().run(&mut on),
            "DEFAULT ON: the forward must happen with no knob set"
        );
        assert_eq!(opcodes(&on)[1], X86Opcode::MovRR);

        let mut off = build();
        assert!(!X86SlotForward::new().with_enabled(false).run(&mut off));
        assert_eq!(opcodes(&off)[1], X86Opcode::MovRM);
    }
}
