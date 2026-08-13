// trust-cg-opt - x86-64 Common Subexpression Elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Conservative common-subexpression elimination for x86-64 ISel-output functions.
//!
//! This pass tracks available expressions, caps the number of tracked
//! expressions, and only rewrites duplicate pure virtual-register computations
//! into virtual-register copies at the duplicate point. It never crosses
//! memory, call, side-effect, fixed-register, or flag barriers within a block.
//!
//! # Cross-block (global) availability
//!
//! In addition to intra-block CSE, the pass performs a provably-sound,
//! restricted form of *global* CSE: when a block has exactly one predecessor
//! reached by a forward edge, its entry available set is seeded from that
//! predecessor's exit set (flag-dependent expressions are dropped at the
//! boundary). This eliminates redundant computations that flow straight from a
//! dominating block into a single-entry successor (the common
//! guard-then-body and straight-line-split shapes) without the unsoundness
//! hazards of merge points or loops. See `single_pred_source` for the full
//! soundness argument. The pass runs only at O2+ (it is wired into the O2
//! pass manager, not O0/O1).
//!
//! ## GLOBAL CSE — design note for the remaining (multi-predecessor) cases
//!
//! The single-predecessor propagation above is the sound subset of a full
//! available-expression dataflow. Extending to merge points and loops requires:
//!
//!   1. **CFG + dominators.** Build predecessor/successor maps (already done
//!      here via the shared `crate::mach_view::predecessor_map`) and a
//!      dominator tree over `X86ISelFunction`'s `Block` CFG
//!      (`crate::mach_view::compute_idom` / `CfgAnalysis` provide the
//!      generalized implementation). ISel output is single-assignment over
//!      vregs, which is what makes "an expression's def dominates the use"
//!      equivalent to "the value is still live at the use".
//!
//!   2. **Forward dataflow with a meet over predecessors.** Compute, per block,
//!      `in[B] = ∩ over preds P of out[P]` and
//!      `out[B] = (in[B] \ kill[B]) ∪ gen[B]`, iterating to a fixpoint. The
//!      intersection at merge points is the crucial soundness step: an
//!      expression is available at `B` only if available on EVERY path into
//!      `B`. Loops require fixpoint iteration with a monotone lattice (start
//!      `out[B] = ⊤` for non-entry blocks) so back-edges converge.
//!
//!   3. **Barrier/kill sets.** `kill[B]` must remove every expression whose
//!      source vreg is redefined in `B`, every flag-dependent expression when
//!      `B` writes flags, and ALL expressions across a hard barrier
//!      (call/memory/side-effect/pseudo/Phi/StackAlloc). The intra-block
//!      invalidation here (`invalidate_available_with_vreg`,
//!      `invalidate_available_depending_on_flags`, `is_hard_barrier`) is the
//!      per-block transfer function and can be reused.
//!
//!   4. **Rewrite legality at the use.** When replacing a redundant
//!      computation in `B` with a copy of an available def `d`, `d` must
//!      dominate `B` (guaranteed by the meet, since `d`'s defining expression
//!      is in `in[B]` only if it reaches along all paths) AND `d` must not be a
//!      fixed physical register or cross an ABI clobber. Flag-dependent
//!      expressions remain restricted to the cases where the producing flags
//!      are provably unclobbered along all incoming paths — easiest to keep
//!      dropping them at merge points, as the single-pred path already does.
//!
//! Until that iterative dataflow is implemented and verified against the
//! differential oracle, the pass stays at the single-predecessor subset rather
//! than shipping a half-done multi-predecessor analysis that could be unsound
//! at merges or loops.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::{InstFlags, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{x86_inst_effect, x86_produces_value, x86_reads_flags, x86_writes_flags};
use crate::mach_view::predecessor_map;
use crate::x86_pass_manager::X86MachinePass;

const MAX_AVAILABLE_EXPRS: usize = 64;
const MAX_SOURCE_OPERANDS: usize = 4;

/// Common subexpression elimination for x86-64 ISel-output machine functions.
pub struct X86CommonSubexpressionElimination;

impl X86CommonSubexpressionElimination {
    /// Run x86 CSE directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86CommonSubexpressionElimination {
    fn name(&self) -> &str {
        "x86-cse"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ExprKey {
    opcode: X86Opcode,
    result_class: RegClass,
    flags: InstFlags,
    operands: Vec<CanonOperand>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CanonOperand {
    VReg(VReg),
    Imm(i64),
    FImm(u64),
    CondCode(u8),
    MemAddr {
        base: Box<CanonOperand>,
        disp: i32,
    },
    SibMemAddr {
        base: Box<CanonOperand>,
        index: Box<CanonOperand>,
        scale: u8,
        disp: i32,
    },
}

#[derive(Debug, Clone)]
struct AvailableExpr {
    def_vreg: VReg,
    source_vregs: HashSet<VReg>,
    depends_on_flags: bool,
}

struct Candidate {
    def_vreg: VReg,
    key: ExprKey,
    source_vregs: HashSet<VReg>,
    depends_on_flags: bool,
}

fn run_impl(func: &mut X86ISelFunction) -> bool {
    let mut changed = false;

    // Cross-block (global) available-expression propagation, restricted to the
    // provably-sound single-predecessor forward case. See `single_pred_source`
    // and the module-level "GLOBAL CSE" note for the soundness argument. The
    // map holds each already-processed block's *exit* available set, keyed by
    // block.
    let order = func.block_order.clone();
    let order_index: HashMap<Block, usize> =
        order.iter().enumerate().map(|(i, b)| (*b, i)).collect();
    let predecessors = predecessor_map(func);
    let mut block_exit: HashMap<Block, HashMap<ExprKey, AvailableExpr>> = HashMap::new();

    for block_id in order {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        // Seed from a single forward predecessor when one exists. Starting
        // empty (the original intra-block behavior) is always sound; seeding
        // only ever adds expressions that are guaranteed available on entry.
        let mut available = match single_pred_source(&block_id, &predecessors, &order_index) {
            Some(pred) => block_exit
                .get(&pred)
                .map(carry_across_edge)
                .unwrap_or_default(),
            None => HashMap::new(),
        };

        // Exit available set used to seed single-predecessor successors. A
        // block's terminator is a `Jmp`/`Jcc`/`Ret`, which `is_hard_barrier`
        // treats as a barrier (clearing `available`). But a *pure*
        // control-flow transfer does not clobber any register, so the values
        // available immediately before it are exactly what the successor sees
        // on entry. We therefore snapshot `available` just before such a
        // terminator. A `Call`/memory/side-effect barrier in the block tail
        // genuinely clobbers state, so it correctly clears the snapshot.
        let mut exit_available: Option<HashMap<ExprKey, AvailableExpr>> = None;

        for index in 0..block.insts.len() {
            if is_hard_barrier(&block.insts[index]) {
                if exit_available.is_none() && is_pure_control_flow_terminator(&block.insts[index])
                {
                    // Register-preserving control transfer: the live exit set
                    // is the availability accumulated up to the FIRST such
                    // terminator (later terminators see a cleared set and must
                    // not overwrite this snapshot).
                    exit_available = Some(available.clone());
                }
                available.clear();
                continue;
            }

            if x86_writes_flags(block.insts[index].opcode) {
                invalidate_available_depending_on_flags(&mut available);
            }

            if let Some(def) = defined_vreg(&block.insts[index]) {
                invalidate_available_with_vreg(&mut available, def);
            }

            let Some(candidate) = make_candidate(&block.insts, index) else {
                if x86_writes_flags(block.insts[index].opcode) {
                    available.clear();
                }
                continue;
            };

            if let Some(avail) = available.get(&candidate.key) {
                block.insts[index] = X86ISelInst::new(
                    movrr_opcode_for_class(candidate.def_vreg.class),
                    vec![
                        X86ISelOperand::VReg(candidate.def_vreg),
                        X86ISelOperand::VReg(avail.def_vreg),
                    ],
                );
                changed = true;
                continue;
            }

            if available.len() >= MAX_AVAILABLE_EXPRS {
                available.clear();
            }

            available.insert(
                candidate.key,
                AvailableExpr {
                    def_vreg: candidate.def_vreg,
                    source_vregs: candidate.source_vregs,
                    depends_on_flags: candidate.depends_on_flags,
                },
            );
        }

        // Record this block's exit available set for downstream single-pred
        // successors. If the block ended in a pure control-flow terminator we
        // captured the register-preserving snapshot above; otherwise (e.g. a
        // block with no terminator, or one whose tail barrier clobbered state)
        // `available` holds the post-tail state.
        let exit = exit_available.unwrap_or(available);
        block_exit.insert(block_id, exit);
    }

    changed
}

/// True for a register-state-preserving control-flow terminator: an
/// unconditional `Jmp`, a conditional `Jcc`, or a `Ret`. These transfer control
/// without clobbering any register, so values available immediately before them
/// remain available to a successor. A `Call` is deliberately excluded: it
/// clobbers caller-saved registers per the ABI and is a true barrier.
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

/// Return the unique predecessor to seed `block` from, when global propagation
/// is provably sound for it.
///
/// SOUNDNESS: we seed `block`'s entry available set from a predecessor `pred`
/// only when BOTH hold:
///
///   1. `block` has exactly one predecessor, `pred`. Every execution that
///      reaches `block` therefore arrives directly from `pred` (edges in this
///      IR carry no instructions), so any value `pred` left in a vreg is still
///      present at `block`'s entry.
///   2. `pred` precedes `block` in `block_order`. Combined with (1) this rules
///      out loop back-edges: a loop header has its preheader AND its latch as
///      predecessors (≥ 2), which fails (1); and the only way a single
///      predecessor could be a back-edge is if it appeared later in the order,
///      which fails (2). Restricting to forward single edges means `pred`'s
///      exit set has already been computed in this same linear pass.
///
/// Because ISel output is single-assignment over virtual registers, a value
/// computed in `pred` is not redefined before `block`, so the carried
/// available expressions remain valid (their source vregs are unchanged and
/// the def vreg holds the same value).
fn single_pred_source(
    block: &Block,
    predecessors: &HashMap<Block, Vec<Block>>,
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
    // Forward edge only: the predecessor must already have been processed.
    if pred_pos < block_pos {
        Some(pred)
    } else {
        None
    }
}

/// Project a predecessor's exit available set onto a successor's entry.
///
/// We drop any flag-dependent expression (e.g. `Setcc`) when crossing a block
/// boundary. Such an expression is only valid while the RFLAGS that produced it
/// are live; rather than reason about RFLAGS liveness across edges we
/// conservatively forget those expressions at the boundary. All flag-INDEPENDENT
/// expressions are carried unchanged.
fn carry_across_edge(exit: &HashMap<ExprKey, AvailableExpr>) -> HashMap<ExprKey, AvailableExpr> {
    exit.iter()
        .filter(|(_, expr)| !expr.depends_on_flags)
        .map(|(key, expr)| (key.clone(), expr.clone()))
        .collect()
}

fn make_candidate(insts: &[X86ISelInst], index: usize) -> Option<Candidate> {
    let inst = &insts[index];
    let flags = inst.flags;

    if !is_supported_cse_opcode(inst.opcode) {
        return None;
    }
    if !x86_inst_effect(inst).is_pure() || !x86_produces_value(inst.opcode) {
        return None;
    }
    if flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.has_side_effects()
        || flags.reads_memory()
        || flags.writes_memory()
        || flags.is_pseudo()
    {
        return None;
    }
    let depends_on_flags = x86_reads_flags(inst.opcode);
    if depends_on_flags && !is_supported_flag_read_cse_opcode(inst.opcode) {
        return None;
    }
    if x86_writes_flags(inst.opcode) && !flags_written_here_are_dead(insts, index) {
        return None;
    }
    if first_operand_is_def_and_use(inst) || inst_touches_fixed_register(inst) {
        return None;
    }

    let def_vreg = match inst.operands.first() {
        Some(X86ISelOperand::VReg(vreg)) if is_supported_result_class(vreg.class) => *vreg,
        _ => return None,
    };

    let source_operands = inst.operands.get(1..)?;
    if source_operands.len() > MAX_SOURCE_OPERANDS {
        return None;
    }

    let mut source_vregs = HashSet::new();
    let mut canon_operands = Vec::with_capacity(source_operands.len());
    for operand in source_operands {
        collect_source_vregs(operand, &mut source_vregs)?;
        canon_operands.push(canon_operand(operand)?);
    }
    if is_commutative_cse_opcode(inst.opcode) && canon_operands.len() == 2 {
        canon_operands.sort_by(canon_operand_cmp);
    }

    if source_vregs.contains(&def_vreg) {
        return None;
    }

    Some(Candidate {
        def_vreg,
        key: ExprKey {
            opcode: inst.opcode,
            result_class: def_vreg.class,
            flags,
            operands: canon_operands,
        },
        source_vregs,
        depends_on_flags,
    })
}

fn is_supported_cse_opcode(opcode: X86Opcode) -> bool {
    use X86Opcode::*;

    matches!(
        opcode,
        MovRR
            | MovRR32
            | MovRI
            | Movzx
            | MovzxW
            | MovsxB
            | MovsxW
            | Movsx
            | Lea
            | LeaSib
            | AddRR
            | SubRR
            | ImulRR
            | ImulRRI
            | AndRR
            | OrRR
            | XorRR
            | Setcc
    )
}

fn is_supported_flag_read_cse_opcode(opcode: X86Opcode) -> bool {
    matches!(opcode, X86Opcode::Setcc)
}

fn is_supported_result_class(class: RegClass) -> bool {
    matches!(class, RegClass::Gpr64 | RegClass::Gpr32)
}

fn is_commutative_cse_opcode(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::AddRR
            | X86Opcode::ImulRR
            | X86Opcode::AndRR
            | X86Opcode::OrRR
            | X86Opcode::XorRR
    )
}

fn movrr_opcode_for_class(class: RegClass) -> X86Opcode {
    match class {
        RegClass::Gpr32 => X86Opcode::MovRR32,
        _ => X86Opcode::MovRR,
    }
}

fn defined_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }

    match inst.operands.first() {
        Some(X86ISelOperand::VReg(vreg)) => Some(*vreg),
        _ => None,
    }
}

fn invalidate_available_with_vreg(available: &mut HashMap<ExprKey, AvailableExpr>, def: VReg) {
    available.retain(|_, expr| expr.def_vreg != def && !expr.source_vregs.contains(&def));
}

fn invalidate_available_depending_on_flags(available: &mut HashMap<ExprKey, AvailableExpr>) {
    available.retain(|_, expr| !expr.depends_on_flags);
}

fn canon_operand(operand: &X86ISelOperand) -> Option<CanonOperand> {
    match operand {
        X86ISelOperand::VReg(vreg) => Some(CanonOperand::VReg(*vreg)),
        X86ISelOperand::Imm(value) => Some(CanonOperand::Imm(*value)),
        X86ISelOperand::FImm(value) => Some(CanonOperand::FImm(value.to_bits())),
        X86ISelOperand::CondCode(cc) => Some(CanonOperand::CondCode(cc.encoding())),
        X86ISelOperand::MemAddr { base, disp } => Some(CanonOperand::MemAddr {
            base: Box::new(canon_address_reg(base)?),
            disp: *disp,
        }),
        X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } => Some(CanonOperand::SibMemAddr {
            base: Box::new(canon_address_reg(base)?),
            index: Box::new(canon_address_reg(index)?),
            scale: *scale,
            disp: *disp,
        }),
        _ => None,
    }
}

fn canon_operand_cmp(a: &CanonOperand, b: &CanonOperand) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    match (a, b) {
        (CanonOperand::VReg(a), CanonOperand::VReg(b)) => a.cmp(b),
        (CanonOperand::Imm(a), CanonOperand::Imm(b)) => a.cmp(b),
        (CanonOperand::FImm(a), CanonOperand::FImm(b)) => a.cmp(b),
        (CanonOperand::CondCode(a), CanonOperand::CondCode(b)) => a.cmp(b),
        (
            CanonOperand::MemAddr {
                base: a_base,
                disp: a_disp,
            },
            CanonOperand::MemAddr {
                base: b_base,
                disp: b_disp,
            },
        ) => canon_operand_cmp(a_base, b_base).then(a_disp.cmp(b_disp)),
        (
            CanonOperand::SibMemAddr {
                base: a_base,
                index: a_index,
                scale: a_scale,
                disp: a_disp,
            },
            CanonOperand::SibMemAddr {
                base: b_base,
                index: b_index,
                scale: b_scale,
                disp: b_disp,
            },
        ) => canon_operand_cmp(a_base, b_base)
            .then_with(|| canon_operand_cmp(a_index, b_index))
            .then(a_scale.cmp(b_scale))
            .then(a_disp.cmp(b_disp)),
        (CanonOperand::VReg(_), _) => Ordering::Less,
        (_, CanonOperand::VReg(_)) => Ordering::Greater,
        (CanonOperand::Imm(_), _) => Ordering::Less,
        (_, CanonOperand::Imm(_)) => Ordering::Greater,
        (CanonOperand::FImm(_), _) => Ordering::Less,
        (_, CanonOperand::FImm(_)) => Ordering::Greater,
        (CanonOperand::CondCode(_), _) => Ordering::Less,
        (_, CanonOperand::CondCode(_)) => Ordering::Greater,
        (CanonOperand::MemAddr { .. }, _) => Ordering::Less,
        (_, CanonOperand::MemAddr { .. }) => Ordering::Greater,
    }
}

fn canon_address_reg(operand: &X86ISelOperand) -> Option<CanonOperand> {
    match operand {
        X86ISelOperand::VReg(vreg) => Some(CanonOperand::VReg(*vreg)),
        _ => None,
    }
}

fn collect_source_vregs(operand: &X86ISelOperand, source_vregs: &mut HashSet<VReg>) -> Option<()> {
    match operand {
        X86ISelOperand::VReg(vreg) => {
            source_vregs.insert(*vreg);
            Some(())
        }
        X86ISelOperand::Imm(_) | X86ISelOperand::FImm(_) | X86ISelOperand::CondCode(_) => Some(()),
        X86ISelOperand::MemAddr { base, .. } => collect_address_reg(base, source_vregs),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_address_reg(base, source_vregs)?;
            collect_address_reg(index, source_vregs)
        }
        _ => None,
    }
}

fn collect_address_reg(operand: &X86ISelOperand, source_vregs: &mut HashSet<VReg>) -> Option<()> {
    match operand {
        X86ISelOperand::VReg(vreg) => {
            source_vregs.insert(*vreg);
            Some(())
        }
        _ => None,
    }
}

fn is_hard_barrier(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    !x86_inst_effect(inst).is_pure()
        || inst_touches_fixed_register(inst)
        || flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.has_side_effects()
        || flags.reads_memory()
        || flags.writes_memory()
        || flags.is_pseudo()
        || matches!(inst.opcode, X86Opcode::Phi | X86Opcode::StackAlloc)
}

fn flags_written_here_are_dead(insts: &[X86ISelInst], index: usize) -> bool {
    if !x86_writes_flags(insts[index].opcode) {
        return true;
    }

    for inst in &insts[index + 1..] {
        if x86_reads_flags(inst.opcode) {
            return false;
        }
        if x86_writes_flags(inst.opcode) {
            return true;
        }
        if instruction_may_export_flags(inst) {
            return false;
        }
    }

    false
}

fn instruction_may_export_flags(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.has_side_effects()
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
    use trust_cg_ir::x86_64_regs::RAX;
    use trust_cg_ir::{InstFlags, X86CondCode};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;

    use crate::X86PassManager;

    fn vreg(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn mem_addr(base: X86ISelOperand, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(base),
            disp,
        }
    }

    fn sib_addr(
        base: X86ISelOperand,
        index: X86ISelOperand,
        scale: u8,
        disp: i32,
    ) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(base),
            index: Box::new(index),
            scale,
            disp,
        }
    }

    fn make_func(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_cse_test".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 16;
        for inst in insts {
            func.push_inst(entry, inst);
        }
        func
    }

    fn entry_insts(func: &X86ISelFunction) -> &[X86ISelInst] {
        &func.blocks.get(&Block(0)).unwrap().insts
    }

    fn entry_opcodes(func: &X86ISelFunction) -> Vec<X86Opcode> {
        entry_insts(func).iter().map(|inst| inst.opcode).collect()
    }

    fn duplicate_add_sequence(middle: X86ISelInst) -> X86ISelFunction {
        make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            middle,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ])
    }

    // --- cross-block (global) CSE helpers ---

    /// Build a multi-block function from `(Block, insts, successors)` tuples.
    /// `block_order` follows the order given. Successors are set verbatim so
    /// tests control the exact predecessor structure the global pass observes.
    fn make_multi_block_func(blocks: Vec<(u32, Vec<X86ISelInst>, Vec<u32>)>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_cse_global_test".to_string(), sig);
        func.next_vreg = 64;
        for (id, insts, _succ) in &blocks {
            let b = Block(*id);
            func.ensure_block(b);
            for inst in insts {
                func.push_inst(b, inst.clone());
            }
        }
        for (id, _insts, succ) in &blocks {
            let b = Block(*id);
            func.blocks.get_mut(&b).unwrap().successors = succ.iter().map(|s| Block(*s)).collect();
        }
        func
    }

    fn block_opcodes(func: &X86ISelFunction, id: u32) -> Vec<X86Opcode> {
        func.blocks
            .get(&Block(id))
            .unwrap()
            .insts
            .iter()
            .map(|inst| inst.opcode)
            .collect()
    }

    fn block_insts(func: &X86ISelFunction, id: u32) -> &[X86ISelInst] {
        &func.blocks.get(&Block(id)).unwrap().insts
    }

    #[test]
    fn x86_cse_global_propagates_across_single_forward_predecessor() {
        // bb0 computes (v0+v1)->v2 and falls through to bb1 (its only pred).
        // bb1 recomputes (v0+v1)->v3, which the global pass should rewrite into
        // a copy of v2.
        // LEA computes an address into a register WITHOUT touching RFLAGS, so it
        // is trackable up to a (flag-escaping) terminator — the natural shape
        // for cross-block availability. bb0 computes `lea v2, [v0+24]` and falls
        // through to bb1 (its only predecessor), which recomputes the same
        // address into v3; the global pass rewrites it into `mov v3, v2`.
        let mut func = make_multi_block_func(vec![
            (
                0,
                vec![
                    X86ISelInst::new(X86Opcode::Lea, vec![vreg(2), mem_addr(vreg(0), 24)]),
                    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
                ],
                vec![1],
            ),
            (
                1,
                vec![
                    X86ISelInst::new(X86Opcode::Lea, vec![vreg(3), mem_addr(vreg(0), 24)]),
                    X86ISelInst::new(X86Opcode::Ret, vec![]),
                ],
                vec![],
            ),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        assert_eq!(
            block_opcodes(&func, 1),
            vec![X86Opcode::MovRR, X86Opcode::Ret]
        );
        assert_eq!(block_insts(&func, 1)[0].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_cse_global_does_not_propagate_into_merge_point() {
        // bb2 has TWO predecessors (bb0 and bb1). Even though both compute the
        // same address, it is only available on entry to bb2 if available on
        // EVERY path — the single-pred guard refuses to seed bb2, so bb2's
        // recompute is preserved (sound: no merge analysis yet).
        let lea =
            |dst: u32| X86ISelInst::new(X86Opcode::Lea, vec![vreg(dst), mem_addr(vreg(0), 24)]);
        let mut func = make_multi_block_func(vec![
            (
                0,
                vec![
                    lea(2),
                    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
                ],
                vec![2],
            ),
            (
                1,
                vec![
                    lea(2),
                    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
                ],
                vec![2],
            ),
            (
                2,
                vec![lea(3), X86ISelInst::new(X86Opcode::Ret, vec![])],
                vec![],
            ),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        let _ = cse.run_on_function(&mut func);

        // bb2's recompute must remain a Lea (not rewritten to a copy).
        assert_eq!(block_opcodes(&func, 2)[0], X86Opcode::Lea);
    }

    #[test]
    fn x86_cse_global_does_not_propagate_across_back_edge() {
        // bb1 is a loop header with predecessors bb0 (forward) and bb1's latch
        // (back edge) — two predecessors — so the single-pred guard refuses to
        // seed it. (Even a hypothetical lone back-edge predecessor is refused
        // because it would not precede the block in block_order.)
        let lea =
            |dst: u32| X86ISelInst::new(X86Opcode::Lea, vec![vreg(dst), mem_addr(vreg(0), 24)]);
        let mut func = make_multi_block_func(vec![
            (
                0,
                vec![
                    lea(2),
                    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
                ],
                vec![1],
            ),
            (
                1,
                vec![
                    // recompute, plus a self back-edge so bb1 has 2 preds.
                    lea(3),
                    X86ISelInst::new(
                        X86Opcode::Jcc,
                        vec![
                            X86ISelOperand::CondCode(X86CondCode::NE),
                            X86ISelOperand::Block(Block(1)),
                        ],
                    ),
                    X86ISelInst::new(X86Opcode::Ret, vec![]),
                ],
                vec![1],
            ),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        let _ = cse.run_on_function(&mut func);

        // The loop body recompute must remain (bb1 has preds {bb0, bb1}).
        assert_eq!(block_opcodes(&func, 1)[0], X86Opcode::Lea);
    }

    #[test]
    fn x86_cse_global_drops_flag_dependent_expr_across_edge() {
        // bb0 produces a Setcc (flag-dependent) and falls through to bb1, the
        // only successor/predecessor. The Setcc must NOT be carried across the
        // edge: bb1's Setcc recompute is preserved (we do not reason about
        // RFLAGS liveness across edges).
        let mut func = make_multi_block_func(vec![
            (
                0,
                vec![
                    X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
                    X86ISelInst::new(
                        X86Opcode::Setcc,
                        vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::E)],
                    ),
                    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
                ],
                vec![1],
            ),
            (
                1,
                vec![
                    X86ISelInst::new(
                        X86Opcode::Setcc,
                        vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::E)],
                    ),
                    X86ISelInst::new(X86Opcode::Ret, vec![]),
                ],
                vec![],
            ),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        let _ = cse.run_on_function(&mut func);

        assert_eq!(block_opcodes(&func, 1)[0], X86Opcode::Setcc);
    }

    #[test]
    fn x86_cse_global_invalidates_when_source_redefined_in_successor() {
        // bb0 computes `lea v2, [v0+24]` and falls through to bb1. bb1 redefines
        // v0 (a source of the carried expression) BEFORE recomputing the
        // address. The carried expression must be invalidated, so the recompute
        // is NOT rewritten into a (now stale) copy of v2.
        let mut func = make_multi_block_func(vec![
            (
                0,
                vec![
                    X86ISelInst::new(X86Opcode::Lea, vec![vreg(2), mem_addr(vreg(0), 24)]),
                    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
                ],
                vec![1],
            ),
            (
                1,
                vec![
                    X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
                    X86ISelInst::new(X86Opcode::Lea, vec![vreg(3), mem_addr(vreg(0), 24)]),
                    X86ISelInst::new(X86Opcode::Ret, vec![]),
                ],
                vec![],
            ),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        let _ = cse.run_on_function(&mut func);

        // The recompute must remain a Lea: v2 is stale after v0 is reassigned.
        assert_eq!(
            block_opcodes(&func, 1),
            vec![X86Opcode::MovRI, X86Opcode::Lea, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_cse_global_does_not_cross_barrier_in_predecessor_tail() {
        // bb0 computes `lea v2, [v0+24]` then a Call (hard barrier) clears
        // availability. Its exit set is therefore empty, so bb1's recompute is
        // not rewritten.
        let mut func = make_multi_block_func(vec![
            (
                0,
                vec![
                    X86ISelInst::new(X86Opcode::Lea, vec![vreg(2), mem_addr(vreg(0), 24)]),
                    X86ISelInst::new(
                        X86Opcode::Call,
                        vec![X86ISelOperand::Symbol("callee".to_string())],
                    ),
                    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
                ],
                vec![1],
            ),
            (
                1,
                vec![
                    X86ISelInst::new(X86Opcode::Lea, vec![vreg(3), mem_addr(vreg(0), 24)]),
                    X86ISelInst::new(X86Opcode::Ret, vec![]),
                ],
                vec![],
            ),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        let _ = cse.run_on_function(&mut func);

        assert_eq!(block_opcodes(&func, 1)[0], X86Opcode::Lea);
    }

    #[test]
    fn x86_cse_replaces_duplicate_pure_add_with_copy() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86CommonSubexpressionElimination));

        assert!(pm.run_once(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::MovRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_cse_replaces_swapped_commutative_add_with_copy() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(3), vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::MovRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_cse_replaces_swapped_commutative_xor_with_copy() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(2), vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(3), vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::MovRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_cse_does_not_replace_swapped_non_commutative_sub() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(2), vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(3), vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::SubRR,
                X86Opcode::SubRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_does_not_sort_imul_rri_immediate_operands() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(0), X86ISelOperand::Imm(7)],
            ),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(3), X86ISelOperand::Imm(7), vreg(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::ImulRRI,
                X86Opcode::ImulRRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_uses_movrr32_for_gpr32_replacement() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(2), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRR32);
        assert_eq!(insts[1].operands, vec![vreg32(2), vreg32(1)]);
    }

    #[test]
    fn x86_cse_tracks_duplicate_movrr32_expressions() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(1), vreg32(0)]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(2), vreg32(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRR32);
        assert_eq!(insts[1].operands, vec![vreg32(2), vreg32(1)]);
    }

    #[test]
    fn x86_cse_replaces_duplicate_virtual_lea_with_copy() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::Lea, vec![vreg(2), mem_addr(vreg(0), 24)]),
            X86ISelInst::new(X86Opcode::Lea, vec![vreg(3), mem_addr(vreg(0), 24)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::Lea, X86Opcode::MovRR, X86Opcode::Ret]
        );
        assert_eq!(insts[1].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_cse_replaces_duplicate_virtual_leasib_with_copy() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![vreg(2), sib_addr(vreg(0), vreg(1), 4, 16)],
            ),
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![vreg(3), sib_addr(vreg(0), vreg(1), 4, 16)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::LeaSib, X86Opcode::MovRR, X86Opcode::Ret]
        );
        assert_eq!(insts[1].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_cse_invalidates_leasib_when_nested_source_is_redefined() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![vreg(2), sib_addr(vreg(0), vreg(1), 4, 16)],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![vreg(3), sib_addr(vreg(0), vreg(1), 4, 16)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::LeaSib,
                X86Opcode::MovRI,
                X86Opcode::LeaSib,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_rejects_fixed_register_address_candidates() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![vreg(2), sib_addr(X86ISelOperand::PReg(RAX), vreg(1), 4, 16)],
            ),
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![vreg(3), sib_addr(X86ISelOperand::PReg(RAX), vreg(1), 4, 16)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::LeaSib, X86Opcode::LeaSib, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_cse_does_not_cross_memory_barrier() {
        let load_addr = X86ISelOperand::MemAddr {
            base: Box::new(vreg(4)),
            disp: 8,
        };
        let mut func =
            duplicate_add_sequence(X86ISelInst::new(X86Opcode::MovRM, vec![vreg(5), load_addr]));
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::MovRM,
                X86Opcode::AddRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_preserves_sib_fixed_physical_register_barrier() {
        let sib_addr = X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::PReg(RAX)),
            index: Box::new(vreg(4)),
            scale: 4,
            disp: 8,
        };
        let mut func =
            duplicate_add_sequence(X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(5), sib_addr]));
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::LeaSib,
                X86Opcode::AddRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_keeps_virtual_only_sib_available() {
        let sib_addr = X86ISelOperand::SibMemAddr {
            base: Box::new(vreg(4)),
            index: Box::new(vreg(5)),
            scale: 2,
            disp: 8,
        };
        let mut func =
            duplicate_add_sequence(X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(6), sib_addr]));
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::LeaSib,
                X86Opcode::MovRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(entry_insts(&func)[2].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_cse_does_not_cross_call_barrier() {
        let mut func = duplicate_add_sequence(X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("callee".to_string())],
        ));
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::Call,
                X86Opcode::AddRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_preserves_duplicate_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(3), vreg(0), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(4), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::AddRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_replaces_duplicate_setcc_under_unchanged_flags() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(cse.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::Setcc,
                X86Opcode::MovRR32,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[2].operands, vec![vreg32(3), vreg32(2)]);
    }

    #[test]
    fn x86_cse_invalidates_setcc_available_on_flag_writer() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::Setcc,
                X86Opcode::CmpRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_keeps_different_setcc_conditions_distinct() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::NE)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::Setcc,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_cse_does_not_merge_distinct_in_place_bswap_operands() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::Bswap, vec![vreg(0)]),
            X86ISelInst::new(X86Opcode::Bswap, vec![vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::Bswap, X86Opcode::Bswap, X86Opcode::Ret]
        );
        assert_eq!(entry_insts(&func)[0].operands, vec![vreg(0)]);
        assert_eq!(entry_insts(&func)[1].operands, vec![vreg(1)]);
    }

    #[test]
    fn x86_cse_does_not_cross_side_effect_barrier() {
        let mut func = duplicate_add_sequence(X86ISelInst::with_flags(
            X86Opcode::MovRR,
            vec![vreg(6), vreg(0)],
            InstFlags::HAS_SIDE_EFFECTS,
        ));
        let mut cse = X86CommonSubexpressionElimination;

        assert!(!cse.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::MovRR,
                X86Opcode::AddRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(entry_insts(&func)[1].flags, InstFlags::HAS_SIDE_EFFECTS);
    }
}
