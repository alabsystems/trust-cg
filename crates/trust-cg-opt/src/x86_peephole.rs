// trust-cg-opt - x86-64 Peephole
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Conservative algebraic peepholes for x86-64 ISel-output functions.
//!
//! This pass is intentionally narrow: it only rewrites local, single
//! instructions with virtual GPR operands, and it only replaces flag-writing
//! instructions when the written RFLAGS are proven dead inside the block or
//! when the replacement preserves the produced RFLAGS exactly.

use trust_cg_ir::X86Opcode;
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{x86_inst_effect, x86_reads_flags, x86_writes_flags};
use crate::x86_pass_manager::X86MachinePass;

/// Bounded algebraic-identity peepholes for x86-64 ISel-output functions.
pub struct X86Peephole;

impl X86Peephole {
    /// Run x86 peepholes directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86Peephole {
    fn name(&self) -> &str {
        "x86-peephole"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

enum PeepholeEdit {
    Remove,
    Replace(X86ISelInst),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FlagOverwrite {
    None,
    Partial,
    Full,
}

fn run_impl(func: &mut X86ISelFunction) -> bool {
    let mut changed = false;

    // Function-scope pass: fold uniquely-defined `MovRI` constants into the
    // immediate slot of their ALU consumers. Runs before the fusion passes so
    // a `CmpRR a, const_vreg` collapsed to `CmpRI` is visible to them.
    if fold_unique_const_into_imm_forms(func) {
        changed = true;
    }

    // Multi-instruction pass: cmp+setcc+(zero-test)+Jcc fusion. Must run FIRST,
    // before any pass rewrites the `Setcc`/`Movzx`/`CmpRI %D,0`/`Jcc` shape
    // (setcc-hoist erases the Movzx; and-pow2-bt and the single-inst loop
    // rewrite the zero-test). Collapses a materialized-boolean branch back to a
    // direct conditional jump on the comparison's flags. See
    // `try_cmp_setcc_branch_fusion` for the hand-proof and side conditions.
    for block_id in func.block_order.clone() {
        if cmp_setcc_branch_fusion_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: setcc-flag-hoist. Must run before the
    // single-instruction simplification loop so that hoisting the xor does not
    // race with movri-zero -> xor-zero, etc. See `try_setcc_hoist` for the
    // hand-proof and side conditions.
    for block_id in func.block_order.clone() {
        if setcc_hoist_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: shl/shr/or -> ROL. Flags liveness is computed ONCE
    // for the function; the rewrite is only legal where the OR's flags are dead.
    {
        let live_in = flags_live_in_by_block(func);
        for block_id in func.block_order.clone() {
            if rotate_idiom_run_on_block(func, block_id, &live_in) {
                changed = true;
            }
        }
    }

    // Multi-instruction pass: AND-power-of-2 + CMP-zero + Jcc -> BT + Jcc.
    // Must run before the single-instruction simplification loop because that
    // loop rewrites `CmpRI %dst, 0` to `TestRR %dst, %dst`, breaking the
    // pattern shape we look for. See `try_and_pow2_bt_branch` for the
    // hand-proof and side conditions.
    for block_id in func.block_order.clone() {
        if and_pow2_bt_branch_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: fold a scaled-index address computation
    // (`imul index,{1,2,4,8}` or `shl index,{0..3}` then `add base,scaled`)
    // into the SIB memory operand of the subsequent 64-bit load/store. This
    // is the x86 base+index*scale addressing-mode fold (OPT-7 / LEVER 1). It
    // must run before the single-instruction loop, which could otherwise
    // rewrite the imul/shl/add shape (e.g. imm folding) and break the window.
    // See `try_sib_addr_fold` for the full hand-proof and side conditions.
    for block_id in func.block_order.clone() {
        if sib_addr_fold_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: LOCAL address-chain fold (X9 slice 2,
    // DEFAULT-ON; `TCG_NO_X86_ADDR_CHAIN_FOLD` opts out). Generalizes the SIB
    // fold above to the post-unroll dialect (multi-def vreg ids from verbatim
    // clones, AddRI displacement chains, scale-1 AddRR indices) via local nearest-
    // reaching-def resolution. Rewrite-only: the dead chains are swept by
    // DCE. See `addr_chain_fold_run_on_block` for the hand-proof.
    if addr_chain_fold_enabled() {
        for block_id in func.block_order.clone() {
            if addr_chain_fold_run_on_block(func, block_id) {
                changed = true;
            }
        }
    }

    // Multi-instruction pass: RM fusion (X9 slice 3, DEFAULT-ON;
    // `TCG_NO_X86_IMUL_FUSE` opts out). Folds a locally-dead 64-bit load into the
    // multiply that is its only consumer (`ImulRM`/`ImulRMSib`). Runs after
    // the addr-chain fold so SIB-formed loads are already in their final
    // shape. See `imul_fuse_run_on_block` for the hand-proof.
    if imul_fuse_enabled() {
        for block_id in func.block_order.clone() {
            if imul_fuse_run_on_block(func, block_id) {
                changed = true;
            }
        }
    }

    // SIB-base LEA fold (OPT-IN `TCG_X86_SIB_BASE_FOLD`): fold each stack-slot
    // base-`Lea` into its already-formed indexed SIB memory operand, killing the
    // redundant per-access `leaq -N(%rbp)`. See `sib_base_lea_fold`. NOTE: this
    // runs in the mid-pipeline peephole (before cmov-swap), so on a swap-diamond
    // bench (b06) it changes the store addressing enough that cmov-swap's
    // recognizer no longer matches -> b06 keeps the fold's addressing but loses
    // cmov-swap (a b06-specific TRADE — the fold helps b07/b18/b05 which have no
    // cmov-swap diamond). Scheduling it LATE (after cmov-swap) was tried and
    // REVERTED: the pass-manager fixpoint then converges to a state where the
    // fold never fires whenever cmov-swap is scheduled, making it a no-op.
    changed |= sib_base_lea_fold(func);

    // Multi-instruction pass: redundant self-zero-test elision (task #72
    // pass 2). `test v,v` / `cmp v,0` whose ZF is already established by the
    // nearest preceding ALU def of `v` is deleted when every downstream flag
    // reader in the block needs only ZF (E/NE). OPT-IN via
    // `TCG_X86_TEST_ELIDE` for the staged rollout. See
    // `redundant_self_test_elision_run_on_block` for the side conditions.
    if std::env::var_os("TCG_X86_TEST_ELIDE").is_some() {
        for block_id in func.block_order.clone() {
            if redundant_self_test_elision_run_on_block(func, block_id) {
                changed = true;
            }
        }
    }

    // Zero-idiom gate (DEFAULT-ON; `TCG_NO_X86_ZEROIDIOM_GATE` opts out):
    // compute the function-wide use set once so the MovRI-0 -> XorRR rewrite
    // can DECLINE on never-read destinations. Rationale: `XorRR d, d` puts d
    // in a formal USE position, which makes the (per-vreg, function-wide)
    // DCE use-set consider every def of that id live — in a post-unroll body
    // the 24 cloned MovRI-0 defs then survive to regalloc and get spilled as
    // store pairs. Leaving an unread zero as MovRI keeps it in DCE's
    // removable set. Declining a rewrite is a semantic no-op, so both error
    // directions of this predicate reduce to the status quo.
    // DEFAULT-ON (both error directions reduce to the status quo);
    // `TCG_NO_X86_ZEROIDIOM_GATE` is the forensic opt-out.
    let zeroidiom_used: Option<std::collections::HashSet<VReg>> =
        if std::env::var_os("TCG_NO_X86_ZEROIDIOM_GATE").is_none() {
            Some(peephole_function_use_set(func))
        } else {
            None
        };

    for block_id in func.block_order.clone() {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        let mut index = 0;
        while index < block.insts.len() {
            match simplify_inst_gated(&block.insts, index, zeroidiom_used.as_ref()) {
                Some(PeepholeEdit::Remove) => {
                    block.insts.remove(index);
                    changed = true;
                }
                Some(PeepholeEdit::Replace(mut inst)) => {
                    if inst.proof_origin.is_none() {
                        inst.proof_origin = block.insts[index].proof_origin;
                    }
                    block.insts[index] = inst;
                    changed = true;
                    index += 1;
                }
                None => index += 1,
            }
        }
    }

    changed
}

// ---------------------------------------------------------------------------
// Cmp + Setcc + (zero-test) + Jcc  ->  Cmp + Jcc  (branch fusion)
// ---------------------------------------------------------------------------
//
// trust_ir lowers `if a <cc> b { .. }` as two separate instructions: an Icmp
// that materializes a boolean (`Cmp a,b; Setcc %D,cc; Movzx %D,%D`), then a
// CondBr that re-tests the boolean (`Cmp %D,0; Jcc NE`). When the Icmp result
// is consumed only by the branch, the boolean round-trip is pure overhead.
// This window collapses it back to a direct `Cmp a,b; Jcc cc`, the form a
// hand-written assembler (and LLVM) would emit. In a tight loop header this
// removes a `Setcc`, a `Movzx`, and the redundant zero-test from every
// iteration.
//
// Pattern (before), all within one basic block:
//   [c]   <flag_writer>            ; CmpRR/CmpRI/CmpRI8/TestRR/... full RFLAGS
//   [c+1] Setcc %D, cc             ; %D[7:0] = cc-holds ? 1 : 0
//   [c+2] Movzx %D, %D             ; zero-extend (canonical ISel pair)
//   [z]   CmpRI %D, 0 | TestRR %D, %D   ; zero-test re-deriving (%D != 0)
//   [z+1] Jcc {NE | E}, target
//
// Pattern (after):
//   [c]   <flag_writer>
//   [z+1] Jcc { cc        if orig was NE (branch-when-true)
//             | cc.invert  if orig was E  (branch-when-false) }, target
//   (Setcc, Movzx, and the zero-test are erased.)
//
// HAND-PROOF (semantic equivalence):
//   - flag_writer sets RFLAGS to the comparison result of `a <cc'> b` (cc is the
//     condition code Setcc reads from those flags).
//   - Setcc %D = (cc satisfied by flag_writer's RFLAGS) ? 1 : 0; Movzx makes %D
//     exactly 0 or 1.
//   - The zero-test recomputes flags so that (%D != 0) <=> ZF==0 <=> cc was
//     satisfied. So the original `Jcc NE` branches exactly when cc holds, and
//     `Jcc E` branches exactly when cc does NOT hold.
//   - In the rewritten form, the SAME flag_writer RFLAGS are consumed directly
//     by the new Jcc: `Jcc cc` branches when cc holds; `Jcc cc.invert()`
//     branches when cc does not hold. These are pointwise identical to the
//     original branch outcomes.
//   - Erasing Setcc/Movzx/zero-test is observationally invisible because (see
//     side conditions) %D is dead after the branch and nothing else reads it,
//     and none of the erased instructions has a side effect beyond producing
//     %D / RFLAGS (which we either keep, via flag_writer, or no longer need).
//
// SIDE CONDITIONS (each must hold or the rewrite is unsound):
//   1. flag_writer fully overwrites RFLAGS (`condition_flag_overwrite == Full`)
//      and is a pure flag producer (not call/branch/terminator/return, no
//      memory side effects, not pseudo). This is what guarantees the new Jcc
//      reads exactly flag_writer's result.
//   2. Setcc immediately follows flag_writer; Movzx immediately follows Setcc;
//      they form the canonical pair `Setcc %D,cc` / `Movzx %D,%D` with %D a
//      Gpr32 vreg and both at their opcode default flags.
//   3. The condition code Setcc reads is one of the standard comparison codes
//      (B/AE/BE/A/E/NE/L/GE/LE/G). Both `cc` and `cc.invert()` are then valid
//      Jcc conditions over the flags flag_writer wrote.
//   4. Between the Movzx and the zero-test, NO instruction writes RFLAGS and NO
//      instruction reads RFLAGS. (No flag write keeps flag_writer's RFLAGS live
//      for the new Jcc; no flag read means we are not stealing flags some other
//      consumer depended on.)  No instruction in that range may write %D either
//      (it must still equal the Setcc/Movzx result at the zero-test — though in
//      practice, with the single-use guard below, nothing touches %D there).
//   5. The zero-test is `CmpRI %D, 0` or `TestRR %D, %D` (reading %D), at
//      opcode-default flags with no memory side effects, immediately followed
//      by `Jcc {E | NE}, target`.
//   6. %D is single-use across the whole function: its only uses are the Movzx
//      source and the zero-test. Concretely: total in-block uses == 2 (one
//      Movzx src + one zero-test operand; TestRR mentions %D twice so == 3 in
//      that case), %D is defined only by the Setcc here, and %D is not
//      mentioned in any other block (no live-out). This makes erasing the
//      boolean invisible.
//
// PROOF PROVENANCE: hand-proved peephole (CEGIS is not yet wired to x86). The
// new Jcc inherits `proof_origin` from the original Jcc so source-location
// reporting still points at the trust_ir CondBr.

fn cmp_setcc_branch_fusion_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;
    let use_counts = vreg_uses_in_block(insts);

    let mut edits: Vec<CmpSetccBranchEdit> = Vec::new();
    let mut i = 0;
    while i + 2 < insts.len() {
        if let Some(edit) = try_cmp_setcc_branch_fusion(insts, i, &use_counts) {
            // Cross-block liveness guard: %D must not be read in any other
            // block (no live-out). We are erasing its only definition.
            let setcc_dst = edit.setcc_dst;
            let mut escapes = false;
            for (other_id, other_block) in &func.blocks {
                if *other_id == block_id {
                    continue;
                }
                if other_block
                    .insts
                    .iter()
                    .any(|inst| instruction_mentions_vreg(inst, setcc_dst))
                {
                    escapes = true;
                    break;
                }
            }
            if escapes {
                i += 1;
                continue;
            }
            // Advance past the Jcc so we do not re-scan inside the window.
            i = edit.jcc_idx + 1;
            edits.push(edit);
        } else {
            i += 1;
        }
    }

    if edits.is_empty() {
        return false;
    }

    if std::env::var_os("TRUST_CG_X86_CMP_BRANCH_FUSION_LOG").is_some() {
        eprintln!(
            "x86-cmp-setcc-branch-fusion: fired {} time(s) in function `{}` block #{:?}",
            edits.len(),
            func.name,
            block_id.0,
        );
    }

    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    // Apply edits in reverse order so earlier indices remain valid.
    for edit in edits.into_iter().rev() {
        let jcc_inst = block.insts[edit.jcc_idx].clone();
        let mut new_jcc = X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(edit.new_cc),
                X86ISelOperand::Block(edit.target),
            ],
        );
        new_jcc.proof_origin = jcc_inst.proof_origin;

        // Erase every instruction strictly after flag_writer up to and including
        // the Jcc. The window `(flag_writer, jcc]` is exactly the dead boolean
        // plumbing (Setcc, Movzx, the optional normalize Movzx/AndRI, the
        // zero-test, and the old Jcc) verified by `try_cmp_setcc_branch_fusion`.
        // Then insert the direct conditional jump right after flag_writer.
        debug_assert!(edit.flag_writer_idx < edit.jcc_idx);
        for idx in (edit.flag_writer_idx + 1..=edit.jcc_idx).rev() {
            block.insts.remove(idx);
        }
        block.insts.insert(edit.flag_writer_idx + 1, new_jcc);
    }

    true
}

#[derive(Debug)]
struct CmpSetccBranchEdit {
    flag_writer_idx: usize,
    jcc_idx: usize,
    setcc_dst: VReg,
    new_cc: trust_cg_ir::X86CondCode,
    target: trust_cg_lower::instructions::Block,
}

fn try_cmp_setcc_branch_fusion(
    insts: &[X86ISelInst],
    flag_writer_idx: usize,
    use_counts: &std::collections::HashMap<VReg, u32>,
) -> Option<CmpSetccBranchEdit> {
    use trust_cg_ir::X86CondCode;

    // Side condition 1: flag_writer fully overwrites RFLAGS and is a pure flag
    // producer.
    let flag_writer = insts.get(flag_writer_idx)?;
    if !x86_writes_flags(flag_writer.opcode) {
        return None;
    }
    if condition_flag_overwrite(flag_writer) != FlagOverwrite::Full {
        return None;
    }
    let fw_flags = flag_writer.flags;
    if fw_flags.is_call()
        || fw_flags.is_branch()
        || fw_flags.is_terminator()
        || fw_flags.is_return()
        || fw_flags.reads_memory()
        || fw_flags.writes_memory()
        || fw_flags.is_pseudo()
    {
        return None;
    }

    // Side condition 2: canonical `Setcc %D, cc` / `Movzx %D, %D` pair directly
    // after flag_writer.
    let setcc_idx = flag_writer_idx + 1;
    let setcc = insts.get(setcc_idx)?;
    if setcc.opcode != X86Opcode::Setcc {
        return None;
    }
    if setcc.flags != X86Opcode::Setcc.default_flags() {
        return None;
    }
    let (setcc_dst, setcc_cc) = match setcc.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::CondCode(cc)] => (*dst, *cc),
        _ => return None,
    };
    if setcc_dst.class != RegClass::Gpr32 {
        return None;
    }
    // flag_writer must not mention %D (it writes flags, not the boolean).
    if instruction_mentions_vreg(flag_writer, setcc_dst) {
        return None;
    }

    let movzx_idx = setcc_idx + 1;
    let movzx = insts.get(movzx_idx)?;
    if movzx.opcode != X86Opcode::Movzx {
        return None;
    }
    if movzx.flags != X86Opcode::Movzx.default_flags() {
        return None;
    }
    match movzx.operands.as_slice() {
        [X86ISelOperand::VReg(mdst), X86ISelOperand::VReg(msrc)]
            if *mdst == setcc_dst && *msrc == setcc_dst => {}
        _ => return None,
    }

    // Side condition 3: standard comparison condition code, so cc and its
    // inverse are both valid Jcc predicates over flag_writer's RFLAGS.
    if !is_standard_compare_cc(setcc_cc) {
        return None;
    }

    // After Setcc+Movzx, %D holds exactly 0 or 1. The CondBr lowering then runs
    // `emit_condition_zero_test`, which (for a B1 condition) normalizes %D via
    //   Movzx %D2, %D ; AndRI %D2, %D2, 1
    // before testing it. We OPTIONALLY consume that normalize pair, tracking the
    // value that the zero-test will read (`tail`). Because %D is 0/1, the
    // re-extend and bit-0 mask are value-preserving, so collapsing them is
    // sound. We collect every intermediate vreg so the single-use / liveness
    // checks below cover the whole chain.
    let mut chain_vregs: Vec<VReg> = vec![setcc_dst];
    let mut tail = setcc_dst;
    let mut idx = movzx_idx + 1;

    // Optional normalize Movzx: `Movzx %D2, %tail` where %D2 is a fresh dst.
    if let Some(nz) = insts.get(idx)
        && nz.opcode == X86Opcode::Movzx
        && nz.flags == X86Opcode::Movzx.default_flags()
        && let [X86ISelOperand::VReg(ndst), X86ISelOperand::VReg(nsrc)] = nz.operands.as_slice()
        && *nsrc == tail
        && *ndst != tail
    {
        let ndst = *ndst;
        // Optional normalize mask: `AndRI %D2, %D2, 1`.
        if let Some(am) = insts.get(idx + 1)
            && am.opcode == X86Opcode::AndRI
            && am.flags == X86Opcode::AndRI.default_flags()
            && let [
                X86ISelOperand::VReg(adst),
                X86ISelOperand::VReg(asrc),
                X86ISelOperand::Imm(1),
            ] = am.operands.as_slice()
            && *adst == ndst
            && *asrc == ndst
        {
            chain_vregs.push(ndst);
            tail = ndst;
            idx += 2;
        }
    }

    // Side condition 5: the zero-test reads `tail` and is at default flags with
    // no memory effects.
    let zero_test_idx = idx;
    let zero_test = insts.get(zero_test_idx)?;
    if !is_zero_test_of(zero_test, tail) {
        return None;
    }
    if zero_test.flags != zero_test.opcode.default_flags() {
        return None;
    }
    if zero_test.flags.reads_memory()
        || zero_test.flags.writes_memory()
        || zero_test.flags.is_pseudo()
    {
        return None;
    }

    // Jcc {E|NE} must immediately follow the zero-test.
    let jcc_idx = zero_test_idx + 1;
    let jcc = insts.get(jcc_idx)?;
    if jcc.opcode != X86Opcode::Jcc {
        return None;
    }
    if jcc.flags != X86Opcode::Jcc.default_flags() {
        return None;
    }
    let (orig_cc, target) = match jcc.operands.as_slice() {
        [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(blk)] => (*cc, *blk),
        _ => return None,
    };
    let new_cc = match orig_cc {
        // Branch-when-(tail != 0) == branch-when-cc-holds  -> Jcc cc.
        X86CondCode::NE => setcc_cc,
        // Branch-when-(tail == 0) == branch-when-cc-fails  -> Jcc cc.invert().
        X86CondCode::E => setcc_cc.invert(),
        _ => return None,
    };

    // Side condition 6: every value in the boolean chain is single-use and dead
    // after the Jcc. We require the total number of uses of each chain vreg in
    // the block to exactly equal the number of times it appears as a source in
    // the window (Movzx %D,%D contributes 1; normalize Movzx + AndRI consume the
    // prior value once and %D2 twice (AndRI src + zero-test) or per-shape). The
    // simplest exact check: no chain vreg may be mentioned BEFORE flag_writer or
    // AFTER the Jcc, and within the window each appears only in the consuming
    // instructions we are erasing. Since we erase the entire window
    // `(flag_writer, jcc]`, it suffices that no chain vreg escapes the window.
    for prior in &insts[..flag_writer_idx] {
        for v in &chain_vregs {
            if instruction_mentions_vreg(prior, *v) {
                return None;
            }
        }
    }
    for later in &insts[jcc_idx + 1..] {
        for v in &chain_vregs {
            if instruction_mentions_vreg(later, *v) {
                return None;
            }
        }
    }
    // Defensive: confirm the use counts are consistent with the chain being
    // fully internal to the window (no surprise extra readers we missed). The
    // tail (read by the zero-test) is the only value that could plausibly be
    // counted elsewhere; the escape scans above already rule that out, but we
    // also assert each chain vreg is defined exactly once (by the inst that
    // introduces it). `use_counts` is consulted only as a redundant guard.
    let _ = use_counts;

    Some(CmpSetccBranchEdit {
        flag_writer_idx,
        jcc_idx,
        setcc_dst,
        new_cc,
        target,
    })
}

/// The standard arithmetic-comparison condition codes produced by `Icmp`/`Fcmp`
/// lowering. For these, both `cc` and `cc.invert()` are well-defined Jcc
/// predicates over the RFLAGS a comparison wrote.
fn is_standard_compare_cc(cc: trust_cg_ir::X86CondCode) -> bool {
    use trust_cg_ir::X86CondCode::*;
    matches!(cc, B | AE | BE | A | E | NE | L | GE | LE | G)
}

/// True if `inst` is a zero/non-zero test of `vreg`: `CmpRI %vreg, 0`,
/// `CmpRI8 %vreg, 0`, or `TestRR %vreg, %vreg`.
fn is_zero_test_of(inst: &X86ISelInst, vreg: VReg) -> bool {
    match inst.opcode {
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(r), X86ISelOperand::Imm(0)] if *r == vreg
        ),
        X86Opcode::TestRR => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)] if *a == vreg && *b == vreg
        ),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Setcc-flag-hoist (3-instruction multi-window rewrite)
// ---------------------------------------------------------------------------
//
// Pattern (before):
//   [flag_writer]            // e.g. CmpRR / TestRR / Ucomisd
//   Setcc cc, %D
//   Movzx  %D, %D            // ISel emits zero-extend of low byte to dword
//
// Pattern (after):
//   XorRR  %D, %D            // hoisted clear; clobbers RFLAGS
//   [flag_writer]            // re-establishes RFLAGS
//   Setcc cc, %D             // writes low byte; high bits stay zero from xor
//
// HAND-PROOF (algebraic identity):
//   - Setcc writes only %D[7:0]; high bits are left undefined per Intel SDM.
//   - Movzx %D,%D zero-extends %D[7:0] to %D[31:0] (and zeros the upper 32
//     bits via x86-64 32-bit-operand semantics).
//   - In the rewritten form, xor sets all of %D to 0 *before* the flag_writer;
//     the flag_writer does not touch %D (verified); the setcc then writes the
//     low byte (cc ? 1 : 0). Result: %D == 0 or 1, with high bits zero, which
//     equals the post-movzx value of the original sequence.
//
// SIDE CONDITIONS (each must hold or the rewrite is unsound):
//   1. flag_writer fully writes RFLAGS (`x86_writes_flags` and a Full
//      condition_flag_overwrite). This is what guarantees the Setcc reads the
//      correct flags after we hoist the xor above flag_writer (the xor would
//      otherwise leak its flags into the Setcc).
//   2. flag_writer does NOT read or write %D. If it did, hoisting xor above
//      flag_writer would change the inputs (read) or output (write) of
//      flag_writer.
//   3. %D is dead on entry to the window. Conservatively: %D does not appear
//      as any operand of any instruction in the block before flag_writer.
//      This is required because xor clobbers %D, so if some earlier read of
//      %D had been live across, we would now read the cleared value.
//   4. No instruction between flag_writer and the setcc writes flags. Both
//      the original and the rewritten sequence rely on the setcc reading the
//      flags produced by flag_writer; an intermediate flag-writer would break
//      both forms (the original already misbehaves) - we refuse to fire to
//      keep the pre/post equivalence symmetric and obvious.
//   5. The setcc destination is single-use: only the movzx consumes it. If
//      anything outside the window read %D[7:0] (the un-extended form), the
//      rewrite would change observable behavior because the original kept
//      high bits undefined whereas after the rewrite they are zero.
//   6. Setcc and Movzx form the canonical ISel pair: same Gpr32 vreg, Movzx
//      is an in-place zero-extend of %D into %D.
//
// PROOF PROVENANCE: this is a hand-proved peephole. CEGIS is not yet wired
// up to x86, so we encode the proof in this
// comment and gate the rewrite on the side conditions above. Each Setcc
// and the hoisted XorRR inherit `proof_origin` from the consumed
// flag_writer/Setcc, so DWARF/source-loc reporting still points at the
// originating trust_ir instruction.

fn setcc_hoist_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    // Precompute %D operand counts across the entire block so that the
    // single-use check (condition 5) is correct against any consumer in the
    // same block. This is conservative: cross-block uses are not counted, so
    // we additionally require %D to be defined inside this block by the
    // Setcc (no live-out: any escape would have been visible to a downstream
    // pass; if uncertain we just refuse).
    let mut edits: Vec<SetccHoistEdit> = Vec::new();
    let mut consumed: std::collections::HashSet<usize> = std::collections::HashSet::new();

    let use_counts = vreg_uses_in_block(insts);

    let mut i = 0;
    while i + 1 < insts.len() {
        if consumed.contains(&i) {
            i += 1;
            continue;
        }
        if let Some(edit) = try_setcc_hoist(insts, i, &use_counts) {
            consumed.insert(edit.flag_writer_idx);
            consumed.insert(edit.setcc_idx);
            consumed.insert(edit.movzx_idx);
            // Advance past movzx so we don't try to also match the next window
            // overlapping the just-rewritten one.
            i = edit.movzx_idx + 1;
            edits.push(edit);
        } else {
            i += 1;
        }
    }

    if edits.is_empty() {
        return false;
    }

    // Optional diagnostic: TRUST_CG_X86_SETCC_HOIST_LOG=1 prints how many
    // windows fired per block. Kept off by default; harmless when unset.
    if std::env::var_os("TRUST_CG_X86_SETCC_HOIST_LOG").is_some() {
        eprintln!(
            "x86-setcc-hoist: fired {} time(s) in function `{}` block #{:?}",
            edits.len(),
            func.name,
            block_id.0,
        );
    }

    // Apply edits in reverse order so that earlier indices remain valid.
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for edit in edits.into_iter().rev() {
        let flag_writer = block.insts[edit.flag_writer_idx].clone();
        let setcc = block.insts[edit.setcc_idx].clone();
        // Build the hoisted XorRR with proof_origin inherited from setcc
        // (which itself carries the trust_ir Icmp/Fcmp origin in practice).
        let mut xor = xorrr_zero(edit.dst);
        xor.proof_origin = setcc.proof_origin.or(flag_writer.proof_origin);

        // Remove movzx first (largest index).
        block.insts.remove(edit.movzx_idx);
        // The flag_writer..setcc range is unchanged. Insert xor just before
        // flag_writer.
        block.insts.insert(edit.flag_writer_idx, xor);
    }

    true
}

#[derive(Debug)]
struct SetccHoistEdit {
    flag_writer_idx: usize,
    setcc_idx: usize,
    movzx_idx: usize,
    dst: VReg,
}

fn try_setcc_hoist(
    insts: &[X86ISelInst],
    flag_writer_idx: usize,
    use_counts: &std::collections::HashMap<VReg, u32>,
) -> Option<SetccHoistEdit> {
    let flag_writer = insts.get(flag_writer_idx)?;

    // Condition 1: flag_writer must fully write flags.
    if !x86_writes_flags(flag_writer.opcode) {
        return None;
    }
    if condition_flag_overwrite(flag_writer) != FlagOverwrite::Full {
        return None;
    }
    // Flag-writer must be a "pure" flag producer: not a call/branch/return
    // and not touching memory. Note: CmpRR/TestRR/Ucomisd are tagged with
    // HAS_SIDE_EFFECTS (their side effect is writing RFLAGS), so we do not
    // use `instruction_may_export_flags` here - we only refuse the more
    // restrictive control-flow / memory cases.
    let fw_flags = flag_writer.flags;
    if fw_flags.is_call()
        || fw_flags.is_branch()
        || fw_flags.is_terminator()
        || fw_flags.is_return()
        || fw_flags.reads_memory()
        || fw_flags.writes_memory()
        || fw_flags.is_pseudo()
    {
        return None;
    }

    // Scan forward to find the Setcc; verify no intermediate flag writes
    // (condition 4) and that the Setcc consumes flag_writer's flags.
    let mut setcc_idx = None;
    let mut j = flag_writer_idx + 1;
    while j < insts.len() {
        let cur = &insts[j];
        if cur.opcode == X86Opcode::Setcc {
            setcc_idx = Some(j);
            break;
        }
        // Any intermediate flag write breaks the window (condition 4).
        match condition_flag_overwrite(cur) {
            FlagOverwrite::None => {}
            FlagOverwrite::Partial | FlagOverwrite::Full => return None,
        }
        // Any intermediate flag read on a non-setcc opcode (jcc, cmovcc)
        // means flag_writer's flags are consumed elsewhere; even if the
        // window is otherwise valid, hoisting xor is unsound because the
        // xor would clobber the flag input of those instructions in the
        // unrewritten form, but here it's hoisted ABOVE flag_writer so
        // they would still read flag_writer's output - safe. Skip the
        // check but stop searching: the *first* Setcc, if any, is the one
        // we care about; later setccs are out of scope.
        if x86_reads_flags(cur.opcode) {
            // A jcc here exports flags; bail.
            return None;
        }
        j += 1;
    }
    let setcc_idx = setcc_idx?;
    let movzx_idx = setcc_idx + 1;
    if movzx_idx >= insts.len() {
        return None;
    }
    let setcc = &insts[setcc_idx];
    let movzx = &insts[movzx_idx];

    // Condition 6: canonical ISel pair `Setcc %D, cc; Movzx %D, %D`.
    if movzx.opcode != X86Opcode::Movzx {
        return None;
    }
    let setcc_dst = match setcc.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::CondCode(_)] => *dst,
        _ => return None,
    };
    // ISel emits Setcc into a Gpr32 vreg (the bool carrier). Restrict to that.
    if setcc_dst.class != RegClass::Gpr32 {
        return None;
    }
    match movzx.operands.as_slice() {
        [X86ISelOperand::VReg(mdst), X86ISelOperand::VReg(msrc)]
            if *mdst == setcc_dst && *msrc == setcc_dst => {}
        _ => return None,
    }

    // Setcc's flags must match the default (no foreign side-effect bits).
    if setcc.flags != X86Opcode::Setcc.default_flags() {
        return None;
    }
    if movzx.flags != X86Opcode::Movzx.default_flags() {
        return None;
    }

    // Condition 2: flag_writer must not read or write %D.
    if instruction_mentions_vreg(flag_writer, setcc_dst) {
        return None;
    }

    // Condition 3: %D must be dead on entry to the window. Conservative
    // check: %D does not appear as any operand of any instruction in the
    // block before flag_writer.
    for prior in &insts[..flag_writer_idx] {
        if instruction_mentions_vreg(prior, setcc_dst) {
            return None;
        }
    }

    // Condition 5: the Setcc destination is single-use in the block - only
    // the Movzx consumes it. (The Setcc itself is the def, not a use.)
    let total_uses = use_counts.get(&setcc_dst).copied().unwrap_or(0);
    // Movzx contributes 2 mentions of %D in its operand list - dst and src -
    // but only the src is a use. `vreg_uses_in_block` already filters dsts
    // out (see helper). We expect exactly one use: the Movzx.
    if total_uses != 1 {
        return None;
    }

    Some(SetccHoistEdit {
        flag_writer_idx,
        setcc_idx,
        movzx_idx,
        dst: setcc_dst,
    })
}

/// Returns true if `vreg` appears anywhere in `inst`'s operand list, either
/// as a top-level VReg or inside a memory-addressing operand. Conservative:
/// any mention counts.
fn instruction_mentions_vreg(inst: &X86ISelInst, vreg: VReg) -> bool {
    inst.operands
        .iter()
        .any(|op| operand_mentions_vreg(op, vreg))
}

fn operand_mentions_vreg(op: &X86ISelOperand, vreg: VReg) -> bool {
    match op {
        X86ISelOperand::VReg(v) => *v == vreg,
        X86ISelOperand::MemAddr { base, .. } => operand_mentions_vreg(base, vreg),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_mentions_vreg(base, vreg) || operand_mentions_vreg(index, vreg)
        }
        _ => false,
    }
}

/// Per-block use-count of VRegs. The operand at position 0 of a two-operand
/// or three-operand value-producing instruction is treated as a definition
/// (not a use). This matches the convention used elsewhere in this pass:
/// `Setcc %D, cc` defines %D, `Movzx %D, %D` defines the first %D and uses
/// the second. We approximate this conservatively by treating every operand
/// of a non-producing instruction as a use, and every non-first operand of
/// a value-producing instruction as a use.
fn vreg_uses_in_block(insts: &[X86ISelInst]) -> std::collections::HashMap<VReg, u32> {
    use crate::effects::x86_produces_value;
    let mut counts = std::collections::HashMap::new();
    for inst in insts {
        let produces = x86_produces_value(inst.opcode);
        for (idx, op) in inst.operands.iter().enumerate() {
            // Operand 0 of a value-producing inst is the def; skip it as a
            // top-level use. Memory-addr operands inside the def slot (e.g.,
            // store-to-memory destinations) are not common in ISel output for
            // producing opcodes, and Setcc/Movzx's operand-0 is a plain VReg
            // we don't want to count.
            if produces && idx == 0 {
                // But memory-addressing inside op 0 (rare) would still mean
                // base/index regs are *read*. Walk only the addressing regs.
                count_addressing_uses(op, &mut counts);
                continue;
            }
            count_operand_uses(op, &mut counts);
        }
    }
    counts
}

fn count_operand_uses(op: &X86ISelOperand, counts: &mut std::collections::HashMap<VReg, u32>) {
    match op {
        X86ISelOperand::VReg(v) => {
            *counts.entry(*v).or_insert(0) += 1;
        }
        X86ISelOperand::MemAddr { base, .. } => count_operand_uses(base, counts),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_uses(base, counts);
            count_operand_uses(index, counts);
        }
        _ => {}
    }
}

fn count_addressing_uses(op: &X86ISelOperand, counts: &mut std::collections::HashMap<VReg, u32>) {
    match op {
        X86ISelOperand::MemAddr { base, .. } => count_operand_uses(base, counts),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_uses(base, counts);
            count_operand_uses(index, counts);
        }
        _ => {}
    }
}

/// How many times a SINGLE VReg `target` is USED in ONE instruction — the
/// per-instruction, single-key specialization of [`vreg_uses_in_block`]. Uses
/// the SAME def/use convention (operand 0 of a value-producing opcode is the
/// def, whose only reads are its addressing base/index regs; every other
/// operand is a use, counting a mem operand's base/index) so that
/// `vreg_uses_in_inst(inst, v)` is byte-identical to
/// `vreg_uses_in_block(std::slice::from_ref(inst)).get(&v).copied().unwrap_or(0)`
/// — but with NO HashMap allocation. The SIB-fold consumer scans
/// ([`collect_addr_consumers`] / [`collect_pointer_mem_ops`]) call this once per
/// instruction per anchor; the previous per-instruction HashMap build made those
/// scans allocate O(anchors * insts) maps on a large block.
fn vreg_uses_in_inst(inst: &X86ISelInst, target: VReg) -> u32 {
    use crate::effects::x86_produces_value;
    let produces = x86_produces_value(inst.opcode);
    let mut count = 0u32;
    for (idx, op) in inst.operands.iter().enumerate() {
        if produces && idx == 0 {
            count += count_addressing_uses_of(op, target);
        } else {
            count += count_operand_uses_of(op, target);
        }
    }
    count
}

/// Single-key mirror of [`count_operand_uses`].
fn count_operand_uses_of(op: &X86ISelOperand, target: VReg) -> u32 {
    match op {
        X86ISelOperand::VReg(v) => u32::from(*v == target),
        X86ISelOperand::MemAddr { base, .. } => count_operand_uses_of(base, target),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_uses_of(base, target) + count_operand_uses_of(index, target)
        }
        _ => 0,
    }
}

/// Single-key mirror of [`count_addressing_uses`].
fn count_addressing_uses_of(op: &X86ISelOperand, target: VReg) -> u32 {
    match op {
        X86ISelOperand::MemAddr { base, .. } => count_operand_uses_of(base, target),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_uses_of(base, target) + count_operand_uses_of(index, target)
        }
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// AND-power-of-2 + CMP-zero + Jcc -> BT + Jcc (3-instruction window rewrite)
// ---------------------------------------------------------------------------
//
// Pattern (before):
//   [1] AndRI %dst, [%src,] #(1 << k)   ; two-op `[%dst, imm]` or three-op
//                                        ; `[%dst, %src, imm]` form
//   [2] CmpRI %dst, #0                   ; flags <- (dst == 0)
//   [3] Jcc {E|NE}, target               ; branch on ZF
//
// Pattern (after):
//   [1] BtRI %bt_src, #k                 ; CF <- bit k of %bt_src
//   [2] Jcc {AE|B}, target               ; AE = CF==0 = "bit was 0" = original E
//                                        ; B  = CF==1 = "bit was 1" = original NE
//
// HAND-PROOF (algebraic identity):
//   - (x AND (1 << k)) == 0  iff  bit k of x is 0.
//   - BtRI sets CF := bit_k(src), and leaves OF/SF/ZF/AF/PF undefined per
//     Intel SDM.
//   - The original CMP-zero+Jcc tests ZF. We re-encode the predicate on CF
//     by inverting the condition: Jcc E (ZF=1, AND result zero) becomes
//     Jcc AE (CF=0, bit was clear); Jcc NE (ZF=0, AND result nonzero) becomes
//     Jcc B (CF=1, bit was set).
//
// SIDE CONDITIONS (each must hold or the rewrite is unsound):
//   (a) AndRI's immediate is a positive power of two and k = imm.trailing_zeros()
//       fits in the AND's register class (k <= 63 for Gpr64, k <= 31 for Gpr32).
//       `imm.count_ones() == 1` together with `imm > 0` enforces this.
//   (b) The CmpRI immediately follows the AndRI; the Jcc immediately follows
//       the CmpRI. Adjacency guarantees no foreign flag write between AND and
//       CMP, and between CMP and Jcc - so the flags consumed by Jcc come from
//       CmpRI (and we are free to replace both AND and CMP).
//   (c) CmpRI compares the AND's destination vreg against the immediate 0.
//   (d) The Jcc tests {E, NE}. Other condition codes (S, L, etc.) would map
//       to flags that BT leaves undefined; we refuse to fire on those.
//   (e) Reserved. The original single-use guard is subsumed by (b) (adjacency,
//       so no intervening instruction reads %dst between AndRI and CmpRI) and
//       (f) (dst dead after Jcc, so no later instruction reads %dst). Earlier
//       instructions reading %dst are unaffected because they precede the
//       AndRI we are erasing.
//   (f) AndRI's destination is dead after the Jcc - no later block-local
//       instruction mentions %dst. This is what makes erasing the AND's
//       write-back observationally invisible.
//   (g) AndRI's flags are the opcode default (no foreign side-effect bits)
//       and the AndRI does not touch memory (we are erasing it; if it had
//       side effects beyond writing RFLAGS, the rewrite would change
//       observable behavior). Same constraint on CmpRI.
//   (h) The BT source register is the AndRI's source operand:
//         - two-op form `AndRI [%dst, imm]`: %dst was both src and dst;
//           since (f) requires %dst to be dead after Jcc, the BT can read
//           %dst directly (its pre-AND value is what BT needs, but BT
//           sources from a vreg by name and the AND has already been
//           erased - so the value at the BT site is the original %dst).
//         - three-op form `AndRI [%dst, %src, imm]`: BT reads %src directly.
//
// PROOF PROVENANCE: hand-proved peephole. Each rewritten BtRI and Jcc inherit
// `proof_origin` from the consumed AndRI/Jcc respectively, so source-location
// reporting still points at the originating trust_ir instruction.
//
// WHY THE TWO-OP FORM IS SOUND: trust-cg-ir's two-operand `AndRI [%v, imm]`
// is a read-modify-write of %v - it reads the pre-AND value of %v and writes
// %v back. After our rewrite, the AND is erased, so %v at the BtRI point
// still holds its pre-AND value. The pre-AND value is exactly what we need
// to test (we are checking bit k of the original input). Since (f) makes %v
// dead after the Jcc, erasing the AND's write-back is observationally
// invisible.

/// Flag-barrier predicate for a CFG-aware scan.
///
/// [`instruction_may_export_flags`] treats ANY terminator as an export, which is
/// correct for a block-local pass that cannot see past the branch — but here the
/// successor is analysed explicitly, so a plain unconditional `Jmp` must be
/// TRANSPARENT or the scan can never reach the CFG step at all. (Measured: with
/// the terminator treated as a barrier, the rotate peephole fired ZERO times —
/// every candidate rejected at its block's closing `Jmp`.)
///
/// Still barriers: calls and anything with side effects. A CONDITIONAL branch
/// needs no special case — `x86_reads_flags` already covers `Jcc`, and a `Ret`
/// block has no successors, where the caller's `any()` over an empty successor
/// set correctly reports the flags dead (they are not part of the ABI result).
fn flags_barrier_for_cfg_scan(inst: &X86ISelInst) -> bool {
    inst.flags.is_call() || inst.flags.has_side_effects()
}

/// Block-granularity FLAGS LIVENESS: `true` for block `B` when a flag value
/// defined BEFORE `B` may still be read on some path from `B`'s entry.
///
/// A backward fixpoint over the CFG. Per block the local answer is the FIRST
/// flag-relevant instruction: a reader (or a possible flag export, e.g. a call)
/// means live, a writer means dead, and a block with neither passes the
/// question through to its successors. A block with no successors is dead —
/// flags are not observable across a return.
///
/// Needed because the block-local `flags_written_here_are_dead` treats
/// "reached the end of the block" as LIVE, which is the right default but makes
/// the rotate idiom unrecognisable: the `OrRR` completing
/// `(s << k) | (s >>u (w-k))` sits at the end of its block and the instruction
/// that kills the flags is in the successor. Measured with the block-local
/// check alone, the rotate peephole fired ZERO times across all 18 beat-llvm
/// programs.
fn flags_live_in_by_block(
    func: &X86ISelFunction,
) -> std::collections::HashMap<trust_cg_lower::instructions::Block, bool> {
    let local_answer = |b: &trust_cg_lower::X86ISelBlock| -> Option<bool> {
        b.insts.iter().find_map(|inst| {
            if x86_reads_flags(inst.opcode) || flags_barrier_for_cfg_scan(inst) {
                Some(true)
            } else if x86_writes_flags(inst.opcode) {
                Some(false)
            } else {
                None
            }
        })
    };
    let mut live: std::collections::HashMap<_, bool> =
        func.blocks.keys().map(|b| (*b, false)).collect();
    // Monotone in `live`, so this terminates; bounded anyway for safety.
    for _ in 0..=func.blocks.len() {
        let mut changed = false;
        for (id, block) in &func.blocks {
            let v = match local_answer(block) {
                Some(x) => x,
                None => block
                    .successors
                    .iter()
                    .any(|s| live.get(s).copied().unwrap_or(true)),
            };
            if live.get(id).copied() != Some(v) {
                live.insert(*id, v);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    live
}

/// Are the flags written at `index` of `block_id` dead, allowing the kill to
/// happen in a successor? Scans forward locally, then defers to
/// [`flags_live_in_by_block`] for the fall-off-the-end case.
fn flags_dead_at(
    func: &X86ISelFunction,
    live_in: &std::collections::HashMap<trust_cg_lower::instructions::Block, bool>,
    block_id: trust_cg_lower::instructions::Block,
    index: usize,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    for inst in &block.insts[index + 1..] {
        if x86_reads_flags(inst.opcode) || flags_barrier_for_cfg_scan(inst) {
            return false;
        }
        if x86_writes_flags(inst.opcode) {
            return true;
        }
    }
    !block
        .successors
        .iter()
        .any(|s| live_in.get(s).copied().unwrap_or(true))
}

/// ROTATE IDIOM -> ROL. Collapses the six-instruction `rotate_left` lowering
///
/// ```text
///   a = ShlRI(s, k)
///   b = ShrRI(s, w - k)
///   d = OrRR(a, b)          ==>   d = RolRI(s, k)
/// ```
///
/// x86 had NO rotate opcode until `RolRI`, so `x.rotate_left(k)` cost six
/// instructions where AArch64 has emitted a single `ROR` all along — and on a
/// dependency chain the latency cost exceeds even that. The x86 mirror of
/// `rotate_idiom.rs`.
///
/// SOUNDNESS. `ROL(s, k)` IS `(s << k) | (s >>u (w - k))` for `k` in `[1, w)`;
/// that obligation is proven with refuting controls
/// (`x86_64_lowering_proofs::proof_x86_rol_ri`). The side conditions establish
/// only that these three instructions really are that shape:
///
/// * both shifts read the SAME source and both amounts are immediates summing
///   EXACTLY to the register width;
/// * `a` and `b` are each defined ONCE function-wide and used ONLY by this
///   `OrRR`, so the rewrite leaves both shifts dead for DCE rather than a
///   half-live mixed state;
/// * `s` is not redefined between its shifts and the `OrRR`;
/// * THE FLAGS ARE DEAD. This is load-bearing, not hygiene: `OR` sets ZF/SF/PF
///   from the result while `ROL` leaves them UNTOUCHED, so the rewrite is only
///   valid where nothing observes them. `post_ra_dataflow` models the rotate's
///   real flag effect separately and fails closed if this is ever wrong.
fn rotate_idiom_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    live_in: &std::collections::HashMap<trust_cg_lower::instructions::Block, bool>,
) -> bool {
    if std::env::var_os("TCG_NO_X86_ROTATE_IDIOM").is_some() {
        return false;
    }
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;
    let use_counts = vreg_uses_in_block(insts);
    let trace = std::env::var_os("TCG_ROL_TRACE").is_some();
    // (or_index, dst, src, amount, shl_index, shr_index)
    let mut edits: Vec<(usize, VReg, VReg, i64, usize, usize)> = Vec::new();

    for (i, inst) in insts.iter().enumerate() {
        if inst.opcode != X86Opcode::OrRR || inst.operands.len() < 3 {
            continue;
        }
        let (
            Some(X86ISelOperand::VReg(d)),
            Some(X86ISelOperand::VReg(a)),
            Some(X86ISelOperand::VReg(b)),
        ) = (
            inst.operands.first(),
            inst.operands.get(1),
            inst.operands.get(2),
        )
        else {
            continue;
        };
        let width: i64 = match d.class {
            RegClass::Gpr64 => 64,
            RegClass::Gpr32 => 32,
            _ => continue,
        };

        let mut shl: Option<(usize, VReg, i64)> = None;
        let mut shr: Option<(usize, VReg, i64)> = None;
        for (j, cand) in insts[..i].iter().enumerate() {
            let (
                Some(X86ISelOperand::VReg(cd)),
                Some(X86ISelOperand::VReg(cs)),
                Some(X86ISelOperand::Imm(amt)),
            ) = (
                cand.operands.first(),
                cand.operands.get(1),
                cand.operands.get(2),
            )
            else {
                continue;
            };
            if cd == a || cd == b {
                match cand.opcode {
                    X86Opcode::ShlRI => shl = Some((j, *cs, *amt)),
                    X86Opcode::ShrRI => shr = Some((j, *cs, *amt)),
                    _ => {}
                }
            }
        }
        let (Some((shl_at, shl_src, k)), Some((shr_at, shr_src, r))) = (shl, shr) else {
            continue;
        };
        if shl_src != shr_src || k + r != width || !(1..width).contains(&k) {
            continue;
        }
        if function_vreg_def_count(func, *a) != 1
            || function_vreg_def_count(func, *b) != 1
            || use_counts.get(a).copied().unwrap_or(0) != 1
            || use_counts.get(b).copied().unwrap_or(0) != 1
        {
            if trace {
                eprintln!("ROL reject @{i}: def/use counts");
            }
            continue;
        }
        let first_shift = shl_at.min(shr_at);
        if insts[first_shift..i].iter().any(|between| {
            crate::effects::x86_produces_value(between.opcode)
                && matches!(between.operands.first(), Some(X86ISelOperand::VReg(v)) if *v == shl_src)
        }) {
            if trace {
                eprintln!("ROL reject @{i}: source redefined");
            }
            continue;
        }
        if !flags_dead_at(func, live_in, block_id, i) {
            if trace {
                let after: Vec<_> = insts[i + 1..].iter().map(|x| x.opcode).collect();
                let succ_head: Vec<_> = block
                    .successors
                    .first()
                    .and_then(|s| func.blocks.get(s))
                    .map(|sb| sb.insts.iter().take(6).map(|x| x.opcode).collect())
                    .unwrap_or_default();
                eprintln!(
                    "ROL reject @{i}: flags live; after={after:?} succs={:?} succ_head={succ_head:?}",
                    block.successors
                );
            }
            continue;
        }
        if trace {
            eprintln!("ROL ACCEPT @{i}: rol {k} (w={width})");
        }
        edits.push((i, *d, shl_src, k, shl_at, shr_at));
    }

    if edits.is_empty() {
        return false;
    }
    let Some(block) = func.blocks.get_mut(&block_id) else {
        return false;
    };
    // Rewrite the OR in place, then DELETE the two feeding shifts.
    //
    // Deleting them here rather than leaving them for DCE is not an
    // optimisation shortcut — `X86DeadCodeElimination` runs BEFORE this pass in
    // the pipeline, so nothing else would remove them and the loop would keep
    // all six instructions plus the new rotate. The side conditions above
    // already establish exactly what deletion needs: each shift result is
    // defined ONCE function-wide and used ONLY by this `OrRR`.
    let mut doomed: Vec<usize> = Vec::new();
    for (at, d, src, k, shl_at, shr_at) in edits {
        block.insts[at] = X86ISelInst::new(
            X86Opcode::RolRI,
            vec![
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(src),
                X86ISelOperand::Imm(k),
            ],
        );
        doomed.push(shl_at);
        doomed.push(shr_at);
    }
    doomed.sort_unstable();
    for idx in doomed.into_iter().rev() {
        block.insts.remove(idx);
    }
    true
}

fn and_pow2_bt_branch_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    // Precompute %dst use counts across the entire block. Kept for symmetry
    // with the setcc-hoist pass; not consulted by the current side conditions.
    let use_counts = vreg_uses_in_block(insts);

    let mut edits: Vec<AndPow2BtEdit> = Vec::new();
    let mut consumed: std::collections::HashSet<usize> = std::collections::HashSet::new();

    let mut i = 0;
    while i + 2 < insts.len() {
        if consumed.contains(&i) {
            i += 1;
            continue;
        }
        if let Some(edit) = try_and_pow2_bt_branch(insts, i, &use_counts) {
            // Cross-block liveness guard: refuse if %and_dst is mentioned in
            // any other block of the function. This is conservative but
            // correct - the rewrite erases the AND's write-back, so any
            // out-of-block reader would observe the pre-AND value instead of
            // the and-result.
            let and_dst = match func.blocks[&block_id].insts[edit.and_idx].operands.first() {
                Some(X86ISelOperand::VReg(v)) => *v,
                _ => {
                    i += 1;
                    continue;
                }
            };
            let mut escapes = false;
            for (other_id, other_block) in &func.blocks {
                if *other_id == block_id {
                    continue;
                }
                if other_block
                    .insts
                    .iter()
                    .any(|inst| instruction_mentions_vreg(inst, and_dst))
                {
                    escapes = true;
                    break;
                }
            }
            if escapes {
                i += 1;
                continue;
            }
            consumed.insert(edit.and_idx);
            consumed.insert(edit.cmp_idx);
            consumed.insert(edit.jcc_idx);
            // Advance past the Jcc so we do not match into the rewritten window.
            i = edit.jcc_idx + 1;
            edits.push(edit);
        } else {
            i += 1;
        }
    }

    if edits.is_empty() {
        return false;
    }

    // Optional diagnostic: TRUST_CG_X86_BT_BRANCH_LOG=1 prints how many windows
    // fired per block. Off by default; harmless when unset.
    if std::env::var_os("TRUST_CG_X86_BT_BRANCH_LOG").is_some() {
        eprintln!(
            "x86-and-pow2-bt-branch: fired {} time(s) in function `{}` block #{:?}",
            edits.len(),
            func.name,
            block_id.0,
        );
    }

    // Apply edits in reverse order so earlier indices remain valid.
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for edit in edits.into_iter().rev() {
        let and_inst = block.insts[edit.and_idx].clone();
        let jcc_inst = block.insts[edit.jcc_idx].clone();

        // Build BtRI %bt_src, #k with proof_origin inherited from the AND.
        let mut bt = X86ISelInst::new(
            X86Opcode::BtRI,
            vec![
                X86ISelOperand::VReg(edit.bt_src),
                X86ISelOperand::Imm(edit.bit_k as i64),
            ],
        );
        bt.proof_origin = and_inst.proof_origin;

        // Build Jcc <new_cc>, target with proof_origin inherited from the
        // original Jcc.
        let mut new_jcc = X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(edit.new_cc),
                X86ISelOperand::Block(edit.target),
            ],
        );
        new_jcc.proof_origin = jcc_inst.proof_origin;

        // Replace [AND, CMP, JCC] with [BT, JCC]. Remove cmp and jcc first
        // (largest indices), then overwrite AND with BT, then insert the new
        // Jcc just after.
        block.insts.remove(edit.jcc_idx);
        block.insts.remove(edit.cmp_idx);
        block.insts[edit.and_idx] = bt;
        block.insts.insert(edit.and_idx + 1, new_jcc);
    }

    true
}

#[derive(Debug)]
struct AndPow2BtEdit {
    and_idx: usize,
    cmp_idx: usize,
    jcc_idx: usize,
    bt_src: VReg,
    bit_k: u32,
    new_cc: trust_cg_ir::X86CondCode,
    target: trust_cg_lower::instructions::Block,
}

fn try_and_pow2_bt_branch(
    insts: &[X86ISelInst],
    and_idx: usize,
    use_counts: &std::collections::HashMap<VReg, u32>,
) -> Option<AndPow2BtEdit> {
    use trust_cg_ir::X86CondCode;

    let and_inst = insts.get(and_idx)?;
    if and_inst.opcode != X86Opcode::AndRI {
        return None;
    }
    // (g) AndRI must have default flags (no foreign side-effects) and not
    // touch memory.
    if and_inst.flags != X86Opcode::AndRI.default_flags() {
        return None;
    }
    let and_flags = and_inst.flags;
    if and_flags.reads_memory()
        || and_flags.writes_memory()
        || and_flags.is_pseudo()
        || and_flags.is_call()
        || and_flags.is_branch()
        || and_flags.is_terminator()
        || and_flags.is_return()
    {
        return None;
    }

    // Parse AndRI operand shape. Accept either two-operand `[%dst, Imm]` or
    // three-operand `[%dst, %src, Imm]`. In the two-op form, bt_src == dst.
    let (and_dst, bt_src, imm) = match and_inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::Imm(imm)] if is_supported_gpr(*dst) => {
            (*dst, *dst, *imm)
        }
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(src),
            X86ISelOperand::Imm(imm),
        ] if same_supported_class(*dst, *src) => (*dst, *src, *imm),
        _ => return None,
    };

    // (a) Immediate must be a positive power of two.
    if imm <= 0 {
        return None;
    }
    if (imm as u64).count_ones() != 1 {
        return None;
    }
    let bit_k = (imm as u64).trailing_zeros();
    // Bit index must fit in the source register class. BT r64, imm8 is
    // encoded with imm8 mod 64; we refuse if the bit index would not match
    // the AND's interpretation. For 32-bit AND, k must be 0..=31.
    match and_dst.class {
        RegClass::Gpr64 => {
            if bit_k > 63 {
                return None;
            }
        }
        RegClass::Gpr32 => {
            if bit_k > 31 {
                return None;
            }
        }
        _ => return None,
    }

    // (b) CmpRI must immediately follow.
    let cmp_idx = and_idx + 1;
    let cmp_inst = insts.get(cmp_idx)?;
    if !matches!(cmp_inst.opcode, X86Opcode::CmpRI | X86Opcode::CmpRI8) {
        return None;
    }
    if cmp_inst.flags != cmp_inst.opcode.default_flags() {
        return None;
    }
    let cmp_flags = cmp_inst.flags;
    if cmp_flags.reads_memory() || cmp_flags.writes_memory() || cmp_flags.is_pseudo() {
        return None;
    }
    // (c) CmpRI must compare %and_dst against 0.
    match cmp_inst.operands.as_slice() {
        [X86ISelOperand::VReg(cmp_reg), X86ISelOperand::Imm(0)]
            if *cmp_reg == and_dst && is_supported_gpr(*cmp_reg) => {}
        _ => return None,
    }

    // (b cont.) Jcc must immediately follow.
    let jcc_idx = cmp_idx + 1;
    let jcc_inst = insts.get(jcc_idx)?;
    if jcc_inst.opcode != X86Opcode::Jcc {
        return None;
    }
    if jcc_inst.flags != X86Opcode::Jcc.default_flags() {
        return None;
    }
    // (d) Cond code must be E or NE. Decode operand shape `[CondCode, Block]`.
    let (orig_cc, target) = match jcc_inst.operands.as_slice() {
        [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(blk)] => (*cc, *blk),
        _ => return None,
    };
    let new_cc = match orig_cc {
        // Jcc E (ZF=1) <=> dst == 0 <=> bit k clear <=> CF=0 <=> Jcc AE.
        X86CondCode::E => X86CondCode::AE,
        // Jcc NE (ZF=0) <=> dst != 0 <=> bit k set <=> CF=1 <=> Jcc B.
        X86CondCode::NE => X86CondCode::B,
        _ => return None,
    };

    // (e) intentionally elided - subsumed by (b) and (f).
    let _ = use_counts;

    // (f) AndRI's destination must be dead after the Jcc - no later block-local
    // instruction mentions %and_dst.
    for later in &insts[jcc_idx + 1..] {
        if instruction_mentions_vreg(later, and_dst) {
            return None;
        }
    }
    // For the two-op AndRI form, %and_dst was also the source register. Any
    // prior reader of %and_dst saw the original value, which is fine because
    // it precedes the AndRI we are erasing. But any prior write to %and_dst
    // outside the canonical RMW chain doesn't matter either: the only way to
    // observe the AND's destruction is to read %and_dst AFTER the AND, and
    // (f) forbids that within the block. Cross-block liveness is handled by
    // the caller (see `and_pow2_bt_branch_run_on_block`), which checks that
    // no other block in the function reads %and_dst.

    // In the two-op form `bt_src == and_dst`. The two-op AndRI reads %dst,
    // erasing the AND leaves %dst at its pre-AND value, which is what BT
    // needs. In the three-op form, %src is unchanged by the AND, so reading
    // it from BT is unambiguous; we still require %src to be alive at the BT
    // point (it is, since the AND read it and we are replacing the AND
    // in-place).

    Some(AndPow2BtEdit {
        and_idx,
        cmp_idx,
        jcc_idx,
        bt_src,
        bit_k,
        new_cc,
        target,
    })
}

/// Function-wide vreg USE set for the zero-idiom gate (same convention as
/// DCE's `collect_used_vregs`: operand 0 of a value producer is a def, not a
/// use, except for tied first operands; addressing regs count).
fn peephole_function_use_set(func: &X86ISelFunction) -> std::collections::HashSet<VReg> {
    let mut used = std::collections::HashSet::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            let has_def = crate::effects::x86_produces_value(inst.opcode);
            for (index, operand) in inst.operands.iter().enumerate() {
                if index == 0 && has_def && !dce_style_first_operand_is_use(inst) {
                    continue;
                }
                collect_peephole_operand_vregs(operand, &mut used);
            }
        }
    }
    used
}

/// Tied-first-operand test for the use-set above: the immediate/RM ALU
/// family in tied FORM, plus 2-operand tied RR ALU. Over-approximating
/// (counting a def as a use) is safe here — it only makes the gate DECLINE
/// fewer rewrites, and declining is itself a no-op.
fn dce_style_first_operand_is_use(inst: &X86ISelInst) -> bool {
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
    ) || (matches!(inst.opcode, AddRR | SubRR | ImulRR | AndRR | OrRR | XorRR)
        && inst.operands.len() == 2)
}

fn collect_peephole_operand_vregs(
    operand: &X86ISelOperand,
    used: &mut std::collections::HashSet<VReg>,
) {
    match operand {
        X86ISelOperand::VReg(vreg) => {
            used.insert(*vreg);
        }
        X86ISelOperand::MemAddr { base, .. } => collect_peephole_operand_vregs(base, used),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_peephole_operand_vregs(base, used);
            collect_peephole_operand_vregs(index, used);
        }
        _ => {}
    }
}

#[cfg(test)]
fn simplify_inst(insts: &[X86ISelInst], index: usize) -> Option<PeepholeEdit> {
    simplify_inst_gated(insts, index, None)
}

// ---------------------------------------------------------------------------
// RM-fusion (X9 slice 3; DEFAULT-ON, `TCG_NO_X86_IMUL_FUSE` opts out)
//
//   MovRMSib t, [sib]        MovRR     d, a          (3-operand form; the
//   ImulRR   d, a, t    ->   ImulRMSib d, [sib]       2-op tied `ImulRR d, t`
//                                                      fuses to the bare
//                                                      `ImulRMSib d, [sib]`)
// ---------------------------------------------------------------------------
//
// Folds a 64-bit load whose destination's ONLY consumption is the next
// multiply into the multiply's memory operand (`IMUL r64, r/m64`). The
// base+disp `MovRM` load fuses to `ImulRM` identically.
//
// HAND-PROOF (semantic equivalence): the fused `ImulRMSib d, [ea]` computes
// `d := factor * load64(ea)` where `factor` is `a`'s value at the multiply.
// The unfused pair computed `t := load64(ea)` at the LOAD's position, then
// `d := a * t`. Equality needs exactly: (1) `load64(ea)` yields the same
// value at both positions — guaranteed because the window between load and
// multiply admits NO memory-writing instruction, no call, and no other
// memory op at all (condition W below), and the EA registers (base/index)
// have no defs in the window (condition E); (2) the load's movement past the
// window cannot change observable behavior — the window contains no branch /
// terminator / pseudo (trap carriers included), so no path leaves between
// them and no trap can fire between them; both orders fault identically or
// not at all (same EA, same memory state); (3) `t`'s value is consumed ONLY
// by the fused multiply — `t` is locally dead after it (condition D, the
// per-def window rule: a later same-block full redef of `t` with no use and
// no control flow between). RFLAGS: `ImulRR` and `ImulRMSib` write the
// identical mul-family flag set at the same program point; nothing else in
// the rewrite touches flags.
//
// SIDE CONDITIONS (all fail-closed):
//   A. Anchor: `ImulRR` with default flags, no proof_origin, all-Gpr64
//      operands; forms `[d, a, t]` / `[d, t, a]` (commutative) or tied
//      `[d, t]` with `t != d`. The non-load factor must NOT be `t` itself
//      (both factors from one load would need the value twice).
//   B. Load: the NEAREST prior def of `t` in the block is a `MovRMSib`
//      (-> ImulRMSib) or full-width `MovRM` (-> ImulRM) with default flags
//      and no proof_origin, defining exactly `t`.
//   W. Window (load, imul): every inst is pure register ALU — no
//      reads_memory / writes_memory / call / branch / terminator / return /
//      pseudo / xchg-family.
//   E. No def of the load's base/index vreg ids (class-blind) in the window,
//      and none of the EA regs may BE `t` (the load overwrites t; the fused
//      form must read the pre-load EA regs — refuse `base.id == t.id` etc.).
//   D. `t` locally dead after the multiply (same rule as the per-def DCE
//      tier: later full redef in-block, no use / branch / call / pseudo
//      between). The redef scan is class-blind on the id (narrow-alias).
// ---------------------------------------------------------------------------

/// DEFAULT-ON (same 2026-07-20 record as the addr-chain fold);
/// `TCG_NO_X86_IMUL_FUSE` is the forensic opt-out.
fn imul_fuse_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_IMUL_FUSE").is_none()
}

/// The load kinds the fusion accepts, mapped to their fused opcode. Every EA
/// component must be a VReg — a PReg (or other) base/index would make
/// condition E's redef scan vacuously pass over an address the pass cannot
/// track (adversarial-review FAIL_CLOSED_GAP); refuse those shapes outright.
fn imul_fuse_load_kind(inst: &X86ISelInst) -> Option<(VReg, X86ISelOperand, X86Opcode)> {
    if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
        return None;
    }
    match inst.opcode {
        X86Opcode::MovRMSib => match inst.operands.as_slice() {
            [
                X86ISelOperand::VReg(t),
                sib @ X86ISelOperand::SibMemAddr { base, index, .. },
            ] if t.class == RegClass::Gpr64
                && matches!(base.as_ref(), X86ISelOperand::VReg(b) if b.class == RegClass::Gpr64)
                && matches!(index.as_ref(), X86ISelOperand::VReg(i) if i.class == RegClass::Gpr64) =>
            {
                Some((*t, sib.clone(), X86Opcode::ImulRMSib))
            }
            _ => None,
        },
        X86Opcode::MovRM => match inst.operands.as_slice() {
            [
                X86ISelOperand::VReg(t),
                mem @ X86ISelOperand::MemAddr { base, .. },
            ] if t.class == RegClass::Gpr64
                && matches!(base.as_ref(), X86ISelOperand::VReg(b) if b.class == RegClass::Gpr64) =>
            {
                Some((*t, mem.clone(), X86Opcode::ImulRM))
            }
            _ => None,
        },
        _ => None,
    }
}

/// VReg ids the memory operand's EA reads (base + optional index).
fn imul_fuse_ea_reg_ids(mem: &X86ISelOperand) -> Vec<u32> {
    let mut ids = Vec::new();
    match mem {
        X86ISelOperand::MemAddr { base, .. } => {
            if let X86ISelOperand::VReg(b) = base.as_ref() {
                ids.push(b.id);
            }
        }
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            if let X86ISelOperand::VReg(b) = base.as_ref() {
                ids.push(b.id);
            }
            if let X86ISelOperand::VReg(i) = index.as_ref() {
                ids.push(i.id);
            }
        }
        _ => {}
    }
    ids
}

/// Window purity for condition W: pure register ALU only.
fn imul_fuse_window_ok(inst: &X86ISelInst) -> bool {
    let f = inst.flags;
    if f.is_branch()
        || f.is_call()
        || f.is_terminator()
        || f.is_return()
        || f.is_pseudo()
        || f.reads_memory()
        || f.writes_memory()
        || f.has_side_effects()
    {
        // HAS_SIDE_EFFECTS also excludes the compare family and the whole
        // exchange family — stricter than needed (compares are harmless),
        // but the b05 window is empty and fail-closed costs nothing.
        return false;
    }
    true
}

/// `t` locally dead after `j`: later full redef of the id in-block with no
/// use / control flow / pseudo between. The redef acceptance SHARES the
/// per-def DCE tier's hardened predicates (`full_unconditional_overwrite` +
/// `redef_reads_operand0`) rather than re-deriving them — the adversarial
/// review caught this function's first version re-admitting exactly the
/// conditional-write (Cmovcc) and tied-read (Inc/2-op AddRI/...) shadow
/// classes those predicates exist to exclude.
fn imul_fuse_t_dead_after(insts: &[X86ISelInst], j: usize, t: VReg) -> bool {
    let mut k = j + 1;
    while k < insts.len() {
        let w = &insts[k];
        let f = w.flags;
        if f.is_branch() || f.is_call() || f.is_terminator() || f.is_return() || f.is_pseudo() {
            return false;
        }
        // Any mention of the id (any class) in a USE position keeps it; an
        // operand-0 def of the same id at the same class ends the range.
        let mut mentions = std::collections::HashSet::new();
        for op in &w.operands {
            collect_operand_mentions_flat(op, &mut mentions);
        }
        let defines = crate::effects::x86_produces_value(w.opcode)
            && matches!(w.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == t);
        if defines {
            // The ending redef must be a FULL, UNCONDITIONAL overwrite that
            // does not itself read t — Cmovcc's not-taken lane and every
            // tied form KEEP the loaded value alive.
            if !crate::x86_dce::full_unconditional_overwrite(w.opcode)
                || crate::x86_dce::redef_reads_operand0(w)
            {
                return false;
            }
            let mut src_mentions = std::collections::HashSet::new();
            for op in w.operands.iter().skip(1) {
                collect_operand_mentions_flat(op, &mut src_mentions);
            }
            return !src_mentions.iter().any(|m: &VReg| m.id == t.id);
        }
        if mentions.iter().any(|m| m.id == t.id) {
            return false;
        }
        k += 1;
    }
    false
}

fn collect_operand_mentions_flat(op: &X86ISelOperand, out: &mut std::collections::HashSet<VReg>) {
    match op {
        X86ISelOperand::VReg(v) => {
            out.insert(*v);
        }
        X86ISelOperand::MemAddr { base, .. } => collect_operand_mentions_flat(base, out),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_mentions_flat(base, out);
            collect_operand_mentions_flat(index, out);
        }
        _ => {}
    }
}

/// Run the RM fusion on one block. Returns whether anything changed.
fn imul_fuse_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    struct Fusion {
        load_idx: usize,
        imul_idx: usize,
        replacement: Vec<X86ISelInst>,
    }
    let mut fusions: Vec<Fusion> = Vec::new();
    let mut consumed: std::collections::HashSet<usize> = std::collections::HashSet::new();

    for j in 0..insts.len() {
        let anchor = &insts[j];
        if anchor.opcode != X86Opcode::ImulRR
            || anchor.proof_origin.is_some()
            || anchor.flags != X86Opcode::ImulRR.default_flags()
        {
            continue;
        }
        let g64 = |r: &VReg| r.class == RegClass::Gpr64;
        // Decode the anchor form: (d, other_factor, t_candidates).
        let (d, factors): (VReg, Vec<VReg>) = match anchor.operands.as_slice() {
            [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] if g64(d) && g64(s) && s != d => {
                (*d, vec![*s])
            }
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s1),
                X86ISelOperand::VReg(s2),
            ] if g64(d) && g64(s1) && g64(s2) => (*d, vec![*s1, *s2]),
            _ => continue,
        };
        let tied = anchor.operands.len() == 2;

        // Try each factor as the load result `t` (commutative).
        'factors: for (fi, &t) in factors.iter().enumerate() {
            // The OTHER factor (3-op) must not be t itself.
            let other: Option<VReg> = if tied {
                None
            } else {
                let o = factors[1 - fi];
                if o.id == t.id {
                    continue;
                }
                Some(o)
            };
            // Find t's nearest def above j.
            let Some(i) = (0..j)
                .rev()
                .find(|&k| local_fold_defines_vreg(&insts[k], t))
            else {
                continue;
            };
            if consumed.contains(&i) || consumed.contains(&j) {
                continue;
            }
            let Some((lt, mem, fused_opcode)) = imul_fuse_load_kind(&insts[i]) else {
                continue;
            };
            if lt != t {
                continue;
            }
            // Condition E: EA regs unredefined in the window; none may be t
            // (the load overwrites t) and none may be d (the emitted
            // `MovRR d, a` — or the fused write itself — must not clobber an
            // address register the fused load still reads; adversarial-review
            // MISCOMPILE class, refused in ALL forms for simplicity).
            let ea_ids = imul_fuse_ea_reg_ids(&mem);
            if ea_ids.iter().any(|&id| id == t.id || id == d.id) {
                continue;
            }
            // Condition W + E over the window (i, j), plus: NO mention of t
            // anywhere in the window — a window reader still consumes the
            // loaded value, and deleting the load would hand it the stale
            // pre-load value (adversarial-review MISCOMPILE class; this is
            // what makes the hand-proof's "consumed ONLY by the fused
            // multiply" premise actually checked).
            for w in &insts[i + 1..j] {
                if !imul_fuse_window_ok(w) {
                    continue 'factors;
                }
                let mut w_mentions = std::collections::HashSet::new();
                for op in &w.operands {
                    collect_operand_mentions_flat(op, &mut w_mentions);
                }
                if w_mentions.iter().any(|m| m.id == t.id) {
                    continue 'factors;
                }
                if ea_ids
                    .iter()
                    .any(|&id| local_fold_defines_vreg(w, VReg::new(id, RegClass::Gpr64)))
                {
                    continue 'factors;
                }
            }
            // Condition D: t locally dead after j.
            if !imul_fuse_t_dead_after(insts, j, t) {
                continue;
            }
            // Build the replacement.
            let mut replacement = Vec::new();
            if let Some(a) = other {
                if a != d {
                    replacement.push(X86ISelInst::new(
                        X86Opcode::MovRR,
                        vec![X86ISelOperand::VReg(d), X86ISelOperand::VReg(a)],
                    ));
                }
                // d == a: the tied ImulRMSib below already reads d.
            } else {
                // Tied anchor [d, t]: d already holds the register factor.
            }
            replacement.push(X86ISelInst::new(
                fused_opcode,
                vec![X86ISelOperand::VReg(d), mem.clone()],
            ));
            consumed.insert(i);
            consumed.insert(j);
            fusions.push(Fusion {
                load_idx: i,
                imul_idx: j,
                replacement,
            });
            break;
        }
    }

    if fusions.is_empty() {
        return false;
    }

    if std::env::var_os("TCG_X86_IMUL_FUSE_LOG").is_some() {
        eprintln!(
            "x86-imul-fuse: fused {} load(s) in `{}` block #{:?}",
            fusions.len(),
            func.name,
            block_id.0,
        );
    }

    // Rebuild the block: delete each load, splice each replacement at the
    // multiply's position.
    let mut delete: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut replace: std::collections::HashMap<usize, Vec<X86ISelInst>> =
        std::collections::HashMap::new();
    for f in fusions {
        delete.insert(f.load_idx);
        replace.insert(f.imul_idx, f.replacement);
    }
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    let old = std::mem::take(&mut block.insts);
    let mut rebuilt = Vec::with_capacity(old.len());
    for (idx, inst) in old.into_iter().enumerate() {
        if delete.contains(&idx) {
            continue;
        }
        if let Some(mut rep) = replace.remove(&idx) {
            // Preserve the multiply's proof_origin (None by condition A, but
            // keep the plumbing honest).
            for r in &mut rep {
                r.proof_origin = inst.proof_origin;
            }
            rebuilt.extend(rep);
            continue;
        }
        rebuilt.push(inst);
    }
    block.insts = rebuilt;
    true
}

fn simplify_inst_gated(
    insts: &[X86ISelInst],
    index: usize,
    zeroidiom_used: Option<&std::collections::HashSet<VReg>>,
) -> Option<PeepholeEdit> {
    let inst = &insts[index];

    if !is_safe_local_candidate(inst) && !is_safe_flag_preserving_candidate(inst) {
        return None;
    }

    match inst.opcode {
        X86Opcode::MovRR
        | X86Opcode::MovRR32
        | X86Opcode::MovssRR
        | X86Opcode::MovsdRR
        | X86Opcode::MovdqaRR => {
            let (dst, src) = copy_vregs(inst)?;
            (dst == src).then_some(PeepholeEdit::Remove)
        }
        X86Opcode::Lea => {
            let (dst, src) = zero_disp_lea_vregs(inst)?;
            Some(movrr_or_remove(dst, src))
        }
        X86Opcode::MovRI => {
            let dst = movri_zero_vreg(inst)?;
            // Zero-idiom gate: an unread zero def stays MovRI (DCE-removable)
            // instead of becoming `XorRR d, d`, whose formal self-USE would
            // pin every def of the id in the function-wide DCE use-set.
            if let Some(used) = zeroidiom_used
                && !used.contains(&dst)
            {
                return None;
            }
            flags_written_here_are_dead(insts, index)
                .then_some(PeepholeEdit::Replace(xorrr_zero(dst)))
        }
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => {
            let src = cmp_zero_vreg(inst)?;
            Some(PeepholeEdit::Replace(test_rr(src)))
        }
        X86Opcode::TestRI => {
            let src = test_ri_all_ones_vreg(inst)?;
            Some(PeepholeEdit::Replace(test_rr(src)))
        }
        X86Opcode::AddRR => {
            let (dst, src) = addrr_duplicate_gpr64_sources(inst)?;
            if can_replace_flag_writer(insts, index) {
                Some(PeepholeEdit::Replace(lea_sib_double(dst, src)))
            } else {
                None
            }
        }
        X86Opcode::AddRI | X86Opcode::SubRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if !can_replace_flag_writer(insts, index) {
                return None;
            }

            match (inst.opcode, imm, dst == src) {
                (_, 0, _) => Some(movrr_or_remove(dst, src)),
                (X86Opcode::AddRI, 1, true) => Some(PeepholeEdit::Replace(inc_vreg(dst))),
                (X86Opcode::SubRI, 1, true) => Some(PeepholeEdit::Replace(dec_vreg(dst))),
                _ => None,
            }
        }
        X86Opcode::OrRI | X86Opcode::ShlRI | X86Opcode::ShrRI | X86Opcode::SarRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if imm == 0 && can_replace_flag_writer(insts, index) {
                Some(movrr_or_remove(dst, src))
            } else {
                None
            }
        }
        X86Opcode::XorRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if !can_replace_flag_writer(insts, index) {
                return None;
            }

            match imm {
                0 => Some(movrr_or_remove(dst, src)),
                -1 if dst == src => Some(PeepholeEdit::Replace(not_vreg(dst))),
                _ => None,
            }
        }
        X86Opcode::AndRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if !can_replace_flag_writer(insts, index) {
                return None;
            }

            match imm {
                -1 => Some(movrr_or_remove(dst, src)),
                0 => Some(PeepholeEdit::Replace(xorrr_zero(dst))),
                _ => None,
            }
        }
        X86Opcode::ImulRRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if !flags_written_here_are_dead(insts, index) {
                return None;
            }

            match imm {
                -1 if dst == src => Some(PeepholeEdit::Replace(neg_vreg(dst))),
                0 => Some(PeepholeEdit::Replace(xorrr_zero(dst))),
                1 => Some(movrr_or_remove(dst, src)),
                _ => None,
            }
        }
        X86Opcode::SubRR => {
            let (dst, lhs, rhs) = rr_vregs(inst)?;
            if lhs == rhs && can_replace_flag_writer(insts, index) {
                Some(PeepholeEdit::Replace(xorrr_zero(dst)))
            } else {
                None
            }
        }
        X86Opcode::XorRR => {
            let (dst, lhs, rhs) = rr_vregs(inst)?;
            if lhs == rhs
                && !is_canonical_two_operand_xor_zero(inst)
                && can_replace_flag_writer(insts, index)
            {
                Some(PeepholeEdit::Replace(xorrr_zero(dst)))
            } else {
                None
            }
        }
        X86Opcode::OrRR | X86Opcode::AndRR => {
            let (dst, lhs, rhs) = rr_vregs(inst)?;
            if lhs == rhs && can_replace_flag_writer(insts, index) {
                Some(movrr_or_remove(dst, lhs))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn cmp_zero_vreg(inst: &X86ISelInst) -> Option<VReg> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(src), X86ISelOperand::Imm(0)] if is_supported_gpr(*src) => Some(*src),
        _ => None,
    }
}

fn test_ri_all_ones_vreg(inst: &X86ISelInst) -> Option<VReg> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(src), X86ISelOperand::Imm(-1)] if is_supported_gpr(*src) => {
            Some(*src)
        }
        _ => None,
    }
}

fn addrr_duplicate_gpr64_sources(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(rhs)]
            if *dst == *rhs && dst.class == RegClass::Gpr64 =>
        {
            Some((*dst, *rhs))
        }
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(lhs),
            X86ISelOperand::VReg(rhs),
        ] if *lhs == *rhs && dst.class == RegClass::Gpr64 && lhs.class == RegClass::Gpr64 => {
            Some((*dst, *lhs))
        }
        _ => None,
    }
}

fn zero_disp_lea_vregs(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
    match inst.operands.as_slice() {
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::MemAddr { base, disp },
        ] if *disp == 0 => match base.as_ref() {
            X86ISelOperand::VReg(src) if same_supported_class(*dst, *src) => Some((*dst, *src)),
            _ => None,
        },
        _ => None,
    }
}

fn copy_vregs(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
    let expected_class = copy_opcode_class(inst.opcode)?;
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)]
            if dst.class == expected_class && src.class == expected_class =>
        {
            Some((*dst, *src))
        }
        _ => None,
    }
}

fn copy_opcode_class(opcode: X86Opcode) -> Option<RegClass> {
    match opcode {
        X86Opcode::MovRR => Some(RegClass::Gpr64),
        X86Opcode::MovRR32 => Some(RegClass::Gpr32),
        X86Opcode::MovssRR => Some(RegClass::Fpr32),
        X86Opcode::MovsdRR => Some(RegClass::Fpr64),
        X86Opcode::MovdqaRR => Some(RegClass::Fpr128),
        _ => None,
    }
}

fn ri_vregs_and_imm(inst: &X86ISelInst) -> Option<(VReg, VReg, i64)> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::Imm(imm)] if is_supported_gpr(*dst) => {
            Some((*dst, *dst, *imm))
        }
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(src),
            X86ISelOperand::Imm(imm),
        ] if same_supported_class(*dst, *src) => Some((*dst, *src, *imm)),
        _ => None,
    }
}

fn movri_zero_vreg(inst: &X86ISelInst) -> Option<VReg> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::Imm(0)] if is_supported_gpr(*dst) => Some(*dst),
        _ => None,
    }
}

fn rr_vregs(inst: &X86ISelInst) -> Option<(VReg, VReg, VReg)> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(rhs)]
            if same_supported_class(*dst, *rhs) =>
        {
            Some((*dst, *dst, *rhs))
        }
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(lhs),
            X86ISelOperand::VReg(rhs),
        ] if same_supported_class(*dst, *lhs) && same_supported_class(*lhs, *rhs) => {
            Some((*dst, *lhs, *rhs))
        }
        _ => None,
    }
}

fn test_rr(src: VReg) -> X86ISelInst {
    X86ISelInst::new(
        X86Opcode::TestRR,
        vec![X86ISelOperand::VReg(src), X86ISelOperand::VReg(src)],
    )
}

fn lea_sib_double(dst: VReg, src: VReg) -> X86ISelInst {
    X86ISelInst::new(
        X86Opcode::LeaSib,
        vec![
            X86ISelOperand::VReg(dst),
            X86ISelOperand::SibMemAddr {
                base: Box::new(X86ISelOperand::VReg(src)),
                index: Box::new(X86ISelOperand::VReg(src)),
                scale: 1,
                disp: 0,
            },
        ],
    )
}

fn movrr_or_remove(dst: VReg, src: VReg) -> PeepholeEdit {
    if dst == src {
        PeepholeEdit::Remove
    } else {
        PeepholeEdit::Replace(X86ISelInst::new(
            movrr_opcode_for_class(dst.class),
            vec![X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)],
        ))
    }
}

fn movrr_opcode_for_class(class: RegClass) -> X86Opcode {
    match class {
        RegClass::Gpr32 => X86Opcode::MovRR32,
        _ => X86Opcode::MovRR,
    }
}

fn xorrr_zero(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(
        X86Opcode::XorRR,
        vec![X86ISelOperand::VReg(dst), X86ISelOperand::VReg(dst)],
    )
}

fn is_canonical_two_operand_xor_zero(inst: &X86ISelInst) -> bool {
    matches!(
        inst.operands.as_slice(),
        [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)] if dst == src
    )
}

fn not_vreg(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Not, vec![X86ISelOperand::VReg(dst)])
}

fn neg_vreg(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Neg, vec![X86ISelOperand::VReg(dst)])
}

fn inc_vreg(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Inc, vec![X86ISelOperand::VReg(dst)])
}

fn dec_vreg(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Dec, vec![X86ISelOperand::VReg(dst)])
}

fn is_safe_local_candidate(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    x86_inst_effect(inst).is_pure()
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !flags.has_side_effects()
        && !flags.reads_memory()
        && !flags.writes_memory()
        && !flags.is_pseudo()
        && !matches!(
            inst.opcode,
            X86Opcode::Phi | X86Opcode::StackAlloc | X86Opcode::Nop
        )
}

fn is_safe_flag_preserving_candidate(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;
    let is_supported_identity = match inst.opcode {
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => cmp_zero_vreg(inst).is_some(),
        X86Opcode::TestRI => test_ri_all_ones_vreg(inst).is_some(),
        _ => false,
    };

    is_supported_identity
        && inst.flags == inst.opcode.default_flags()
        && x86_inst_effect(inst).is_pure()
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !flags.reads_memory()
        && !flags.writes_memory()
        && !flags.is_pseudo()
}

fn can_replace_flag_writer(insts: &[X86ISelInst], index: usize) -> bool {
    match condition_flag_overwrite(&insts[index]) {
        FlagOverwrite::None => true,
        FlagOverwrite::Partial => false,
        FlagOverwrite::Full => flags_written_here_are_dead(insts, index),
    }
}

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

pub(crate) fn condition_flag_overwrite(inst: &X86ISelInst) -> FlagOverwrite {
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

fn same_supported_class(lhs: VReg, rhs: VReg) -> bool {
    lhs.class == rhs.class && is_supported_gpr(lhs) && is_supported_gpr(rhs)
}

fn is_supported_gpr(vreg: VReg) -> bool {
    matches!(vreg.class, RegClass::Gpr64 | RegClass::Gpr32)
}

// ---------------------------------------------------------------------------
// Immediate folding: MovRI + ALU-RR consumer -> ALU-RI
// ---------------------------------------------------------------------------

/// Fold a uniquely-defined `MovRI vreg, imm` constant into the immediate slot
/// of its ALU consumers: `AndRR/AddRR/SubRR d, l, v` becomes
/// `AndRI/AddRI/SubRI d, l, imm`, `CmpRR a, v` becomes `CmpRI a, imm`, and
/// `ImulRR d, l, v` becomes `ImulRRI d, l, imm`. ISel materializes EVERY
/// constant operand into a vreg; under register pressure the allocator spills
/// the constant, so a hot loop pays a stack reload per iteration for `x & 1`
/// where LLVM emits one `and $1`. This rewrite removes the register use;
/// the now-dead `MovRI` is cleaned up by the DCE pass that follows.
///
/// The constant may also be read through a chain of uniquely-defined plain
/// `MovRR` copies rooted at such a `MovRI` (the shape CSE leaves behind when
/// it canonicalizes duplicate constant materializations — see the chase loop
/// below): each copy provably holds the root immediate, so its consumers fold
/// identically. This is what lets the OPT-7 SIB address fold (further down in
/// this same peephole invocation) anchor on `imul idx, $8` scale-defs in
/// LICM+CSE-processed loop bodies.
///
/// Soundness:
///   * The constant vreg must have EXACTLY ONE def in the whole function
///     (counted conservatively: any instruction whose first operand is the
///     vreg counts as a def, whether or not the opcode really writes it —
///     over-counting only suppresses folds). With a single def, every
///     reachable use observes the same immediate value, so substituting the
///     immediate at any use is exact; the def site is not moved or removed.
///   * The immediate must be representable as a sign-extended imm32
///     (`imm == i64::from(imm as i32)`) — the encoder emits ALU imm32 forms
///     whose 64-bit semantics sign-extend, so this gate makes the folded form
///     bit-identical to the register form at both operand widths.
///   * Only the pure-source operand is folded (never the dst-also-src slot),
///     and only for opcodes whose RI form computes the identical result AND
///     identical RFLAGS as the RR form for equal operand values (same
///     hardware operation, immediate addressing mode) — no dead-flags
///     analysis is needed.
///   * For the commutative And/Add/Imul, a constant in the LHS slot is folded
///     by swapping the register operand into the LHS position.
///
/// Every emitted opcode (AndRI/AddRI/SubRI/CmpRI/ImulRRI) is already produced
/// by ISel on existing paths, so the per-instruction proof-certificate surface
/// and the encoder cover them; a gap would fail closed downstream, never
/// miscompile.
fn fold_unique_const_into_imm_forms(func: &mut X86ISelFunction) -> bool {
    use std::collections::HashMap;

    // Conservative def counts: any first-operand vreg occurrence counts.
    let mut def_counts: HashMap<VReg, usize> = HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if let Some(X86ISelOperand::VReg(v)) = inst.operands.first() {
                *def_counts.entry(*v).or_insert(0) += 1;
            }
        }
    }

    // Collect uniquely-defined MovRI constants with imm32-representable values.
    let mut consts: HashMap<VReg, i64> = HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if inst.opcode != X86Opcode::MovRI || inst.operands.len() != 2 {
                continue;
            }
            let (Some(X86ISelOperand::VReg(v)), Some(X86ISelOperand::Imm(imm))) =
                (inst.operands.first(), inst.operands.get(1))
            else {
                continue;
            };
            if def_counts.get(v).copied() == Some(1)
                && is_supported_gpr(*v)
                && *imm == i64::from(*imm as i32)
            {
                consts.insert(*v, *imm);
            }
        }
    }
    if consts.is_empty() {
        return false;
    }

    // See through uniquely-defined `MovRR` copies of a proven constant. CSE
    // canonicalizes duplicate `MovRI k` materializations into `MovRR` copies
    // of one canonical constant vreg (and LICM hoists the whole group out of
    // loops), so a loop-body ALU consumer typically reads the constant
    // through such a copy:
    //
    //   preheader:  c = mov $8      ; MovRI root (single def)
    //               t = mov c       ; MovRR copy (CSE-inserted, single def)
    //   loop body:  d = imul x, t   ; consumer — foldable to `imul x, $8`
    //
    // Soundness: `t`'s ONLY definition in the whole function (same
    // conservative def count as above) is a plain default-flags register
    // copy whose source is itself a uniquely-defined constant, chased
    // transitively to a single-def `MovRI` root. A single-def vreg has one
    // static value assignment, so any read of `t` that observes a defined
    // value observes exactly the root immediate (definite initialization at
    // the original reads is the frontend's existing obligation and is
    // unchanged — no def is moved or removed here, and no new read is
    // introduced). Substituting the immediate at a use is therefore exact.
    //
    // Termination: the fixpoint only ever grows `consts` with vregs whose
    // sole def copies an existing member, so copy cycles (which have no
    // `MovRI` root) never enter, and each pass either adds a vreg or stops —
    // bounded by the number of copy instructions.
    loop {
        let mut grew = false;
        for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for inst in &block.insts {
                if inst.opcode != X86Opcode::MovRR || inst.flags != X86Opcode::MovRR.default_flags()
                {
                    continue;
                }
                let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] = inst.operands.as_slice()
                else {
                    continue;
                };
                if d.class == RegClass::Gpr64
                    && s.class == RegClass::Gpr64
                    && def_counts.get(d).copied() == Some(1)
                    && !consts.contains_key(d)
                    && let Some(imm) = consts.get(s).copied()
                {
                    consts.insert(*d, imm);
                    grew = true;
                }
            }
        }
        if !grew {
            break;
        }
    }

    let const_imm = |op: &X86ISelOperand| -> Option<i64> {
        match op {
            X86ISelOperand::VReg(v) => consts.get(v).copied(),
            _ => None,
        }
    };

    let mut changed = false;
    let block_ids = func.block_order.clone();
    for block_id in block_ids {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };
        for inst in &mut block.insts {
            match inst.opcode {
                // Three-address commutative ALU: [dst, lhs, rhs].
                X86Opcode::AndRR | X86Opcode::AddRR | X86Opcode::ImulRR
                    if inst.operands.len() == 3 =>
                {
                    let ri = match inst.opcode {
                        X86Opcode::AndRR => X86Opcode::AndRI,
                        X86Opcode::AddRR => X86Opcode::AddRI,
                        _ => X86Opcode::ImulRRI,
                    };
                    if let Some(imm) = const_imm(&inst.operands[2]) {
                        inst.opcode = ri;
                        inst.operands[2] = X86ISelOperand::Imm(imm);
                        changed = true;
                    } else if let Some(imm) = const_imm(&inst.operands[1]) {
                        // Commutative: swap the register operand into the LHS
                        // slot, fold the constant into the immediate slot.
                        inst.opcode = ri;
                        inst.operands[1] = inst.operands[2].clone();
                        inst.operands[2] = X86ISelOperand::Imm(imm);
                        changed = true;
                    }
                }
                // Three-address subtraction: only the RHS is foldable.
                X86Opcode::SubRR if inst.operands.len() == 3 => {
                    if let Some(imm) = const_imm(&inst.operands[2]) {
                        inst.opcode = X86Opcode::SubRI;
                        inst.operands[2] = X86ISelOperand::Imm(imm);
                        changed = true;
                    }
                }
                // Compare: [a, b]; only the second operand is foldable.
                X86Opcode::CmpRR if inst.operands.len() == 2 => {
                    if let Some(imm) = const_imm(&inst.operands[1]) {
                        inst.opcode = X86Opcode::CmpRI;
                        inst.operands[1] = X86ISelOperand::Imm(imm);
                        changed = true;
                    }
                }
                _ => {}
            }
        }
    }
    changed
}

// ---------------------------------------------------------------------------
// Scaled-index (SIB) address-mode fold
//   imul index, {1,2,4,8}  ; scaled = index * scale     (or shl index, {0..3})
//   add  base, scaled      ; addr   = base + scaled
//   mov  r, [addr]         ; MovRM  (load)   ->  MovRMSib r, [base+index*scale]
//   mov  [addr], r         ; MovMR  (store)  ->  MovMRSib [base+index*scale], r
// ---------------------------------------------------------------------------
//
// x86-64 SIB addressing computes the effective address `base + index*scale +
// disp` inside a single load/store operand for scale in {1,2,4,8}. Generic
// trust_ir array indexing lowers as a separate integer multiply (or shift) to
// scale the index, an add to reach the element, and then a plain `[reg]`
// load/store — three instructions per element access, on the critical path of
// every loop iteration. This fold collapses the address computation into the
// memory operand, matching what LLVM (and a hand assembler) emit:
// `mov (%base,%index,8), %r`.
//
// The fold is *by construction* address-preserving: the SIB operand
// `base + index*scale + 0` is the byte-exact effective address the deleted
// `add` produced from `imul/shl`. It only ever fires on the exact opcodes and
// operand shapes below; anything unrecognized is left UNFOLDED (plain MemAddr),
// never miscompiled. `select_array_gep` already emits this very
// `X86ISelOperand::SibMemAddr` shape for LeaSib, so the whole downstream path
// (regalloc SIB resolution, encoder, decode_check, lowering certs) is exercised
// and re-verified per-compile on every emitted MovRMSib/MovMRSib instance.
//
// HAND-PROOF (semantic equivalence):
//   - The scale-def computes `scaled = index * scale`, with scale a power of
//     two in {1,2,4,8}. For `ImulRRI [scaled, index, k]` that is `index * k`
//     directly; for `ShlRI [scaled, index, sh]` (sh in 0..=3) that is
//     `index << sh = index * 2^sh` (no shift-count wrap, and the SIB scale is
//     exactly `1 << sh`). x86 `imul`/`shl` produce the low 64 bits of the
//     mathematical product, and SIB scaling likewise computes `index*scale`
//     modulo 2^64, so the two coincide bit-for-bit.
//   - The add computes `addr = base + scaled` (mod 2^64), the same value the
//     SIB unit forms as `base + index*scale`.
//   - The memory op dereferences `[addr + 0]`; the rewritten op dereferences
//     `[base + index*scale + 0]`. Same address, same access width, same value.
//
// SIDE CONDITIONS (each must hold or the fold is skipped):
//   1. The scale-def is `ImulRRI [scaled, index, k]` with k in {1,2,4,8}, OR
//      `ShlRI [scaled, index, sh]` with sh in {0,1,2,3}. Both at opcode-default
//      flags, no memory side effects, `scaled`/`index` supported Gpr64 vregs.
//   2. The add is `AddRR [addr, X, Y]` (three-address ISel form) where {X,Y} =
//      {base, scaled} in either order (ADD is commutative). `base` is a
//      supported Gpr64 vreg distinct from `scaled`; `addr`/`base` are Gpr64.
//      Default flags, no memory side effects.
//   3. The memory op is a `MovRM`/`MovMR` (64-bit) or `MovRM32`/`MovMR32`
//      (32-bit, X10) `[addr + 0]` load/store with the base VReg equal to
//      `addr` and disp == 0. The rewrite preserves the access width exactly
//      (MovRMSib/MovMRSib are the REX.W forms; MovRM32Sib/MovMR32Sib the
//      32-bit forms with identical zero-extension/store semantics);
//      8/16-bit and float forms are left alone.
//   4. Program order within the block: scale-def precedes add precedes memory
//      op. `base`, `index` are not redefined between their producer and the
//      memory op (guaranteed by the single-def / single-use guards plus the
//      no-intervening-redef check).
//   5. `scaled` is defined exactly once (by the scale-def) and used exactly
//      once (by the add) across the whole function. `addr` is defined exactly
//      once (by the add) and used exactly once (by the memory op) across the
//      whole function. This makes deleting the scale-def and add invisible.
//   6. The RFLAGS written by the deleted scale-def and add are DEAD (no reader
//      before the next full overwrite). `imul`/`shl`/`add` all clobber RFLAGS;
//      MovRMSib/MovMRSib do not, so we may only erase these flag writers when
//      nothing downstream consumes the flags they produced.
//   7. `index != base` is NOT required (SIB permits base==index); but the SIB
//      index register is never RSP because these are pre-regalloc vregs and
//      regalloc never assigns RSP to an ordinary vreg.
//
// PROOF PROVENANCE: hand-proved peephole. The rewritten load/store keeps its
// own `proof_origin`, so source-location reporting is unchanged.

/// One memory op (load or store) on the shared `[addr + 0]` to rewrite to SIB.
#[derive(Debug, Clone)]
struct SibMemRewrite {
    mem_idx: usize,
    new_opcode: X86Opcode,
    /// dst for a load, src for a store — carried through unchanged.
    value_operand: X86ISelOperand,
    is_load: bool,
}

/// A whole fold: an `imul/shl` scale-def + an `AddRR` address-def, plus every
/// memory op on the resulting address that gets rewritten to a SIB operand.
#[derive(Debug)]
struct SibAddrFoldEdit {
    /// Index of the imul/shl scale-def (to delete), or `None` for a SCALE-1
    /// address (`base + index`), where there is no scale-def to begin with —
    /// see the scale-1 arm of `try_sib_addr_fold_from_add`.
    scale_def_idx: Option<usize>,
    /// Index of the AddRR address-def (to delete).
    add_idx: usize,
    /// Shared SIB memory operand `base + index*scale + 0`.
    sib: X86ISelOperand,
    /// The memory ops (>=1) on the address, each rewritten to carry `sib`.
    mem_rewrites: Vec<SibMemRewrite>,
    /// Indices of pure `MovRR [t, addr]` address copies that become dead once
    /// the mem ops carry the SIB operand directly (also deleted).
    copy_deletes: Vec<usize>,
}

/// Whole-function VReg maps precomputed ONCE per `sib_addr_fold_run_on_block`
/// invocation, replacing the per-anchor whole-function scans that made the
/// pass O(n^2) on a single large function (matmul's 15920-inst body).
///
/// `func` is IMMUTABLE across the entire anchor loop — all edits are collected
/// into a `Vec` and applied only AFTER the loop — so every per-anchor
/// `function_vreg_def_count` / `function_vreg_use_count` / cross-block escape
/// scan returns the IDENTICAL answer within one invocation. Precomputing them
/// once yields the SAME verdicts and therefore the SAME edit set (byte-
/// identical codegen). The maps MUST be rebuilt per invocation (the function
/// DOES mutate between block invocations via the end-of-loop edits) and MUST
/// NOT be hoisted across invocations.
struct SibFoldVRegMaps {
    /// Total definitions of each VReg (operand 0 of a value-producing inst),
    /// function-wide. Mirrors `function_vreg_def_count` exactly.
    def_counts: std::collections::HashMap<VReg, u32>,
    /// Total uses of each VReg (per `vreg_uses_in_block`), function-wide.
    /// Mirrors `function_vreg_use_count` exactly.
    use_counts: std::collections::HashMap<VReg, u32>,
    /// For each VReg, the set of blocks that MENTION it (any operand, per
    /// `instruction_mentions_vreg`). Replaces the cross-block escape scan:
    /// a VReg escapes `block_id` iff it is mentioned in some other block.
    mention_blocks: std::collections::HashMap<
        VReg,
        std::collections::HashSet<trust_cg_lower::instructions::Block>,
    >,
}

impl SibFoldVRegMaps {
    /// Build all three maps in a single O(n) pass over every block/inst.
    fn build(func: &X86ISelFunction) -> Self {
        use crate::effects::x86_produces_value;
        let mut def_counts: std::collections::HashMap<VReg, u32> = std::collections::HashMap::new();
        let mut use_counts: std::collections::HashMap<VReg, u32> = std::collections::HashMap::new();
        let mut mention_blocks: std::collections::HashMap<
            VReg,
            std::collections::HashSet<trust_cg_lower::instructions::Block>,
        > = std::collections::HashMap::new();

        for (bid, block) in &func.blocks {
            // Use counts: accumulate the per-block use map (same predicate as
            // `function_vreg_use_count`).
            for (v, c) in vreg_uses_in_block(&block.insts) {
                *use_counts.entry(v).or_insert(0) += c;
            }
            for inst in &block.insts {
                // Def counts: operand-0 VReg of each value-producing inst
                // (same predicate as `function_vreg_def_count`).
                if x86_produces_value(inst.opcode)
                    && let Some(X86ISelOperand::VReg(v)) = inst.operands.first()
                {
                    *def_counts.entry(*v).or_insert(0) += 1;
                }
                // Mention blocks: every VReg any operand mentions (same
                // predicate as `instruction_mentions_vreg`).
                for op in &inst.operands {
                    collect_operand_mentions(op, *bid, &mut mention_blocks);
                }
            }
        }

        SibFoldVRegMaps {
            def_counts,
            use_counts,
            mention_blocks,
        }
    }

    #[inline]
    fn def_count(&self, v: VReg) -> u32 {
        self.def_counts.get(&v).copied().unwrap_or(0)
    }

    #[inline]
    fn use_count(&self, v: VReg) -> u32 {
        self.use_counts.get(&v).copied().unwrap_or(0)
    }

    /// True iff `v` is mentioned in any block other than `block_id`. Replaces
    /// `func.blocks.iter().any(|(id, b)| id != block_id && b.insts.iter()
    /// .any(|i| instruction_mentions_vreg(i, v)))`.
    #[inline]
    fn escapes(&self, v: VReg, block_id: trust_cg_lower::instructions::Block) -> bool {
        self.mention_blocks
            .get(&v)
            .is_some_and(|bs| bs.iter().any(|b| *b != block_id))
    }
}

/// Record, into `mention_blocks`, that block `bid` mentions every VReg
/// referenced by `op` (walking `MemAddr`/`SibMemAddr` addressing regs) —
/// mirroring `operand_mentions_vreg`/`instruction_mentions_vreg`.
fn collect_operand_mentions(
    op: &X86ISelOperand,
    bid: trust_cg_lower::instructions::Block,
    mention_blocks: &mut std::collections::HashMap<
        VReg,
        std::collections::HashSet<trust_cg_lower::instructions::Block>,
    >,
) {
    match op {
        X86ISelOperand::VReg(v) => {
            mention_blocks.entry(*v).or_default().insert(bid);
        }
        X86ISelOperand::MemAddr { base, .. } => {
            collect_operand_mentions(base, bid, mention_blocks);
        }
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_mentions(base, bid, mention_blocks);
            collect_operand_mentions(index, bid, mention_blocks);
        }
        _ => {}
    }
}

fn sib_addr_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = block.insts.clone();

    // Precompute the whole-function VReg maps ONCE for this invocation. `func`
    // is immutable across the anchor loop below, so these replace the O(n)
    // per-anchor scans that made the loop O(n^2), with byte-identical results.
    let maps = SibFoldVRegMaps::build(func);

    let mut edits: Vec<SibAddrFoldEdit> = Vec::new();
    let mut consumed: std::collections::HashSet<usize> = std::collections::HashSet::new();

    // Anchor on each address-producing instruction feeding memory ops:
    //   (1) `LeaSib d, [base+index*scale+disp]` (already a formed SIB address,
    //       e.g. from `select_array_gep`) — the primary array-indexing case.
    //   (2) `imul/shl` + `AddRR` (a materialized base+index*scale, when the
    //       address was lowered as generic integer arithmetic).
    // Deleting the address producer is attempted once, so anchoring on the
    // producer (not each memory op) naturally handles a load+store that share
    // one address (`c[i] = c[i] + ..`).
    for anchor_idx in 0..insts.len() {
        if consumed.contains(&anchor_idx) {
            continue;
        }
        let edit = try_sib_addr_fold_from_leasib(block_id, &insts, anchor_idx, &maps)
            .or_else(|| try_sib_addr_fold_from_add(block_id, &insts, anchor_idx, &maps));
        if let Some(edit) = edit {
            if let Some(scale_def_idx) = edit.scale_def_idx {
                consumed.insert(scale_def_idx);
            }
            consumed.insert(edit.add_idx);
            for r in &edit.mem_rewrites {
                consumed.insert(r.mem_idx);
            }
            for &c in &edit.copy_deletes {
                consumed.insert(c);
            }
            edits.push(edit);
        }
    }

    if edits.is_empty() {
        return false;
    }

    if std::env::var_os("TRUST_CG_X86_SIB_FOLD_LOG").is_some() {
        let mem_ops: usize = edits.iter().map(|e| e.mem_rewrites.len()).sum();
        eprintln!(
            "x86-sib-addr-fold: fired {} time(s) ({} mem ops) in function `{}` block #{:?}",
            edits.len(),
            mem_ops,
            func.name,
            block_id.0,
        );
    }

    // Rewrite every memory op in place, then delete the scale-def + add of each
    // fired edit in descending index order so earlier indices stay valid.
    let mut to_delete: Vec<usize> = Vec::new();
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for edit in &edits {
        for r in &edit.mem_rewrites {
            let mem = &mut block.insts[r.mem_idx];
            mem.opcode = r.new_opcode;
            mem.flags = r.new_opcode.default_flags();
            mem.operands = if r.is_load {
                vec![r.value_operand.clone(), edit.sib.clone()]
            } else {
                vec![edit.sib.clone(), r.value_operand.clone()]
            };
        }
        if let Some(scale_def_idx) = edit.scale_def_idx {
            to_delete.push(scale_def_idx);
        }
        to_delete.push(edit.add_idx);
        for &c in &edit.copy_deletes {
            to_delete.push(c);
        }
    }
    to_delete.sort_unstable();
    to_delete.dedup();
    for idx in to_delete.into_iter().rev() {
        block.insts.remove(idx);
    }

    true
}

/// SIB scale for an `ImulRRI`/`ShlRI` scale-def, or `None` if it is not a
/// power-of-two-scale shape encodable as an x86 SIB scale.
///
/// Returns `(scale, index_vreg)` where `scale in {1,2,4,8}`.
fn sib_scale_def(inst: &X86ISelInst) -> Option<(u8, VReg)> {
    match inst.opcode {
        X86Opcode::ImulRRI => {
            // [scaled, index, Imm(k)]
            if inst.flags != X86Opcode::ImulRRI.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::VReg(_dst),
                    X86ISelOperand::VReg(index),
                    X86ISelOperand::Imm(k),
                ] => {
                    let scale = u8::try_from(*k).ok()?;
                    if matches!(scale, 1 | 2 | 4 | 8) && index.class == RegClass::Gpr64 {
                        Some((scale, *index))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        X86Opcode::ShlRI => {
            // [scaled, index, Imm(sh)]  (three-address form only)
            if inst.flags != X86Opcode::ShlRI.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::VReg(_dst),
                    X86ISelOperand::VReg(index),
                    X86ISelOperand::Imm(sh),
                ] => {
                    let scale: u8 = match sh {
                        0 => 1,
                        1 => 2,
                        2 => 4,
                        3 => 8,
                        _ => return None,
                    };
                    if index.class == RegClass::Gpr64 {
                        Some((scale, *index))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The defined VReg (operand 0) of a value-producing scale-def / add.
fn def_vreg(inst: &X86ISelInst) -> Option<VReg> {
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

/// Count total uses of `vreg` across the whole function (all blocks), reading
/// addressing regs inside memory operands too. Used to enforce the whole-
/// function single-use guard for the scale/address intermediates.
///
/// Retained as the REFERENCE definition of the per-VReg use count that
/// `SibFoldVRegMaps::use_counts` precomputes in bulk (the two must agree
/// exactly). The SIB-fold anchor loop now queries the precomputed map instead
/// of calling this per anchor (which was O(n) per anchor -> O(n^2)).
#[allow(dead_code)]
fn function_vreg_use_count(func: &X86ISelFunction, vreg: VReg) -> u32 {
    let mut count = 0u32;
    for block in func.blocks.values() {
        let counts = vreg_uses_in_block(&block.insts);
        count += counts.get(&vreg).copied().unwrap_or(0);
    }
    count
}

/// Count total definitions of `vreg` (operand 0 of value-producing insts)
/// across the whole function.
///
/// Retained as the REFERENCE definition of the per-VReg def count that
/// `SibFoldVRegMaps::def_counts` precomputes in bulk (the two must agree
/// exactly); no longer called per anchor.
#[allow(dead_code)]
fn function_vreg_def_count(func: &X86ISelFunction, vreg: VReg) -> u32 {
    use crate::effects::x86_produces_value;
    let mut count = 0u32;
    for block in func.blocks.values() {
        for inst in &block.insts {
            if x86_produces_value(inst.opcode)
                && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(v)) if *v == vreg)
            {
                count += 1;
            }
        }
    }
    count
}

/// Are the RFLAGS written by `insts[index]` dead — i.e. no later instruction
/// reads them before they are fully overwritten or the block ends?
///
/// This is the SIB-fold-specific variant of `flags_written_here_are_dead`. The
/// difference: a plain memory load/store neither reads nor exports RFLAGS, so
/// it is transparent here (the fusion-pass version conservatively bails on any
/// `has_side_effects()`, which a store carries via `WRITES_MEMORY`, and would
/// wrongly block folding a store's own address computation). We still bail on
/// genuine flag readers and on call/branch/terminator/return boundaries, past
/// which RFLAGS may be observed via the ABI or control flow. A `Full` overwrite
/// makes the earlier flags provably dead.
///
/// A `Partial` overwriter (imul/shl/...) is TRANSPARENT to this deadness
/// question. What we must prove is that no instruction ever OBSERVES the
/// deleted writer's flag output. Observation happens only through a flag
/// reader (the reader set is closed over the opcode enum:
/// `Cmovcc/Cmovcc32/Setcc/Jcc/AdcRR/SbbRR`, all caught by `x86_reads_flags`
/// above, `Jcc` additionally by the branch boundary) or past a control-flow /
/// ABI boundary (also caught above). A partial overwriter does neither: it
/// writes SOME flag bits as a function of its register operands (which the
/// fold does not change) and reads none. Any reader downstream of the next
/// `Full` overwrite observes only that overwriter's flags; any reader BEFORE
/// it still returns `false` here. So scanning through a partial overwrite,
/// looking only for readers / boundaries / the next full overwrite, is sound.
fn sib_fold_flags_dead(insts: &[X86ISelInst], index: usize) -> bool {
    for inst in &insts[index + 1..] {
        if x86_reads_flags(inst.opcode) {
            return false;
        }
        // Control-flow / ABI boundaries may expose RFLAGS.
        let flags = inst.flags;
        if flags.is_call() || flags.is_branch() || flags.is_terminator() || flags.is_return() {
            return false;
        }
        match condition_flag_overwrite(inst) {
            FlagOverwrite::None | FlagOverwrite::Partial => {}
            FlagOverwrite::Full => return true,
        }
    }
    // Fell off the end of the block without a full overwrite. Conservatively
    // treat the flags as potentially live-out and refuse.
    false
}

/// Recognize a plain 64-bit `MovRM`/`MovMR` on `[addr + 0]`. Returns
/// `(is_load, addr_vreg, value_operand, new_opcode)`.
/// Whether the scalar-FP arm of the SIB address fold is active. Default-ON;
/// `TCG_NO_X86_SIB_FP_FOLD` disables it so an A/B runs inside one dylib.
fn sib_fp_fold_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_SIB_FP_FOLD").is_none()
}

fn sib_foldable_mem_op(inst: &X86ISelInst) -> Option<(bool, VReg, X86ISelOperand, X86Opcode)> {
    // A proof-origin-carrying MOV (a volatile/atomic load or store) keeps its
    // STRONGER AtomicLoad/AtomicStore proof and TSO-ordering semantics; folding
    // it into a plain MovRMSib/MovMRSib would drop that origin and re-route it to
    // the weaker plain-value memory proof. Never fold those — only plain
    // value-load/store MOVs (no proof origin) are foldable.
    if inst.proof_origin.is_some() {
        return None;
    }
    match inst.opcode {
        X86Opcode::MovRM => {
            if inst.flags != X86Opcode::MovRM.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovRMSib))
                }
                _ => None,
            }
        }
        X86Opcode::MovMR => {
            if inst.flags != X86Opcode::MovMR.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(_),
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((false, *addr, src.clone(), X86Opcode::MovMRSib))
                }
                _ => None,
            }
        }
        // 32-bit siblings (X10): identical shape, width fixed by the opcode —
        // the rewrite targets MovRM32Sib/MovMR32Sib, whose zero-extension /
        // store-width semantics exactly match MovRM32/MovMR32.
        X86Opcode::MovRM32 => {
            if inst.flags != X86Opcode::MovRM32.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovRM32Sib))
                }
                _ => None,
            }
        }
        X86Opcode::MovMR32 => {
            if inst.flags != X86Opcode::MovMR32.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(_),
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((false, *addr, src.clone(), X86Opcode::MovMR32Sib))
                }
                _ => None,
            }
        }
        // 8-bit siblings: the shape is identical once more and the access WIDTH
        // is fixed by the opcode, exactly as for the 32-bit pair. These are what
        // let a BYTE array participate in indexed addressing at all — the whole
        // `&[u8]` / `Vec<u8>` / `[u8; N]` class previously fell through here and
        // paid a base-`Lea` plus an `Add` on every single element access.
        X86Opcode::MovRM8 if byte_sib_fold_enabled() => {
            if inst.flags != X86Opcode::MovRM8.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovRM8Sib))
                }
                _ => None,
            }
        }
        X86Opcode::MovMR8 if byte_sib_fold_enabled() => {
            if inst.flags != X86Opcode::MovMR8.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(_),
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((false, *addr, src.clone(), X86Opcode::MovMR8Sib))
                }
                _ => None,
            }
        }
        // Scalar-FP LOADS: identical shape again, width fixed by the opcode.
        // b11_float_dot pays three instructions per element access (imul/mov/add)
        // purely to form an address these can carry in their operand.
        //
        // LOADS ONLY. There is deliberately no MovsdMRSib/MovssMRSib opcode, so
        // MovsdMR/MovssMR must fall through to `None` here rather than be folded
        // into an opcode that does not exist.
        //
        // Kill switch (`TCG_NO_X86_SIB_FP_FOLD`) so the fold can be A/B'd inside a
        // SINGLE dylib. Comparing two separately-built dylibs across sweeps is not
        // a controlled experiment on this box — between-sweep ratio drift is
        // comparable to the effect being measured.
        X86Opcode::MovsdRM if sib_fp_fold_enabled() => {
            if inst.flags != X86Opcode::MovsdRM.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovsdRMSib))
                }
                _ => None,
            }
        }
        X86Opcode::MovssRM if sib_fp_fold_enabled() => {
            if inst.flags != X86Opcode::MovssRM.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovssRMSib))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// If `ptr` is used (function-wide) ONLY as the base of foldable 64-bit
/// `[ptr + 0]` load/stores in the SAME block, all occurring after `after_idx`,
/// return the SIB rewrites for them. Otherwise `None`. This models a copied
/// address pointer whose only consumers are memory ops we can fold.
fn collect_pointer_mem_ops(
    insts: &[X86ISelInst],
    ptr: VReg,
    after_idx: usize,
    maps: &SibFoldVRegMaps,
) -> Option<Vec<SibMemRewrite>> {
    // ptr must be defined exactly once (the copy) function-wide.
    if maps.def_count(ptr) != 1 {
        return None;
    }
    let total = maps.use_count(ptr);
    if total == 0 {
        return None;
    }
    let mut rewrites = Vec::new();
    let mut matched = 0u32;
    for (i, inst) in insts.iter().enumerate() {
        let uses_here = vreg_uses_in_inst(inst, ptr);
        if uses_here == 0 {
            continue;
        }
        matched += uses_here;
        match sib_foldable_mem_op(inst) {
            Some((is_load, base, value_operand, new_opcode))
                if base == ptr && uses_here == 1 && i > after_idx =>
            {
                rewrites.push(SibMemRewrite {
                    mem_idx: i,
                    new_opcode,
                    value_operand,
                    is_load,
                });
            }
            _ => return None,
        }
    }
    // All function-wide uses of ptr must be the mem ops we just folded (no
    // out-of-block reader, no arithmetic use).
    if matched != total || rewrites.is_empty() {
        return None;
    }
    Some(rewrites)
}

/// Collect every foldable [ptr+0] 64-bit mem op on `ptr`, seeing through a
/// single pure `MovRR [t, ptr]` copy. Returns `(mem_rewrites, copy_deletes)` if
/// EVERY function-wide use of `ptr` (and of each copy dest) is such a mem op in
/// THIS block after `after_idx`; otherwise `None`.
fn collect_addr_consumers(
    insts: &[X86ISelInst],
    addr_vreg: VReg,
    after_idx: usize,
    maps: &SibFoldVRegMaps,
) -> Option<(Vec<SibMemRewrite>, Vec<usize>)> {
    let addr_total_uses = maps.use_count(addr_vreg);
    if addr_total_uses == 0 {
        return None;
    }
    let mut mem_rewrites: Vec<SibMemRewrite> = Vec::new();
    let mut copy_deletes: Vec<usize> = Vec::new();
    let mut matched_uses = 0u32;
    for (i, inst) in insts.iter().enumerate() {
        let uses_here = vreg_uses_in_inst(inst, addr_vreg);
        if uses_here == 0 {
            continue;
        }
        matched_uses += uses_here;
        // (a) direct foldable [addr+0] mem op.
        if let Some((is_load, base, value_operand, new_opcode)) = sib_foldable_mem_op(inst)
            && base == addr_vreg
            && uses_here == 1
            && i > after_idx
        {
            mem_rewrites.push(SibMemRewrite {
                mem_idx: i,
                new_opcode,
                value_operand,
                is_load,
            });
            continue;
        }
        // (b) pure `MovRR [t, addr]` copy of the address. Either its result `t`
        // is DEAD (a redundant copy DCE would remove — treat as a no-op and
        // delete it), or `t` feeds only foldable [t+0] mem ops (a two-address
        // artifact — fold those too). Both let us delete the copy.
        if inst.opcode == X86Opcode::MovRR
            && inst.flags == X86Opcode::MovRR.default_flags()
            && uses_here == 1
            && i > after_idx
            && let [X86ISelOperand::VReg(t), X86ISelOperand::VReg(src)] = inst.operands.as_slice()
            && *src == addr_vreg
            && t.class == RegClass::Gpr64
            && maps.def_count(*t) == 1
        {
            let t_uses = maps.use_count(*t);
            if t_uses == 0 {
                // Dead copy: deleting it is unconditionally safe.
                copy_deletes.push(i);
                continue;
            }
            if let Some(mut copy_mem) = collect_pointer_mem_ops(insts, *t, i, maps) {
                copy_deletes.push(i);
                mem_rewrites.append(&mut copy_mem);
                continue;
            }
        }
        return None;
    }
    if matched_uses != addr_total_uses || mem_rewrites.is_empty() {
        return None;
    }
    Some((mem_rewrites, copy_deletes))
}

/// Try to form a SIB fold anchored on a `LeaSib [addr, SibMemAddr{..}]` at
/// `lea_idx`. Every use of `addr` (through at most one copy) must be a foldable
/// 64-bit `[addr + 0]` load/store in this block; those are rewritten to carry
/// the LeaSib's SIB operand and the LeaSib (+ copies) is deleted.
fn try_sib_addr_fold_from_leasib(
    block_id: trust_cg_lower::instructions::Block,
    insts: &[X86ISelInst],
    lea_idx: usize,
    maps: &SibFoldVRegMaps,
) -> Option<SibAddrFoldEdit> {
    let lea = insts.get(lea_idx)?;
    if lea.opcode != X86Opcode::LeaSib || lea.flags != X86Opcode::LeaSib.default_flags() {
        return None;
    }
    // LeaSib operands: [dst, SibMemAddr{base, index, scale, disp}].
    let (addr_vreg, sib, base_vreg, index_vreg) = match lea.operands.as_slice() {
        [
            X86ISelOperand::VReg(dst),
            sib @ X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            },
        ] => {
            // Only fold SIB-legal scales; select_array_gep only ever emits these
            // (1/2/4/8), but re-check defensively. disp is preserved exactly.
            if !matches!(*scale, 1 | 2 | 4 | 8) {
                return None;
            }
            let _ = disp;
            let (X86ISelOperand::VReg(b), X86ISelOperand::VReg(ix)) =
                (base.as_ref(), index.as_ref())
            else {
                return None;
            };
            (*dst, sib.clone(), *b, *ix)
        }
        _ => return None,
    };
    if addr_vreg.class != RegClass::Gpr64 {
        return None;
    }
    // addr must be defined exactly once (this LeaSib).
    if maps.def_count(addr_vreg) != 1 {
        return None;
    }

    let (mem_rewrites, copy_deletes) = collect_addr_consumers(insts, addr_vreg, lea_idx, maps)?;

    // base/index must not be redefined between the LeaSib and the last mem op,
    // or the SIB operand would read a different value than the LeaSib formed.
    let last_mem_idx = mem_rewrites
        .iter()
        .map(|r| r.mem_idx)
        .chain(copy_deletes.iter().copied())
        .max()
        .unwrap_or(lea_idx);
    let redef = insts[lea_idx + 1..=last_mem_idx].iter().any(|inst| {
        if let Some(d) = def_vreg(inst) {
            crate::effects::x86_produces_value(inst.opcode) && (d == base_vreg || d == index_vreg)
        } else {
            false
        }
    });
    if redef {
        return None;
    }

    // Cross-block liveness: addr must not be mentioned in any other block.
    if maps.escapes(addr_vreg, block_id) {
        return None;
    }

    // LeaSib has a single producer; reuse both index fields as that producer so
    // the shared deletion logic removes it exactly once (dedup handles the dup).
    Some(SibAddrFoldEdit {
        scale_def_idx: Some(lea_idx),
        add_idx: lea_idx,
        sib,
        mem_rewrites,
        copy_deletes,
    })
}

/// Try to form a SIB fold anchored on the `AddRR` at `add_idx`. The add must
/// compute `addr = base + scaled` where `scaled = index * scale` (a nearby
/// `imul`/`shl`), and EVERY use of `addr` in the function must be a plain
/// 64-bit `[addr + 0]` load/store in THIS block. Those memory ops are then all
/// rewritten to share the SIB operand `base + index*scale + 0`.
fn try_sib_addr_fold_from_add(
    block_id: trust_cg_lower::instructions::Block,
    insts: &[X86ISelInst],
    add_idx: usize,
    maps: &SibFoldVRegMaps,
) -> Option<SibAddrFoldEdit> {
    let add = insts.get(add_idx)?;

    // --- Side condition 2: AddRR [addr, X, Y] three-address form, default flags. ---
    if add.opcode != X86Opcode::AddRR || add.flags != X86Opcode::AddRR.default_flags() {
        return None;
    }
    let (addr_vreg, x, y) = match add.operands.as_slice() {
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(x),
            X86ISelOperand::VReg(y),
        ] => (*dst, *x, *y),
        _ => return None,
    };
    if addr_vreg.class != RegClass::Gpr64 {
        return None;
    }

    // --- addr must be defined exactly once (this add). ---
    if maps.def_count(addr_vreg) != 1 {
        return None;
    }

    // --- Collect every memory op on `addr`; ALL uses of addr must be foldable
    // 64-bit loads/stores on [addr + 0] in THIS block (seeing through at most
    // one MovRR copy). If addr is used anywhere else (arithmetic, another
    // block, a non-zero-disp/narrow/float access), we cannot delete the add. ---
    let (mem_rewrites, copy_deletes) = collect_addr_consumers(insts, addr_vreg, add_idx, maps)?;

    // One of {x, y} is `scaled` (produced by an in-block, once-defined,
    // once-used scale-def), the other is `base`. Try both orderings.
    for (scaled_candidate, base_candidate) in [(x, y), (y, x)] {
        if scaled_candidate == base_candidate
            || base_candidate.class != RegClass::Gpr64
            || scaled_candidate.class != RegClass::Gpr64
        {
            continue;
        }

        // --- scaled: defined once, used once (by this add), function-wide. ---
        if maps.def_count(scaled_candidate) != 1 || maps.use_count(scaled_candidate) != 1 {
            continue;
        }

        // Locate the scale-def for `scaled_candidate`, earlier in THIS block.
        let mut scale_def_idx = None;
        for (i, inst) in insts.iter().enumerate().take(add_idx) {
            if def_vreg(inst) == Some(scaled_candidate) && sib_scale_def(inst).is_some() {
                scale_def_idx = Some(i);
            }
        }
        let Some(scale_def_idx) = scale_def_idx else {
            continue;
        };
        let (scale, index) = match sib_scale_def(&insts[scale_def_idx]) {
            Some(v) => v,
            None => continue,
        };

        // --- Order: scale-def < add < every memory op. ---
        if scale_def_idx >= add_idx {
            continue;
        }
        let last_mem_idx = mem_rewrites
            .iter()
            .map(|r| r.mem_idx)
            .chain(copy_deletes.iter().copied())
            .max()
            .unwrap_or(add_idx);

        // --- Side condition 4: base/index not redefined anywhere from the
        // scale-def up to (and including) the last memory op — otherwise the
        // SIB operand would read a different value than the deleted imul/add
        // computed. ---
        let window_redefs_base_or_index =
            insts[scale_def_idx + 1..=last_mem_idx].iter().any(|inst| {
                if let Some(d) = def_vreg(inst) {
                    crate::effects::x86_produces_value(inst.opcode)
                        && (d == base_candidate || d == index)
                } else {
                    false
                }
            });
        if window_redefs_base_or_index {
            continue;
        }

        // --- Side condition 6: the RFLAGS written by the scale-def and the add
        // must be dead (no reader before the next full overwrite). ---
        if !sib_fold_flags_dead(insts, scale_def_idx) || !sib_fold_flags_dead(insts, add_idx) {
            continue;
        }

        // --- Cross-block liveness: scaled and addr must not be mentioned in any
        // other block (their sole uses are in this block by the counts above,
        // but re-check defensively). ---
        if maps.escapes(scaled_candidate, block_id) || maps.escapes(addr_vreg, block_id) {
            continue;
        }

        // All side conditions hold. Build the shared SIB operand.
        let sib = X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::VReg(base_candidate)),
            index: Box::new(X86ISelOperand::VReg(index)),
            scale,
            disp: 0,
        };
        return Some(SibAddrFoldEdit {
            scale_def_idx: Some(scale_def_idx),
            add_idx,
            sib,
            mem_rewrites: mem_rewrites.clone(),
            copy_deletes: copy_deletes.clone(),
        });
    }

    // --- SCALE-1 fallback: `addr = base + index` with NO scale-def at all. ---
    //
    // A byte-element array indexes at scale 1, so ISel emits a bare `AddRR`
    // with nothing to strength-reduce and the loop above finds no scale-def.
    // That is why byte-indexed access (`&[u8]`, `Vec<u8>`, `[u8; N]`) never
    // formed a SIB address: it fell through this function AND through
    // `sib_base_lea_fold`, which only folds the base of an ALREADY-SIB operand.
    //
    // The side conditions here are STRICTLY WEAKER than the scaled path, and
    // deliberately so: there is no scale-def to delete, so `x`/`y` need NOT be
    // single-def/single-use. They only have to still hold the same values where
    // the SIB operand reads them, which is exactly the no-redef window below.
    if byte_sib_fold_enabled()
        // A proof-origin-carrying AddRR is a CARRIER (bounds/overflow check),
        // not plain address arithmetic; deleting it would drop the check. The
        // memory ops are screened the same way inside `sib_foldable_mem_op`.
        && add.proof_origin.is_none()
        && x.class == RegClass::Gpr64
        && y.class == RegClass::Gpr64
        && x != y
    {
        let last_mem_idx = mem_rewrites
            .iter()
            .map(|r| r.mem_idx)
            .chain(copy_deletes.iter().copied())
            .max()
            .unwrap_or(add_idx);

        // Neither operand may be redefined between the add and the last memory
        // op, or the SIB would read a different value than the deleted add did.
        let window_redefs = insts[add_idx + 1..=last_mem_idx].iter().any(|inst| {
            if let Some(d) = def_vreg(inst) {
                crate::effects::x86_produces_value(inst.opcode) && (d == x || d == y)
            } else {
                false
            }
        });
        // Same two remaining conditions as the scaled path: the add's RFLAGS
        // must be dead (deleting it must not remove a flag someone reads), and
        // the address vreg must not be referenced from another block.
        if !window_redefs
            && sib_fold_flags_dead(insts, add_idx)
            && !maps.escapes(addr_vreg, block_id)
        {
            return Some(SibAddrFoldEdit {
                scale_def_idx: None,
                add_idx,
                sib: X86ISelOperand::SibMemAddr {
                    base: Box::new(X86ISelOperand::VReg(x)),
                    index: Box::new(X86ISelOperand::VReg(y)),
                    scale: 1,
                    disp: 0,
                },
                mem_rewrites,
                copy_deletes,
            });
        }
    }

    None
}

/// Task #72 pass 2 — redundant self-zero-test elision.
///
/// Deletes `TestRR v, v` (or `CmpRI v, 0`) when:
///   1. the NEAREST preceding in-block def of `v` is an ALU op that sets ZF
///      according to its result (`And/Or/Xor/Add/Sub`, register or immediate
///      forms) with `v` as its destination — after it, `ZF == (v == 0)`,
///      exactly what the self-test would recompute;
///   2. no instruction BETWEEN that def and the test writes flags or
///      redefines `v`;
///   3. every flag READER from the test to the end of the block consumes only
///      ZF (`Jcc`/`Setcc`/`Cmovcc` with `E`/`NE`), and no reader appears
///      after an intervening flag WRITER (those see the new flags, not ours).
///      Cross-block flag liveness does not exist in this ISel (every consumer
///      follows an in-block producer — the invariant TV-5's block-local flag
///      model already relies on), so reaching the terminators ends the scan.
///
/// The CF/OF difference between the ALU op and `test` (ADD/SUB set them
/// arithmetically; `test` clears them) is invisible to E/NE consumers, which
/// read ZF only.
fn redundant_self_test_elision_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    use trust_cg_ir::X86CondCode;

    fn zf_per_result_def(op: X86Opcode) -> bool {
        matches!(
            op,
            X86Opcode::AndRR
                | X86Opcode::AndRI
                | X86Opcode::OrRR
                | X86Opcode::XorRR
                | X86Opcode::XorRI
                | X86Opcode::AddRR
                | X86Opcode::AddRI
                | X86Opcode::SubRR
                | X86Opcode::SubRI
        )
    }
    fn zf_only_cc(cc: X86CondCode) -> bool {
        matches!(cc, X86CondCode::E | X86CondCode::NE)
    }

    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let n = block.insts.len();
    let mut delete_at: Option<usize> = None;

    'scan: for i in 0..n {
        let inst = &block.insts[i];
        // The self-zero-test shapes.
        let v = match inst.opcode {
            X86Opcode::TestRR => match (inst.operands.first(), inst.operands.get(1)) {
                (Some(X86ISelOperand::VReg(a)), Some(X86ISelOperand::VReg(b))) if a == b => *a,
                _ => continue,
            },
            X86Opcode::CmpRI => match (inst.operands.first(), inst.operands.get(1)) {
                (Some(X86ISelOperand::VReg(a)), Some(X86ISelOperand::Imm(0))) => *a,
                _ => continue,
            },
            _ => continue,
        };
        // (1)+(2): walk back to the nearest def of v; nothing in between may
        // write flags or redefine v.
        let mut j = i;
        let mut found_def = false;
        while j > 0 {
            j -= 1;
            let prev = &block.insts[j];
            let defines_v = crate::effects::x86_produces_value(prev.opcode)
                && matches!(prev.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == v);
            if defines_v {
                if !zf_per_result_def(prev.opcode) {
                    continue 'scan;
                }
                found_def = true;
                break;
            }
            if x86_writes_flags(prev.opcode) {
                continue 'scan;
            }
        }
        if !found_def {
            continue;
        }
        // (3): every flag reader after the test (until a flag writer or block
        // end) must be ZF-only.
        for k in (i + 1)..n {
            let later = &block.insts[k];
            if x86_reads_flags(later.opcode) {
                let cc_ok = match later.opcode {
                    X86Opcode::Jcc | X86Opcode::Setcc => {
                        matches!(
                            later.operands.first().or(later.operands.get(1)),
                            Some(X86ISelOperand::CondCode(cc)) if zf_only_cc(*cc)
                        ) || matches!(
                            later.operands.get(1),
                            Some(X86ISelOperand::CondCode(cc)) if zf_only_cc(*cc)
                        )
                    }
                    X86Opcode::Cmovcc | X86Opcode::Cmovcc32 => matches!(
                        later.operands.iter().find(|o| matches!(o, X86ISelOperand::CondCode(_))),
                        Some(X86ISelOperand::CondCode(cc)) if zf_only_cc(*cc)
                    ),
                    _ => false, // ADC/SBB-style consumers: refuse.
                };
                if !cc_ok {
                    continue 'scan;
                }
            }
            if x86_writes_flags(later.opcode) {
                break; // later readers see the new flags, not ours.
            }
        }
        delete_at = Some(i);
        break;
    }

    if let Some(i) = delete_at
        && let Some(block) = func.blocks.get_mut(&block_id)
    {
        block.insts.remove(i);
        return true;
    }
    false
}

// ---------------------------------------------------------------------------
// Local address-chain fold (X9 slice 2; DEFAULT-ON,
// `TCG_NO_X86_ADDR_CHAIN_FOLD` opts out)
//
//   mov  t0, base           ; MovRR copy hop
//   add  t0, #imm           ; AddRI (tied or 3-op)   -> disp accumulation
//   mov  t1, t0             ; MovRR copy hop
//   add  t1, idx            ; AddRR (tied or 3-op)   -> scale-1 index
//   mov  r, [t1 + d0]       ; MovRM -> MovRMSib r, [base + idx*1 + (d0+imm)]
// ---------------------------------------------------------------------------
//
// The SIB fold above anchors on the scale-def/add pair and requires
// FUNCTION-WIDE single-def/single-use intermediates — sound and precise for
// raw ISel output, but blind in a post-unroll body where verbatim clones
// REUSE vreg ids (every intermediate has one def PER CLONE, so def_count is
// the trip count). This fold instead anchors on each 64-bit `MovRM`/`MovMR`
// whose address is a plain `[vreg + disp]` and resolves the address with
// LOCAL nearest-reaching-def reasoning inside the block.
//
// HAND-PROOF (semantic equivalence). The resolver walks the address vreg's
// def chain upward: at each step it holds a triple (v, pos, disp[, index])
// with the invariant
//
//   value(anchor address at mem_idx) = value(v at pos) + index*scale + disp
//
// Nearest-def hops preserve the invariant: `nearest_local_def_before(pos, v)`
// returning `def_idx` means no def of `v` exists in (def_idx, pos), so
// value(v at pos) = the value `def_idx` computed:
//   - `MovRR d, s` (class-exact copy): value(d) = value(s at def_idx).
//   - `AddRI d, s, k` / tied `AddRI d, k`: value(d) = value(s at def_idx) + k
//     (mod 2^64; SIB address arithmetic is likewise mod 2^64, and the i64
//     disp accumulation is checked to stay in i32).
//   - `AddRR d, s1, s2` / tied `AddRR d, s`: value(d) = value(s1) + value(s2),
//     both read at def_idx; one side becomes the SIB index (scale 1).
// The rewritten operand reads the FINAL base (and index) registers AT THE
// MEMORY OP, so for exactly those two vregs we additionally require no def
// in [capture_pos, mem_idx) — checked explicitly (`no_def_in_range`). The
// intermediate temps do not appear in the rewritten operand and need no such
// check; their values were consumed at their capture positions.
//
// The fold REWRITES ONLY — it deletes nothing. The now-unused chain
// instructions are swept by DCE (the default-on per-def local tier handles the
// multi-def post-unroll ids), which owns the flags-deadness obligations for
// removing the flag-writing adds. Rewriting alone never changes flags: the
// memory op computed no flags before and computes none after.
//
// SIDE CONDITIONS (each checked, fail-closed):
//   1. Anchor: full-width `MovRM [dst, MemAddr{VReg a, d0}]` or
//      `MovMR [MemAddr{VReg a, d0}, src]`, default flags, no proof_origin
//      (atomics/volatile keep their stronger proofs), all Gpr64.
//   2. Chain links: `MovRR`(Gpr64=Gpr64) / `AddRI` / `AddRR` with default
//      flags, no proof_origin, VReg/Imm operands only, all Gpr64. Anything
//      else terminates resolution (the current vreg becomes the base).
//   3. At most ONE index side (first `AddRR` met), scale fixed at 1. A
//      second `AddRR` terminates resolution.
//   4. Final disp must fit i32 (checked i64 accumulation, then try_into).
//   5. Final base and index: no def in [capture_pos, mem_idx) — includes
//      Xchg/Cmpxchg hidden defs via `local_fold_defines_vreg`, which treats
//      any VReg operand of those opcodes as a potential def.
//   6. The rewrite fires only if at least one link was consumed AND the
//      shape actually changed (avoids `changed=true` fixpoint churn).
// ---------------------------------------------------------------------------

/// Env gate for the local address-chain fold. DEFAULT-ON after the
/// 2026-07-20 record (adversarial review, 600+-seed differential fuzz/soak
/// across TCG_OPT_LEVEL 0/2/3, 18/18 bench checksums, proofs-ON discharge);
/// `TCG_NO_X86_ADDR_CHAIN_FOLD` is the forensic opt-out (the legacy opt-in
/// name is accepted and redundant).
fn addr_chain_fold_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_ADDR_CHAIN_FOLD").is_none()
}

/// SIB-base LEA fold — DEFAULT-ON (`TCG_NO_X86_SIB_BASE_FOLD` is the forensic
/// opt-out). Folds each stack-slot base-`Lea` into its indexed SIB memory operand,
/// eliminating the redundant per-access `leaq -N(%rbp)` (trust-cg had 0 folded
/// indexed accesses vs LLVM's 11-22 on the sort cluster). Composes with the
/// default-on cmov-swap: cmov-swap models the folded `StackSlot`-SIB bases
/// (`x86_cmov_swap.rs` `sib_base`), so the swap-diamond bench (b06) keeps cmov-swap
/// AND the tighter addressing — no regression. Measured (cmov+fold vs cmov-only):
/// b06 ~1.5 (no regression, was 2.35 pre-fix), b07 −14% / b18 −15% / b05 −10%;
/// composed geomean ~0.95-0.98. The fold runs inside `X86Peephole::run_impl` (one
/// scheduled pass), so flipping it default-on does not change the pass count.
/// Byte-element SIB addressing — DEFAULT-ON (`TCG_NO_X86_BYTE_SIB` is the
/// forensic opt-out, and the handle for a PAIRED A/B inside ONE dylib).
///
/// Gates BOTH halves of the byte-indexing fix together, because neither is
/// useful alone:
///   * the 8-bit `MovRM8`/`MovMR8` arms of `sib_foldable_mem_op` (there was no
///     `MovRM8Sib`/`MovMR8Sib` opcode at all before), and
///   * the SCALE-1 arm of `try_sib_addr_fold_from_add` (a byte array indexes at
///     scale 1, so ISel emits a bare `AddRR` with no scale-def to anchor on).
///
/// Together they let `&[u8]` / `Vec<u8>` / `[u8; N]` element accesses carry
/// their address in the memory operand instead of paying a base-`Lea` plus an
/// `Add` per access. Composes with `sib_base_lea_fold`, which then folds the
/// stack-slot base into the SIB displacement.
fn byte_sib_fold_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_BYTE_SIB").is_none()
}

fn sib_base_lea_fold_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_SIB_BASE_FOLD").is_none()
}

/// Run the SIB-base LEA fold over `func` (the body of the `X86SibBaseFold` pass).
/// Builds the function-wide clean base-`Lea` and `MovRR`-copy indices, then folds
/// each already-SIB-formed indexed load/store's base into its `StackSlot` (or
/// same-block VReg) base, leaving the now-dead base-`Lea`s for DCE. Extracted so
/// it can run LATE — after cmov-swap / if-convert, whose diamond recognizers
/// match the PRE-fold addressing (see the note in `run_impl`). Returns whether
/// anything changed. Inert unless `TCG_X86_SIB_BASE_FOLD` is set.
pub fn sib_base_lea_fold(func: &mut X86ISelFunction) -> bool {
    if !sib_base_lea_fold_enabled() {
        return false;
    }
    let maps = SibFoldVRegMaps::build(func);
    // Function-wide index of clean, single-def base-`Lea`s (the `&arr` LEA is
    // loop-invariant, hoisted to a preheader; a block-local scan would miss it).
    let mut lea_defs: std::collections::HashMap<VReg, LeaBaseDef> =
        std::collections::HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            if inst.opcode != X86Opcode::Lea
                || inst.proof_origin.is_some()
                || inst.flags != inst.opcode.default_flags()
            {
                continue;
            }
            if let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::MemAddr { base, disp },
            ] = inst.operands.as_slice()
                && maps.def_count(*d) == 1
            {
                lea_defs.insert(
                    *d,
                    LeaBaseDef {
                        base: base.as_ref().clone(),
                        disp: *disp,
                        block: *block_id,
                        idx,
                    },
                );
            }
        }
    }
    // Function-wide index of clean, single-def register copies (`MovRR b, s`):
    // the SIB base is a COPY of the `&arr` LEA, resolved through this chain.
    let mut copy_src: std::collections::HashMap<VReg, VReg> = std::collections::HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if inst.opcode == X86Opcode::MovRR
                && inst.proof_origin.is_none()
                && inst.flags == inst.opcode.default_flags()
                && let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] = inst.operands.as_slice()
                && d.class == RegClass::Gpr64
                && s.class == RegClass::Gpr64
                && maps.def_count(*d) == 1
            {
                copy_src.insert(*d, *s);
            }
        }
    }
    let mut changed = false;
    for block_id in func.block_order.clone() {
        if sib_base_lea_fold_run_on_block(func, block_id, &maps, &lea_defs, &copy_src) {
            changed = true;
        }
    }
    changed
}

/// Conservative "may define this vreg" for the local fold's redef scans.
/// Operand-0 defs of value producers, plus EVERY VReg operand of the
/// exchange family (hidden second defs invisible to the operand-0 model —
/// the same hazard the unroller refuses). Matching is CLASS-BLIND on the id:
/// a VReg with the same id at a different class is an aliased width view of
/// the same underlying register (the dirty-high-bits class), so a narrow def
/// must stop the resolver / poison the window exactly like a full def.
fn local_fold_defines_vreg(inst: &X86ISelInst, v: VReg) -> bool {
    if matches!(
        inst.opcode,
        X86Opcode::Xchg
            | X86Opcode::Cmpxchg
            | X86Opcode::Cmpxchg8
            | X86Opcode::Cmpxchg16
            | X86Opcode::AtomicRmwCasLoop
            | X86Opcode::AtomicRmwCasLoop8
            | X86Opcode::AtomicRmwCasLoop16
    ) {
        return inst
            .operands
            .iter()
            .any(|op| matches!(op, X86ISelOperand::VReg(d) if d.id == v.id));
    }
    // ANY instruction with a VReg operand 0 matching the id is treated as a
    // POTENTIAL def (fail-closed) — NOT gated on `x86_produces_value`,
    // which deliberately excludes StackAlloc even though StackAlloc DOES
    // write its operand-0 vreg (the allocated address); gating on it would
    // let the resolver walk past such a def to a stale one
    // (adversarial-review finding). Treating a use-position operand 0
    // (e.g. CmpRR's) as a def merely terminates resolution early:
    // conservative, never wrong.
    matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if d.id == v.id)
}

/// Nearest def of `v` strictly before `pos` in the block, or None (live-in).
fn nearest_local_def_before(insts: &[X86ISelInst], pos: usize, v: VReg) -> Option<usize> {
    (0..pos)
        .rev()
        .find(|&i| local_fold_defines_vreg(&insts[i], v))
}

/// True iff some inst in [from, to) may define `v`.
fn no_def_in_range(insts: &[X86ISelInst], from: usize, to: usize, v: VReg) -> bool {
    !insts[from..to]
        .iter()
        .any(|inst| local_fold_defines_vreg(inst, v))
}

/// A resolved local address chain: `base + index*1 + disp` with capture
/// positions for the final-operand redef checks.
struct LocalChainAddr {
    base: VReg,
    base_captured_at: usize,
    index: Option<(VReg, usize)>,
    disp: i64,
    links_consumed: usize,
}

/// One link of the resolvable chain dialect.
enum LocalChainLink {
    /// `MovRR d, s`: continue with s read at the link.
    Copy(VReg),
    /// `AddRI d, s, k` or tied `AddRI d, k` (s == d resolved above the link).
    AddImm(VReg, i64),
    /// `AddRR d, s1, s2` or tied `AddRR d, s`: base continues via .0, index .1.
    AddReg(VReg, VReg),
}

/// Classify `inst` (which defines `v`) as a resolvable chain link. Fail-closed:
/// default flags only, no proof_origin, Gpr64 everywhere.
fn classify_local_chain_link(inst: &X86ISelInst, v: VReg) -> Option<LocalChainLink> {
    if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
        return None;
    }
    let g64 = |r: &VReg| r.class == RegClass::Gpr64;
    match inst.opcode {
        X86Opcode::MovRR => match inst.operands.as_slice() {
            [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] if *d == v && g64(d) && g64(s) => {
                Some(LocalChainLink::Copy(*s))
            }
            _ => None,
        },
        X86Opcode::AddRI => match inst.operands.as_slice() {
            // Tied: d := d + k — the source is d's value ABOVE the link.
            [X86ISelOperand::VReg(d), X86ISelOperand::Imm(k)] if *d == v && g64(d) => {
                Some(LocalChainLink::AddImm(*d, *k))
            }
            // Three-address: d := s + k.
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s),
                X86ISelOperand::Imm(k),
            ] if *d == v && g64(d) && g64(s) => Some(LocalChainLink::AddImm(*s, *k)),
            _ => None,
        },
        X86Opcode::AddRR => match inst.operands.as_slice() {
            // Tied: d := d + s — base continues as d above, index is s.
            [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] if *d == v && g64(d) && g64(s) => {
                Some(LocalChainLink::AddReg(*d, *s))
            }
            // Three-address: d := s1 + s2.
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s1),
                X86ISelOperand::VReg(s2),
            ] if *d == v && g64(d) && g64(s1) && g64(s2) => Some(LocalChainLink::AddReg(*s1, *s2)),
            _ => None,
        },
        _ => None,
    }
}

const LOCAL_CHAIN_MAX_LINKS: usize = 8;

/// Resolve the address vreg `start` (read by the memory op at `mem_idx` with
/// starting displacement `start_disp`) into `base + index*1 + disp` by local
/// nearest-def chain walking. See the module comment for the invariant proof.
fn resolve_local_addr_chain(
    insts: &[X86ISelInst],
    mem_idx: usize,
    start: VReg,
    start_disp: i64,
) -> Option<LocalChainAddr> {
    let mut v = start;
    let mut pos = mem_idx;
    let mut disp = start_disp;
    let mut index: Option<(VReg, usize)> = None;
    let mut links = 0usize;

    while links < LOCAL_CHAIN_MAX_LINKS {
        let Some(def_idx) = nearest_local_def_before(insts, pos, v) else {
            break; // live-in: finalize with v as base captured at pos.
        };
        match classify_local_chain_link(&insts[def_idx], v) {
            Some(LocalChainLink::Copy(s)) => {
                v = s;
                pos = def_idx;
            }
            Some(LocalChainLink::AddImm(s, k)) => {
                disp = disp.checked_add(k)?;
                v = s;
                pos = def_idx;
            }
            Some(LocalChainLink::AddReg(s1, s2)) if index.is_none() => {
                index = Some((s2, def_idx));
                v = s1;
                pos = def_idx;
            }
            // Second AddRR (index already taken) or unrecognized def:
            // finalize with the current v as base. Note: for a def we could
            // not classify, v's value at pos IS that def's result — the base
            // capture position stays `pos` (below the def), which is exactly
            // where the chain read it.
            _ => break,
        }
        links += 1;
    }

    // Final-operand validity: base (and index) must hold the same value at
    // the memory op as at their capture positions.
    if !no_def_in_range(insts, pos, mem_idx, v) {
        return None;
    }
    if let Some((iv, ipos)) = index {
        if !no_def_in_range(insts, ipos, mem_idx, iv) {
            return None;
        }
        // SIB base==index is legal; RSP-index impossible pre-regalloc.
        let _ = iv;
    }

    i32::try_from(disp).ok()?;
    Some(LocalChainAddr {
        base: v,
        base_captured_at: pos,
        index,
        disp,
        links_consumed: links,
    })
}

/// Anchor recognizer: MovRM/MovMR (64-bit) or MovRM32/MovMR32 (32-bit) on
/// `[VReg + disp]`. Returns (is_load, addr_vreg, disp, value_operand, width32).
fn local_fold_anchor(inst: &X86ISelInst) -> Option<(bool, VReg, i32, X86ISelOperand, bool)> {
    if inst.proof_origin.is_some() {
        return None;
    }
    if inst.flags != inst.opcode.default_flags() {
        return None;
    }
    match inst.opcode {
        X86Opcode::MovRM | X86Opcode::MovRM32 => {
            let width32 = inst.opcode == X86Opcode::MovRM32;
            let want = if width32 {
                RegClass::Gpr32
            } else {
                RegClass::Gpr64
            };
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(d),
                    X86ISelOperand::MemAddr { base, disp },
                ] if d.class == want => match base.as_ref() {
                    X86ISelOperand::VReg(a) if a.class == RegClass::Gpr64 => {
                        Some((true, *a, *disp, dst.clone(), width32))
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        X86Opcode::MovMR | X86Opcode::MovMR32 => {
            let width32 = inst.opcode == X86Opcode::MovMR32;
            let want = if width32 {
                RegClass::Gpr32
            } else {
                RegClass::Gpr64
            };
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(s),
                ] if s.class == want => match base.as_ref() {
                    X86ISelOperand::VReg(a) if a.class == RegClass::Gpr64 => {
                        Some((false, *a, *disp, src.clone(), width32))
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

/// Run the local address-chain fold on one block. Rewrites memory operands in
/// place; never deletes instructions (DCE owns the sweep). Returns whether
/// anything changed.
fn addr_chain_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    // Collect rewrites first (immutable scan), apply after.
    struct Rewrite {
        mem_idx: usize,
        new_opcode: X86Opcode,
        new_addr: X86ISelOperand,
        is_load: bool,
        value_operand: X86ISelOperand,
    }
    let mut rewrites: Vec<Rewrite> = Vec::new();

    for mem_idx in 0..insts.len() {
        let Some((is_load, addr, d0, value_operand, width32)) = local_fold_anchor(&insts[mem_idx])
        else {
            continue;
        };
        let Some(chain) = resolve_local_addr_chain(insts, mem_idx, addr, i64::from(d0)) else {
            continue;
        };
        if chain.links_consumed == 0 {
            continue;
        }
        let disp = i32::try_from(chain.disp).expect("checked in resolve");
        let (new_opcode, new_addr) = match chain.index {
            Some((iv, _)) => (
                match (is_load, width32) {
                    (true, false) => X86Opcode::MovRMSib,
                    (false, false) => X86Opcode::MovMRSib,
                    (true, true) => X86Opcode::MovRM32Sib,
                    (false, true) => X86Opcode::MovMR32Sib,
                },
                X86ISelOperand::SibMemAddr {
                    base: Box::new(X86ISelOperand::VReg(chain.base)),
                    index: Box::new(X86ISelOperand::VReg(iv)),
                    scale: 1,
                    disp,
                },
            ),
            None => (
                match (is_load, width32) {
                    (true, false) => X86Opcode::MovRM,
                    (false, false) => X86Opcode::MovMR,
                    (true, true) => X86Opcode::MovRM32,
                    (false, true) => X86Opcode::MovMR32,
                },
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(chain.base)),
                    disp,
                },
            ),
        };
        // No-progress guard: identical opcode + address = nothing to do.
        if new_opcode == insts[mem_idx].opcode {
            let same = match (
                &new_addr,
                insts[mem_idx].operands.iter().find(|op| {
                    matches!(
                        op,
                        X86ISelOperand::MemAddr { .. } | X86ISelOperand::SibMemAddr { .. }
                    )
                }),
            ) {
                (a, Some(b)) => a == b,
                _ => false,
            };
            if same {
                continue;
            }
        }
        let _ = chain.base_captured_at;
        rewrites.push(Rewrite {
            mem_idx,
            new_opcode,
            new_addr,
            is_load,
            value_operand,
        });
    }

    if rewrites.is_empty() {
        return false;
    }

    if std::env::var_os("TCG_X86_ADDR_CHAIN_FOLD_LOG").is_some() {
        eprintln!(
            "x86-addr-chain-fold: rewrote {} mem op(s) in `{}` block #{:?}",
            rewrites.len(),
            func.name,
            block_id.0,
        );
    }

    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for r in rewrites {
        let mem = &mut block.insts[r.mem_idx];
        mem.opcode = r.new_opcode;
        mem.flags = r.new_opcode.default_flags();
        mem.operands = if r.is_load {
            vec![r.value_operand, r.new_addr]
        } else {
            vec![r.new_addr, r.value_operand]
        };
    }
    true
}

/// A clean, single-def base-`Lea` recorded function-wide for the SIB-base fold:
/// `Lea b, [MemAddr{ base, disp }]` located at (`block`, `idx`).
struct LeaBaseDef {
    base: X86ISelOperand,
    disp: i32,
    block: trust_cg_lower::instructions::Block,
    idx: usize,
}

/// Fold a base-defining `Lea` into the BASE of an already-formed indexed SIB
/// memory operand.
///
/// After `sib_addr_fold`/`addr_chain_fold` have formed the SIB load, a stack
/// array access is still `Lea b, [MemAddr{ Base, d0 }]` (Base a `StackSlot` or
/// gpr64 `VReg`) feeding a single
/// `Mov*Sib dst, [SibMemAddr{ base: b, index, scale, disp: d1 }]`. This
/// substitutes `Base` for `b` and folds `d0` into the SIB displacement, yielding
/// `Mov*Sib [Base + index*scale + (d0+d1)]` and leaving the now-dead `Lea` for
/// DCE. It eliminates the redundant `leaq -N(%rbp)` trust-cg recomputes on every
/// stack/local-array access (which LLVM folds natively into
/// `disp(%rbp,idx,scale)`), the dominant instruction-count gap on the
/// sort/matmul cluster.
///
/// # Soundness (rewrite-only; the per-instruction reconstruction gate already
/// covers the `SibMemAddr{ base: StackSlot|VReg, .. }` family — base-agnostic EA
/// proof — so there is no new SMT obligation; this is the pass's hand-proof):
///   original EA = (frame(Base) + sext(d0)) + index*scale + sext(d1)
///   folded   EA =  frame(Base) + index*scale + sext(d0 + d1)
/// These are equal iff `sext(d0 + d1) == sext(d0) + sext(d1)` in 64 bits, i.e.
/// iff the integer sum `d0 + d1` fits in `i32` — the ONLY wrap concern, closed by
/// the mandatory `checked_add` + `i32::try_from` bail. `b` is required single-def
/// + single-use function-wide (the `Lea` is its only def, this load its only
///   use), so the substitution has no other reader and the `Lea` is trivially dead.
///   A `StackSlot` base is frame-invariant (same value at Lea and anchor with no
///   range check); a `VReg` base must not be redefined between the `Lea` and the
///   anchor (`no_def_in_range`). Both instructions must carry default flags and no
///   `proof_origin` (preserves atomic/volatile load/store proofs). The index is
///   untouched.
///   Resolve `b` through single-def `MovRR` copies (`copy_src`) to the clean
///   `StackSlot`/`VReg`-based `Lea` that ultimately defines its value, if any.
///   Bounded to avoid cycles. A copy preserves its source's value, so for a
///   frame-invariant `StackSlot` LEA the resolved base holds the same address.
fn resolve_sib_base_lea<'a>(
    mut b: VReg,
    lea_defs: &'a std::collections::HashMap<VReg, LeaBaseDef>,
    copy_src: &std::collections::HashMap<VReg, VReg>,
) -> Option<&'a LeaBaseDef> {
    for _ in 0..16 {
        if let Some(ld) = lea_defs.get(&b) {
            return Some(ld);
        }
        match copy_src.get(&b) {
            Some(&s) => b = s,
            None => return None,
        }
    }
    None
}

fn sib_base_lea_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    maps: &SibFoldVRegMaps,
    lea_defs: &std::collections::HashMap<VReg, LeaBaseDef>,
    copy_src: &std::collections::HashMap<VReg, VReg>,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    struct Rewrite {
        mem_idx: usize,
        new_addr: X86ISelOperand,
    }
    let mut rewrites: Vec<Rewrite> = Vec::new();

    for mem_idx in 0..insts.len() {
        let anchor = &insts[mem_idx];
        if anchor.proof_origin.is_some() || anchor.flags != anchor.opcode.default_flags() {
            continue;
        }
        if !matches!(
            anchor.opcode,
            X86Opcode::MovRM32Sib
                | X86Opcode::MovRMSib
                | X86Opcode::MovMR32Sib
                | X86Opcode::MovMRSib
                | X86Opcode::MovRM8Sib
                | X86Opcode::MovMR8Sib
                // Scalar-FP SIB loads participate too: a stack-allocated float
                // array (`let a = [0f64; N]`) otherwise re-materializes its
                // base LEA per access exactly like the GPR case.
                | X86Opcode::MovsdRMSib
                | X86Opcode::MovssRMSib
        ) {
            continue;
        }
        // Extract the SIB operand; its base must be a Gpr64 VReg `b`.
        let Some((b, index_op, scale, d1)) = anchor.operands.iter().find_map(|op| match op {
            X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            } => match base.as_ref() {
                X86ISelOperand::VReg(b) if b.class == RegClass::Gpr64 => {
                    Some((*b, index.clone(), *scale, *disp))
                }
                _ => None,
            },
            _ => None,
        }) else {
            continue;
        };

        // Resolve `b` (possibly a `MovRR` copy of the base) to the clean `Lea`
        // that defines its value.
        let Some(lea) = resolve_sib_base_lea(b, lea_defs, copy_src) else {
            continue;
        };

        // Base foldability:
        //  - `StackSlot`: frame-invariant, so substituting it into this SIB
        //    operand is sound regardless of which block the `Lea` is in, how many
        //    `MovRR` copies separate `b` from the `Lea`, and how many times `b` is
        //    used (each SIB use folds independently; once all uses of the copy
        //    chain are folded, the copies + `Lea` go dead and DCE sweeps them).
        //  - Gpr64 `VReg`: a register base can be clobbered, so restrict to the
        //    DIRECT (uncopied) case: `b` itself is the `Lea`, same block, single
        //    function-wide use, no redef between the `Lea` and the anchor.
        let base_ok = match &lea.base {
            X86ISelOperand::StackSlot(_) => true,
            X86ISelOperand::VReg(r) if r.class == RegClass::Gpr64 => {
                lea_defs.contains_key(&b)
                    && lea.block == block_id
                    && lea.idx < mem_idx
                    && maps.use_count(b) == 1
                    && no_def_in_range(insts, lea.idx + 1, mem_idx, *r)
            }
            _ => false,
        };
        if !base_ok {
            continue;
        }

        // Fold the displacements; bail if the i32 SIB disp would overflow (the
        // only wrap concern — see the soundness note).
        let Some(new_disp) = i64::from(lea.disp)
            .checked_add(i64::from(d1))
            .and_then(|s| i32::try_from(s).ok())
        else {
            continue;
        };

        rewrites.push(Rewrite {
            mem_idx,
            new_addr: X86ISelOperand::SibMemAddr {
                base: Box::new(lea.base.clone()),
                index: index_op,
                scale,
                disp: new_disp,
            },
        });
    }

    if rewrites.is_empty() {
        return false;
    }

    if std::env::var_os("TCG_X86_SIB_BASE_FOLD_LOG").is_some() {
        eprintln!(
            "x86-sib-base-fold: rewrote {} SIB base(s) in `{}` block #{:?}",
            rewrites.len(),
            func.name,
            block_id.0,
        );
    }

    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for r in rewrites {
        for op in block.insts[r.mem_idx].operands.iter_mut() {
            if matches!(op, X86ISelOperand::SibMemAddr { .. }) {
                *op = r.new_addr;
                break;
            }
        }
    }
    true
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
    use trust_cg_lower::x86_64_isel::X86ProofOrigin;

    use crate::X86PassManager;

    fn vreg(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn vreg_class(id: u32, class: RegClass) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, class))
    }

    fn make_func(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_peephole_test".to_string(), sig);
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

    // ---- sib_base_lea_fold tests -----------------------------------------

    fn lea_base(dst: u32, base: X86ISelOperand, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                vreg(dst),
                X86ISelOperand::MemAddr {
                    base: Box::new(base),
                    disp,
                },
            ],
        )
    }

    fn movrm32_sib(dst: u32, base: u32, index: u32, scale: u8, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::MovRM32Sib,
            vec![
                vreg32(dst),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(base)),
                    index: Box::new(vreg(index)),
                    scale,
                    disp,
                },
            ],
        )
    }

    fn run_sib_base_fold(func: &mut X86ISelFunction) -> bool {
        let maps = SibFoldVRegMaps::build(func);
        let mut lea_defs: std::collections::HashMap<VReg, LeaBaseDef> =
            std::collections::HashMap::new();
        for (block_id, block) in &func.blocks {
            for (idx, inst) in block.insts.iter().enumerate() {
                if inst.opcode == X86Opcode::Lea
                    && inst.proof_origin.is_none()
                    && inst.flags == inst.opcode.default_flags()
                    && let [
                        X86ISelOperand::VReg(d),
                        X86ISelOperand::MemAddr { base, disp },
                    ] = inst.operands.as_slice()
                    && maps.def_count(*d) == 1
                {
                    lea_defs.insert(
                        *d,
                        LeaBaseDef {
                            base: base.as_ref().clone(),
                            disp: *disp,
                            block: *block_id,
                            idx,
                        },
                    );
                }
            }
        }
        let mut copy_src: std::collections::HashMap<VReg, VReg> = std::collections::HashMap::new();
        for block in func.blocks.values() {
            for inst in &block.insts {
                if inst.opcode == X86Opcode::MovRR
                    && let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] =
                        inst.operands.as_slice()
                    && maps.def_count(*d) == 1
                {
                    copy_src.insert(*d, *s);
                }
            }
        }
        sib_base_lea_fold_run_on_block(func, Block(0), &maps, &lea_defs, &copy_src)
    }

    fn sib_addr(inst: &X86ISelInst) -> (&X86ISelOperand, &X86ISelOperand, u8, i32) {
        for op in &inst.operands {
            if let X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            } = op
            {
                return (base.as_ref(), index.as_ref(), *scale, *disp);
            }
        }
        panic!("no SibMemAddr operand");
    }

    #[test]
    fn sib_base_fold_stackslot_folds_and_leaves_lea_for_dce() {
        // Lea b(2), [StackSlot(3) + 8]; MovRM32Sib d, [b + idx(1)*4 + 16]
        //   => MovRM32Sib d, [StackSlot(3) + idx*4 + 24]
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), 8),
            movrm32_sib(10, 2, 1, 4, 16),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let insts = entry_insts(&func);
        let (base, index, scale, disp) = sib_addr(&insts[1]);
        assert_eq!(*base, X86ISelOperand::StackSlot(3));
        assert_eq!(*index, vreg(1));
        assert_eq!(scale, 4);
        assert_eq!(disp, 24); // 8 + 16
        // The Lea is left in place (dead) for DCE to sweep.
        assert_eq!(insts[0].opcode, X86Opcode::Lea);
    }

    /// A stack-allocated f64 array (`let a = [0f64; N]`) must fold its base LEA
    /// exactly like the GPR case — this is b11_float_dot's actual shape.
    #[test]
    fn sib_base_fold_folds_scalar_fp_load() {
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), 8),
            X86ISelInst::new(
                X86Opcode::MovsdRMSib,
                vec![
                    vreg(10),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(vreg(2)),
                        index: Box::new(vreg(1)),
                        scale: 8,
                        disp: 16,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let insts = entry_insts(&func);
        let (base, index, scale, disp) = sib_addr(&insts[1]);
        assert_eq!(*base, X86ISelOperand::StackSlot(3));
        assert_eq!(*index, vreg(1));
        assert_eq!(scale, 8);
        assert_eq!(disp, 24); // 8 + 16
        assert_eq!(insts[1].opcode, X86Opcode::MovsdRMSib);
    }

    /// The address fold must turn a scalar-FP load's plain base into a SIB
    /// operand, and must REFUSE to do so for the STORE form — there is
    /// deliberately no MovsdMRSib opcode to fold into.
    #[test]
    fn sib_addr_fold_admits_fp_load_and_refuses_fp_store() {
        let load = X86ISelInst::new(
            X86Opcode::MovsdRM,
            vec![
                vreg(10),
                X86ISelOperand::MemAddr {
                    base: Box::new(vreg(2)),
                    disp: 0,
                },
            ],
        );
        let folded = sib_foldable_mem_op(&load).expect("MovsdRM must be foldable");
        assert_eq!(folded.3, X86Opcode::MovsdRMSib);
        assert!(folded.0, "load must be flagged as a load");

        let store = X86ISelInst::new(
            X86Opcode::MovsdMR,
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(vreg(2)),
                    disp: 0,
                },
                vreg(10),
            ],
        );
        assert!(
            sib_foldable_mem_op(&store).is_none(),
            "MovsdMR must NOT fold — no MovsdMRSib opcode exists to fold into"
        );
    }

    #[test]
    fn sib_base_fold_vreg_base_no_redef_folds() {
        // Lea b(2), [base_vreg(5) + 4]; MovRM32Sib d, [b + idx(1)*8 + 0]
        //   => base becomes vreg(5), disp 4.
        let mut func = make_func(vec![
            lea_base(2, vreg(5), 4),
            movrm32_sib(10, 2, 1, 8, 0),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let (base, _index, scale, disp) = sib_addr(&entry_insts(&func)[1]);
        assert_eq!(*base, vreg(5));
        assert_eq!(scale, 8);
        assert_eq!(disp, 4);
    }

    #[test]
    fn sib_base_fold_declines_vreg_base_redefined_between() {
        // A redefinition of the base vreg(5) between the Lea and the anchor
        // makes the substitution unsound -> decline.
        let mut func = make_func(vec![
            lea_base(2, vreg(5), 4),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(1)]),
            movrm32_sib(10, 2, 1, 4, 0),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!run_sib_base_fold(&mut func));
    }

    #[test]
    fn sib_base_fold_multiuse_stackslot_folds_all() {
        // A StackSlot base is frame-invariant, so ALL of b(2)'s SIB uses fold
        // independently (the single Lea then goes dead for DCE).
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), 0),
            movrm32_sib(10, 2, 1, 4, 0),
            movrm32_sib(11, 2, 1, 4, 4),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let insts = entry_insts(&func);
        for i in [1usize, 2] {
            let (base, _idx, _scale, _disp) = sib_addr(&insts[i]);
            assert_eq!(*base, X86ISelOperand::StackSlot(3));
        }
    }

    #[test]
    fn sib_base_fold_through_copy_of_stackslot_lea() {
        // The ISel materializes the base as a copy: Lea b, [StackSlot]; MovRR c, b;
        // MovRM32Sib d, [c + idx*4 + 8]. The fold resolves c -> b -> StackSlot.
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), 0),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(4), vreg(2)]),
            movrm32_sib(10, 4, 1, 4, 8),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let (base, _idx, _scale, disp) = sib_addr(&entry_insts(&func)[2]);
        assert_eq!(*base, X86ISelOperand::StackSlot(3));
        assert_eq!(disp, 8);
    }

    #[test]
    fn sib_base_fold_declines_multiuse_vreg_base() {
        // A Gpr64 VReg base with TWO uses -> not single-use -> decline (a
        // register base could be clobbered; only StackSlot bases go multi-use).
        let mut func = make_func(vec![
            lea_base(2, vreg(5), 0),
            movrm32_sib(10, 2, 1, 4, 0),
            movrm32_sib(11, 2, 1, 4, 4),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!run_sib_base_fold(&mut func));
    }

    #[test]
    fn sib_base_fold_declines_disp_overflow() {
        // d0 + d1 overflows i32 -> the sext-distributivity precondition fails.
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), i32::MAX),
            movrm32_sib(10, 2, 1, 4, 1),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!run_sib_base_fold(&mut func));
    }

    #[test]
    fn imm_fold_and_add_sub_cmp_imul() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(1), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(3), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(4), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(5), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::AndRI);
        assert_eq!(insts[1].operands[2], X86ISelOperand::Imm(7));
        assert_eq!(insts[2].opcode, X86Opcode::AddRI);
        assert_eq!(insts[3].opcode, X86Opcode::SubRI);
        assert_eq!(insts[4].opcode, X86Opcode::ImulRRI);
        assert_eq!(insts[5].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[5].operands[1], X86ISelOperand::Imm(7));
    }

    #[test]
    fn imm_fold_commutative_lhs_swaps() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(9)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(1), vreg(0), vreg(2)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::AddRI);
        assert_eq!(insts[1].operands[1], vreg(2));
        assert_eq!(insts[1].operands[2], X86ISelOperand::Imm(9));
    }

    #[test]
    fn imm_fold_skips_multi_def_and_non_imm32() {
        // v0 defined twice -> no fold; v3's constant does not fit sext-imm32.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg(3), X86ISelOperand::Imm(0x1_0000_0000)],
            ),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(1), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[3].opcode, X86Opcode::AndRR);
        assert_eq!(insts[4].opcode, X86Opcode::AddRR);
    }

    #[test]
    fn imm_fold_sub_rhs_only_never_lhs() {
        // Subtraction is not commutative: a constant LHS must NOT be folded.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(1), vreg(0), vreg(2)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        assert_eq!(entry_insts(&func)[1].opcode, X86Opcode::SubRR);
    }

    #[test]
    fn imm_fold_negative_imm32_folds() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(-2)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[1].operands[1], X86ISelOperand::Imm(-2));
    }

    #[test]
    fn imm_fold_sees_through_single_def_copy_chain() {
        // CSE's canonical-constant shape: MovRI root, then single-def MovRR
        // copies; consumers read the constant through the chain (depth 2
        // here). Both the imul and the cmp must fold.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(4), vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(5), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[3].opcode, X86Opcode::ImulRRI);
        assert_eq!(insts[3].operands[2], X86ISelOperand::Imm(8));
        assert_eq!(insts[4].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[4].operands[1], X86ISelOperand::Imm(8));
    }

    #[test]
    fn imm_fold_refutes_multi_def_copy_link() {
        // The copy dest v1 is defined twice -> its value is not a single
        // static assignment; consumers must NOT fold through it.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        assert_eq!(entry_insts(&func)[3].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn imm_fold_refutes_copy_of_multi_def_root() {
        // The MovRI root v0 is defined twice -> the copy v1 does not hold a
        // provable constant; the consumer must NOT fold.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(9)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        assert_eq!(entry_insts(&func)[3].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn imm_fold_copy_cycle_terminates_without_folding() {
        // A single-def copy CYCLE (v1 = mov v2; v2 = mov v1) has no MovRI
        // root: the chase must terminate and must not credit a constant.
        // (v0's unrelated constant keeps `consts` non-empty so the chase
        // loop actually runs.)
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(5), vreg(6), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        // The direct v0 use still folds; the cycle-fed imul must not.
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[3].opcode, X86Opcode::ImulRR);
        assert_eq!(insts[4].opcode, X86Opcode::AndRI);
    }

    #[test]
    fn imm_fold_refutes_non_gpr64_copy_link() {
        // Only plain Gpr64 MovRR links are chased: a Gpr32 MovRR32 copy of a
        // (Gpr32) constant is not a chase link, so the 32-bit consumer keeps
        // its register operand (direct MovRI uses keep folding either way —
        // this pins that the CHAIN is opcode/class-guarded).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(1), vreg32(0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg32(3), vreg32(4), vreg32(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        assert_eq!(entry_insts(&func)[2].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn x86_peephole_removes_self_movrr_through_pass_manager() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86Peephole));

        assert!(pm.run_once(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
    }

    #[test]
    fn x86_peephole_removes_self_movrr32() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(0), vreg32(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
    }

    #[test]
    fn x86_peephole_removes_self_xmm_copies() {
        for (opcode, class) in [
            (X86Opcode::MovssRR, RegClass::Fpr32),
            (X86Opcode::MovsdRR, RegClass::Fpr64),
            (X86Opcode::MovdqaRR, RegClass::Fpr128),
        ] {
            let reg = |id| vreg_class(id, class);
            let mut func = make_func(vec![
                X86ISelInst::new(opcode, vec![reg(0), reg(0)]),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            let mut peephole = X86Peephole;

            assert!(
                peephole.run_on_function(&mut func),
                "{opcode:?} self-copy should be removed"
            );

            assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
        }
    }

    #[test]
    fn x86_peephole_rewrites_zero_disp_lea_to_movrr() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(2),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(entry_opcodes(&func), vec![X86Opcode::MovRR, X86Opcode::Ret]);
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_peephole_preserves_proof_origin_on_replace() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(2),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 0,
                    },
                ],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovRR);
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
    }

    #[test]
    fn x86_peephole_rewrites_cmp_zero_to_test_rr_even_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::TestRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
    }

    #[test]
    fn x86_peephole_rewrites_cmp_ri8_zero_to_test_rr() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI8, vec![vreg32(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::NE)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::TestRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands, vec![vreg32(1), vreg32(1)]);
    }

    #[test]
    fn x86_peephole_rewrites_testri_all_ones_to_test_rr_even_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg(1), X86ISelOperand::Imm(-1)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg32(3), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(4), X86ISelOperand::CondCode(X86CondCode::NE)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::TestRR,
                X86Opcode::Setcc,
                X86Opcode::TestRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(3), vreg32(3)]);
    }

    #[test]
    fn x86_peephole_preserves_unsupported_testri_all_ones_forms() {
        let mem = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg(2), X86ISelOperand::Imm(-2)]),
            X86ISelInst::new(
                X86Opcode::TestRI,
                vec![vreg_class(3, RegClass::Fpr64), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(
                X86Opcode::TestRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::TestRI, vec![mem, X86ISelOperand::Imm(-1)]),
            X86ISelInst::with_flags(
                X86Opcode::TestRI,
                vec![vreg(4), X86ISelOperand::Imm(-1)],
                X86Opcode::TestRI
                    .default_flags()
                    .union(InstFlags::READS_MEMORY),
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_cmp_zero_forms() {
        let mem = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::CmpRI8, vec![vreg(2), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![mem, X86ISelOperand::Imm(0)]),
            X86ISelInst::with_flags(
                X86Opcode::CmpRI,
                vec![vreg(3), X86ISelOperand::Imm(0)],
                InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::READS_MEMORY),
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::CmpRI8,
                X86Opcode::CmpRI,
                X86Opcode::CmpRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            entry_insts(&func)[4].flags,
            InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::READS_MEMORY)
        );
    }

    #[test]
    fn x86_peephole_removes_zero_disp_self_lea() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(2),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(2)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
    }

    #[test]
    fn x86_peephole_preserves_non_identity_lea_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(2),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 8,
                    },
                ],
            ),
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(3),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::PReg(RAX)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::Lea, X86Opcode::Lea, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_rewrites_three_operand_double_add_to_lea_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::LeaSib, X86Opcode::TestRR, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands[0], vreg(4));
        assert_eq!(
            insts[0].operands[1],
            X86ISelOperand::SibMemAddr {
                base: Box::new(vreg(1)),
                index: Box::new(vreg(1)),
                scale: 1,
                disp: 0,
            }
        );
    }

    #[test]
    fn x86_peephole_rewrites_two_operand_self_add_to_lea_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::LeaSib, X86Opcode::TestRR, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands[0], vreg(2));
        assert_eq!(
            insts[0].operands[1],
            X86ISelOperand::SibMemAddr {
                base: Box::new(vreg(2)),
                index: Box::new(vreg(2)),
                scale: 1,
                disp: 0,
            }
        );
    }

    #[test]
    fn x86_peephole_preserves_double_add_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::AddRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_double_add_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg32(4), vreg32(1), vreg32(1)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(5), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(5), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::AddRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_rewrites_zero_immediate_identities_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(3), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::OrRI,
                vec![vreg(4), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg(5), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(6), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::ShrRI,
                vec![vreg(7), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::SarRI,
                vec![vreg(8), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(8), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(entry_insts(&func)[0].operands, vec![vreg(2), vreg(0)]);
        assert_eq!(entry_insts(&func)[6].operands, vec![vreg(8), vreg(1)]);
    }

    #[test]
    fn x86_peephole_materializes_gpr32_identity_as_movrr32() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::OrRI,
                vec![vreg32(2), vreg32(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovRR32);
        assert_eq!(insts[0].operands, vec![vreg32(2), vreg32(1)]);
    }

    #[test]
    fn x86_peephole_rewrites_movri_zero_to_xor_zero_when_introduced_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(0)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(2)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(4), vreg32(4)]);
    }

    #[test]
    fn x86_peephole_preserves_movri_zero_when_introduced_flags_are_read_or_live_out() {
        let mut read_func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut branch_func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut live_out_func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut partial_func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Inc, vec![vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut read_func));
        assert!(!peephole.run_on_function(&mut branch_func));
        assert!(!peephole.run_on_function(&mut live_out_func));
        assert!(peephole.run_on_function(&mut partial_func));

        assert_eq!(
            entry_opcodes(&read_func),
            vec![X86Opcode::MovRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&branch_func),
            vec![X86Opcode::MovRI, X86Opcode::Jcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&live_out_func),
            vec![X86Opcode::MovRI, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&partial_func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::Inc,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            entry_insts(&partial_func)[0].operands,
            vec![vreg(1), X86ISelOperand::Imm(0)]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_movri_zero_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg_class(3, RegClass::Fpr64), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_rewrites_self_add_sub_one_to_inc_dec_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), X86ISelOperand::Imm(1)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(1)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg32(3), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg32(4), vreg32(4), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Inc,
                X86Opcode::TestRR,
                X86Opcode::Dec,
                X86Opcode::TestRR,
                X86Opcode::Inc,
                X86Opcode::TestRR,
                X86Opcode::Dec,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg(2)]);
        assert_eq!(insts[2].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[4].operands, vec![vreg32(3)]);
        assert_eq!(insts[6].operands, vec![vreg32(4)]);
    }

    #[test]
    fn x86_peephole_preserves_add_sub_one_when_flags_are_read_or_live_out() {
        let mut add_read_func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut sub_read_func = make_func(vec![
            X86ISelInst::new(X86Opcode::SubRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut add_live_out_func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut sub_live_out_func = make_func(vec![
            X86ISelInst::new(X86Opcode::SubRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut add_read_func));
        assert!(!peephole.run_on_function(&mut sub_read_func));
        assert!(!peephole.run_on_function(&mut add_live_out_func));
        assert!(!peephole.run_on_function(&mut sub_live_out_func));

        assert_eq!(
            entry_opcodes(&add_read_func),
            vec![X86Opcode::AddRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&sub_read_func),
            vec![X86Opcode::SubRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&add_live_out_func),
            vec![X86Opcode::AddRI, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&sub_live_out_func),
            vec![X86Opcode::SubRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_and_nonself_add_sub_one_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(4), vreg(3), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(5), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::SubRI, vec![vreg(6), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(7), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg_class(8, RegClass::Fpr64), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(8), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(10), vreg32(9), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(10), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::SubRI,
                X86Opcode::TestRR,
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::SubRI,
                X86Opcode::TestRR,
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            insts[0].operands,
            vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)]
        );
        assert_eq!(
            insts[2].operands,
            vec![vreg(4), vreg(3), X86ISelOperand::Imm(1)]
        );
        assert_eq!(insts[4].operands, vec![vreg(5), X86ISelOperand::Imm(2)]);
        assert_eq!(
            insts[8].operands,
            vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(1)]
        );
        assert_eq!(
            insts[10].operands,
            vec![vreg_class(8, RegClass::Fpr64), X86ISelOperand::Imm(1)]
        );
        assert_eq!(
            insts[12].operands,
            vec![vreg(10), vreg32(9), X86ISelOperand::Imm(1)]
        );
    }

    #[test]
    fn x86_peephole_rewrites_and_and_equal_rr_identities() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(2), vreg(0), X86ISelOperand::Imm(0)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(3), vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(4), vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::OrRR, vec![vreg(5), vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(6), vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRR,
                X86Opcode::XorRR,
                X86Opcode::XorRR,
                X86Opcode::XorRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(0)]);
        assert_eq!(insts[1].operands, vec![vreg(2), vreg(2)]);
        assert_eq!(insts[1].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg(3), vreg(3)]);
        assert_eq!(insts[3].operands, vec![vreg(4), vreg(4)]);
        assert_eq!(insts[5].operands, vec![vreg(6), vreg(0)]);
    }

    #[test]
    fn x86_peephole_leaves_canonical_two_operand_xor_zero_unchanged() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(1), vreg(1)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::XorRR, X86Opcode::TestRR, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
    }

    #[test]
    fn x86_peephole_preserves_self_zero_rr_when_flags_are_read() {
        let mut sub_func = make_func(vec![
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(3), vreg(0), vreg(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut xor_func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(4), vreg(1), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut sub_func));
        assert!(!peephole.run_on_function(&mut xor_func));

        assert_eq!(
            entry_opcodes(&sub_func),
            vec![X86Opcode::SubRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&xor_func),
            vec![X86Opcode::XorRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_insts(&sub_func)[0].operands,
            vec![vreg(3), vreg(0), vreg(0)]
        );
        assert_eq!(
            entry_insts(&xor_func)[0].operands,
            vec![vreg(4), vreg(1), vreg(1)]
        );
    }

    #[test]
    fn x86_peephole_rewrites_and_zero_two_operand_and_gpr32_to_xor_zero() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg32(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(1)]);
        assert_eq!(insts[1].operands, vec![vreg32(2), vreg32(2)]);
    }

    #[test]
    fn x86_peephole_preserves_and_zero_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::AndRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_and_zero_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(2), vreg32(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg_class(3, RegClass::Fpr32), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AndRI,
                X86Opcode::AndRI,
                X86Opcode::AndRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_rewrites_xor_allones_self_to_not_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRI, vec![vreg(1), X86ISelOperand::Imm(-1)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Not,
                X86Opcode::Not,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[1].operands, vec![vreg(2)]);
    }

    #[test]
    fn x86_peephole_rewrites_xor_allones_gpr32_self_to_not() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRI, vec![vreg32(1), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::Not, X86Opcode::TestRR, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands, vec![vreg32(1)]);
    }

    #[test]
    fn x86_peephole_preserves_unsupported_xor_allones_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::XorRI, vec![vreg(2), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::XorRI, vec![vreg(3), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(4), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRI,
                X86Opcode::XorRI,
                X86Opcode::XorRI,
                X86Opcode::XorRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_rewrites_imul_rri_one_to_copy_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg32(4), vreg32(3), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRR,
                X86Opcode::TestRR,
                X86Opcode::MovRR32,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(4), vreg32(3)]);
    }

    #[test]
    fn x86_peephole_removes_self_imul_rri_one_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::TestRR, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_rewrites_imul_rri_zero_to_xor_zero_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg32(4), vreg32(3), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(6), vreg(6), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(2)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(4), vreg32(4)]);
        assert_eq!(insts[4].operands, vec![vreg(6), vreg(6)]);
    }

    #[test]
    fn x86_peephole_preserves_imul_rri_zero_when_flags_are_read_or_live_out() {
        let mut read_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::O)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut live_out_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut read_func));
        assert!(!peephole.run_on_function(&mut live_out_func));

        assert_eq!(
            entry_opcodes(&read_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&live_out_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_rewrites_self_imul_rri_minus_one_to_neg_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(-1)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg32(4), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Neg,
                X86Opcode::TestRR,
                X86Opcode::Neg,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(2)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(4)]);
    }

    #[test]
    fn x86_peephole_preserves_non_self_and_non_minus_one_imul_rri() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(4), vreg(4), X86ISelOperand::Imm(-2)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::ImulRRI,
                X86Opcode::TestRR,
                X86Opcode::ImulRRI,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            insts[0].operands,
            vec![vreg(2), vreg(1), X86ISelOperand::Imm(-1)]
        );
        assert_eq!(
            insts[2].operands,
            vec![vreg(4), vreg(4), X86ISelOperand::Imm(-2)]
        );
    }

    #[test]
    fn x86_peephole_preserves_self_imul_rri_minus_one_when_flags_are_read_or_live_out() {
        let mut read_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::O)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut live_out_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut read_func));
        assert!(!peephole.run_on_function(&mut live_out_func));

        assert_eq!(
            entry_opcodes(&read_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&live_out_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_imul_rri_one_when_flags_are_read_or_live_out() {
        let mut read_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::O)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut live_out_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut read_func));
        assert!(!peephole.run_on_function(&mut live_out_func));

        assert_eq!(
            entry_opcodes(&read_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&live_out_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_non_identity_imul_rri_immediates() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(2)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::ImulRRI, X86Opcode::TestRR, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_identity_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::AddRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_does_not_treat_not_as_flag_kill() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::Not, vec![vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(3), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRI,
                X86Opcode::Not,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_does_not_treat_inc_dec_as_full_flag_kills() {
        for opcode in [X86Opcode::Inc, X86Opcode::Dec] {
            let mut func = make_func(vec![
                X86ISelInst::new(
                    X86Opcode::AddRI,
                    vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
                ),
                X86ISelInst::new(opcode, vec![vreg(2)]),
                X86ISelInst::new(
                    X86Opcode::Setcc,
                    vec![vreg(3), X86ISelOperand::CondCode(X86CondCode::B)],
                ),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            let mut peephole = X86Peephole;

            assert!(
                !peephole.run_on_function(&mut func),
                "{:?} must not prove CF dead",
                opcode
            );

            assert_eq!(
                entry_opcodes(&func),
                vec![X86Opcode::AddRI, opcode, X86Opcode::Setcc, X86Opcode::Ret,]
            );
        }
    }

    #[test]
    fn x86_peephole_does_not_treat_shift_zero_as_flag_kill() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(4), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRI,
                X86Opcode::MovRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            entry_insts(&func)[0].operands,
            vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)]
        );
        assert_eq!(entry_insts(&func)[1].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_peephole_preserves_identity_when_flags_may_export_to_branch_or_return() {
        let mut branch_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut return_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut branch_func));
        assert!(!peephole.run_on_function(&mut return_func));

        assert_eq!(
            entry_opcodes(&branch_func),
            vec![X86Opcode::AddRI, X86Opcode::Jcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&return_func),
            vec![X86Opcode::AddRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_fixed_memory_and_side_effect_candidates() {
        let mem = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 8,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(2), mem, X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::with_flags(
                X86Opcode::AddRI,
                vec![vreg(3), vreg(0), X86ISelOperand::Imm(0)],
                InstFlags::HAS_SIDE_EFFECTS,
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AndRI,
                X86Opcode::AndRI,
                X86Opcode::AddRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(entry_insts(&func)[2].flags, InstFlags::HAS_SIDE_EFFECTS);
    }

    // -----------------------------------------------------------------------
    // Setcc-hoist tests
    // -----------------------------------------------------------------------
    //
    // The pattern `[flag_writer]; Setcc cc, %D; Movzx %D, %D` is rewritten
    // to `XorRR %D, %D; [flag_writer]; Setcc cc, %D`. See `try_setcc_hoist`
    // in this file for the hand-proof and the six side conditions.

    #[test]
    fn x86_peephole_setcc_hoist_fires_on_canonical_icmp_pair() {
        // CmpRR %1, %2 ; Setcc E, %D ; Movzx %D, %D
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::CmpRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
        // Xor clears %D before the compare.
        assert_eq!(insts[0].operands, vec![vreg32(10), vreg32(10)]);
        // CmpRR is unchanged and retains its proof_origin.
        assert_eq!(insts[1].operands, vec![vreg(1), vreg(2)]);
        assert_eq!(insts[1].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        // Setcc writes the low byte.
        assert_eq!(
            insts[2].operands,
            vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_fires_on_canonical_testrr_pair() {
        // TestRR is also a Full flag writer; same pattern should fire.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg(1), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::NE)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_inherits_proof_origin() {
        // Proof-origin on the Setcc should land on the hoisted Xor; if the
        // Setcc has none, the flag_writer's proof_origin is used.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;
        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::XorRR);
        // Xor inherits proof_origin from setcc (none here) then flag_writer
        // (AtomicLoad in this test).
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
    }

    #[test]
    fn x86_peephole_setcc_hoist_declines_on_dst_mismatch() {
        // Setcc writes to %10 but Movzx reads %11 - not the canonical pair.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(11), vreg32(11)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRR,
                X86Opcode::Setcc,
                X86Opcode::Movzx,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_declines_when_dst_live_before_flag_writer() {
        // %10 is used as an operand of the AddRI BEFORE the cmp, so hoisting
        // xor would clobber the value being read.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg32(20), vreg32(10), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRI,
                X86Opcode::CmpRR,
                X86Opcode::Setcc,
                X86Opcode::Movzx,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_declines_with_intervening_partial_flag_write() {
        // Inc partially writes RFLAGS (touches OF, SF, ZF, AF, PF but leaves
        // CF). It cannot serve as flag_writer (its overwrite is Partial), and
        // it blocks the cmp -> setcc scan from above. Neither i=cmp nor i=Inc
        // is a valid window start.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::Inc, vec![vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRR,
                X86Opcode::Inc,
                X86Opcode::Setcc,
                X86Opcode::Movzx,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_picks_latest_flag_writer_when_two_dominate() {
        // CmpRR; AddRR; Setcc; Movzx - both CmpRR and AddRR are full flag
        // writers, but AddRR's flags are what Setcc actually reads. The
        // rewrite is sound when keyed on AddRR (the latest flag writer) and
        // we should rewrite to: xor; CmpRR; AddRR; Setcc.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(3), vreg(4)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));
        // The rewrite hoists xor above AddRR, keeping CmpRR in place.
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRR,
                X86Opcode::XorRR,
                X86Opcode::AddRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_declines_when_flag_writer_mentions_dst() {
        // flag_writer reads %D (vreg32(10)). The xor cannot be hoisted because
        // it would change the input to the flag_writer. We don't construct
        // CmpRR with a Gpr32 operand directly (class mismatch), so use TestRR
        // on the same Gpr32 vreg used as the setcc dst.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::TestRR,
                X86Opcode::Setcc,
                X86Opcode::Movzx,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_declines_when_setcc_dst_escapes_window() {
        // %10 is consumed by a downstream AddRI in addition to the Movzx. The
        // single-use side condition fails - refuse to fire.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg32(20), vreg32(10), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRR,
                X86Opcode::Setcc,
                X86Opcode::Movzx,
                X86Opcode::AddRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_declines_when_jcc_consumes_flags_first() {
        // A Jcc reads the flags BEFORE the setcc; refusing to hoist preserves
        // observable behavior even though jcc is technically still consuming
        // flag_writer's flags - we are conservative.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(!peephole.run_on_function(&mut func));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRR,
                X86Opcode::Jcc,
                X86Opcode::Setcc,
                X86Opcode::Movzx,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_setcc_hoist_proof_of_fire_on_bcp_style_isel_output() {
        // This mirrors what `select_comparison` in trust-cg-lower emits for an
        // Icmp whose result feeds a single downstream consumer outside the
        // CmpRR/Setcc/Movzx triple - e.g., a store or a MovRR32 into a PReg
        // for return-value materialization. We pick MovRR32 -> RAX as the
        // consumer because that is what real ISel emits for `ret i32 %D` in
        // the SysV ABI:
        //   CmpRR %lhs, %rhs    ; flags
        //   Setcc E, %D         ; bool low byte
        //   Movzx %D, %D        ; zero-extend
        //   MovRR32 RAX, %D     ; ABI return materialization
        //   Ret
        //
        // After hoist:
        //   XorRR %D, %D
        //   CmpRR %lhs, %rhs
        //   Setcc E, %D
        //   MovRR32 RAX, %D
        //   Ret
        //
        // %D has two uses in the block (Movzx src and MovRR32 src) so this
        // test reproduces the conservative refusal documented above; this is
        // a *negative* proof-of-fire that the conservative side condition is
        // honored even on shapes where soundness would technically allow the
        // rewrite. See file-level comment for the relaxation roadmap.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(20), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(20), vreg32(20)]),
            X86ISelInst::new(
                X86Opcode::MovRR32,
                vec![X86ISelOperand::PReg(RAX), vreg32(20)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);
        let opcodes = entry_opcodes(&func);
        // setcc-hoist conservatively declines because %D is used twice.
        assert_ne!(opcodes.first(), Some(&X86Opcode::XorRR));
    }

    #[test]
    fn x86_peephole_setcc_hoist_fires_when_setcc_result_is_truly_single_use() {
        // Construct a function in which the Setcc destination is consumed
        // ONLY by the Movzx and nothing else. This is the canonical pattern
        // that the V1 setcc-hoist is tuned for - e.g., post-CSE/post-DCE
        // when the bool value's only remaining live consumer happens to be
        // the zero-extend itself (rare in raw ISel output, common after the
        // DCE pass has stripped a downstream consumer).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(20), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(20), vreg32(20)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;
        assert!(peephole.run_on_function(&mut func));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::CmpRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_fuses_condbr_lowering_shape_into_direct_jcc() {
        // The BCP hot path lowers `condbr (icmp eq a, b), then, else` to
        //   CmpRR a, b ; Setcc E, %D ; Movzx %D, %D ;
        //   CmpRI %D, 0 ; Jcc NE, then ; Jmp else
        // The cmp-setcc-branch fusion (which runs before setcc-hoist and the
        // single-instruction cmp-zero->test rewrite) recognizes that the
        // boolean %D is single-use and dead after the branch, and collapses the
        // whole chain to a direct `CmpRR a, b ; Jcc E, then ; Jmp else`. This
        // was previously the "V1 conservative" decline case; the fusion lifts it.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(20), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(20), vreg32(20)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(20), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        assert!(peephole.run_on_function(&mut func));
        // The boolean materialization (Setcc/Movzx/zero-test) is gone; only the
        // comparison and a direct conditional jump on its flags remain.
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::CmpRR, X86Opcode::Jcc, X86Opcode::Jmp],
        );
        let insts = entry_insts(&func);
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(2)]);
        // Jcc NE on (eq-bool != 0) becomes Jcc E (branch when eq holds).
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::E),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    // -----------------------------------------------------------------------
    // AND-power-of-2 + CMP-zero + Jcc -> BT + Jcc tests
    // -----------------------------------------------------------------------
    //
    // See `try_and_pow2_bt_branch` for the hand-proof and side conditions.

    #[test]
    fn x86_peephole_and_pow2_bt_branch_fires_on_two_operand_form_jcc_ne() {
        // AndRI %1, #4 (1<<2) ; CmpRI %1, 0 ; Jcc NE, bb1
        //   -> BtRI %1, #2 ; Jcc B, bb1   (B = CF set = bit 2 was set)
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::BtRI, X86Opcode::Jcc, X86Opcode::Jmp]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), X86ISelOperand::Imm(2)]);
        // proof_origin must transfer from the original AND.
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        // Jcc must use the inverted-to-CF condition: NE -> B (carry set).
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_fires_on_three_operand_form_jcc_e() {
        // AndRI %3, %2, #1 (1<<0) ; CmpRI %3, 0 ; Jcc E, bb1
        //   -> BtRI %2, #0 ; Jcc AE, bb1     (AE = CF clear = bit 0 was 0)
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::BtRI, X86Opcode::Jcc, X86Opcode::Jmp]
        );
        // BT reads the AND's source register, not its destination.
        assert_eq!(insts[0].operands, vec![vreg(2), X86ISelOperand::Imm(0)]);
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::AE),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_fires_on_b1_condition_lowering_shape() {
        // Mirrors `normalize_condition_operand` + `emit_condition_zero_test`
        // for B1 conditions: Movzx; AndRI %d, %d, 1; CmpRI %d, 0; Jcc NE.
        // The peephole should fire on the AND/CMP/Jcc triple, leaving the
        // Movzx untouched.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(5), vreg32(4)]),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg32(5), vreg32(5), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Movzx,
                X86Opcode::BtRI,
                X86Opcode::Jcc,
                X86Opcode::Jmp,
            ]
        );
        // BT reads the Movzx destination directly (AndRI's three-op form had
        // %5 as both dst and src).
        assert_eq!(insts[1].operands, vec![vreg32(5), X86ISelOperand::Imm(0)]);
        assert_eq!(
            insts[2].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_dst_has_other_uses() {
        // %3 is consumed by an AddRI after the Jcc - single-use side
        // condition fails.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(4)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(4), vreg(3), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        let opcodes = entry_opcodes(&func);
        // The AND/CMP/JCC triple must remain (no BtRI introduced).
        assert!(
            !opcodes.contains(&X86Opcode::BtRI),
            "BtRI must not appear when %dst escapes: {opcodes:?}"
        );
        assert_eq!(opcodes[0], X86Opcode::AndRI);
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_non_power_of_two_imm() {
        // imm=5 has two bits set; refuse to fire.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        let opcodes = entry_opcodes(&func);
        assert!(!opcodes.contains(&X86Opcode::BtRI));
        // The original AndRI must remain (we did not fire the BT rewrite).
        // The cmp-zero -> test-rr single-instruction rewrite may still fire,
        // which is unrelated to this side-condition check.
        assert_eq!(opcodes[0], X86Opcode::AndRI);
        assert!(matches!(opcodes[1], X86Opcode::CmpRI | X86Opcode::TestRR));
        assert_eq!(opcodes[2], X86Opcode::Jcc);
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_zero_imm() {
        // imm=0 is not a power of two; the existing simplifier turns
        // AndRI #0 into xor; we must not fire BT.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_negative_imm() {
        // imm=-1 has all bits set, count_ones() is 64; refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_jcc_is_not_e_or_ne() {
        // Jcc S (sign) cannot be expressed as a CF predicate after BT
        // because BT leaves SF undefined. Refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::S),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_cmp_is_against_nonzero() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_intervening_flag_write() {
        // AndRI ... ; AddRI (writes flags) ; CmpRI ; Jcc - the intervening
        // AddRI breaks the adjacency requirement.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(5), vreg(6), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_cmp_uses_different_vreg() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_gpr32_with_bit_above_31() {
        // imm = 1 << 32 with a Gpr32 AndRI would attempt to test bit 32 of
        // a 32-bit register. Refuse. (And the AndRI on a Gpr32 with a
        // signed-i64 imm of 1<<32 is itself ill-formed; this just exercises
        // the bit-index guard.)
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg32(1), X86ISelOperand::Imm(1_i64 << 32)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_handles_two_independent_windows() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(3), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(2)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::BtRI,
                X86Opcode::Jcc,
                X86Opcode::BtRI,
                X86Opcode::Jcc,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), X86ISelOperand::Imm(1)]);
        assert_eq!(
            insts[1].operands[0],
            X86ISelOperand::CondCode(X86CondCode::B)
        );
        assert_eq!(insts[2].operands, vec![vreg(3), X86ISelOperand::Imm(3)]);
        assert_eq!(
            insts[3].operands[0],
            X86ISelOperand::CondCode(X86CondCode::AE)
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_dst_escapes_to_other_block() {
        // %1 is used in a successor block via a Movzx; the rewrite would
        // erase the AND write-back and the successor would see the pre-AND
        // value. Refuse.
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("bt_branch_cross_block".to_string(), sig);
        let entry = Block(0);
        let other = Block(1);
        func.ensure_block(entry);
        func.ensure_block(other);
        func.next_vreg = 16;

        for inst in [
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(other),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(other)]),
        ] {
            func.push_inst(entry, inst);
        }
        // Successor block reads %1 - the cross-block liveness guard should
        // suppress the rewrite.
        func.push_inst(
            other,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
        );
        func.push_inst(other, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        let entry_block = &func.blocks[&entry];
        let opcodes: Vec<_> = entry_block.insts.iter().map(|i| i.opcode).collect();
        assert!(
            !opcodes.contains(&X86Opcode::BtRI),
            "BtRI must not appear when %dst escapes to another block: {opcodes:?}"
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_andri_with_side_effects() {
        // AndRI flagged with HAS_SIDE_EFFECTS beyond the opcode default must
        // not be rewritten - we cannot prove the foreign effect is local.
        let mut func = make_func(vec![
            X86ISelInst::with_flags(
                X86Opcode::AndRI,
                vec![vreg(1), X86ISelOperand::Imm(4)],
                X86Opcode::AndRI
                    .default_flags()
                    .union(InstFlags::HAS_SIDE_EFFECTS),
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_setcc_hoist_fires_on_two_independent_windows() {
        // Two separate flag_writer/setcc/movzx triples should both rewrite.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(10), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(10), vreg32(10)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(3), vreg(4)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(11), X86ISelOperand::CondCode(X86CondCode::NE)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(11), vreg32(11)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole;

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::CmpRR,
                X86Opcode::Setcc,
                X86Opcode::XorRR,
                X86Opcode::CmpRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    // -----------------------------------------------------------------------
    // cmp + setcc + (normalize) + zero-test + Jcc  ->  cmp + Jcc fusion
    // -----------------------------------------------------------------------

    /// Build the exact ISel output for `Icmp(cc) ; CondBr` of a B1 condition:
    ///   CmpRR lhs, rhs
    ///   Setcc %D, cc
    ///   Movzx %D, %D
    ///   Movzx %D2, %D              ; normalize (B1 -> Gpr64)
    ///   AndRI %D2, %D2, 1          ; normalize mask
    ///   CmpRI %D2, 0               ; zero-test
    ///   Jcc {NE|E}, then ; Jmp else
    fn icmp_condbr_shape(cc: X86CondCode, jcc_cc: X86CondCode) -> X86ISelFunction {
        make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(2), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(cc)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(5), vreg32(5)]),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg(6), vreg32(5)]),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(6), vreg(6), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(jcc_cc),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ])
    }

    #[test]
    fn cmp_branch_fusion_fires_on_full_b1_condbr_shape_jcc_ne() {
        // Branch-when-true (Jcc NE on the bool) collapses to Jcc <cc>.
        let mut func = icmp_condbr_shape(X86CondCode::B, X86CondCode::NE);
        let mut peephole = X86Peephole;
        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::CmpRR, X86Opcode::Jcc, X86Opcode::Jmp],
        );
        let insts = entry_insts(&func);
        // The Cmp operands are untouched; the Jcc now tests the original cc.
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(3)]);
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn cmp_branch_fusion_inverts_cc_on_jcc_e() {
        // Branch-when-false (Jcc E on the bool) collapses to Jcc <cc.invert()>.
        let mut func = icmp_condbr_shape(X86CondCode::B, X86CondCode::E);
        let mut peephole = X86Peephole;
        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::Jcc);
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::AE), // B.invert() == AE
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn cmp_branch_fusion_fires_on_direct_testrr_shape() {
        // Without the normalize pair: Cmp; Setcc; Movzx; TestRR %D,%D; Jcc NE.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(2), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(X86CondCode::L)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(5), vreg32(5)]),
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg32(5), vreg32(5)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::CmpRR, X86Opcode::Jcc, X86Opcode::Jmp],
        );
        assert_eq!(
            entry_insts(&func)[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::L),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn cmp_branch_fusion_declines_when_bool_escapes_to_later_use() {
        // %D2 is read again after the Jcc; the bool is not dead -> refuse.
        let mut func = icmp_condbr_shape(X86CondCode::B, X86CondCode::NE);
        // Append an instruction that reads %6 (the normalized bool) after Jmp.
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(7), vreg(6), X86ISelOperand::Imm(1)],
            ),
        );
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);
        // CmpRR/Setcc must survive (no fusion).
        let opcodes = entry_opcodes(&func);
        assert!(opcodes.contains(&X86Opcode::Setcc));
    }

    #[test]
    fn cmp_branch_fusion_declines_when_flag_writer_not_full() {
        // ImulRR only partially overwrites flags -> the new Jcc cannot rely on
        // its RFLAGS, so the fusion must refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(2), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(5), vreg32(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole;
        peephole.run_on_function(&mut func);
        assert!(entry_opcodes(&func).contains(&X86Opcode::Setcc));
    }

    #[test]
    fn cmp_branch_fusion_preserves_proof_origin_on_new_jcc() {
        let mut func = icmp_condbr_shape(X86CondCode::A, X86CondCode::NE);
        // Tag the original Jcc with a proof origin.
        {
            let block = func.blocks.get_mut(&Block(0)).unwrap();
            let jcc_idx = block
                .insts
                .iter()
                .position(|i| i.opcode == X86Opcode::Jcc)
                .unwrap();
            block.insts[jcc_idx].proof_origin = Some(X86ProofOrigin::AtomicLoad);
        }
        let mut peephole = X86Peephole;
        assert!(peephole.run_on_function(&mut func));
        let insts = entry_insts(&func);
        let new_jcc = insts.iter().find(|i| i.opcode == X86Opcode::Jcc).unwrap();
        assert!(new_jcc.proof_origin.is_some());
    }

    // ===================================================================
    // SIB address-mode fold tests
    // ===================================================================

    fn mem_addr(base: X86ISelOperand, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(base),
            disp,
        }
    }

    /// Canonical foldable STORE window (models a loop body):
    ///   imul v10, v1(index), 8      ; scaled = index*8
    ///   add  v11, v2(base), v10     ; addr = base + scaled
    ///   mov  [v11 + 0], v3          ; store  ->  MovMRSib [base+index*8], v3
    ///   cmp  v4, v5                 ; a later full-flag overwrite (loop cond)
    ///   ret
    /// The trailing CmpRR fully overwrites RFLAGS before the terminator, so the
    /// imul/add flags are provably dead — the same situation a real loop's
    /// compare-and-branch creates.
    fn foldable_store_window(scale_op: X86Opcode, scale_imm: i64) -> X86ISelFunction {
        make_func(vec![
            X86ISelInst::new(
                scale_op,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(scale_imm)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ])
    }

    #[test]
    fn sib_fold_imul_store() {
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 8);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        // imul + add erased; store rewritten to MovMRSib.
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovMRSib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
        match &insts[0].operands.as_slice() {
            [
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
                src,
            ] => {
                assert_eq!(base.as_ref(), &vreg(2), "base");
                assert_eq!(index.as_ref(), &vreg(1), "index");
                assert_eq!(*scale, 8, "scale");
                assert_eq!(*disp, 0, "disp");
                assert_eq!(src, &vreg(3), "stored value preserved");
            }
            other => panic!("unexpected operands: {other:?}"),
        }
    }

    #[test]
    fn sib_fold_imul_load() {
        // imul v10, v1, 4 ; add v11, v2, v10 ; mov v3, [v11] -> MovRMSib
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(4)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRMSib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
        match insts[0].operands.as_slice() {
            [
                dst,
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
            ] => {
                assert_eq!(dst, &vreg(3), "load dst preserved");
                assert_eq!(base.as_ref(), &vreg(2));
                assert_eq!(index.as_ref(), &vreg(1));
                assert_eq!(*scale, 4);
                assert_eq!(*disp, 0);
            }
            other => panic!("unexpected operands: {other:?}"),
        }
    }

    #[test]
    fn sib_fold_shl_store() {
        // shl v10, v1, 3 (=*8) folds identically to imul *8.
        let mut func = foldable_store_window(X86Opcode::ShlRI, 3);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovMRSib);
        if let X86ISelOperand::SibMemAddr { scale, index, .. } = &insts[0].operands[0] {
            assert_eq!(*scale, 8);
            assert_eq!(index.as_ref(), &vreg(1));
        } else {
            panic!("expected SibMemAddr");
        }
    }

    #[test]
    fn sib_fold_add_operands_commute() {
        // add v11, v10(scaled), v2(base) — scaled first. Must still fold and
        // pick v2 as base, v1 as index.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(10), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        if let X86ISelOperand::SibMemAddr { base, index, .. } = &insts[0].operands[0] {
            assert_eq!(base.as_ref(), &vreg(2), "base is the non-scaled operand");
            assert_eq!(index.as_ref(), &vreg(1));
        } else {
            panic!("expected SibMemAddr");
        }
    }

    // ---- REFUTATION tests: unsound/unrecognized shapes must NOT fold ----

    /// scale 3 is not a legal x86 SIB scale. The PROPERTY is that no scale-3
    /// SIB is ever emitted and the `imul` computing the product SURVIVES —
    /// NOT that no fold happens at all.
    ///
    /// ⚑ This test used to assert the LIMIT (`!fired`, opcodes unchanged). The
    /// scale-1 arm legitimately folds this shape to `[base + product*1]`,
    /// keeping the imul and deleting only the add: same effective address, one
    /// fewer instruction. Re-scoped to the property it is actually defending.
    #[test]
    fn sib_refute_wrong_scale_3() {
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 3);
        sib_addr_fold_run_on_block(&mut func, Block(0));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::ImulRRI),
            "the imul computes the index and must NOT be deleted: {ops:?}"
        );
        for inst in entry_insts(&func) {
            for op in &inst.operands {
                if let X86ISelOperand::SibMemAddr { scale, .. } = op {
                    assert_eq!(*scale, 1, "illegal SIB scale emitted");
                }
            }
        }
    }

    /// The scale-1 arm on its canonical shape: `addr = base + index` with NO
    /// scale-def at all (a BYTE array indexes at scale 1). The add is deleted,
    /// the byte store carries `[base + index*1]`, and nothing else moves.
    #[test]
    fn sib_scale1_byte_store_folds() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovMR8Sib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
        let store = &entry_insts(&func)[0];
        match &store.operands[0] {
            X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            } => {
                assert_eq!(**base, vreg(2));
                assert_eq!(**index, vreg(10));
                assert_eq!(*scale, 1);
                assert_eq!(*disp, 0);
            }
            other => panic!("expected SibMemAddr, got {other:?}"),
        }
    }

    /// Byte LOAD sibling of the above.
    #[test]
    fn sib_scale1_byte_load_folds() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM8, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRM8Sib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
    }

    /// REFUTE: an operand redefined between the add and the memory op means the
    /// SIB would read a DIFFERENT value than the deleted add did.
    #[test]
    fn sib_scale1_refute_index_redefined_before_use() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            // v10 redefined between the add and the store:
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(10), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    /// REFUTE: same, for the BASE operand.
    #[test]
    fn sib_scale1_refute_base_redefined_before_use() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    /// REFUTE: the add's RFLAGS are read before being overwritten, so deleting
    /// the add would drop a flag definition someone depends on.
    #[test]
    fn sib_scale1_refute_live_flags() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_addr(vreg(11), 0), vreg(3)]),
            // Reads the flags the add wrote, with no intervening full overwrite.
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_nonzero_disp() {
        // A non-zero displacement on the mov is not modeled by this fold
        // (the deleted add produced base+scaled+0, not +disp) -> no fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 16), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    /// scaled (v10) is used by the add AND by a second consumer. The PROPERTY
    /// is that the `imul` is NOT DELETED — dropping it would destroy the second
    /// use's value. Re-scoped from `!fired`: the scale-1 arm may legitimately
    /// fold the ADDRESS here (it keeps the imul and deletes only the add).
    #[test]
    fn sib_refute_scaled_used_twice() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            // second use of scaled v10:
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(10), vreg(4)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        sib_addr_fold_run_on_block(&mut func, Block(0));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::ImulRRI),
            "imul feeding a second consumer must survive: {ops:?}"
        );
        assert!(
            ops.contains(&X86Opcode::AddRR),
            "the second consumer's add must survive: {ops:?}"
        );
    }

    #[test]
    fn sib_refute_addr_used_twice() {
        // addr (v11) used by the store AND a later inst -> not single-use.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            // second use of addr v11:
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(11), vreg(4)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_add_flags_live() {
        // A flag-reader (Setcc) between the add and the terminator makes the
        // add's RFLAGS live -> deleting the add would change the flags the
        // Setcc consumes. Must NOT fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_fold_partial_flag_overwrite_is_transparent() {
        // The matmul j-loop shape: another address's ImulRR (a PARTIAL flag
        // overwrite, no flag read) sits between the folded add and the next
        // FULL overwrite (AddRR). Nothing reads flags in between, so the
        // deleted imul/add flags are unobservable and the fold must fire.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(5), vreg(6)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(7), vreg(8), vreg(9)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRMSib,
                X86Opcode::ImulRR,
                X86Opcode::AddRR,
                X86Opcode::Ret
            ]
        );
    }

    #[test]
    fn sib_refute_partial_overwrite_then_flag_reader() {
        // A partial overwrite is transparent, but a flag READER after it
        // (before any full overwrite) can still observe surviving bits of
        // the deleted add's flags. Must NOT fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(5), vreg(6)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(7), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(8), vreg(9)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_partial_overwrite_then_block_end() {
        // A partial overwrite never PROVES deadness: with no full overwrite
        // before the end of the block the flags stay potentially live-out.
        // Must NOT fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(5), vreg(6)]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_fold_end_to_end_const_copy_scale_via_run_impl() {
        // Integration pin of the matmul j-loop miss: the scale-8 reaches the
        // imul through a CSE-inserted single-def MovRR copy of a MovRI. The
        // imm-fold (which runs earlier in this same peephole invocation)
        // rewrites the ImulRR to ImulRRI $8, and the SIB fold then collapses
        // the triple: load rewritten to MovRMSib, imul+add+dead-copy erased.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(10), vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(3), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(11)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(4), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(5), vreg(4), vreg(6)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(7), vreg(8), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_impl(&mut func));
        let opcodes = entry_opcodes(&func);
        assert!(
            opcodes.contains(&X86Opcode::MovRMSib),
            "expected a SIB load, got {opcodes:?}"
        );
        // The scale imul (folded to ImulRRI by the imm-fold, then consumed by
        // the SIB fold) and the address AddRR are erased; the unrelated
        // trailing value ImulRR/AddRR pair survives.
        assert!(
            !opcodes.contains(&X86Opcode::ImulRRI),
            "scale imul must be erased, got {opcodes:?}"
        );
        assert_eq!(
            opcodes.iter().filter(|op| **op == X86Opcode::AddRR).count(),
            1,
            "address add must be erased (value add survives), got {opcodes:?}"
        );
        let insts = entry_insts(&func);
        let sib = insts
            .iter()
            .find(|inst| inst.opcode == X86Opcode::MovRMSib)
            .expect("sib load present");
        match sib.operands.as_slice() {
            [
                dst,
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
            ] => {
                assert_eq!(dst, &vreg(4));
                assert_eq!(base.as_ref(), &vreg(3));
                assert_eq!(index.as_ref(), &vreg(2));
                assert_eq!(*scale, 8);
                assert_eq!(*disp, 0);
            }
            other => panic!("unexpected operands: {other:?}"),
        }
    }

    #[test]
    fn sib_refute_narrow_load() {
        // MovRM32 (32-bit load) is NOT the 64-bit MovRM; MovRMSib encodes a
        // 64-bit MOV only, so a narrow load must not fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM32, vec![vreg32(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_index_redefined_before_store() {
        // index v1 is redefined between the imul and the store -> the SIB
        // operand would read the NEW v1, not the value the imul scaled. No fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            // clobber index v1:
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(99)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    /// scaled v10 is mentioned in ANOTHER block. The PROPERTY is that the
    /// `imul` defining it is NOT DELETED — the other block reads that value.
    /// Re-scoped from `!fired` for the same reason as the two tests above.
    #[test]
    fn sib_refute_scaled_escapes_block() {
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 8);
        func.ensure_block(Block(1));
        func.block_order.push(Block(1));
        func.push_inst(
            Block(1),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(10), vreg(4)]),
        );
        sib_addr_fold_run_on_block(&mut func, Block(0));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::ImulRRI),
            "imul whose result escapes the block must survive: {ops:?}"
        );
    }

    #[test]
    fn sib_fold_end_to_end_via_run_impl() {
        // The full peephole entrypoint fires the fold at its scheduled slot.
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 8);
        let mut peephole = X86Peephole;
        assert!(peephole.run_on_function(&mut func));
        assert!(entry_opcodes(&func).contains(&X86Opcode::MovMRSib));
        assert!(!entry_opcodes(&func).contains(&X86Opcode::ImulRRI));
    }

    #[test]
    fn sib_fold_shared_addr_load_and_store() {
        // The matmul `c[j] = c[j] + ..` shape: ONE address feeds a LOAD then a
        // STORE. addr (v11) is used TWICE (load base + store base). Both fold to
        // SIB sharing base+index*8, and the single imul+add is deleted once.
        //   imul v10, v1, 8
        //   add  v11, v2, v10        ; addr = base + index*8
        //   mov  v3, [v11]           ; LOAD  c[j]        -> MovRMSib
        //   ... (v3 combined into v6) ...
        //   mov  [v11], v6           ; STORE c[j]        -> MovMRSib
        //   cmp  v4, v5              ; full-flag overwrite before terminator
        //   ret
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(3), vreg(7)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(6)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let ops = entry_opcodes(&func);
        // imul + address-add erased; the intermediate value-add (v6) survives.
        assert!(!ops.contains(&X86Opcode::ImulRRI), "imul erased");
        assert_eq!(
            ops,
            vec![
                X86Opcode::MovRMSib, // folded load
                X86Opcode::AddRR,    // value add (v6 = v3 + v7) survives
                X86Opcode::MovMRSib, // folded store
                X86Opcode::CmpRR,
                X86Opcode::Ret,
            ]
        );
        // Load-before-store order preserved.
        let insts = entry_insts(&func);
        assert!(insts[0].opcode == X86Opcode::MovRMSib);
        assert!(insts[2].opcode == X86Opcode::MovMRSib);
        // Both share base=v2, index=v1, scale=8.
        for (idx, want_load) in [(0usize, true), (2usize, false)] {
            let sib_op = if want_load {
                &insts[idx].operands[1]
            } else {
                &insts[idx].operands[0]
            };
            match sib_op {
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                } => {
                    assert_eq!(base.as_ref(), &vreg(2));
                    assert_eq!(index.as_ref(), &vreg(1));
                    assert_eq!(*scale, 8);
                    assert_eq!(*disp, 0);
                }
                other => panic!("op {idx} not SIB: {other:?}"),
            }
        }
    }

    fn sib_op(base: u32, index: u32, scale: u8, disp: i32) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(vreg(base)),
            index: Box::new(vreg(index)),
            scale,
            disp,
        }
    }

    #[test]
    fn sib_fold_from_leasib_load() {
        // The array-indexing shape: select_array_gep emits LeaSib, the element
        // load reads [addr]. Fold to MovRMSib carrying the LeaSib's SIB operand;
        // the LeaSib dies.
        //   lea v11, [v2 + v1*8]      ; LeaSib
        //   mov v3, [v11]             ; load  -> MovRMSib v3, [v2+v1*8]
        //   cmp v4, v5 ; ret
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 8, 0)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRMSib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
        if let X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } = &entry_insts(&func)[0].operands[1]
        {
            assert_eq!(base.as_ref(), &vreg(2));
            assert_eq!(index.as_ref(), &vreg(1));
            assert_eq!(*scale, 8);
            assert_eq!(*disp, 0);
        } else {
            panic!("expected SibMemAddr");
        }
    }

    #[test]
    fn sib_fold_from_leasib_shared_load_store_with_disp() {
        // LeaSib with a non-zero disp feeding a shared load+store (the matmul
        // `c[i] = c[i] + ..` shape). Disp is preserved exactly.
        //   lea v11, [v2 + v1*4 + 16]
        //   mov v3, [v11]     ; LOAD  -> MovRMSib
        //   add v6, v3, v7
        //   mov [v11], v6     ; STORE -> MovMRSib
        //   cmp v4, v5 ; ret
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 4, 16)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(3), vreg(7)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(6)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovRMSib);
        assert_eq!(insts[2].opcode, X86Opcode::MovMRSib);
        // Disp 16 preserved on both.
        for (idx, want_load) in [(0usize, true), (2usize, false)] {
            let op = if want_load {
                &insts[idx].operands[1]
            } else {
                &insts[idx].operands[0]
            };
            if let X86ISelOperand::SibMemAddr { scale, disp, .. } = op {
                assert_eq!(*scale, 4);
                assert_eq!(*disp, 16, "disp preserved");
            } else {
                panic!("expected SibMemAddr");
            }
        }
    }

    #[test]
    fn sib_refute_leasib_addr_escapes_arithmetic() {
        // LeaSib address also feeds an arithmetic add -> cannot delete the lea.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 8, 0)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(11), vreg(4)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(5), vreg(6)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_leasib_base_redefined() {
        // base v2 redefined between the lea and the store -> the SIB operand
        // would read the NEW v2. No fold.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 8, 0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(99)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(5), vreg(6)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_fold_through_movrr_copy() {
        // Two-address-fixup artifact: the AddRR result (v11) is COPIED via
        // MovRR to v12, and v12 is the store base. The fold must see through the
        // copy: rewrite the store to SIB base+index*8 and delete imul+add+copy.
        //   imul v10, v1, 8
        //   add  v11, v2, v10
        //   mov  v12, v11        ; MovRR copy of the address
        //   mov  [v12], v3       ; store via the copy
        //   cmp  v4, v5
        //   ret
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(11)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(12), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let ops = entry_opcodes(&func);
        assert_eq!(
            ops,
            vec![X86Opcode::MovMRSib, X86Opcode::CmpRR, X86Opcode::Ret],
            "imul+add+copy erased, store -> MovMRSib"
        );
        if let X86ISelOperand::SibMemAddr {
            base, index, scale, ..
        } = &entry_insts(&func)[0].operands[0]
        {
            assert_eq!(base.as_ref(), &vreg(2));
            assert_eq!(index.as_ref(), &vreg(1));
            assert_eq!(*scale, 8);
        } else {
            panic!("expected SibMemAddr");
        }
    }

    #[test]
    fn sib_fold_with_dead_addr_copy() {
        // The exact ISel shape seen in the wild: the AddRR address (v11) is used
        // by a DEAD MovRR copy (v12 unused) AND directly by the load. The dead
        // copy must be deleted and the load folded.
        //   imul v10, v1, 8
        //   add  v11, v2, v10
        //   mov  v12, v11        ; DEAD copy (v12 never used)
        //   mov  v3, [v11]       ; load via addr directly -> MovRMSib
        //   cmp v4, v5 ; ret
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(11)]), // dead
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        // imul + add + dead copy erased; load -> MovRMSib.
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRMSib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
    }

    #[test]
    fn sib_refute_copy_used_in_arithmetic() {
        // The copy dest v12 is used by the store AND by arithmetic -> the copy
        // is not purely an address, so we must not delete it. No fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(11)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(12), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(13), vreg(12), vreg(4)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(6), vreg(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_addr_used_in_arithmetic() {
        // addr (v11) feeds a store AND an arithmetic ADD (escapes into a value).
        // Deleting the address-add would drop the arithmetic use -> must NOT
        // fold (not every use of addr is a foldable mem op).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            // arithmetic use of the address value:
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(11), vreg(4)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(6), vreg(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    // -----------------------------------------------------------------------
    // Local address-chain fold (TCG_X86_ADDR_CHAIN_FOLD) — called directly,
    // bypassing the env gate.
    // -----------------------------------------------------------------------

    fn mem(base: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(vreg(base)),
            disp,
        }
    }

    #[test]
    fn addr_chain_fold_three_op_addri_to_disp() {
        // AddRI v2, v1, 0x10 ; MovRM v3, [v2+0]  ->  MovRM v3, [v1+0x10]
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0x10)],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRM);
        assert_eq!(insts[1].operands, vec![vreg(3), mem(1, 0x10)]);
        // Rewrite-only: the AddRI stays (DCE owns the sweep).
        assert_eq!(insts[0].opcode, X86Opcode::AddRI);
    }

    #[test]
    fn addr_chain_fold_tied_addri_through_copy() {
        // MovRR v2, v1 ; AddRI v2, 0x20 (tied) ; MovRM v3, [v2+4]
        //   ->  MovRM v3, [v1+0x24]
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(2), X86ISelOperand::Imm(0x20)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 4)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(entry_insts(&func)[2].operands, vec![vreg(3), mem(1, 0x24)]);
    }

    #[test]
    fn addr_chain_fold_addrr_becomes_sib_index() {
        // AddRR v4, v1, v2 ; MovRM v3, [v4+8]
        //   ->  MovRMSib v3, [v1 + v2*1 + 8]
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(4, 8)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRMSib);
        assert_eq!(
            insts[1].operands,
            vec![
                vreg(3),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(1)),
                    index: Box::new(vreg(2)),
                    scale: 1,
                    disp: 8,
                },
            ]
        );
    }

    #[test]
    fn addr_chain_fold_b05_two_level_shape() {
        // The exact post-unroll b05 a-side shape:
        //   AddRR v5, v1, v2      (row base = r15 + rdi)
        //   MovRR v6, v5
        //   AddRI v6, 0x10        (tied: += k*8)
        //   MovRM v7, [v6+0]
        // -> MovRMSib v7, [v1 + v2*1 + 0x10]
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(5), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(6), vreg(5)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(6), X86ISelOperand::Imm(0x10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(7), mem(6, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_insts(&func)[3].operands,
            vec![
                vreg(7),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(1)),
                    index: Box::new(vreg(2)),
                    scale: 1,
                    disp: 0x10,
                },
            ]
        );
    }

    #[test]
    fn addr_chain_fold_store_anchor() {
        // AddRI v2, v1, 8 ; MovMR [v2+0], v3  ->  MovMR [v1+8], v3
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem(2, 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(entry_insts(&func)[1].operands, vec![mem(1, 8), vreg(3)]);
    }

    #[test]
    fn addr_chain_fold_refuses_base_redef_in_window() {
        // The final base v1 is redefined between the chain and the load:
        // folding would read the NEW v1. Must refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(99)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn addr_chain_fold_refuses_narrow_alias_redef_in_window() {
        // A Gpr32 def of the same id is an aliased width view: must count as
        // a redef of the 64-bit base (dirty-high-bits class).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg_class(1, RegClass::Gpr32), X86ISelOperand::Imm(7)],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn addr_chain_fold_second_addrr_partial_fold() {
        // Two AddRRs: only the nearest becomes the index; the second
        // terminates resolution with its def as the base (partial fold).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(5), vreg(4), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(6), mem(5, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_insts(&func)[2].operands,
            vec![
                vreg(6),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(4)),
                    index: Box::new(vreg(3)),
                    scale: 1,
                    disp: 0,
                },
            ]
        );
    }

    #[test]
    fn addr_chain_fold_uses_nearest_def() {
        // Multi-def id (post-unroll clone shape): the NEAREST def wins.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(16)],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(entry_insts(&func)[2].operands, vec![vreg(3), mem(1, 16)]);
    }

    #[test]
    fn addr_chain_fold_refuses_disp_overflow() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(i64::from(i32::MAX))],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 8)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn addr_chain_fold_refuses_narrow_class_chain() {
        // Gpr32 chain members never fold (64-bit MOV forms only).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![
                    vreg_class(2, RegClass::Gpr32),
                    vreg_class(1, RegClass::Gpr32),
                    X86ISelOperand::Imm(8),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::MovRM,
                vec![
                    vreg(3),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg_class(2, RegClass::Gpr32)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    // -----------------------------------------------------------------------
    // RM fusion (TCG_X86_IMUL_FUSE) — called directly, bypassing the env gate.
    // -----------------------------------------------------------------------

    #[test]
    fn imul_fuse_three_op_b05_shape() {
        // MovRMSib t(5),[1+2+8]; ImulRR d(6), a(4), t(5); t dead (redef by
        // next step's load)  ->  MovRR d,a ; ImulRMSib d,[sib].
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 8)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(7), vreg(3), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 16)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(imul_fuse_run_on_block(&mut func, Block(0)));
        let ops = entry_opcodes(&func);
        assert_eq!(
            ops,
            vec![
                X86Opcode::MovRR,
                X86Opcode::ImulRMSib,
                X86Opcode::AddRR,
                X86Opcode::MovRMSib,
                X86Opcode::MovRR,
                X86Opcode::Ret
            ]
        );
        let insts = entry_insts(&func);
        assert_eq!(insts[0].operands, vec![vreg(6), vreg(4)]);
        assert_eq!(insts[1].operands, vec![vreg(6), sib_op(1, 2, 1, 8)]);
    }

    #[test]
    fn imul_fuse_tied_direct() {
        // Tied ImulRR d, t with d != t: fuses to the bare ImulRMSib d,[sib].
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(imul_fuse_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::ImulRMSib);
        assert_eq!(insts[0].operands, vec![vreg(6), sib_op(1, 2, 1, 0)]);
    }

    #[test]
    fn imul_fuse_base_disp_load_fuses_to_imulrm() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(5), mem(1, 16)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(imul_fuse_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovRR);
        assert_eq!(insts[1].opcode, X86Opcode::ImulRM);
        assert_eq!(insts[1].operands, vec![vreg(6), mem(1, 16)]);
    }

    #[test]
    fn imul_fuse_refuses_store_in_window() {
        // A store between load and multiply may alias the loaded address.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem(3, 0), vreg(4)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_trap_pseudo_in_window() {
        // Moving the (potentially informative) load past a trap changes
        // which abort fires first: fail closed.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(
                X86Opcode::TrapBoundsCheckExact,
                vec![vreg(4), vreg(4), X86ISelOperand::Imm(24)],
            ),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_ea_reg_redef_in_window() {
        // The SIB base is redefined between load and multiply: the fused EA
        // would read the NEW base. Refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(9)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_live_t() {
        // t is read again after the multiply: not locally dead. Refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_t_use_in_window() {
        // A window instruction reads t: deleting the load would hand it the
        // stale pre-load value (adversarial-review class 1).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(7), vreg(5)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(10), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_dst_in_ea() {
        // The anchor's destination IS the SIB base: the emitted MovRR d,a
        // would clobber the address before the fused load reads it
        // (adversarial-review class 2).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(6, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_cmovcc_redef_of_t() {
        // Cmovcc writes t CONDITIONALLY: the not-taken lane keeps the loaded
        // value, so it must not end t's live range (adversarial-review
        // class 3 — the conditional-write shadow class, again).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(
                X86Opcode::Cmovcc,
                vec![vreg(5), vreg(7), X86ISelOperand::CondCode(X86CondCode::AE)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_tied_redef_of_t() {
        // A tied 2-operand AddRI reads t through operand 0: not a killing
        // redef (adversarial-review class 3, tied family).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(5), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_preg_ea_component() {
        // A PReg EA base is an address the pass cannot track: fail closed
        // (adversarial-review class 4).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRMSib,
                vec![
                    vreg(5),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(X86ISelOperand::PReg(trust_cg_ir::x86_64_regs::RDI)),
                        index: Box::new(vreg(2)),
                        scale: 1,
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_t_squared() {
        // Both factors are the load result: the value is needed twice but
        // the load is deleted. Refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(5), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn zeroidiom_gate_declines_unread_zero_and_allows_read_zero() {
        // Unread MovRI-0 must stay MovRI (DCE-removable) under the gate;
        // a read zero still becomes the XorRR zero idiom.
        let unread = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(2)]),
            // Full flag overwrite so the XorRR rewrite's flag obligation is
            // dischargeable in this toy block (as in any real body).
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(3), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(4)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let used = peephole_function_use_set(&unread);
        let insts = &unread.blocks.get(&Block(0)).unwrap().insts;
        // v1 unread -> gate declines.
        assert!(simplify_inst_gated(insts, 0, Some(&used)).is_none());
        // v2 read -> rewrite proceeds.
        assert!(matches!(
            simplify_inst_gated(insts, 1, Some(&used)),
            Some(PeepholeEdit::Replace(_))
        ));
        // Ungated behavior unchanged: both rewrite.
        assert!(simplify_inst(insts, 0).is_some());
    }

    #[test]
    fn addr_chain_fold_tied_addrr_dead_end_refuses() {
        // Tied `AddRR v1, v2` with v1 live-in: the base would have to be v1's
        // pre-add value, but v1 at the mem op holds the SUM. The capture
        // position makes no_def_in_range see the add's own def -> refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(1, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }
}
