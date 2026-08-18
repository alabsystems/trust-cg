// trust-cg-opt - AArch64 scalar post-index formation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fold a loop's per-iteration address recompute into a POST-INDEXED load.
//!
//! ```text
//! header:  lsl  t,   V, #2                 header:  ldr  D, [P], #4
//!          add  idx, t, inv, lsl #11   =>
//!          ldr  D, [base, idx]
//! latch:   add  V, V, #1                   latch:   add  V, V, #1
//! ```
//!
//! trust-cg emitted **zero** post-indexed scalar loads anywhere before this
//! pass: `LdrPostIndex` existed and was fully encoded, but every producer was a
//! NEON/specialised pass (`neon_map`, `neon_stencil`, `neon_bytesum`,
//! `neon_find`, `neon_array`, `neon_condstore`, `swap_range_guard`). clang emits
//! 11 in Stanford/Puzzle alone and 4 in Shootout-hash.
//!
//! # Why this is a separate pass from [`crate::ptr_iv_sr`]
//!
//! `ptr_iv_sr` walks the same 2-D shape but its soundness argument pairs the
//! pointer update with the IV's SINGLE latch `MovR`, so it demands a body of
//! exactly `{header}` or `{header, latch}` with EXACTLY ONE back-edge. Puzzle's
//! hot loop has TWO back-edges (`if (p[i][k]) if (puzzl[j+k])` makes the body a
//! diamond), so that pass can never fire there — verified by instrumenting it.
//! It also emits `[P, #0]` plus a separate latch `add`/`mov`, which is one real
//! instruction saved, not two.
//!
//! Post-index needs a STRICTLY WEAKER condition, because the pointer advances
//! when the LOAD executes rather than when the IV does:
//!
//! > the load is in the loop HEADER, and the IV advances exactly once per
//! > header visit.
//!
//! A natural loop's header executes exactly once per iteration by definition,
//! and a basic block has no internal control flow, so an unconditional load in
//! the header advances `P` exactly once per iteration. The IV's in-loop def is
//! required to be a single `AddRI V, V, #step` in the body, which likewise runs
//! once per iteration. Both counters therefore step together and `P == base +
//! (V << s)` is preserved — including across the FIRST iteration, which reaches
//! the header from the preheader without executing the IV update, because `P0`
//! is seeded from `V`'s preheader value.
//!
//! # Fail-closed constraints (all must hold)
//!
//! 1. Innermost natural loop with a real preheader.
//! 2. Access is `LdrRO dst, base, idx` — the PLAIN 3-operand `[Xn, Xm]` form
//!    only. The packed-extend forms carry `SXTW`/`UXTW`, where a sign/zero
//!    extend of a loop-variant 32-bit index does not commute with the 64-bit
//!    step; that is the historic matrix-multiply miscompile and is never
//!    touched here.
//! 3. Index chain is exactly `LslRI t, V, #s` optionally followed by
//!    `AddRR idx, t, inv` / `AddRRShift idx, t, inv, #k`, every member
//!    whole-function single-def, in the header, before its user, and used
//!    exactly ONCE (so deleting it is safe).
//! 4. The transfer width implied by `dst`'s class equals `1 << s`, i.e. the
//!    pointer advance is exactly the element size.
//! 5. `V` is a `Gpr64` with EXACTLY two whole-function defs: an init whose
//!    block dominates the preheader, and `AddRI V, V, #1` in the loop body.
//!    A step of 1 is required so the byte advance is exactly `1 << s`.
//! 6. `base` and `inv` are whole-function single-def `Gpr64` (never SP) defined
//!    outside the loop, with their defs dominating the preheader.
//! 7. The loaded value must not be `V`, `base` or `inv` (no self-clobber), and
//!    `dst` must differ from the pointer carrier.
//!
//! Anything unrecognised bails. A missed fold costs speed; a wrong one
//! miscompiles.
//!
//! # Measured
//!
//! Validated by binary patch BEFORE being written, on the actually-executing
//! copy of the loop (`_Trial+0x12c`; note `_Fit` is inlined and has zero call
//! sites): Stanford/Puzzle 636.58M -> 531.44M instructions (-105.13M, against
//! -107.78M predicted from 2/iter x 53,890,200), cycles 0.9670 min / 0.9754
//! trimmed median, 1.2839 -> 1.2416 vs clang -O3 — 14.9% of that program's gap.
//! The marginal price of these instructions is 0.0443 cyc, NOT Puzzle's
//! program-average 0.1326; pricing at the average overstates this lever 3x.
//!
//! # Status: correct, and provably out of reach from the opt pipeline
//!
//! The recognizer now admits BOTH register-offset forms and still folds nothing
//! on Stanford/Puzzle. `TCG_DUMP_POSTIDX=1` gives the reason without ambiguity:
//!
//! ```text
//! 4 bail: idx chain: defs=2 same_block=false reads=3
//! ```
//!
//! The index operand has TWO definitions, lives in a DIFFERENT block from the
//! load, and is read THREE times. That is a loop-carried register, not a
//! freshly-computed `lsl`+`add` chain — so there is nothing to delete and
//! refusing is correct. Combined with the block dump (the other candidate loads
//! sit on diamond arms, where a writeback would desynchronise), this closes the
//! question: **the shape the binary patch exploited is created AFTER the opt
//! pipeline.** No slot reachable from here can see it.
//!
//! ⇒ Capturing the measured 14.9% requires a peephole over the post-layout /
//! post-RA form, not a mid-end pass. This module is the recognizer and the
//! soundness argument for that future peephole; its refusals are all pinned.
//!
//! ## Where that peephole goes, and what it can reuse
//!
//! Slot: `trust-cg-codegen/src/pipeline.rs`, the post-RA region — beside
//! `elide_redundant_spill_slot_reloads` (`:16080`) and
//! `crate::branch_forward::forward_post_ra_branches` (`:16101`). Both already
//! run on the post-RA `MachFunction` with PHYSICAL registers and the final block
//! layout, which is precisely where the shape exists.
//!
//! Pattern to match there (the emitted Puzzle loop, `_Trial+0x12c`):
//! ```text
//!   latch: add x2,x2,#1 ; cmp x2,x3 ; b.eq exit
//!   body:  lsl x1,x2,#2 ; add x0,x1,x20,lsl#11 ; ldr w1,[x22,x0] ; cbz w1,latch
//!     =>
//!   pre:   add xP,x22,x20,lsl#11
//!   body:  ldr w1,[xP],#4
//! ```
//!
//! The one thing this module does NOT solve for that setting: registers are
//! physical, so the pointer cannot be a fresh vreg — the peephole must prove its
//! chosen register is dead across the loop. `frame.rs:2299-2348` already does
//! exactly that and is the template: pick a scratch, test `scratch_live_after`
//! against the block live-out, and FAIL CLOSED when the IP scratch would be
//! clobbered. The hand patch used `x16` and verified it dead by inspection.
//!
//! Both remaining ingredients are already available at that slot, so nothing
//! has to be ported:
//!   * LOOP STRUCTURE — `trust-cg-codegen/src/loop_align.rs:782 backedge_spans`
//!     derives backward-edge targets and spans from the FINAL layout, which is
//!     the CFG this fold needs (and the one the mid-end cannot see).
//!   * LIVENESS — `frame.rs:1149 scratch_live_after`.
//!   * `trust-cg-codegen` already depends on `trust-cg-opt` (Cargo.toml:48), so
//!     the admission predicates below can be called directly rather than copied.
//!
//! # Kill switch
//!
//! `TCG_NO_POST_INDEX` (any value) — [`run`] becomes a no-op.

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    RegClass, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Packed extend operand value (`(option << 1) | S`) for the LSL option with no
/// scaling, matching the `LdrRO` encoder contract in trust-cg-codegen.
const PACKED_LSL_UNSHIFTED: i64 = 0b0110;

/// Packed extend for LSL with the shift implied by the transfer class: the
/// hardware scales the index by the element size.
const PACKED_LSL_SHIFTED: i64 = 0b0111;

/// Scalar post-index formation pass.
pub struct PostIndexForm;

fn pass_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_POST_INDEX").is_none()
}

fn pass_id() -> PassId {
    PassId::new("post-index")
}

impl MachinePass for PostIndexForm {
    fn name(&self) -> &str {
        "post-index"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_post_index(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_post_index(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_post_index(func, Some(provenance))
    }
}

/// Where a vreg is defined: (block, index in block, inst).
#[derive(Clone, Copy)]
struct DefSite {
    block: BlockId,
    pos: usize,
    inst: InstId,
}

/// Transfer width in bytes implied by a destination register class.
fn transfer_bytes(v: VReg) -> Option<i64> {
    match v.class {
        RegClass::Gpr32 => Some(4),
        RegClass::Gpr64 => Some(8),
        _ => None,
    }
}

fn collect_defs(func: &MachFunction) -> (HashMap<VReg, Vec<DefSite>>, HashMap<VReg, u32>) {
    let mut defs: HashMap<VReg, Vec<DefSite>> = HashMap::new();
    let mut reads: HashMap<VReg, u32> = HashMap::new();
    for &block in &func.block_order {
        for (pos, &inst_id) in func.block(block).insts.iter().enumerate() {
            let inst = func.inst(inst_id);
            let opcode = inst.opcode;
            let n = inst.operands.len();
            let mut is_def = vec![false; n];
            crate::effects::aarch64_for_each_def_position(opcode, n, |i| {
                if i < n {
                    is_def[i] = true;
                }
            });
            for (i, op) in inst.operands.iter().enumerate() {
                let MachOperand::VReg(v) = op else { continue };
                if is_def[i] {
                    defs.entry(*v).or_default().push(DefSite {
                        block,
                        pos,
                        inst: inst_id,
                    });
                } else {
                    *reads.entry(*v).or_default() += 1;
                }
            }
        }
    }
    (defs, reads)
}

/// A recognised fold: what to delete, and what to seed the pointer from.
struct Plan {
    load_inst: InstId,
    dst: VReg,
    base: VReg,
    /// `LslRI t, V, #s` — absent in the hardware-scaled form.
    lsl_inst: Option<InstId>,
    iv: VReg,
    shift: i64,
    /// optional `AddRR/AddRRShift idx, t, inv[, #k]`
    add_inst: Option<InstId>,
    inv: Option<(VReg, i64)>,
    elem: i64,
}

fn run_post_index(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    if !pass_enabled() {
        return false;
    }
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    let (defs, reads) = collect_defs(func);

    let single_outside = |v: VReg, pre: BlockId, lp: &std::collections::HashSet<BlockId>| -> bool {
        match defs.get(&v) {
            Some(d) if d.len() == 1 => !lp.contains(&d[0].block) && dom.dominates(d[0].block, pre),
            _ => false,
        }
    };

    let dbg = crate::env_lock::var_os("TCG_DUMP_POSTIDX").is_some();
    macro_rules! bail {
        ($w:expr) => {{
            if dbg {
                eprintln!("POSTIDX bail: {}", $w);
            }
            continue;
        }};
    }
    let mut plans: Vec<Plan> = Vec::new();

    for lp in loops.all_loops() {
        let Some(pre) = lp.preheader else { continue };
        let header = lp.header;
        // (1) innermost only: no nested loop whose body is a strict subset.
        if loops
            .all_loops()
            .any(|o| o.header != header && lp.body.contains(&o.header))
        {
            continue;
        }

        // Blocks that execute EXACTLY ONCE per iteration: dominated by the
        // header and dominating every back-edge source. In a rotated loop the
        // header is the trip-test block and the load sits in the fall-through
        // body block, so restricting to the header alone misses the real shape
        // (it missed Stanford/Puzzle entirely).
        let latches: Vec<BlockId> = lp
            .body
            .iter()
            .copied()
            .filter(|&b| func.block(b).succs.contains(&header))
            .collect();
        if latches.is_empty() {
            continue;
        }
        let once_per_iter: Vec<BlockId> = lp
            .body
            .iter()
            .copied()
            .filter(|&b| dom.dominates(header, b) && latches.iter().all(|&m| dom.dominates(b, m)))
            .collect();

        if dbg {
            let ldr_blocks: Vec<_> = lp
                .body
                .iter()
                .filter(|&&b| {
                    func.block(b).insts.iter().any(|&i| {
                        matches!(
                            func.inst(i).opcode,
                            AArch64Opcode::LdrRO | AArch64Opcode::LdrRI
                        )
                    })
                })
                .collect();
            let edges: Vec<String> = lp
                .body
                .iter()
                .map(|&b| format!("{:?}->{:?}", b, func.block(b).succs))
                .collect();
            eprintln!(
                "POSTIDX loop hdr={:?} latches={:?} once={:?} ldr_in={:?} edges={:?}",
                header, latches, once_per_iter, ldr_blocks, edges
            );
        }
        for &host in &once_per_iter {
            let hinsts = func.block(host).insts.clone();
            for (lpos, &load_id) in hinsts.iter().enumerate() {
                let load = func.inst(load_id).clone();
                // (2) plain 3-operand LdrRO only — never the packed-extend forms.
                // Accept the plain 3-operand `[Xn, Xm]` form AND the 4-operand
                // packed-extend form when the extend is LSL-UNSHIFTED (0b0110) --
                // that is how an unscaled register offset is normally represented,
                // and it prints as `[Xn, Xm]`. The SHIFTED LSL variant (0b0111)
                // scales the index by the transfer size, so its chain carries no
                // explicit `lsl` and the arithmetic below would be wrong; SXTW/UXTW
                // are the historic matrix-multiply miscompile. Both are refused.
                if load.opcode != AArch64Opcode::LdrRO {
                    if dbg && format!("{:?}", load.opcode).contains("Ldr") {
                        eprintln!(
                            "POSTIDX saw load opcode {:?} ops={}",
                            load.opcode,
                            load.operands.len()
                        );
                    }
                    continue;
                }
                let scaled = match load.operands.len() {
                    3 => false,
                    4 => match load.operands.get(3) {
                        Some(MachOperand::Imm(x)) if *x == PACKED_LSL_UNSHIFTED => false,
                        Some(MachOperand::Imm(x)) if *x == PACKED_LSL_SHIFTED => true,
                        other => bail!(format!("LdrRO extend {:?} is not an LSL form", other)),
                    },
                    _ => bail!("LdrRO arity"),
                };
                let (
                    Some(MachOperand::VReg(dst)),
                    Some(MachOperand::VReg(base)),
                    Some(MachOperand::VReg(idx)),
                ) = (
                    load.operands.first(),
                    load.operands.get(1),
                    load.operands.get(2),
                )
                else {
                    continue;
                };
                let (dst, base, idx) = (*dst, *base, *idx);
                let Some(elem) = transfer_bytes(dst) else {
                    bail!("dst class");
                };
                if base.class != RegClass::Gpr64 || idx.class != RegClass::Gpr64 {
                    continue;
                }

                // (3) walk the index chain back: optional Add*, then LslRI.
                let chain_def = |v: VReg| -> Option<DefSite> {
                    let d = defs.get(&v)?;
                    if d.len() != 1 || d[0].block != host || d[0].pos >= lpos {
                        return None;
                    }
                    // used exactly once (by its consumer in this chain)
                    if reads.get(&v).copied().unwrap_or(0) != 1 {
                        return None;
                    }
                    Some(d[0])
                };
                let Some(idx_def) = chain_def(idx) else {
                    let d = defs.get(&idx);
                    bail!(format!(
                        "idx chain: defs={} same_block={:?} reads={}",
                        d.map(|v| v.len()).unwrap_or(0),
                        d.and_then(|v| v.first()).map(|x| x.block == host),
                        reads.get(&idx).copied().unwrap_or(0)
                    ));
                };
                let idx_inst = func.inst(idx_def.inst).clone();
                let (lsl_carrier, add_inst, inv) = match idx_inst.opcode {
                    AArch64Opcode::LslRI => (idx, None, None),
                    AArch64Opcode::AddRR if idx_inst.operands.len() == 3 => {
                        let (Some(MachOperand::VReg(t)), Some(MachOperand::VReg(iv2))) =
                            (idx_inst.operands.get(1), idx_inst.operands.get(2))
                        else {
                            continue;
                        };
                        (*t, Some(idx_def.inst), Some((*iv2, 0)))
                    }
                    AArch64Opcode::AddRRShift if idx_inst.operands.len() == 4 => {
                        let (
                            Some(MachOperand::VReg(t)),
                            Some(MachOperand::VReg(iv2)),
                            Some(MachOperand::Imm(k)),
                        ) = (
                            idx_inst.operands.get(1),
                            idx_inst.operands.get(2),
                            idx_inst.operands.get(3),
                        )
                        else {
                            continue;
                        };
                        if !(0..64).contains(k) {
                            continue;
                        }
                        (*t, Some(idx_def.inst), Some((*iv2, *k)))
                    }
                    _ => continue,
                };

                let log2_elem = elem.trailing_zeros() as i64;
                let (lsl_inst_opt, iv, shift, inv) = if scaled {
                    // `base + (idx << log2 elem)`: the HARDWARE scales, so there
                    // is no `lsl` in the chain and `idx` must be affine in V with
                    // derivative exactly 1. The invariant addend is re-scaled by
                    // log2(elem) when the seed materialises it.
                    if add_inst.is_none() {
                        bail!("scaled with raw-IV index: already optimal, nothing to delete");
                    }
                    let inv2 = match inv {
                        Some((r, k)) if k + log2_elem < 64 => Some((r, k + log2_elem)),
                        Some(_) => bail!("scaled: invariant shift would overflow"),
                        None => None,
                    };
                    (None, lsl_carrier, log2_elem, inv2)
                } else {
                    let lsl_site = if add_inst.is_some() {
                        match chain_def(lsl_carrier) {
                            Some(d) => d,
                            None => bail!("no LslRI in chain"),
                        }
                    } else {
                        idx_def
                    };
                    let li = func.inst(lsl_site.inst).clone();
                    if li.opcode != AArch64Opcode::LslRI || li.operands.len() != 3 {
                        bail!("chain head is not LslRI");
                    }
                    let (Some(MachOperand::VReg(v)), Some(MachOperand::Imm(sh))) =
                        (li.operands.get(1), li.operands.get(2))
                    else {
                        bail!("malformed LslRI");
                    };
                    if !(0..64).contains(sh) || (1i64 << *sh) != elem {
                        bail!("shift vs elem");
                    }
                    (Some(lsl_site.inst), *v, *sh, inv)
                };

                // (5) IV: exactly two defs — init dominating the preheader, and a
                // single `AddRI V, V, #1` inside the loop body.
                if iv.class != RegClass::Gpr64 {
                    continue;
                }
                let Some(ivdefs) = defs.get(&iv) else {
                    continue;
                };
                if ivdefs.len() != 2 {
                    bail!("iv def count");
                }
                let mut init_ok = false;
                let mut step_ok = false;
                for d in ivdefs {
                    if !lp.body.contains(&d.block) {
                        if dom.dominates(d.block, pre) {
                            init_ok = true;
                        }
                    } else {
                        let di = func.inst(d.inst);
                        if di.opcode == AArch64Opcode::AddRI
                            && di.operands.len() == 3
                            && matches!(di.operands.first(), Some(MachOperand::VReg(x)) if *x == iv)
                            && matches!(di.operands.get(1), Some(MachOperand::VReg(x)) if *x == iv)
                            && matches!(di.operands.get(2), Some(MachOperand::Imm(1)))
                        {
                            step_ok = true;
                        }
                    }
                }
                if !(init_ok && step_ok) {
                    bail!("iv init/step");
                }

                // (6) base / inv defined once, outside, dominating the preheader.
                if !single_outside(base, pre, &lp.body) {
                    bail!("base not invariant");
                }
                if let Some((iv2, _)) = inv {
                    if iv2.class != RegClass::Gpr64 || !single_outside(iv2, pre, &lp.body) {
                        continue;
                    }
                }
                // (7) no self-clobber.
                if dst == base || dst == iv || inv.is_some_and(|(r, _)| dst == r) {
                    continue;
                }

                plans.push(Plan {
                    load_inst: load_id,
                    dst,
                    base,
                    lsl_inst: lsl_inst_opt,
                    iv,
                    shift,
                    add_inst,
                    inv,
                    elem,
                });
            }
        }
    }

    if plans.is_empty() {
        return false;
    }

    let mut changed = false;
    for p in plans {
        // Seed P at the END of the preheader: P = base + (inv << k) + (V << s).
        // Every leaf is single-def outside the loop with its def dominating the
        // preheader, and `V` still holds its init value there, so this reads
        // exactly what iteration 1's chain would have read.
        let Some(lp) = loops.all_loops().find(|l| {
            l.body
                .iter()
                .any(|&b| func.block(b).insts.contains(&p.load_inst))
        }) else {
            continue;
        };
        let Some(pre) = lp.preheader else { continue };

        let t0 = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
        let acc = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
        let carrier = VReg::new(func.alloc_vreg(), RegClass::Gpr64);

        let mut seed = vec![
            MachInst::new(
                AArch64Opcode::LslRI,
                vec![
                    MachOperand::VReg(t0),
                    MachOperand::VReg(p.iv),
                    MachOperand::Imm(p.shift),
                ],
            ),
            MachInst::new(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::VReg(acc),
                    MachOperand::VReg(p.base),
                    MachOperand::VReg(t0),
                ],
            ),
        ];
        match p.inv {
            Some((r, 0)) => seed.push(MachInst::new(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::VReg(carrier),
                    MachOperand::VReg(acc),
                    MachOperand::VReg(r),
                ],
            )),
            Some((r, k)) => seed.push(MachInst::new(
                AArch64Opcode::AddRRShift,
                vec![
                    MachOperand::VReg(carrier),
                    MachOperand::VReg(acc),
                    MachOperand::VReg(r),
                    MachOperand::Imm(k),
                ],
            )),
            None => seed.push(MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::VReg(carrier), MachOperand::VReg(acc)],
            )),
        }
        insert_before_terminator(func, pre, seed);

        // Rewrite the load and neutralise the dead chain.
        *func.inst_mut(p.load_inst) = MachInst::new(
            AArch64Opcode::LdrPostIndex,
            vec![
                MachOperand::VReg(p.dst),
                MachOperand::VReg(carrier),
                MachOperand::Imm(p.elem),
            ],
        );
        if let Some(l) = p.lsl_inst {
            *func.inst_mut(l) = MachInst::new(AArch64Opcode::Nop, vec![]);
        }
        if let Some(a) = p.add_inst {
            *func.inst_mut(a) = MachInst::new(AArch64Opcode::Nop, vec![]);
        }
        if let Some(prov) = provenance.as_deref_mut() {
            let merged: Vec<InstId> = p.lsl_inst.into_iter().chain([p.load_inst]).collect();
            prov.record_merge(&merged, p.load_inst, pass_id());
        }
        changed = true;
    }
    changed
}

/// Append `insts` to `block` immediately before its terminator run.
fn insert_before_terminator(func: &mut MachFunction, block: BlockId, insts: Vec<MachInst>) {
    let mut ids = Vec::with_capacity(insts.len());
    for inst in insts {
        ids.push(func.push_inst(inst));
    }
    let mut at = func.block(block).insts.len();
    while at > 0 {
        if !func.inst(func.block(block).insts[at - 1]).is_terminator() {
            break;
        }
        at -= 1;
    }
    let b = func.block_mut(block);
    for id in ids.into_iter().rev() {
        b.insts.insert(at, id);
    }
}

#[cfg(test)]
mod tests;
