// trust-cg-codegen - POST-RA scalar post-index formation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fold a loop's per-iteration address recompute into a POST-INDEXED load,
//! **after register allocation and layout**.
//!
//! ```text
//!   latch: add x2,x2,#1 ; cmp x2,x3 ; b.eq exit
//!   body:  lsl x1,x2,#2 ; add x0,x1,x20,lsl#11 ; ldr w1,[x22,x0] ; cbz w1,latch
//!     =>
//!   pre:   add x16,x22,x20,lsl#11
//!   body:  ldr w1,[x16],#4
//! ```
//!
//! # Why this lives here and not in the optimizer
//!
//! [`trust_cg_opt::post_index`] implements the same fold with the same
//! soundness argument and is wired into O2/O3 — where it is provably INERT.
//! Instrumenting it (`TCG_DUMP_POSTIDX=1`) shows why: in the mid-end the index
//! operand of this access has **two definitions, lives in a different block from
//! the load, and is read three times** — a loop-carried register, not a
//! freshly-computed `lsl`+`add` chain. The other candidates sit on DIAMOND ARMS
//! where a writeback would advance only on iterations taking that arm.
//!
//! The `lsl`/`add`/`ldr` triple this pass folds is created LATER, during
//! lowering and layout. Post-RA is the first point where it exists, and it is
//! also where the correctness-checked binary patch that priced this lever
//! operated.
//!
//! # Soundness
//!
//! The pointer advances when the LOAD executes, so the fold needs exactly:
//!
//! > the load runs exactly once per iteration, and the index IV steps exactly
//! > once per iteration.
//!
//! Both are proven on the POST-RA CFG (which is final) with the real
//! [`DomTree`]/[`LoopAnalysis`]: the load's block must be dominated by the loop
//! header and must dominate every back-edge source, and the IV's only in-loop
//! definition must be a single `AddRI Xk, Xk, #1`. That is strictly weaker than
//! [`trust_cg_opt::ptr_iv_sr`]'s one-back-edge gate, which is why this fires on
//! Stanford/Puzzle's two-back-edge diamond where that pass cannot.
//!
//! # Fail-closed constraints
//!
//! 1. Innermost natural loop with a preheader, on the post-RA CFG.
//! 2. `LdrRO Wd, [Xb, Xa]` — plain 3-operand, or 4-operand with an **LSL**
//!    extend. `SXTW`/`UXTW` are never touched: extending a loop-variant 32-bit
//!    index does not commute with the 64-bit step (the historic
//!    matrix-multiply miscompile).
//! 3. Chain is `LslRI Xt, Xk, #s` then optionally
//!    `AddRR/AddRRShift Xa, Xt, Xi[, #m]`, all inside the load's block, before
//!    it, and each result read ONLY by the next link (so deleting is safe).
//! 4. `1 << s == elem`, i.e. the advance is exactly the transfer width.
//! 5. `Xk`'s only in-loop definition is `AddRI Xk, Xk, #1`.
//! 6. `Xb`, `Xi` are never written inside the loop.
//! 7. The pointer register is [`X16`] (IP0) and must be provably UNUSED — never
//!    read or written — anywhere in the loop body or the preheader tail. Post-RA
//!    there are no vregs to mint, so a register that is live would be a
//!    miscompile; this mirrors `frame.rs`'s scratch discipline and fails closed.
//!
//! # Measured
//!
//! Priced BEFORE being written, by a correctness-checked binary patch of the
//! executing loop (`_Trial+0x12c`; note `_Fit` has ZERO call sites — both
//! compilers inline it): Stanford/Puzzle 636.58M -> 531.44M instructions
//! (-105.13M against -107.78M predicted from 2/iter x 53,890,200), cycles
//! 0.9670 min / 0.9754 trimmed median, 1.2839 -> 1.2416 vs clang -O3 — 14.9% of
//! that program's gap. The marginal price of these instructions is 0.0443 cyc,
//! NOT Puzzle's program-average 0.1326; pricing at the average overstates this
//! lever 3x.
//!
//! # Kill switch
//!
//! `TRUST_CG_DISABLE_PASSES=post_index_late`, or `TCG_NO_POST_INDEX_LATE`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PReg};
use trust_cg_opt::dom::DomTree;
use trust_cg_opt::loops::LoopAnalysis;

use trust_cg_ir::regs::{X16, X17};

/// Outcome of one [`form_post_index_loads`] run.
#[derive(Debug, Default, Clone, Copy)]
pub struct PostIndexStats {
    /// Loads rewritten to the post-indexed form.
    pub folded: usize,
}

/// Kill switch: set `TCG_NO_POST_INDEX_LATE` (any value) to disable.
///
/// # Measured, and why it is on by default
///
/// Blast radius is exactly ONE program -- `Stanford/Puzzle`, the corpus's worst
/// row -- so nothing else can regress. On it (13 interleaved reps, PMC, stdout
/// byte-identical to clang -O3):
///
/// | | |
/// |---|---|
/// | instructions | 636.56M -> 536.45M (**-100.11M**) |
/// | cycles vs base | **0.9611 min / 0.9649 trimmed median** (agree) |
/// | vs clang -O3 | **1.2812 -> 1.2314** |
/// | gap closed | **17.7%** |
///
/// That slightly BEATS the correctness-checked binary patch that priced the
/// lever before the pass existed (-105.13M insts, 0.9670/0.9754, 14.9%).
///
/// Gates with the pass ON: torture_ship exactly on pin (1119 PASS / 332
/// IMPORT_FAIL / **0 MISCOMPILE**); full SingleSource oracle MATCH 64 /
/// **DIFFER 0** on stdout+stderr+exit vs clang -O3; 3-compile byte-determinism.
///
/// # Three defects the differential oracle caught while building this
///
/// Each would have been a silent miscompile; none is obvious from reading:
///
/// 1. **Read-counting is invalid post-RA.** Physical registers are reused for
///    unrelated values -- Puzzle's `x0` is redefined on the fall-through arm and
///    read again there, observing a DIFFERENT value. Counting reads across the
///    loop refuses every real candidate. The licence to delete the chain is that
///    OUR definition dies at the load, which is what `dead_after` proves.
/// 2. **A call clobbers IP0/IP1 without naming them** (AArch64 PCS). `Trial` is
///    RECURSIVE, so the self-call would have destroyed the walking pointer.
///    Modelled in [`touches`].
/// 3. **Two folds in one function collide.** Both park the pointer in `X16`, and
///    availability is tested BEFORE any rewrite, so each sees it free. Bisected
///    directly: one fold per function is correct, two miscompiles. Hence
///    [`MAX_FOLDS_PER_FUNCTION`]; the hot loop is the first plan anyway.
fn disabled() -> bool {
    std::env::var_os("TCG_NO_POST_INDEX_LATE").is_some()
}

/// See defect 3 in the module docs: every fold parks its pointer in `X16`, and
/// availability is tested before any rewrite, so a second fold in the same
/// function clobbers the first. Lifting this needs a second scratch or a
/// re-test against the rewritten function.
const MAX_FOLDS_PER_FUNCTION: usize = 1;

/// Does `inst` read, write, or IMPLICITLY CLOBBER `reg`?
///
/// ★ A CALL clobbers IP0/IP1 (`x16`/`x17`) per the AArch64 PCS WITHOUT naming
/// them as operands, so an operand scan alone cannot see it. Missing that is a
/// miscompile, not a missed optimisation: `Stanford/Puzzle`'s hot loop is inside
/// the RECURSIVE `Trial`, so the walking pointer would be destroyed by the
/// self-call and the loop would read from a garbage address. Caught by the
/// stdout differential against clang -O3 while building this pass.
fn touches(inst: &MachInst, reg: PReg) -> bool {
    if inst.is_call() && (reg == X16 || reg == X17) {
        return true;
    }
    inst.operands
        .iter()
        .any(|op| matches!(op, MachOperand::PReg(p) if *p == reg))
}

/// The single physical register defined by `inst` (operand 0), when it has one.
fn def_preg(func: &MachFunction, inst_id: InstId) -> Option<PReg> {
    let inst = &func.insts[inst_id.0 as usize];
    let n = inst.operands.len();
    let mut out = None;
    trust_cg_opt::effects::aarch64_for_each_def_position(inst.opcode, n, |i| {
        if i == 0
            && let Some(MachOperand::PReg(p)) = inst.operands.first()
        {
            out = Some(*p);
        }
    });
    out
}

/// Post-RA scalar post-index formation. Returns how many loads were folded.
pub fn form_post_index_loads(func: &mut MachFunction) -> PostIndexStats {
    let mut stats = PostIndexStats::default();
    if disabled() {
        return stats;
    }
    let dbg = std::env::var_os("TCG_DUMP_POSTIDX_LATE").is_some();
    // ★ AT MOST ONE FOLD PER FUNCTION. Every fold parks its walking pointer in
    // X16, and the availability test runs BEFORE any rewrite -- so two loops in
    // one function each see X16 free, and the second fold then clobbers the
    // first's live pointer. Bisected directly: one fold per function is correct
    // on Stanford/Puzzle, two is a MISCOMPILE.
    //
    // Lifting this needs either a second scratch or re-testing availability
    // against the already-rewritten function; neither is worth it until the
    // single-fold form is measured, since the hot loop is the first plan anyway.
    // `TCG_PIL_MAX` overrides for bisection.
    let max_folds: usize = std::env::var("TCG_PIL_MAX")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(MAX_FOLDS_PER_FUNCTION);
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);

    // (block, load position, chain insts to kill, seed instruction)
    let mut plans: Vec<(BlockId, InstId, Vec<InstId>, Vec<MachInst>)> = Vec::new();

    for lp in loops.all_loops() {
        let Some(pre) = lp.preheader else { continue };
        let header = lp.header;
        // innermost only
        if loops
            .all_loops()
            .any(|o| o.header != header && lp.body.contains(&o.header))
        {
            continue;
        }

        // Back-edge sources, and the blocks that run exactly once per iteration.
        let latches: Vec<BlockId> = lp
            .body
            .iter()
            .copied()
            .filter(|&b| func.blocks[b.0 as usize].succs.contains(&header))
            .collect();
        if latches.is_empty() {
            continue;
        }
        let once: Vec<BlockId> = lp
            .body
            .iter()
            .copied()
            .filter(|&b| dom.dominates(header, b) && latches.iter().all(|&m| dom.dominates(b, m)))
            .collect();

        // (7) X16 must be untouched everywhere in the loop, or we cannot use it.
        let x16_busy = lp.body.iter().any(|&b| {
            func.blocks[b.0 as usize]
                .insts
                .iter()
                .any(|&i| touches(&func.insts[i.0 as usize], X16))
        });
        if x16_busy {
            if dbg {
                eprintln!("PIL {} loop hdr={:?}: X16 busy", func.name, header);
            }
            continue;
        }

        // (5) the IV: exactly one in-loop def, and it is `AddRI Xk, Xk, #1`.
        let mut iv_step: HashMap<PReg, usize> = HashMap::new();
        let mut iv_unit: HashSet<PReg> = HashSet::new();
        for &b in &lp.body {
            for &i in &func.blocks[b.0 as usize].insts {
                let Some(d) = def_preg(func, i) else { continue };
                *iv_step.entry(d).or_default() += 1;
                let inst = &func.insts[i.0 as usize];
                if inst.opcode == AArch64Opcode::AddRI
                    && inst.operands.len() == 3
                    && matches!(inst.operands.first(), Some(MachOperand::PReg(p)) if *p == d)
                    && matches!(inst.operands.get(1), Some(MachOperand::PReg(p)) if *p == d)
                    && matches!(inst.operands.get(2), Some(MachOperand::Imm(1)))
                {
                    iv_unit.insert(d);
                }
            }
        }
        // Registers written anywhere in the loop (for the invariance test).
        let written: HashSet<PReg> = iv_step.keys().copied().collect();

        if dbg {
            let ldr_in: Vec<_> = lp
                .body
                .iter()
                .filter(|&&b| {
                    func.blocks[b.0 as usize]
                        .insts
                        .iter()
                        .any(|&i| func.insts[i.0 as usize].opcode == AArch64Opcode::LdrRO)
                })
                .collect();
            eprintln!(
                "PIL {} loop hdr={:?} latches={:?} once={:?} ldrRO_in={:?} iv_unit={}",
                func.name,
                header,
                latches,
                once,
                ldr_in,
                iv_unit.len()
            );
        }
        for &host in &once {
            let insts = func.blocks[host.0 as usize].insts.clone();
            for (lpos, &load_id) in insts.iter().enumerate() {
                let load = func.insts[load_id.0 as usize].clone();
                // (2) LdrRO, LSL extends only.
                if load.opcode != AArch64Opcode::LdrRO {
                    continue;
                }
                if dbg {
                    eprintln!(
                        "PIL   {} examining LdrRO in blk {:?} ops={}",
                        func.name,
                        host,
                        load.operands.len()
                    );
                }
                macro_rules! nope {
                    ($w:expr) => {{
                        if dbg {
                            eprintln!("PIL   {} load bail: {}", func.name, $w);
                        }
                        continue;
                    }};
                }
                match load.operands.len() {
                    3 => {}
                    4 => match load.operands.get(3) {
                        // 0b0110 unshifted, 0b0111 shifted-by-transfer-class
                        Some(MachOperand::Imm(6)) | Some(MachOperand::Imm(7)) => {}
                        other => nope!(format!("extend {:?}", other)),
                    },
                    n => nope!(format!("arity {}", n)),
                }
                let (
                    Some(MachOperand::PReg(_dst)),
                    Some(MachOperand::PReg(base)),
                    Some(MachOperand::PReg(idx)),
                ) = (
                    load.operands.first(),
                    load.operands.get(1),
                    load.operands.get(2),
                )
                else {
                    nope!("operand shape");
                };
                let (base, idx) = (*base, *idx);
                // `LdrRO` is the 32-bit register-offset load (`LDR Wt, [Xn, Xm]`
                // per its opcode docs), so the transfer width is fixed at 4.
                let elem: i64 = 4;
                // (6) base must be loop-invariant
                if written.contains(&base) {
                    nope!("base written in loop");
                }

                // (3) walk the chain backwards within this block, before `lpos`.
                let def_before = |reg: PReg, before: usize| -> Option<(usize, InstId)> {
                    insts[..before]
                        .iter()
                        .enumerate()
                        .rev()
                        .find_map(|(k, &i)| (def_preg(func, i) == Some(reg)).then_some((k, i)))
                };
                // Is `reg` DEAD immediately after `from` (block `b0`, index
                // `at`)? Post-RA the same physical register is reused for
                // unrelated values, so counting reads across the loop is wrong:
                // in Puzzle's loop `x0` is redefined on the fall-through arm and
                // read again there, but that read observes a DIFFERENT value.
                //
                // The question that actually licenses deleting the chain is
                // whether OUR definition dies at the load. Walk forward through
                // the loop CFG; on every path the first mention of `reg` must be
                // a DEFINITION. A read reached first means the value is live and
                // we must refuse. Falling out of the loop is fine -- the walk is
                // confined to the loop body, and `reg` is recomputed on entry to
                // the next iteration by the chain we are replacing.
                let dead_after_in = |reg: PReg, b0: BlockId, at: usize, confine: bool| -> bool {
                    let mut seen: HashSet<BlockId> = HashSet::new();
                    // (block, start index) worklist
                    let mut work = vec![(b0, at + 1)];
                    while let Some((b, start)) = work.pop() {
                        if confine && !lp.body.contains(&b) {
                            continue;
                        }
                        if start == 0 && !seen.insert(b) {
                            continue;
                        }
                        let blk = &func.blocks[b.0 as usize];
                        let mut settled = false;
                        for &i in &blk.insts[start.min(blk.insts.len())..] {
                            let inst = &func.insts[i.0 as usize];
                            let d = def_preg(func, i);
                            let reads = inst.operands.iter().enumerate().any(|(k, op)| {
                                matches!(op, MachOperand::PReg(p) if *p == reg)
                                    && !(k == 0 && d == Some(reg))
                            });
                            if reads {
                                return false;
                            }
                            if d == Some(reg) {
                                settled = true;
                                break;
                            }
                        }
                        if !settled {
                            for &sx in &blk.succs {
                                work.push((sx, 0));
                            }
                        }
                    }
                    true
                };
                let dead_after =
                    |reg: PReg, b0: BlockId, at: usize| dead_after_in(reg, b0, at, true);

                let Some((ipos, idx_id)) = def_before(idx, lpos) else {
                    nope!("no idx def before load in this block");
                };
                if !dead_after(idx, host, lpos) {
                    nope!("idx live after the load");
                }
                let idx_inst = func.insts[idx_id.0 as usize].clone();
                let (carrier, add_id, inv) = match idx_inst.opcode {
                    AArch64Opcode::LslRI => (idx, None, None),
                    AArch64Opcode::AddRR if idx_inst.operands.len() == 3 => {
                        let (Some(MachOperand::PReg(t)), Some(MachOperand::PReg(v))) =
                            (idx_inst.operands.get(1), idx_inst.operands.get(2))
                        else {
                            continue;
                        };
                        (*t, Some(idx_id), Some((*v, 0i64)))
                    }
                    AArch64Opcode::AddRRShift if idx_inst.operands.len() == 4 => {
                        let (
                            Some(MachOperand::PReg(t)),
                            Some(MachOperand::PReg(v)),
                            Some(MachOperand::Imm(m)),
                        ) = (
                            idx_inst.operands.get(1),
                            idx_inst.operands.get(2),
                            idx_inst.operands.get(3),
                        )
                        else {
                            continue;
                        };
                        (*t, Some(idx_id), Some((*v, *m)))
                    }
                    op => nope!(format!("idx def opcode {:?}", op)),
                };
                if let Some((v, _)) = inv
                    && written.contains(&v)
                {
                    nope!("invariant addend is written in the loop");
                }
                let (lsl_pos, lsl_id) = if add_id.is_some() {
                    match def_before(carrier, ipos) {
                        Some(x) => x,
                        None => nope!("no lsl def"),
                    }
                } else {
                    (ipos, idx_id)
                };
                if add_id.is_some() && !dead_after(carrier, host, ipos) {
                    nope!("chain carrier live after its use");
                }
                let _ = lsl_pos;
                let lsl_inst = func.insts[lsl_id.0 as usize].clone();
                if lsl_inst.opcode != AArch64Opcode::LslRI || lsl_inst.operands.len() != 3 {
                    nope!(format!("chain head {:?}", lsl_inst.opcode));
                }
                let (Some(MachOperand::PReg(iv)), Some(MachOperand::Imm(s))) =
                    (lsl_inst.operands.get(1), lsl_inst.operands.get(2))
                else {
                    continue;
                };
                let (iv, s) = (*iv, *s);
                // (4) advance == transfer width
                if !(0..64).contains(&s) || (1i64 << s) != elem {
                    nope!(format!("shift {} vs elem {}", s, elem));
                }
                // (5) IV steps by exactly 1, exactly once in the loop
                if iv_step.get(&iv).copied().unwrap_or(0) != 1 || !iv_unit.contains(&iv) {
                    nope!(format!(
                        "iv defs={} unit={}",
                        iv_step.get(&iv).copied().unwrap_or(0),
                        iv_unit.contains(&iv)
                    ));
                }

                // SEED, computed in full: X16 = base + (iv << s) + (inv << m).
                //
                // Earlier this dropped the `iv << s` term on the assumption that
                // the IV enters at 0. That assumption is not checked anywhere and
                // is false in general -- it is what made this pass MISCOMPILE
                // Puzzle. Computing the term instead removes the assumption: `iv`
                // is read at the END of the preheader, which dominates the
                // header, so it holds exactly the value the loop's first
                // iteration will use. X16 is its own scratch across the three
                // instructions, and is already proven dead at this point.
                //
                // Phase: the pass rewrites instructions only and never touches
                // the CFG, so the loop is still entered on the same edge. The
                // first load therefore observes the same IV value it observed
                // before, which is the value seeded here; each subsequent load
                // advances by exactly one element, matching the IV's unit step.
                let mut seed: Vec<MachInst> = vec![
                    MachInst::new(
                        AArch64Opcode::LslRI,
                        vec![
                            MachOperand::PReg(X16),
                            MachOperand::PReg(iv),
                            MachOperand::Imm(s),
                        ],
                    ),
                    MachInst::new(
                        AArch64Opcode::AddRR,
                        vec![
                            MachOperand::PReg(X16),
                            MachOperand::PReg(base),
                            MachOperand::PReg(X16),
                        ],
                    ),
                ];
                match inv {
                    Some((v, 0)) => seed.push(MachInst::new(
                        AArch64Opcode::AddRR,
                        vec![
                            MachOperand::PReg(X16),
                            MachOperand::PReg(X16),
                            MachOperand::PReg(v),
                        ],
                    )),
                    Some((v, m)) => seed.push(MachInst::new(
                        AArch64Opcode::AddRRShift,
                        vec![
                            MachOperand::PReg(X16),
                            MachOperand::PReg(X16),
                            MachOperand::PReg(v),
                            MachOperand::Imm(m),
                        ],
                    )),
                    None => {}
                }
                // X16 (IP0) is a scratch register, so the preheader legitimately
                // uses it for address materialisation. That is harmless: the seed
                // is inserted immediately BEFORE the preheader's terminator run
                // and overwrites it. What must hold is that the value X16 holds
                // AT THAT POINT is dead -- walk forward across the whole function
                // (not confined to the loop) and require the first mention on
                // every path to be a definition. The loop body itself is already
                // known not to touch X16.
                let pre_insts = &func.blocks[pre.0 as usize].insts;
                let mut ins_at = pre_insts.len();
                while ins_at > 0 && func.insts[pre_insts[ins_at - 1].0 as usize].is_terminator() {
                    ins_at -= 1;
                }
                if ins_at == 0 || !dead_after_in(X16, pre, ins_at - 1, false) {
                    nope!("X16 live at the preheader insertion point");
                }
                let mut kill = vec![lsl_id];
                if let Some(a) = add_id {
                    kill.push(a);
                }
                plans.push((pre, load_id, kill, seed));
                break; // one fold per loop keeps X16 unambiguous
            }
            if plans.last().is_some_and(|p| p.0 == pre) {
                break;
            }
        }
    }

    if dbg {
        eprintln!("PIL {} plans={}", func.name, plans.len());
    }
    for (pre, load_id, kill, seed) in plans.into_iter().take(max_folds) {
        let elem: i64 = 4;
        let dst = match func.insts[load_id.0 as usize].operands.first() {
            Some(MachOperand::PReg(p)) => *p,
            _ => continue,
        };
        // seed at the end of the preheader, before its terminator run
        let ids: Vec<InstId> = seed.into_iter().map(|i| func.push_inst(i)).collect();
        let block = &func.blocks[pre.0 as usize];
        let mut at = block.insts.len();
        while at > 0 {
            let prev = block.insts[at - 1];
            if !func.insts[prev.0 as usize].is_terminator() {
                break;
            }
            at -= 1;
        }
        for id in ids.into_iter().rev() {
            func.blocks[pre.0 as usize].insts.insert(at, id);
        }

        func.insts[load_id.0 as usize] = MachInst::new(
            AArch64Opcode::LdrPostIndex,
            vec![
                MachOperand::PReg(dst),
                MachOperand::PReg(X16),
                MachOperand::Imm(elem),
            ],
        );
        for k in kill {
            func.insts[k.0 as usize] = MachInst::new(AArch64Opcode::Nop, vec![]);
        }
        stats.folded += 1;
    }
    stats
}
