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
//! [`DomTree`]/[`LoopAnalysis`]: the loop body must have no cycle that avoids
//! the header, the load's block must be dominated by the loop header and must
//! dominate every back-edge source, and the IV's only in-loop definition must
//! be a single `AddRI Xk, Xk, #1` in such a block, after the load. The
//! acyclicity test is what makes "dominates every back-edge source" mean
//! "exactly once": an irreducible cycle inside the body has no dominator
//! back-edge, so the loop still looks innermost while a block on that cycle
//! runs twice in one iteration. That is strictly weaker than
//! [`trust_cg_opt::ptr_iv_sr`]'s one-back-edge gate, which is why this fires on
//! Stanford/Puzzle's two-back-edge diamond where that pass cannot.
//!
//! # Fail-closed constraints
//!
//! 1. Innermost natural loop with a preheader, on the post-RA CFG, whose body
//!    has no cycle that avoids the header
//!    ([`trust_cg_opt::loops::body_is_acyclic_dag`]).
//! 2. `LdrRO Wd, [Xb, Xa]` — plain 3-operand, or 4-operand with the
//!    **unshifted LSL** mode (`Imm(6)`). The size-scaled LSL (`Imm(7)`,
//!    `[Xb, Xa, lsl #log2 size]`) is refused: it multiplies the whole index,
//!    so the stride is not `1 << s`. `SXTW`/`UXTW` are never touched: extending
//!    a loop-variant 32-bit index does not commute with the 64-bit step (the
//!    historic matrix-multiply miscompile).
//! 3. Chain is `LslRI Xt, Xk, #s` then optionally
//!    `AddRR/AddRRShift Xa, Xt, Xi[, #m]`, all inside the load's block, before
//!    it, and each result read ONLY by the next link (so deleting is safe) --
//!    on every path through the whole function, loop exits included, counting
//!    implicit reads (`ret`, call arguments).
//! 4. `1 << s == elem`, i.e. the advance is exactly the transfer width.
//! 5. `Xk`'s only in-loop definition is `AddRI Xk, Xk, #1`, in a block that
//!    runs exactly once per iteration (like the load's), and not before the
//!    load.
//! 6. `Xb`, `Xi` are never written inside the loop.
//! 7. The pointer register is [`X16`] (IP0) and must be provably UNUSED — never
//!    read or written — anywhere in the loop body or the preheader tail,
//!    including by a call or a `Trap*` carrier, which clobber it without naming
//!    it (see [`touches`]). Post-RA there are no vregs to mint, so a register
//!    that is live would be a miscompile; this mirrors `frame.rs`'s scratch
//!    discipline and fails closed.
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
use trust_cg_opt::loops::{LoopAnalysis, NaturalLoop, body_is_acyclic_dag};
use trust_cg_opt::post_index::runs_before_in_iteration;

use trust_cg_ir::regs::{X16, X17, reg_root, regs_overlap};

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
/// # The SECOND fold (round loop): instructions real, cycles are a lottery
///
/// Re-analysing between folds admits a second loop in `Trial`. Blast radius is
/// still exactly one program, and instructions drop another **3.91%**. The
/// cycle effect does NOT survive an R3 control:
///
/// | regime | min | trimmed median |
/// |---|---|---|
/// | default (ships) | 0.9750 / 0.9741 (repeat) | 0.9823 / 0.9809 |
/// | `TCG_NO_LOOP_HEAD_ALIGN=1` | **1.0037** | **1.0050** |
///
/// Null arm 0.9999/0.9993. Both statistics agree WITHIN each regime and the two
/// regimes disagree in SIGN, which is the signature of a code-size change
/// reshuffling loop placement -- not of the fold buying cycles. Consistent with
/// the free-class list: an `lsl`+`add` feeding an address in a loop that is not
/// issue-bound costs about nothing. So: do not quote the 2.5% as a mechanism.
/// It is landed because it is correct, because it removes real instructions, and
/// because re-analysis replaces a cap that was a symptom-level fix.
///
/// Gates with the pass ON: torture_ship exactly on pin (1119 PASS / 332
/// IMPORT_FAIL / **0 MISCOMPILE**); full SingleSource oracle MATCH 64 /
/// **DIFFER 0** on stdout+stderr+exit vs clang -O3; 3-compile byte-determinism.
///
/// # Where the remaining opportunity is (corpus census, TCG_DUMP_POSTIDX_LATE)
///
/// 310 `LdrRO` candidates are examined across SingleSource; today only
/// Stanford/Puzzle folds. What blocks the rest, in order:
///
/// | blocker | n | note |
/// |---|---|---|
/// | `idx live after the load` | **150** | broken down below. |
/// | `no idx def before load in this block` | 81 | the chain sits in a dominating block inside the loop; the search is block-local today. Linpack 20, lpbench 12, oourafft 7. |
/// | `extend Imm(13)` (SXTW) | 41 | CORRECTLY refused -- sign-extending a loop-variant 32-bit index does not commute with the 64-bit step. Do not "fix" this. |
/// | chain head `AddRI`/`Madd`/`SubRI` | 29 | straightforward additions to the chain matcher. Madd is 2-D indexing (Stanford ...MM); AddRI is Linpack. |
/// | `base written in loop` | 8 | genuinely not invariant. |
///
/// ★ The 150 were once recorded here as "likely read-modify-write". THEY ARE
/// NOT, and the dump now names the blocking reader rather than guessing:
///
/// | next reader of the index | n | what it means |
/// |---|---|---|
/// | `LdrRO` (index operand) | **52** | a SECOND register-offset load sharing one index -- `a[i]` and `b[i]`. The generalisation is N walking pointers replacing one shared `lsl`, which SAVES a register rather than costing one, but it is a different transform. |
/// | `StrRO` (index operand) | 39 | the actual read-modify-write case, only a quarter of the bucket. |
/// | `AddRI` (destination) | 17 | the index is itself the IV. |
/// | `Copy`/`Orr`/`AddRR`/`Cbz` | 42 | miscellaneous reuse. |
///
/// # Four defects the differential oracle caught while building this
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
///    availability was tested BEFORE any rewrite, so each saw it free. Fixed by
///    re-analysing between folds -- see [`form_post_index_loads`] -- not by
///    capping the count, which was the first (and merely symptomatic) fix.
/// 4. **W and X are the same register and different `PReg`s.** See [`reg_file`].
///    `ldur w16, [x29, #-0x54]` in a loop body destroys a pointer parked in X16,
///    and every width-blind test in this pass was blind to it. This one was
///    LATENT IN THE SHIPPED SINGLE-FOLD PASS, not introduced by the round loop:
///    it happened not to fire only because Puzzle's first foldable loop has no
///    `w16` write. The same hole covered the base and the IV, where it would
///    have made a written register look loop-invariant.
fn disabled() -> bool {
    std::env::var_os("TCG_NO_POST_INDEX_LATE").is_some()
}

/// Round cap for [`form_post_index_loads`]. Each round re-analyses the rewritten
/// function and applies at most one fold, so this bounds work rather than
/// licensing anything: the soundness comes from the re-analysis, not the number.
/// Corpus-wide the deepest function (Stanford/Puzzle's `Trial`) offers 3.
const MAX_FOLDS_PER_FUNCTION: usize = 8;

/// ★★ W AND X ARE THE SAME REGISTER, AND THEY ARE DIFFERENT `PReg` VALUES.
/// `X16` is `PReg(16)`, `W16` is `PReg(48)`, so `X16 == W16` is FALSE while
/// `ldur w16, [x29, #-0x54]` zero-extends into the top half of X16 and destroys
/// a 64-bit pointer parked there. Exactly that instruction sits in the body of
/// Stanford/Puzzle's second foldable loop and turned the walking pointer into a
/// small integer -- a SIGSEGV, caught by the differential oracle.
///
/// The same hazard applies to the base and the IV, not just to the scratch: a
/// loop that writes `w22` while `x22` is the load's base would pass the
/// "base is loop-invariant" test and be miscompiled. So every availability,
/// liveness, def-search and invariance test in this pass compares through
/// [`regs_overlap`] rather than comparing `PReg`s directly.
///
/// [`regs_overlap`] is the CANONICAL authority (`frame.rs`'s scratch discipline
/// uses it too); this pass deliberately does not carry its own copy, because two
/// definitions of register aliasing is how one of them ends up wrong.
///
/// A hash key that is equal exactly when [`regs_overlap`] is true. `reg_root`
/// returns `None` only for the system registers, which this pass never handles;
/// they fall back to their own encoding and so compare only with themselves.
fn reg_key(reg: PReg) -> (u8, u16) {
    match reg_root(reg) {
        Some((n, group)) => (group, n as u16),
        None => (u8::MAX, reg.encoding()),
    }
}

/// Does `inst` read, write, or IMPLICITLY CLOBBER `reg`?
///
/// ★ A CALL clobbers IP0/IP1 (`x16`/`x17`) per the AArch64 PCS WITHOUT naming
/// them as operands, so an operand scan alone cannot see it. Missing that is a
/// miscompile, not a missed optimisation: `Stanford/Puzzle`'s hot loop is inside
/// the RECURSIVE `Trial`, so the walking pointer would be destroyed by the
/// self-call and the loop would read from a garbage address. Caught by the
/// stdout differential against clang -O3 while building this pass.
///
/// ★ A `Trap*` guard carrier names no IP register either, but Phase 7.25
/// expands it AFTER this pass into code that writes them:
/// `expand_trap_bounds_check_exact` materialises a bound above the `CMP`
/// immediate as `MOVZ X16` (+`MOVK`), and `expand_trap_overflow_exact` computes
/// a 64-bit mul check in `X16`/`X17`. So every carrier counts as an IP-register
/// clobber -- the rule the spill-reload CSE applies for the same reason.
fn touches(inst: &MachInst, reg: PReg) -> bool {
    if (inst.is_call() || inst.opcode.is_trap_pseudo())
        && (regs_overlap(reg, X16) || regs_overlap(reg, X17))
    {
        return true;
    }
    inst.operands
        .iter()
        .any(|op| matches!(op, MachOperand::PReg(p) if regs_overlap(*p, reg)))
}

/// Whether the loop's increment of `iv` can run before `host[lpos]` within one
/// iteration: earlier in `host`, or in a loop block from which `host` is
/// reachable without passing through the header (that would be the next
/// iteration), per the opt-level twin's
/// [`trust_cg_opt::post_index::runs_before_in_iteration`]. The seed reads `iv`
/// at the end of the preheader, so the first load must observe that same value.
fn iv_advances_before_load(
    func: &MachFunction,
    lp: &NaturalLoop,
    host: BlockId,
    lpos: usize,
    iv: PReg,
) -> bool {
    lp.body.iter().any(|&b| {
        func.blocks[b.0 as usize]
            .insts
            .iter()
            .enumerate()
            .any(|(pos, &id)| {
                def_preg(func, id).is_some_and(|d| reg_key(d) == reg_key(iv))
                    && runs_before_in_iteration(func, lp, b, pos, host, lpos)
            })
    })
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
///
/// ★ ONE FOLD PER ROUND, RE-ANALYSED EACH TIME. Every fold parks its walking
/// pointer in X16, so folds are not independent: the original pass collected all
/// plans against the UNMODIFIED function and applied several, and the second one
/// clobbered the first's live pointer (a bisected miscompile on Stanford/Puzzle).
///
/// The fix is not a second scratch -- it is to re-test availability against the
/// already-rewritten function. That falls out of re-running the analysis, since
/// every admission test reads `func` directly:
///
/// * the `x16_busy` scan sees the previous fold's `LdrPostIndex` (X16 is an
///   operand of it) and refuses any further fold in that loop;
/// * `dead_after(X16, ...)` walks the whole function forward
///   from the new seed point and refuses if any path reaches a READ of X16
///   before a redefinition -- which is exactly "the earlier fold's pointer is
///   still live here". It equally protects the earlier fold from this seed and
///   this seed from the earlier fold; the relation is symmetric.
///
/// So the loop below re-derives the dominator tree and loop forest each round.
/// That is only paid by functions that actually fold (4 in the whole corpus),
/// and it is what makes more than one fold sound.
pub fn form_post_index_loads(func: &mut MachFunction) -> PostIndexStats {
    let mut stats = PostIndexStats::default();
    if disabled() {
        return stats;
    }
    // `TCG_PIL_MAX` overrides for bisection.
    let max_folds: usize = std::env::var("TCG_PIL_MAX")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(MAX_FOLDS_PER_FUNCTION);
    for _ in 0..max_folds {
        let round = form_one_post_index_load(func);
        if round.folded == 0 {
            break;
        }
        stats.folded += round.folded;
    }
    stats
}

/// One round: analyse the CURRENT `func` and apply at most one fold.
fn form_one_post_index_load(func: &mut MachFunction) -> PostIndexStats {
    let mut stats = PostIndexStats::default();
    let dbg = std::env::var_os("TCG_DUMP_POSTIDX_LATE").is_some();
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
        // (1) ... and no cycle in the body that avoids the header. An
        // irreducible cycle has no dominator back-edge, so the test above
        // cannot see it, and a block on it can run twice in one iteration.
        if !body_is_acyclic_dag(func, lp) {
            if dbg {
                eprintln!(
                    "PIL {} loop hdr={:?}: body has a cycle that avoids the header",
                    func.name, header
                );
            }
            continue;
        }

        // Back-edge sources, and the blocks that run exactly once per iteration
        // (dominated by the header, dominating every latch, in a body checked
        // acyclic above).
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
        //
        // Keyed by [`reg_key`], not by `PReg`: a loop that writes `w2` must count
        // as writing `x2`, or the IV would look single-defined and a base would
        // look loop-invariant when neither is true.
        let mut iv_step: HashMap<(u8, u16), usize> = HashMap::new();
        let mut iv_unit: HashSet<(u8, u16)> = HashSet::new();
        for &b in &lp.body {
            for &i in &func.blocks[b.0 as usize].insts {
                let Some(d) = def_preg(func, i) else { continue };
                *iv_step.entry(reg_key(d)).or_default() += 1;
                let inst = &func.insts[i.0 as usize];
                if inst.opcode == AArch64Opcode::AddRI
                    && inst.operands.len() == 3
                    && matches!(inst.operands.first(), Some(MachOperand::PReg(p)) if *p == d)
                    && matches!(inst.operands.get(1), Some(MachOperand::PReg(p)) if *p == d)
                    && matches!(inst.operands.get(2), Some(MachOperand::Imm(1)))
                {
                    iv_unit.insert(reg_key(d));
                }
            }
        }
        // Registers written anywhere in the loop (for the invariance test).
        let written: HashSet<(u8, u16)> = iv_step.keys().copied().collect();

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
                        // 0b0110: LSL #0, the address the 3-operand form takes.
                        Some(MachOperand::Imm(6)) => {}
                        // 0b0111: LSL by log2 of the transfer size, so the load
                        // reads `base + (idx << log2 size)`. The seed and the
                        // `#elem` step below model only the chain's own shift.
                        Some(MachOperand::Imm(7)) => nope!("size-scaled index Imm(7)"),
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
                if written.contains(&reg_key(base)) {
                    nope!("base written in loop");
                }

                // (3) walk the chain backwards within this block, before `lpos`.
                let def_before = |reg: PReg, before: usize| -> Option<(usize, InstId)> {
                    insts[..before]
                        .iter()
                        .enumerate()
                        .rev()
                        .find_map(|(k, &i)| {
                            def_preg(func, i)
                                .is_some_and(|d| regs_overlap(d, reg))
                                .then_some((k, i))
                        })
                };
                // Is `reg` DEAD immediately after `from` (block `b0`, index
                // `at`)? Post-RA the same physical register is reused for
                // unrelated values, so counting reads across the loop is wrong:
                // in Puzzle's loop `x0` is redefined on the fall-through arm and
                // read again there, but that read observes a DIFFERENT value.
                //
                // The question that actually licenses deleting the chain is
                // whether OUR definition dies at the load. Walk forward through
                // the WHOLE function's CFG; on every path the first mention of
                // `reg` must be a DEFINITION. A read reached first means the
                // value is live and we must refuse. The walk is NOT confined to
                // the loop: a loop EXIT can read the value too (an exit's
                // `ldr [b, x1]` sharing the loop's scaled index), and deleting the
                // chain would leave that reader with no definition. Implicit
                // reads count -- a `ret` reads its result registers and a call
                // its arguments through `implicit_uses`.
                let dead_after = |reg: PReg, b0: BlockId, at: usize| -> bool {
                    let mut seen: HashSet<BlockId> = HashSet::new();
                    // (block, start index) worklist
                    let mut work = vec![(b0, at + 1)];
                    while let Some((b, start)) = work.pop() {
                        if start == 0 && !seen.insert(b) {
                            continue;
                        }
                        let blk = &func.blocks[b.0 as usize];
                        let mut settled = false;
                        for &i in &blk.insts[start.min(blk.insts.len())..] {
                            let inst = &func.insts[i.0 as usize];
                            let d = def_preg(func, i);
                            let defs_reg = d.is_some_and(|d| regs_overlap(d, reg));
                            let reads =
                                inst.operands.iter().enumerate().any(|(k, op)| {
                                    matches!(op, MachOperand::PReg(p) if regs_overlap(*p, reg))
                                        && !(k == 0 && defs_reg)
                                }) || inst.implicit_uses.iter().any(|&u| regs_overlap(u, reg));
                            if reads {
                                return false;
                            }
                            // A W-width def still KILLS the 64-bit value (AArch64
                            // zero-extends), so an aliasing def settles the path.
                            if defs_reg {
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
                // (3) A deleted value is read ONLY by the next link. `dead_after`
                // covers everything after that link; this covers the stretch of
                // the block between the value's definition (`lo - 1`) and the
                // link (`hi`) -- e.g. an earlier load sharing the same `lsl`.
                // `def_before` returned the LAST definition before the link, so
                // nothing in the stretch defines `reg` and any mention is a read.
                let read_between = |reg: PReg, lo: usize, hi: usize| -> bool {
                    insts[lo..hi].iter().any(|&i| {
                        let inst = &func.insts[i.0 as usize];
                        inst.operands
                            .iter()
                            .any(|op| matches!(op, MachOperand::PReg(p) if regs_overlap(*p, reg)))
                            || inst.implicit_uses.iter().any(|&u| regs_overlap(u, reg))
                    })
                };

                let Some((ipos, idx_id)) = def_before(idx, lpos) else {
                    nope!("no idx def before load in this block");
                };
                if !dead_after(idx, host, lpos) {
                    // R4: name the blocking reader rather than guessing at the
                    // shape. This walk mirrors `dead_after` exactly but
                    // reports the first instruction that reads `idx`, so the
                    // census says *why* the index is live instead of only that
                    // it is. Debug-only -- it never influences a decision.
                    let blocker = || -> String {
                        let mut seen: HashSet<BlockId> = HashSet::new();
                        let mut work = vec![(host, lpos + 1)];
                        while let Some((b, start)) = work.pop() {
                            if start == 0 && !seen.insert(b) {
                                continue;
                            }
                            let blk = &func.blocks[b.0 as usize];
                            let mut settled = false;
                            for &i in &blk.insts[start.min(blk.insts.len())..] {
                                let inst = &func.insts[i.0 as usize];
                                let d = def_preg(func, i);
                                let defs_idx = d.is_some_and(|d| regs_overlap(d, idx));
                                let reads =
                                    inst.operands.iter().enumerate().any(|(k, op)| {
                                        matches!(op, MachOperand::PReg(p) if regs_overlap(*p, idx))
                                            && !(k == 0 && defs_idx)
                                    }) || inst.implicit_uses.iter().any(|&u| regs_overlap(u, idx));
                                if reads {
                                    // Which operand slot? Slot 1 of a store is
                                    // the base, slot 2 the index -- that
                                    // distinction is the read-modify-write test.
                                    let slot = inst
                                        .operands
                                        .iter()
                                        .position(|op| {
                                            matches!(op, MachOperand::PReg(p) if regs_overlap(*p, idx))
                                        })
                                        .unwrap_or(0);
                                    return format!("{:?}@op{}", inst.opcode, slot);
                                }
                                if defs_idx {
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
                        "none".to_string()
                    };
                    nope!(format!(
                        "idx live after the load, next reader {}",
                        blocker()
                    ));
                }
                if read_between(idx, ipos + 1, lpos) {
                    nope!("idx read between its def and the load");
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
                    && written.contains(&reg_key(v))
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
                if add_id.is_some() && read_between(carrier, lsl_pos + 1, ipos) {
                    nope!("chain carrier read before its add");
                }
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
                if iv_step.get(&reg_key(iv)).copied().unwrap_or(0) != 1
                    || !iv_unit.contains(&reg_key(iv))
                {
                    nope!(format!(
                        "iv defs={} unit={}",
                        iv_step.get(&reg_key(iv)).copied().unwrap_or(0),
                        iv_unit.contains(&reg_key(iv))
                    ));
                }
                // (5a) ... and that one increment runs on EVERY iteration: its
                // block is one of `once`, like the load's. On a conditional arm
                // the IV stays put on the iterations that skip the arm, while
                // the post-indexed pointer advances on each.
                let iv_block = lp.body.iter().copied().find(|&b| {
                    func.blocks[b.0 as usize]
                        .insts
                        .iter()
                        .any(|&i| def_preg(func, i).is_some_and(|d| reg_key(d) == reg_key(iv)))
                });
                if !iv_block.is_some_and(|b| once.contains(&b)) {
                    nope!("iv steps in a block that does not run every iteration");
                }
                // (5b) the seed below reads the IV at the end of the
                // preheader, so the IV's one increment must not run between
                // the header's entry and this load.
                if iv_advances_before_load(func, lp, host, lpos, iv) {
                    nope!("iv advances before the load");
                }

                // SEED, computed in full: X16 = base + (iv << s) + (inv << m).
                //
                // Earlier this dropped the `iv << s` term on the assumption that
                // the IV enters at 0. That assumption is not checked anywhere and
                // is false in general -- it is what made this pass MISCOMPILE
                // Puzzle. Computing the term instead removes the assumption: `iv`
                // is read at the END of the preheader, which dominates the
                // header, so it holds exactly the value the loop's first
                // iteration will use, given (5b): the increment runs after the
                // load. X16 is its own scratch across the three
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
                // and require the first mention on every path to be a
                // definition. The loop body itself is already known not to
                // touch X16.
                let pre_insts = &func.blocks[pre.0 as usize].insts;
                let mut ins_at = pre_insts.len();
                while ins_at > 0 && func.insts[pre_insts[ins_at - 1].0 as usize].is_terminator() {
                    ins_at -= 1;
                }
                if ins_at == 0 || !dead_after(X16, pre, ins_at - 1) {
                    nope!("X16 live at the preheader insertion point");
                }
                // The terminator run executes AFTER the seed, so it must not
                // touch X16 either. AArch64 stamps every `Trap*` carrier
                // IS_TERMINATOR, so a trailing carrier sits in this run, and its
                // later `MOVZ X16` would overwrite the seeded pointer.
                if pre_insts[ins_at..]
                    .iter()
                    .any(|&i| touches(&func.insts[i.0 as usize], X16))
                {
                    nope!("X16 touched in the preheader's terminator run");
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
    for (pre, load_id, kill, seed) in plans.into_iter().take(1) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::Signature;
    use trust_cg_ir::regs::{W3, W16, W22, X0, X1, X2, X3, X4, X20, X21, X22, X29};

    fn inst(f: &mut MachFunction, op: AArch64Opcode, ops: Vec<MachOperand>) -> InstId {
        f.push_inst(MachInst::new(op, ops))
    }
    fn install_edges(f: &mut MachFunction) {
        let e = crate::pipeline::derive_ir_cfg_edges_from_branch_operands(f);
        crate::pipeline::install_ir_cfg_edges(f, e);
    }
    fn p(r: PReg) -> MachOperand {
        MachOperand::PReg(r)
    }

    /// The shape this pass folds, as a hand-built post-RA function:
    ///
    /// ```text
    ///   pre:   mov x2, #0                <- the IV init; see note below
    ///   head:  lsl x1,x2,#2 ; add x0,x1,x20 ; ldr w3,[x22,x0] ; cbz w3,latch
    ///   body:  <extra>                       <- caller-supplied, the variable
    ///   latch: add x2,x2,#1 ; b head
    /// ```
    ///
    /// `head` dominates the only latch and is dominated by the header, so the
    /// load runs once per iteration and the fold is admissible.
    fn loop_fixture(extra: Vec<(AArch64Opcode, Vec<MachOperand>)>) -> MachFunction {
        let mut f = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let pre = f.entry;
        let head = f.create_block();
        let body = f.create_block();
        let latch = f.create_block();
        let exit = f.create_block();

        // The preheader needs a real (non-terminator) instruction: the seed is
        // inserted immediately BEFORE the terminator run, and the pass anchors
        // its X16-liveness check on the instruction preceding that point. A
        // preheader holding nothing but a branch is refused -- which never
        // happens in generated code, since a preheader carries the loop setup.
        let i = inst(
            &mut f,
            AArch64Opcode::MovI,
            vec![p(X2), MachOperand::Imm(0)],
        );
        f.append_inst(pre, i);
        let i = inst(&mut f, AArch64Opcode::B, vec![MachOperand::Block(head)]);
        f.append_inst(pre, i);

        for (op, ops) in [
            (
                AArch64Opcode::LslRI,
                vec![p(X1), p(X2), MachOperand::Imm(2)],
            ),
            (AArch64Opcode::AddRR, vec![p(X0), p(X1), p(X20)]),
            (AArch64Opcode::LdrRO, vec![p(X3), p(X22), p(X0)]),
            (AArch64Opcode::BCond, vec![MachOperand::Block(body)]),
        ] {
            let i = inst(&mut f, op, ops);
            f.append_inst(head, i);
        }
        for (op, ops) in extra {
            let i = inst(&mut f, op, ops);
            f.append_inst(body, i);
        }
        let i = inst(&mut f, AArch64Opcode::B, vec![MachOperand::Block(latch)]);
        f.append_inst(body, i);

        for (op, ops) in [
            (
                AArch64Opcode::AddRI,
                vec![p(X2), p(X2), MachOperand::Imm(1)],
            ),
            (AArch64Opcode::B, vec![MachOperand::Block(head)]),
        ] {
            let i = inst(&mut f, op, ops);
            f.append_inst(latch, i);
        }
        let i = inst(&mut f, AArch64Opcode::Ret, vec![]);
        f.append_inst(exit, i);
        install_edges(&mut f);
        f
    }

    fn folds(f: &MachFunction) -> usize {
        f.blocks
            .iter()
            .flat_map(|b| b.insts.iter())
            .filter(|&&i| f.insts[i.0 as usize].opcode == AArch64Opcode::LdrPostIndex)
            .count()
    }

    #[test]
    fn folds_the_canonical_shape() {
        let mut f = loop_fixture(vec![]);
        assert_eq!(form_post_index_loads(&mut f).folded, 1);
        assert_eq!(folds(&f), 1);
    }

    /// ★ REGRESSION, and a real miscompile before the fix: the loop body writes
    /// `w16`, which zero-extends into X16 and destroys the walking pointer this
    /// pass would park there. `X16` is `PReg(16)` and `W16` is `PReg(48)`, so an
    /// exact `PReg` comparison sees no conflict at all.
    ///
    /// Observed end-to-end: Stanford/Puzzle's second foldable loop contains
    /// `ldur w16, [x29, #-0x54]`; folding it SIGSEGVs (exit 139) while clang -O3
    /// and the single-fold build both print the reference output.
    #[test]
    fn refuses_when_the_body_writes_the_w_alias_of_the_scratch() {
        let mut f = loop_fixture(vec![(
            AArch64Opcode::LdrRI,
            vec![p(W16), p(X29), MachOperand::Imm(-84)],
        )]);
        assert_eq!(
            form_post_index_loads(&mut f).folded,
            0,
            "w16 write must make X16 unavailable"
        );
    }

    /// Same aliasing hazard on the BASE: a loop that writes `w22` is writing
    /// `x22`, so the load's base is not loop-invariant and the pointer would
    /// drift. Caught by the invariance test only if it normalises widths.
    #[test]
    fn refuses_when_the_body_writes_the_w_alias_of_the_base() {
        let mut f = loop_fixture(vec![(
            AArch64Opcode::LdrRI,
            vec![p(W22), p(X29), MachOperand::Imm(-84)],
        )]);
        assert_eq!(
            form_post_index_loads(&mut f).folded,
            0,
            "w22 write means x22 is not loop-invariant"
        );
    }

    /// And on the IV: `add w2,w2,#1` in the body means X2 has TWO in-loop
    /// definitions, so it no longer steps exactly once per iteration.
    #[test]
    fn refuses_when_the_body_writes_the_w_alias_of_the_iv() {
        let mut f = loop_fixture(vec![(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::PReg(trust_cg_ir::regs::W2),
                MachOperand::PReg(trust_cg_ir::regs::W2),
                MachOperand::Imm(1),
            ],
        )]);
        assert_eq!(
            form_post_index_loads(&mut f).folded,
            0,
            "w2 write is a second definition of the IV"
        );
    }

    /// The kill switch is read per call and the suite runs in parallel, so this
    /// asserts the plumbing rather than mutating the environment: `disabled()`
    /// gates the whole pass, and with it off the canonical shape folds.
    #[test]
    fn kill_switch_is_wired_and_off_by_default() {
        let mut f = loop_fixture(vec![]);
        assert!(
            !disabled(),
            "TCG_NO_POST_INDEX_LATE must not be set in tests"
        );
        assert_eq!(form_post_index_loads(&mut f).folded, 1);
    }

    /// W and X of the same number alias; different numbers do not; and the FP
    /// views of one V register alias each other.
    /// `reg_key` must agree with [`regs_overlap`] on every pair this pass can
    /// present, or the map-keyed tests (loop-invariance, IV step count) and the
    /// scan-based tests (availability, liveness) would disagree with each other.
    #[test]
    fn reg_key_agrees_with_regs_overlap() {
        use trust_cg_ir::regs::{D0, D1, S0, V0, W17, X0 as GX0};
        for (a, b) in [
            (X16, W16),
            (W16, X16),
            (X16, X17),
            (X16, W17),
            (V0, D0),
            (D0, S0),
            (V0, D1),
            (GX0, D0),
        ] {
            assert_eq!(
                regs_overlap(a, b),
                reg_key(a) == reg_key(b),
                "{a:?} vs {b:?}"
            );
        }
        // Spot-check the direction that matters, so a vacuous helper cannot pass.
        assert!(regs_overlap(X16, W16));
        assert!(!regs_overlap(X16, X17));
    }

    /// Every block's `(opcode, operands)` in order: equal before and after a run
    /// exactly when the pass left the function untouched.
    fn shape(f: &MachFunction) -> Vec<Vec<(AArch64Opcode, Vec<MachOperand>)>> {
        f.blocks
            .iter()
            .map(|b| {
                b.insts
                    .iter()
                    .map(|&i| {
                        let inst = &f.insts[i.0 as usize];
                        (inst.opcode, inst.operands.clone())
                    })
                    .collect()
            })
            .collect()
    }

    /// A loop whose EXIT is reachable from the load's block (`loop_fixture`'s
    /// exit is not):
    ///
    /// ```text
    ///   pre:   mov x2, #0 ; b head
    ///   head:  <chain, ending in the LdrRO that defines x3> ; cbz x3,exit ; b latch
    ///   latch: add x2,x2,#1 ; b head
    ///   exit:  <exit> ; ret                  <- `ret` implicitly reads `ret_uses`
    /// ```
    fn exit_fixture(
        chain: Vec<(AArch64Opcode, Vec<MachOperand>)>,
        exit: Vec<(AArch64Opcode, Vec<MachOperand>)>,
        ret_uses: &'static [PReg],
    ) -> MachFunction {
        let mut f = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let pre = f.entry;
        let head = f.create_block();
        let latch = f.create_block();
        let exit_b = f.create_block();

        let i = inst(
            &mut f,
            AArch64Opcode::MovI,
            vec![p(X2), MachOperand::Imm(0)],
        );
        f.append_inst(pre, i);
        let i = inst(&mut f, AArch64Opcode::B, vec![MachOperand::Block(head)]);
        f.append_inst(pre, i);

        for (op, ops) in chain.into_iter().chain([
            (AArch64Opcode::Cbz, vec![p(X3), MachOperand::Block(exit_b)]),
            (AArch64Opcode::B, vec![MachOperand::Block(latch)]),
        ]) {
            let i = inst(&mut f, op, ops);
            f.append_inst(head, i);
        }
        for (op, ops) in [
            (
                AArch64Opcode::AddRI,
                vec![p(X2), p(X2), MachOperand::Imm(1)],
            ),
            (AArch64Opcode::B, vec![MachOperand::Block(head)]),
        ] {
            let i = inst(&mut f, op, ops);
            f.append_inst(latch, i);
        }
        for (op, ops) in exit {
            let i = inst(&mut f, op, ops);
            f.append_inst(exit_b, i);
        }
        let i = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(ret_uses));
        f.append_inst(exit_b, i);
        install_edges(&mut f);
        f
    }

    /// `lsl x1,x2,#2 ; ldr x3,[x22,x1]` -- the one-link chain.
    fn one_link_chain() -> Vec<(AArch64Opcode, Vec<MachOperand>)> {
        vec![
            (
                AArch64Opcode::LslRI,
                vec![p(X1), p(X2), MachOperand::Imm(2)],
            ),
            (AArch64Opcode::LdrRO, vec![p(X3), p(X22), p(X1)]),
        ]
    }

    /// `lsl x1,x2,#2 ; add x0,x1,x20 ; ldr x3,[x22,x0]` -- the two-link chain,
    /// whose CARRIER x1 and index x0 are both deleted by the fold.
    fn two_link_chain() -> Vec<(AArch64Opcode, Vec<MachOperand>)> {
        vec![
            (
                AArch64Opcode::LslRI,
                vec![p(X1), p(X2), MachOperand::Imm(2)],
            ),
            (AArch64Opcode::AddRR, vec![p(X0), p(X1), p(X20)]),
            (AArch64Opcode::LdrRO, vec![p(X3), p(X22), p(X0)]),
        ]
    }

    /// Asserts the pass declines `f` and leaves every instruction as it was.
    fn assert_declines(mut f: MachFunction, why: &str) {
        let before = shape(&f);
        assert_eq!(form_post_index_loads(&mut f).folded, 0, "{why}");
        assert_eq!(shape(&f), before, "a declined fold must not rewrite: {why}");
    }

    /// The seed reads the IV at the end of the preheader, which is the value
    /// the first load sees only if the IV's increment runs AFTER the load in
    /// each iteration. Here the head increments it first (`add x2,x2,#1 ;
    /// lsl x1,x2,#2 ; ldr x3,[x22,x1]`), so the first load reads `x22 + 4`
    /// and a pointer seeded from `x2 = 0` would start one element early.
    #[test]
    fn refuses_when_the_iv_advances_before_the_load() {
        let mut chain = vec![(
            AArch64Opcode::AddRI,
            vec![p(X2), p(X2), MachOperand::Imm(1)],
        )];
        chain.extend(one_link_chain());
        let mut f = exit_fixture(chain, vec![], &[]);
        // The increment moved into the head: the latch only branches back.
        let latch = BlockId(2);
        assert_eq!(f.block(latch).insts.len(), 2);
        f.block_mut(latch).insts.remove(0);
        assert_declines(f, "the IV advances before the load");
    }

    /// Positive control for the exit tests below: the same loop, with an exit
    /// that never reads the chain, still folds -- so each refusal is caused by
    /// its exit reader and not by the fixture.
    #[test]
    fn folds_when_the_loop_exit_does_not_read_the_chain() {
        let mut f = exit_fixture(one_link_chain(), vec![], &[]);
        assert_eq!(form_post_index_loads(&mut f).folded, 1);
        let mut f = exit_fixture(two_link_chain(), vec![], &[]);
        assert_eq!(form_post_index_loads(&mut f).folded, 1);
        // An exit that REDEFINES the index before reading it observes its own
        // value, not the deleted chain's.
        let mut f = exit_fixture(
            one_link_chain(),
            vec![
                (AArch64Opcode::MovI, vec![p(X1), MachOperand::Imm(0)]),
                (AArch64Opcode::LdrRO, vec![p(X0), p(X20), p(X1)]),
            ],
            &[X0],
        );
        assert_eq!(form_post_index_loads(&mut f).folded, 1);
    }

    /// ★ REGRESSION (refuter reproduction): the loop exit reads the index the
    /// fold deletes. `lsl x1` is the only definition of x1 in the function, so
    /// after the fold `ldr x0,[x20,x1]` in the exit reads whatever x1 held on
    /// entry. The liveness walk was confined to the loop body and never
    /// looked at the exit.
    #[test]
    fn refuses_when_the_loop_exit_reads_the_deleted_index() {
        let f = exit_fixture(
            one_link_chain(),
            vec![(AArch64Opcode::LdrRO, vec![p(X0), p(X20), p(X1)])],
            &[X0],
        );
        assert_declines(f, "the exit reads x1, the deleted lsl's result");
    }

    /// The same hole on the two-link chain, for each deleted value: the exit
    /// reads the carrier x1 (the `lsl`) or the index x0 (the `add`).
    #[test]
    fn refuses_when_the_loop_exit_reads_a_deleted_two_link_value() {
        for (reg, what) in [(X1, "carrier x1"), (X0, "index x0")] {
            let f = exit_fixture(
                two_link_chain(),
                vec![(AArch64Opcode::LdrRO, vec![p(X4), p(X21), p(reg)])],
                &[X4],
            );
            assert_declines(f, &format!("the exit reads the {what}"));
        }
    }

    /// A RETURN reads its result registers without naming them as operands:
    /// `ret` here returns x0, the deleted `add`'s result, so an operand-only scan
    /// would call x0 dead on the exit path.
    #[test]
    fn refuses_when_the_return_reads_the_deleted_index() {
        let f = exit_fixture(two_link_chain(), vec![], &[X0]);
        assert_declines(f, "ret implicitly reads x0, the deleted add's result");
    }

    /// The deleted value can also be read INSIDE the load's block, before the
    /// load: two loads share one `lsl`. The first load's index is live (the
    /// second reads it) and is refused, but the second's liveness walk starts
    /// after the second load and never sees the first reader. Folding it deletes
    /// the `lsl` the first load still reads.
    #[test]
    fn refuses_when_an_earlier_load_in_the_block_shares_the_index() {
        let f = exit_fixture(
            vec![
                (
                    AArch64Opcode::LslRI,
                    vec![p(X1), p(X2), MachOperand::Imm(2)],
                ),
                (AArch64Opcode::LdrRO, vec![p(X4), p(X21), p(X1)]),
                (AArch64Opcode::LdrRO, vec![p(X3), p(X22), p(X1)]),
            ],
            vec![],
            &[],
        );
        assert_declines(f, "the first load reads x1 before the folded one");
    }

    /// The same, for the two-link chain's carrier: x1 is read between the
    /// `lsl` and the `add`, where no liveness walk looked.
    #[test]
    fn refuses_when_the_carrier_is_read_before_its_add() {
        let f = exit_fixture(
            vec![
                (
                    AArch64Opcode::LslRI,
                    vec![p(X1), p(X2), MachOperand::Imm(2)],
                ),
                (AArch64Opcode::LdrRO, vec![p(X4), p(X21), p(X1)]),
                (AArch64Opcode::AddRR, vec![p(X0), p(X1), p(X20)]),
                (AArch64Opcode::LdrRO, vec![p(X3), p(X22), p(X0)]),
            ],
            vec![],
            &[],
        );
        assert_declines(f, "a load reads the carrier x1 before the add");
    }

    /// Does any instruction of `f` write X16 (or W16) through operand 0?
    fn writes_x16(f: &MachFunction) -> bool {
        f.blocks
            .iter()
            .flat_map(|b| b.insts.iter())
            .any(|&i| def_preg(f, i).is_some_and(|d| regs_overlap(d, X16)))
    }

    /// ★ REGRESSION (refuter reproduction): a `Trap*` carrier names no X16
    /// operand, but Phase 7.25 expands it AFTER this pass, and the expansions
    /// write X16 -- `MOVZ X16,#bound` for a bounds bound above the CMP
    /// immediate, `UMULH X16` for a 64-bit unsigned-mul overflow check. A
    /// walking pointer parked in X16 across the loop is destroyed by the next
    /// iteration's check.
    #[test]
    fn refuses_when_the_loop_holds_a_trap_carrier_that_expands_into_x16() {
        use trust_cg_ir::{OverflowOp, pack_overflow_tag};
        for (op, ops) in [
            (
                AArch64Opcode::TrapBoundsCheckExact,
                vec![p(X22), p(X2), MachOperand::Imm(5000)],
            ),
            (
                AArch64Opcode::TrapOverflowExact,
                vec![
                    p(X4),
                    p(X21),
                    MachOperand::Imm(pack_overflow_tag(OverflowOp::UnsignedMul, 64)),
                ],
            ),
        ] {
            let f = loop_fixture(vec![(op, ops.clone())]);
            // Ground the hazard in the real expanders, not in this test's word.
            let mut expanded = f.clone();
            assert!(!writes_x16(&expanded), "{op:?}: fixture writes no X16 yet");
            crate::lower::expand_trap_bounds_check_exact(&mut expanded);
            crate::lower::expand_trap_overflow_exact(&mut expanded);
            assert!(writes_x16(&expanded), "{op:?}: its expansion writes X16");
            assert_declines(f, &format!("{op:?} in the loop expands into X16"));
        }
    }

    /// The seed is inserted BEFORE the preheader's terminator run, and AArch64
    /// stamps every `Trap*` carrier `IS_TERMINATOR`: a carrier at the end of
    /// the preheader lands AFTER the seed, so its later `MOVZ X16` overwrites
    /// the pointer before the loop's first load.
    #[test]
    fn refuses_when_the_preheader_tail_holds_a_trap_carrier() {
        let mut f = loop_fixture(vec![]);
        let pre = f.entry;
        let carrier = inst(
            &mut f,
            AArch64Opcode::TrapBoundsCheckExact,
            vec![p(X22), p(X2), MachOperand::Imm(5000)],
        );
        let at = f.blocks[pre.0 as usize].insts.len() - 1; // before `b head`
        f.blocks[pre.0 as usize].insts.insert(at, carrier);
        assert!(f.insts[carrier.0 as usize].is_terminator());
        assert_declines(
            f,
            "the preheader's trailing carrier writes X16 after the seed",
        );
    }

    /// `chain` with its `LdrRO` given transfer register `dst` and the
    /// 4-operand register-offset mode `mode` (`Imm(6)`: LSL #0, `Imm(7)`: LSL
    /// by log2 of the transfer size -- see `aarch64::encode::register_offset_mode`).
    fn with_load_mode(
        chain: Vec<(AArch64Opcode, Vec<MachOperand>)>,
        dst: PReg,
        mode: i64,
    ) -> Vec<(AArch64Opcode, Vec<MachOperand>)> {
        chain
            .into_iter()
            .map(|(op, mut ops)| {
                if op == AArch64Opcode::LdrRO {
                    ops[0] = p(dst);
                    ops.push(MachOperand::Imm(mode));
                }
                (op, ops)
            })
            .collect()
    }

    /// ★ REGRESSION (refuter reproduction): `Imm(7)` is `LSL #log2(size)`, so
    /// after `lsl x1,x2,#2` the load `ldr w3,[x22,x1,lsl #2]` reads
    /// `x22 + 16*x2` (`x22 + 32*x2` for an X transfer). The fold admitted the
    /// mode, then seeded `X16 = x22 + (x2 << 2)` and stepped it by 4 -- a walk
    /// over `a[k]` instead of `a[4k]` -- because nothing after the operand
    /// check read the mode again.
    #[test]
    fn refuses_the_scaled_register_offset_form() {
        for (chain, links) in [(one_link_chain(), "one"), (two_link_chain(), "two")] {
            for dst in [W3, X3] {
                let f = exit_fixture(with_load_mode(chain.clone(), dst, 7), vec![], &[]);
                assert_declines(
                    f,
                    &format!("{links}-link chain, {dst:?} load scales its index by the size"),
                );
            }
        }
    }

    /// Positive control for the test above: the UNSHIFTED LSL mode `Imm(6)`
    /// addresses exactly what the 3-operand form does, so it still folds.
    #[test]
    fn folds_the_unshifted_lsl_register_offset_form() {
        for chain in [one_link_chain(), two_link_chain()] {
            for dst in [W3, X3] {
                let mut f = exit_fixture(with_load_mode(chain.clone(), dst, 6), vec![], &[]);
                assert_eq!(form_post_index_loads(&mut f).folded, 1, "{dst:?}");
            }
        }
    }

    /// `add x2,x2,#1` -- the IV's unit step.
    fn iv_step() -> (AArch64Opcode, Vec<MachOperand>) {
        (
            AArch64Opcode::AddRI,
            vec![p(X2), p(X2), MachOperand::Imm(1)],
        )
    }

    /// A loop with a conditional ARM between the load and the latch:
    ///
    /// ```text
    ///   pre:   mov x2, #0 ; b head
    ///   head:  lsl x1,x2,#2 ; add x0,x1,x20 ; ldr x3,[x22,x0] ; cbz x3,latch ; b arm
    ///   arm:   <arm> ; b latch               <- runs on SOME iterations only
    ///   latch: <latch> ; b.cond head ; b exit
    ///   exit:  ret
    /// ```
    fn arm_fixture(
        arm: Vec<(AArch64Opcode, Vec<MachOperand>)>,
        latch: Vec<(AArch64Opcode, Vec<MachOperand>)>,
    ) -> MachFunction {
        let mut f = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let pre = f.entry;
        let head = f.create_block();
        let arm_b = f.create_block();
        let latch_b = f.create_block();
        let exit = f.create_block();

        let i = inst(
            &mut f,
            AArch64Opcode::MovI,
            vec![p(X2), MachOperand::Imm(0)],
        );
        f.append_inst(pre, i);
        let i = inst(&mut f, AArch64Opcode::B, vec![MachOperand::Block(head)]);
        f.append_inst(pre, i);

        for (op, ops) in two_link_chain().into_iter().chain([
            (AArch64Opcode::Cbz, vec![p(X3), MachOperand::Block(latch_b)]),
            (AArch64Opcode::B, vec![MachOperand::Block(arm_b)]),
        ]) {
            let i = inst(&mut f, op, ops);
            f.append_inst(head, i);
        }
        for (op, ops) in arm
            .into_iter()
            .chain([(AArch64Opcode::B, vec![MachOperand::Block(latch_b)])])
        {
            let i = inst(&mut f, op, ops);
            f.append_inst(arm_b, i);
        }
        for (op, ops) in latch.into_iter().chain([
            (AArch64Opcode::BCond, vec![MachOperand::Block(head)]),
            (AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        ]) {
            let i = inst(&mut f, op, ops);
            f.append_inst(latch_b, i);
        }
        let i = inst(&mut f, AArch64Opcode::Ret, vec![]);
        f.append_inst(exit, i);
        install_edges(&mut f);
        f
    }

    /// ★ REGRESSION (refuter reproduction): the IV's one `add x2,x2,#1` sits on
    /// a conditional arm, so `x2` advances only on iterations that take it,
    /// while a post-indexed load would advance the pointer on EVERY iteration
    /// -- reading `a[j]` instead of `a[k]` from the first skipped arm on. The
    /// step count and the unit-step test were taken over the whole body, and
    /// the increment-before-load walk from the arm never reaches the header.
    #[test]
    fn refuses_when_the_iv_steps_only_on_a_conditional_arm() {
        let f = arm_fixture(vec![iv_step()], vec![]);
        assert_declines(f, "x2 steps only on iterations that take the arm");
    }

    /// Positive control for the test above: the same loop with the increment in
    /// the latch, which every iteration passes through, still folds.
    #[test]
    fn folds_when_the_iv_steps_in_the_latch_past_an_arm() {
        let mut f = arm_fixture(vec![], vec![iv_step()]);
        assert_eq!(form_post_index_loads(&mut f).folded, 1);
    }

    /// A loop whose body holds the two-entry cycle `{arm, inner}`:
    ///
    /// ```text
    ///   pre:   mov x2, #0 ; b head
    ///   head:  <head> ; cbz x4, inner ; b arm
    ///   arm:   add x4,x4,#1 ; b inner
    ///   inner: <inner> ; cbnz x4, arm ; b latch    <- `cbnz` only with `cycle`
    ///   latch: <latch> ; b.cond head ; b exit
    ///   exit:  ret
    /// ```
    ///
    /// With `cycle`, neither `arm` nor `inner` dominates the other, so the
    /// cycle has no dominator back-edge and the loop at `head` is the only,
    /// innermost, loop. `inner` dominates the latch, so it passes the
    /// once-per-iteration test, yet `head -> inner -> arm -> inner` runs it
    /// twice. Without `cycle`, `arm` is a plain conditional arm.
    fn two_entry_cycle_fixture(
        head: Vec<(AArch64Opcode, Vec<MachOperand>)>,
        inner: Vec<(AArch64Opcode, Vec<MachOperand>)>,
        latch: Vec<(AArch64Opcode, Vec<MachOperand>)>,
        cycle: bool,
    ) -> MachFunction {
        let mut f = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let pre = f.entry;
        let head_b = f.create_block();
        let arm_b = f.create_block();
        let inner_b = f.create_block();
        let latch_b = f.create_block();
        let exit = f.create_block();

        let i = inst(
            &mut f,
            AArch64Opcode::MovI,
            vec![p(X2), MachOperand::Imm(0)],
        );
        f.append_inst(pre, i);
        let i = inst(&mut f, AArch64Opcode::B, vec![MachOperand::Block(head_b)]);
        f.append_inst(pre, i);

        for (op, ops) in head.into_iter().chain([
            (AArch64Opcode::Cbz, vec![p(X4), MachOperand::Block(inner_b)]),
            (AArch64Opcode::B, vec![MachOperand::Block(arm_b)]),
        ]) {
            let i = inst(&mut f, op, ops);
            f.append_inst(head_b, i);
        }
        for (op, ops) in [
            (
                AArch64Opcode::AddRI,
                vec![p(X4), p(X4), MachOperand::Imm(1)],
            ),
            (AArch64Opcode::B, vec![MachOperand::Block(inner_b)]),
        ] {
            let i = inst(&mut f, op, ops);
            f.append_inst(arm_b, i);
        }
        let back_to_arm =
            cycle.then(|| (AArch64Opcode::Cbnz, vec![p(X4), MachOperand::Block(arm_b)]));
        for (op, ops) in inner
            .into_iter()
            .chain(back_to_arm)
            .chain([(AArch64Opcode::B, vec![MachOperand::Block(latch_b)])])
        {
            let i = inst(&mut f, op, ops);
            f.append_inst(inner_b, i);
        }
        for (op, ops) in latch.into_iter().chain([
            (AArch64Opcode::BCond, vec![MachOperand::Block(head_b)]),
            (AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        ]) {
            let i = inst(&mut f, op, ops);
            f.append_inst(latch_b, i);
        }
        let i = inst(&mut f, AArch64Opcode::Ret, vec![]);
        f.append_inst(exit, i);
        install_edges(&mut f);
        f
    }

    /// The head's load runs once per iteration, but `add x2,x2,#1` sits on the
    /// irreducible cycle and runs twice on iterations that take it, so `x2`
    /// moves two elements while a post-indexed pointer would move one.
    #[test]
    fn refuses_when_an_irreducible_cycle_runs_the_iv_step_twice() {
        let f = two_entry_cycle_fixture(two_link_chain(), vec![iv_step()], vec![], true);
        assert_declines(f, "x2 steps on a block an irreducible cycle runs twice");
    }

    /// The load sits on the irreducible cycle and reads the same `x2` twice on
    /// iterations that take it, while `x2` steps once in the latch, so a
    /// post-indexed pointer would move two elements per iteration.
    #[test]
    fn refuses_when_an_irreducible_cycle_runs_the_load_twice() {
        let f = two_entry_cycle_fixture(vec![], two_link_chain(), vec![iv_step()], true);
        assert_declines(
            f,
            "the load sits on a block an irreducible cycle runs twice",
        );
    }

    /// Positive control for the two refusals above: the same loops without the
    /// `inner -> arm` edge fold, so each refusal is caused by the cycle.
    #[test]
    fn folds_the_two_entry_shapes_once_the_cycle_is_gone() {
        let mut f = two_entry_cycle_fixture(two_link_chain(), vec![iv_step()], vec![], false);
        assert_eq!(
            form_post_index_loads(&mut f).folded,
            1,
            "IV stepped in inner"
        );
        let mut f = two_entry_cycle_fixture(vec![], two_link_chain(), vec![iv_step()], false);
        assert_eq!(form_post_index_loads(&mut f).folded, 1, "load in inner");
    }
}
