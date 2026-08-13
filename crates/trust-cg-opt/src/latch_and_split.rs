// trust-cg-opt - Hot-latch AND branch-condition splitting.
//
//! clang -O1 collapses a short-circuit `a && b` loop-latch condition into
//! `%t = and i1 %a, %b; br i1 %t, THEN, ELSE`, which tcg lowers faithfully to
//!   `cmp; cset a; cmp; cset b; and t,a,b; cbnz t, THEN; b ELSE`
//! — ONE combined, hard-to-predict branch plus a serial `cset -> and -> cbnz`
//! dependency chain. clang -O3 RE-SPLITS the `and` back into two separately-
//! predictable conditional branches. On the recursive-backtracker exec tail
//! (Queens/Puzzle) the combined branch is the measured loss: same instruction
//! count as clang, ~1.5x slower, and the spill/addressing angle is dead (three
//! independent 0% falsifications — see the allocator-quality diagnosis note).
//!
//! This pass performs clang -O3's split for hot loop latches, rewriting
//!   B:    cmp_x ; b.<!cc_x> ELSE ; b MID        (short-circuit early exit)
//!   MID:  cmp_y ; b.<cc_y>  THEN ; b ELSE
//! so each condition is predicted independently and the serial chain is gone.
//!
//! SOUND: `and` is commutative and this is the textbook short-circuit expansion
//! of `THEN <= a && b`. The only non-local effect is control flow: THEN is now
//! reached from MID (not B) and ELSE from BOTH B and MID, so the pred-keyed
//! `Phi` operand pairs in THEN (`Block(B) -> Block(MID)`) and ELSE (append the
//! `Block(B)` value under `Block(MID)`) are rewritten here; `phi_elim` later
//! materialises the parallel copies on the actual edges.
//!
//! GATED, fail-closed on every departure from the exact shape:
//!  * B must lie ON A CYCLE (a successor of B reaches B again) — the "runs every
//!    iteration" signal. Rotated importer loops carry this combined test in the
//!    header, whose taken edge enters the body (a FORWARD edge), so a backedge
//!    test would wrongly reject it; cycle membership is robust to layout.
//!  * the terminator is exactly `cmp; cset; cmp; cset; and; cbnz; b` (the last
//!    seven instructions of B) with each boolean single-def AND used ONLY by the
//!    `and`/`cbnz` (checked over the live CFG, so no other consumer / not
//!    live-out); the `and` combines exactly the two `cset` results.
//!  * both compares are pure-flag compares feeding their `cset`.
//!  * PROFILE GATE (2026-07-23, the resurrection this pass's history demanded):
//!    the pass carries an `Option<ProfileHotness>`. With NO profile it is
//!    INERT — the default compile stays byte-identical. With a profile, the
//!    `cbnz -> THEN` edge's observed taken rate `r` must resolve
//!    ([`ProfileHotness::branch_taken_rate`], fail-safe `None` on any block the
//!    canary never saw — e.g. blocks minted by a later USE-mode pass) and lie
//!    in the UNPREDICTABLE band `0.15 <= r <= 0.85`. Outside the band the
//!    combined branch predicts well and the split only adds a branch
//!    (the measured Treesort +8.7% regression class).
//!    Kill switch: `TCG_NO_LATCH_AND_SPLIT`.
//!
//! HISTORY (2026-07-22): built + validated on HEAD 8a80f586 — torture 1066
//! PASS / 0 MISCOMPILE, output byte-identical to clang on Queens, fires as
//! designed (Queens Try `and` 1->0). DROPPED unconditionally-enabled per
//! measured-net-positive: amplified compact Queens -5.4% (real) but shipped
//! Queens +0.2% flat and Treesort +8.7% REGRESSION (its combined condition is
//! well-predicted; the split only adds a branch). The split pays off ONLY on
//! unpredictable/favorably-biased combined branches — indistinguishable at
//! compile time. RESURRECTED BEHIND THE PROFILE GATE above: fire only where
//! profile data shows the combined condition unpredictable, and use the bias
//! to order the two tests so the hot path falls through (see
//! TCG_LATCH_SPLIT_SWAP).

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, VReg,
};

use crate::pass_manager::MachinePass;
use crate::pgo::ProfileHotness;

/// AArch64 hot-latch AND-condition branch split (profile-gated).
pub struct LatchAndSplit {
    /// Hotness summary from a loaded `.profdata`. `None` (no profile) leaves
    /// the pass inert, preserving default byte-identity.
    hotness: Option<ProfileHotness>,
}

impl LatchAndSplit {
    /// Construct the pass. Without a profile the pass never fires.
    pub fn new(hotness: Option<ProfileHotness>) -> Self {
        Self { hotness }
    }
}

impl MachinePass for LatchAndSplit {
    fn name(&self) -> &str {
        "latch-and-split"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_latch_and_split(func, self.hotness.as_ref())
    }
}

fn enabled() -> bool {
    std::env::var_os("TCG_NO_LATCH_AND_SPLIT").is_none()
}

/// When set, flip whichever test order the profile chose (default: the SECOND
/// cset's condition — the compare nearest the branch, empirically the
/// loop-bound / predictable one — is tested first as the early exit; a
/// short-circuit-dominant profile `r <= 0.5` flips to the FIRST cset, the
/// likelier-false data condition). Exists to A/B the ordering.
fn swap_order() -> bool {
    std::env::var_os("TCG_LATCH_SPLIT_SWAP").is_some()
}

/// Opt-in decision log (`TCG_LATCH_SPLIT_LOG=1`): one stderr line per
/// candidate that reaches the profile gate, recording the observed taken rate
/// and the verdict. Off by default so compiles stay silent.
fn log_decisions() -> bool {
    std::env::var_os("TCG_LATCH_SPLIT_LOG").is_some()
}

/// The unpredictable band: fire only when the combined `cbnz -> THEN` edge is
/// taken between 15% and 85% of executions. Outside it the hardware predictor
/// already wins and the split just adds a branch.
const TAKEN_RATE_LO: f64 = 0.15;
const TAKEN_RATE_HI: f64 = 0.85;

fn run_latch_and_split(func: &mut MachFunction, hotness: Option<&ProfileHotness>) -> bool {
    if !enabled() {
        return false;
    }
    // NO profile -> inert. This is the default-path byte-identity guarantee:
    // the pass is scheduled unconditionally at O2/O3 but can only transform
    // when a canary profile was explicitly attached.
    let Some(hotness) = hotness else {
        return false;
    };
    let mut any = false;
    // Each application strictly replaces one combined latch with a split that no
    // longer matches the recogniser, so a productive sweep cannot re-fire on the
    // same block; the block count bounds the loop.
    let cap = func.blocks.len() + 1;
    for _ in 0..cap {
        match find_split(func, hotness) {
            Some(plan) => {
                apply_split(func, plan);
                any = true;
            }
            None => break,
        }
    }
    any
}

/// A validated split site. All ids/vregs are captured read-only; `apply_split`
/// performs the mutation.
struct SplitPlan {
    b: BlockId,
    then_blk: BlockId,
    else_blk: BlockId,
    /// Number of instructions to keep at the head of B (the tail 7 are replaced).
    prefix_len: usize,
    /// Compare re-emitted in B (the early-exit test) and its take-THEN cond.
    x_cmp: InstId,
    x_cond: CondCode,
    /// Compare re-emitted in MID and its take-THEN cond.
    y_cmp: InstId,
    y_cond: CondCode,
}

fn as_vreg(op: &MachOperand) -> Option<VReg> {
    match op {
        MachOperand::VReg(v) => Some(*v),
        _ => None,
    }
}
fn as_block(op: &MachOperand) -> Option<BlockId> {
    match op {
        MachOperand::Block(b) => Some(*b),
        _ => None,
    }
}
fn as_imm(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::Imm(i) => Some(*i),
        _ => None,
    }
}

fn is_pure_flag_compare(op: AArch64Opcode) -> bool {
    matches!(
        op,
        AArch64Opcode::CmpRR
            | AArch64Opcode::CmpRI
            | AArch64Opcode::CMPWrr
            | AArch64Opcode::CMPXrr
            | AArch64Opcode::CMPWri
            | AArch64Opcode::CMPXri
    )
}

fn decode_cond(enc: i64) -> Option<CondCode> {
    Some(match enc as u8 {
        0 => CondCode::EQ,
        1 => CondCode::NE,
        2 => CondCode::HS,
        3 => CondCode::LO,
        4 => CondCode::MI,
        5 => CondCode::PL,
        6 => CondCode::VS,
        7 => CondCode::VC,
        8 => CondCode::HI,
        9 => CondCode::LS,
        10 => CondCode::GE,
        11 => CondCode::LT,
        12 => CondCode::GT,
        13 => CondCode::LE,
        _ => return None, // AL/NV never carry a meaningful sense for a split.
    })
}

/// Total number of explicit-operand appearances of `v` across the LIVE CFG
/// (defs AND uses in instructions still referenced by a block — the arena also
/// holds dead insts orphaned by earlier passes, e.g. the `CmpRI t,#0` that
/// `cmp_branch_fusion` drops when it forms `Cbnz t`, so counting the raw arena
/// over-approximates). For a boolean defined once and consumed once this is
/// exactly 2 — anything else means an extra live consumer we must not orphan.
fn total_operand_appearances(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut m: HashMap<VReg, u32> = HashMap::new();
    for &block in &func.block_order {
        for &iid in &func.blocks[block.0 as usize].insts {
            for op in &func.inst(iid).operands {
                if let MachOperand::VReg(v) = op {
                    *m.entry(*v).or_insert(0) += 1;
                }
            }
        }
    }
    m
}

fn find_split(func: &MachFunction, hotness: &ProfileHotness) -> Option<SplitPlan> {
    let appearances = total_operand_appearances(func);

    for &b in func.block_order.iter() {
        let insts = &func.blocks[b.0 as usize].insts;
        let n = insts.len();
        if n < 7 {
            continue;
        }
        let tail = &insts[n - 7..];
        let cmp_a = func.inst(tail[0]);
        let cset_a = func.inst(tail[1]);
        let cmp_b = func.inst(tail[2]);
        let cset_b = func.inst(tail[3]);
        let and = func.inst(tail[4]);
        let cbnz = func.inst(tail[5]);
        let b_else = func.inst(tail[6]);

        // Exact opcode shape.
        if !is_pure_flag_compare(cmp_a.opcode)
            || cset_a.opcode != AArch64Opcode::CSet
            || !is_pure_flag_compare(cmp_b.opcode)
            || cset_b.opcode != AArch64Opcode::CSet
            || and.opcode != AArch64Opcode::AndRR
            || cbnz.opcode != AArch64Opcode::Cbnz
            || b_else.opcode != AArch64Opcode::B
        {
            continue;
        }
        if cset_a.operands.len() < 2 || cset_b.operands.len() < 2 || and.operands.len() != 3 {
            continue;
        }

        let (Some(a), Some(cca)) = (
            as_vreg(&cset_a.operands[0]),
            as_imm(&cset_a.operands[1]).and_then(decode_cond),
        ) else {
            continue;
        };
        let (Some(bb), Some(ccb)) = (
            as_vreg(&cset_b.operands[0]),
            as_imm(&cset_b.operands[1]).and_then(decode_cond),
        ) else {
            continue;
        };
        let (Some(t), Some(s1), Some(s2)) = (
            as_vreg(&and.operands[0]),
            as_vreg(&and.operands[1]),
            as_vreg(&and.operands[2]),
        ) else {
            continue;
        };
        // `and` must combine exactly the two cset booleans.
        if !((s1 == a && s2 == bb) || (s1 == bb && s2 == a)) {
            continue;
        }
        // `cbnz` must test the `and` result and target THEN; `b` gives ELSE.
        let (Some(ct), Some(then_blk)) =
            (as_vreg(&cbnz.operands[0]), as_block(cbnz.operands.get(1)?))
        else {
            continue;
        };
        if ct != t {
            continue;
        }
        let Some(else_blk) = as_block(&b_else.operands[0]) else {
            continue;
        };
        if then_blk == else_blk {
            continue;
        }

        // Booleans must be single-def/single-use: `a`,`bb` appear exactly twice
        // (cset def + and use), `t` exactly twice (and def + cbnz use). Anything
        // else means another consumer (or live-out) we must not orphan.
        if appearances.get(&a).copied().unwrap_or(0) != 2
            || appearances.get(&bb).copied().unwrap_or(0) != 2
            || appearances.get(&t).copied().unwrap_or(0) != 2
        {
            continue;
        }

        // Hot gate: B must be INSIDE A LOOP (reachable from itself). Rotated
        // importer loops put this combined test in the header, whose taken edge
        // enters the body (a forward edge, not a back edge) — so a backedge test
        // is wrong; cycle membership is the robust "runs every iteration" signal.
        if !block_in_cycle(func, b) {
            continue;
        }

        // PROFILE GATE: the combined `cbnz -> THEN` edge must have an observed
        // taken rate, and it must sit in the unpredictable band. `None`
        // (unprofiled function, zero-hit or post-canary-minted block,
        // unresolvable flow) fails SAFE — no split.
        let Some(rate) = hotness.branch_taken_rate(&func.name, func, b, then_blk) else {
            continue;
        };
        let in_band = (TAKEN_RATE_LO..=TAKEN_RATE_HI).contains(&rate);
        if log_decisions() {
            eprintln!(
                "[latch-and-split] func={} block={} then={} taken_rate={:.4} verdict={}",
                func.name,
                b.0,
                then_blk.0,
                rate,
                if in_band {
                    "SPLIT"
                } else {
                    "skip(predictable)"
                }
            );
        }
        if !in_band {
            continue;
        }

        // Map the two (cmp, cset-cond) pairs to and-operand identity. Pair-A is
        // (cmp_a, cca) defining `a`; pair-B is (cmp_b, ccb) defining `bb`.
        //
        // Ordering: block counters give the COMBINED rate `r` only — the two
        // conditions' individual truth rates are not observable (edge/condition
        // profiles are a schema-v1 `edges` follow-up). The static prior from the
        // measured builds is that pair-B (the compare nearest the branch) is the
        // guard/bound-like, usually-true test. When `r <= 0.5` the combined AND
        // mostly FAILS, and under that prior the falseness lives in pair-A — so
        // test pair-A first to short-circuit sooner. When `r > 0.5` keep the
        // default (pair-B first). `TCG_LATCH_SPLIT_SWAP` flips the chosen order
        // for A/B measurement.
        let profile_first_a = rate <= 0.5;
        let first_a = profile_first_a ^ swap_order();
        let (x_cmp, x_cond, y_cmp, y_cond) = if first_a {
            (tail[0], cca, tail[2], ccb)
        } else {
            (tail[2], ccb, tail[0], cca)
        };
        if log_decisions() {
            eprintln!(
                "[latch-and-split] func={} block={} order={} (profile_first_a={} swap_env={})",
                func.name,
                b.0,
                if first_a {
                    "pair-A-first"
                } else {
                    "pair-B-first"
                },
                profile_first_a,
                swap_order()
            );
        }

        return Some(SplitPlan {
            b,
            then_blk,
            else_blk,
            prefix_len: n - 7,
            x_cmp,
            x_cond,
            y_cmp,
            y_cond,
        });
    }
    None
}

/// True if `b` lies on a cycle: some successor of `b` can reach `b` again.
/// (A block that runs on every loop iteration — header or latch — satisfies
/// this; straight-line code does not.)
fn block_in_cycle(func: &MachFunction, b: BlockId) -> bool {
    use std::collections::VecDeque;
    let mut seen = vec![false; func.blocks.len()];
    let mut q: VecDeque<BlockId> = func.blocks[b.0 as usize].succs.iter().copied().collect();
    while let Some(x) = q.pop_front() {
        if x == b {
            return true;
        }
        let xi = x.0 as usize;
        if xi >= seen.len() || seen[xi] {
            continue;
        }
        seen[xi] = true;
        for &s in &func.blocks[xi].succs {
            q.push_back(s);
        }
    }
    false
}

fn clone_inst(func: &MachFunction, id: InstId) -> MachInst {
    let src = func.inst(id);
    let mut c = MachInst::new(src.opcode, src.operands.clone());
    c.source_loc = src.source_loc;
    c
}

fn apply_split(func: &mut MachFunction, plan: SplitPlan) {
    let SplitPlan {
        b,
        then_blk,
        else_blk,
        prefix_len,
        x_cmp,
        x_cond,
        y_cmp,
        y_cond,
    } = plan;

    // Re-emit the two compares (fresh copies; the originals are orphaned).
    let x_cmp_i = clone_inst(func, x_cmp);
    let y_cmp_i = clone_inst(func, y_cmp);
    let b_xcmp = func.push_inst(x_cmp_i);
    // B: if NOT the early-exit condition -> ELSE (short circuit); else fall to MID.
    let b_bcond = func.push_inst(MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(x_cond.invert().encoding() as i64),
            MachOperand::Block(else_blk),
        ],
    ));

    let mid = func.create_block();

    let b_bmid = func.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(mid)],
    ));
    let m_ycmp = func.push_inst(y_cmp_i);
    let m_bcond = func.push_inst(MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(y_cond.encoding() as i64),
            MachOperand::Block(then_blk),
        ],
    ));
    let m_belse = func.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(else_blk)],
    ));

    // Rewrite B: keep the prefix, replace the 7-inst tail with the split test.
    {
        let blk = &mut func.blocks[b.0 as usize];
        blk.insts.truncate(prefix_len);
        blk.insts.extend_from_slice(&[b_xcmp, b_bcond, b_bmid]);
        // Successor convention (matches ISel): BCond target first, B target next.
        blk.succs = vec![else_blk, mid];
    }
    // Populate MID.
    let then_depth = func.blocks[then_blk.0 as usize].loop_depth;
    {
        let m = &mut func.blocks[mid.0 as usize];
        m.insts = vec![m_ycmp, m_bcond, m_belse];
        m.preds = vec![b];
        m.succs = vec![then_blk, else_blk];
        m.loop_depth = then_depth;
    }
    // THEN now reached from MID instead of B.
    for p in &mut func.blocks[then_blk.0 as usize].preds {
        if *p == b {
            *p = mid;
        }
    }
    // ELSE reached from BOTH B (still) and MID (new).
    func.blocks[else_blk.0 as usize].preds.push(mid);

    // Phi fixup — THEN: pred B becomes MID.
    rewrite_phi_pred(func, then_blk, b, mid);
    // Phi fixup — ELSE: duplicate B's incoming value under the new MID pred.
    duplicate_phi_pred(func, else_blk, b, mid);

    // Place MID right after B in layout order (create_block appended it to end).
    func.block_order.retain(|&x| x != mid);
    if let Some(pos) = func.block_order.iter().position(|&x| x == b) {
        func.block_order.insert(pos + 1, mid);
    } else {
        func.block_order.push(mid);
    }
}

/// In every `Phi` of `block`, rewrite the predecessor `old` to `new` (values
/// unchanged). Phi operands: `[def, v0, Block(p0), v1, Block(p1), ...]`.
fn rewrite_phi_pred(func: &mut MachFunction, block: BlockId, old: BlockId, new: BlockId) {
    let inst_ids = func.blocks[block.0 as usize].insts.clone();
    for id in inst_ids {
        let inst = &mut func.insts[id.0 as usize];
        if inst.opcode != AArch64Opcode::Phi {
            continue;
        }
        let mut i = 2;
        while i < inst.operands.len() {
            if let MachOperand::Block(p) = inst.operands[i]
                && p == old
            {
                inst.operands[i] = MachOperand::Block(new);
            }
            i += 2;
        }
    }
}

/// In every `Phi` of `block`, append `(value_from `old`, Block(new))` so the new
/// `new -> block` edge supplies the same value the `old -> block` edge did.
fn duplicate_phi_pred(func: &mut MachFunction, block: BlockId, old: BlockId, new: BlockId) {
    let inst_ids = func.blocks[block.0 as usize].insts.clone();
    for id in inst_ids {
        let inst = &mut func.insts[id.0 as usize];
        if inst.opcode != AArch64Opcode::Phi {
            continue;
        }
        // Find the (value, Block(old)) pair.
        let mut found_val: Option<MachOperand> = None;
        let mut i = 2;
        while i < inst.operands.len() {
            if let MachOperand::Block(p) = inst.operands[i]
                && p == old
            {
                found_val = Some(inst.operands[i - 1].clone());
                break;
            }
            i += 2;
        }
        if let Some(val) = found_val {
            inst.operands.push(val);
            inst.operands.push(MachOperand::Block(new));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pgo::{BlockProfile, FunctionProfile, ProfData};
    use trust_cg_ir::Signature;

    /// Build the exact recognised shape: a 2-block cycle where HEADER ends in
    /// `cmp;cset;cmp;cset;and;cbnz THEN;b ELSE`, THEN is the body (backedge to
    /// HEADER) and ELSE is the exit.
    fn combined_latch_func(name: &str) -> MachFunction {
        let mut f = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let header = f.entry; // B0
        let then_blk = f.create_block(); // B1 (body, loops back)
        let else_blk = f.create_block(); // B2 (exit)

        let va = VReg::new(f.alloc_vreg(), trust_cg_ir::RegClass::Gpr32);
        let vb = VReg::new(f.alloc_vreg(), trust_cg_ir::RegClass::Gpr32);
        let vt = VReg::new(f.alloc_vreg(), trust_cg_ir::RegClass::Gpr32);
        let vx = VReg::new(f.alloc_vreg(), trust_cg_ir::RegClass::Gpr32);
        let vy = VReg::new(f.alloc_vreg(), trust_cg_ir::RegClass::Gpr32);

        let push = |f: &mut MachFunction, block, op, operands: Vec<MachOperand>| {
            let id = f.push_inst(MachInst::new(op, operands));
            f.append_inst(block, id);
        };

        push(
            &mut f,
            header,
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(vx), MachOperand::Imm(5)],
        );
        push(
            &mut f,
            header,
            AArch64Opcode::CSet,
            vec![
                MachOperand::VReg(va),
                MachOperand::Imm(CondCode::LT.encoding() as i64),
            ],
        );
        push(
            &mut f,
            header,
            AArch64Opcode::CmpRR,
            vec![MachOperand::VReg(vy), MachOperand::VReg(vx)],
        );
        push(
            &mut f,
            header,
            AArch64Opcode::CSet,
            vec![
                MachOperand::VReg(vb),
                MachOperand::Imm(CondCode::NE.encoding() as i64),
            ],
        );
        push(
            &mut f,
            header,
            AArch64Opcode::AndRR,
            vec![
                MachOperand::VReg(vt),
                MachOperand::VReg(va),
                MachOperand::VReg(vb),
            ],
        );
        push(
            &mut f,
            header,
            AArch64Opcode::Cbnz,
            vec![MachOperand::VReg(vt), MachOperand::Block(then_blk)],
        );
        push(
            &mut f,
            header,
            AArch64Opcode::B,
            vec![MachOperand::Block(else_blk)],
        );

        push(
            &mut f,
            then_blk,
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        );
        push(&mut f, else_blk, AArch64Opcode::Ret, vec![]);

        f.add_edge(header, then_blk);
        f.add_edge(header, else_blk);
        f.add_edge(then_blk, header);
        f
    }

    fn profile_with_rate(name: &str, header: u64, then_hits: u64, exit_hits: u64) -> ProfData {
        let mut p = ProfData::new(0xfeed);
        let mut fp = FunctionProfile::new(name);
        fp.call_count = 1;
        fp.blocks.push(BlockProfile::new(0, header));
        fp.blocks.push(BlockProfile::new(1, then_hits));
        fp.blocks.push(BlockProfile::new(2, exit_hits));
        p.functions.push(fp);
        p
    }

    fn hotness(p: &ProfData) -> ProfileHotness {
        ProfileHotness::from_profile(p)
    }

    #[test]
    fn no_profile_is_inert() {
        let mut f = combined_latch_func("try");
        let before_blocks = f.blocks.len();
        let mut pass = LatchAndSplit::new(None);
        assert!(!pass.run(&mut f), "no profile must leave the pass inert");
        assert_eq!(f.blocks.len(), before_blocks);
    }

    #[test]
    fn unpredictable_band_fires() {
        let mut f = combined_latch_func("try");
        // 100 header executions, 50 -> THEN: r = 0.5, squarely in band.
        let p = profile_with_rate("try", 100, 50, 50);
        let mut pass = LatchAndSplit::new(Some(hotness(&p)));
        assert!(pass.run(&mut f), "in-band rate must split");
        // One new MID block; header now ends cmp/bcond/b.
        assert_eq!(f.blocks.len(), 4);
        let header_insts = &f.blocks[0].insts;
        assert_eq!(header_insts.len(), 3);
        assert_eq!(
            f.inst(header_insts[1]).opcode,
            AArch64Opcode::BCond,
            "split header early-exit"
        );
        // Idempotent: the split shape no longer matches.
        assert!(!pass.run(&mut f));
    }

    #[test]
    fn predictable_rate_skips() {
        // 100 header executions, 95 -> THEN: r = 0.95 > 0.85 — predictable.
        let mut f = combined_latch_func("try");
        let p = profile_with_rate("try", 100, 95, 5);
        let mut pass = LatchAndSplit::new(Some(hotness(&p)));
        assert!(!pass.run(&mut f), "out-of-band rate must not split");

        // And the almost-never-taken side.
        let mut f2 = combined_latch_func("try");
        let p2 = profile_with_rate("try", 100, 5, 95);
        let mut pass2 = LatchAndSplit::new(Some(hotness(&p2)));
        assert!(!pass2.run(&mut f2));
    }

    #[test]
    fn unprofiled_function_or_block_skips() {
        // Profile exists but for a DIFFERENT function name.
        let mut f = combined_latch_func("try");
        let p = profile_with_rate("other_fn", 100, 50, 50);
        let mut pass = LatchAndSplit::new(Some(hotness(&p)));
        assert!(!pass.run(&mut f), "unprofiled function must fail safe");

        // Profiled function, zero-hit header (canary never reached it).
        let mut f2 = combined_latch_func("try");
        let p2 = profile_with_rate("try", 0, 0, 0);
        let mut pass2 = LatchAndSplit::new(Some(hotness(&p2)));
        assert!(!pass2.run(&mut f2), "zero-hit block must fail safe");
    }

    #[test]
    fn profile_bias_chooses_test_order() {
        // r = 0.2 (<= 0.5): pair-A (the FIRST cset's compare, CmpRI #5 / LT)
        // is tested first in B.
        let mut f = combined_latch_func("try");
        let p = profile_with_rate("try", 100, 20, 80);
        let mut pass = LatchAndSplit::new(Some(hotness(&p)));
        assert!(pass.run(&mut f));
        let header_insts = &f.blocks[0].insts;
        assert_eq!(f.inst(header_insts[0]).opcode, AArch64Opcode::CmpRI);
        // B's early-exit BCond takes the INVERTED pair-A cond (LT -> GE).
        let bcond = f.inst(header_insts[1]);
        assert_eq!(
            bcond.operands[0],
            MachOperand::Imm(CondCode::GE.encoding() as i64)
        );

        // r = 0.8 (> 0.5): default order — pair-B (CmpRR / NE) first.
        let mut f2 = combined_latch_func("try");
        let p2 = profile_with_rate("try", 100, 80, 20);
        let mut pass2 = LatchAndSplit::new(Some(hotness(&p2)));
        assert!(pass2.run(&mut f2));
        let header_insts2 = &f2.blocks[0].insts;
        assert_eq!(f2.inst(header_insts2[0]).opcode, AArch64Opcode::CmpRR);
        let bcond2 = f2.inst(header_insts2[1]);
        assert_eq!(
            bcond2.operands[0],
            MachOperand::Imm(CondCode::EQ.encoding() as i64)
        );
    }
}
