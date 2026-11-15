// trust-cg-opt - SOUND NEON per-byte 8-bit-reverse memory-MAP vectorizer (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # NEON per-byte bit-reverse map vectorizer (`neon-bitrev`)
//!
//! Vectorizes the counted byte STORE (map) loop
//!
//! ```text
//! for i in 0..N (i <u N):   out[i] = a[i].reverse_bits()
//! ```
//!
//! over two `[u8; N]` arrays, into the LLVM-`-O3` shape
//! `ldp q,q / RBIT.16B (x4) / stp q,q` over 64-byte blocks, followed by the
//! UNTOUCHED scalar tail. `RBIT.16B` reverses the 8 bits WITHIN each of the 16
//! byte lanes (a bit never crosses a byte boundary), the FAITHFULLY-PROVEN
//! per-byte reversal (`trust-cg-verify::neon_lowering_proofs::proof_neon_rbitv_16b`,
//! `NeonRbitV`'s `opcode_to_proof_query` `"rbitv.16b per-byte-reverse-intent"`),
//! so a program emitting it PROMOTES at the coverage gate.
//!
//! The bridge lowers `u8::reverse_bits()` NOT to a scalar `RBIT` (there is no
//! 8-bit scalar RBIT — only `Wd`/`Xd`) but to the bit-by-bit isolate/shift/OR
//! ladder `bitmanip_reverse_bits(n=8)` run per element in a clean `I64`
//! (8x `AndRI(byte, 1<<i)` placed at bit `7-i` via `LslRI`/`LsrRI`, OR-combined).
//! This pass recognizes that EXACT ladder and lowers each 16-byte Q register to
//! one `RBIT.16B`.
//!
//! Runs immediately after [`crate::neon_map`] (the general elementwise map
//! vectorizer, whose `i32`/`i64` lane set and 2-block/chain shapes both MISS the
//! byte-elementwise `.16B` reverse over a 4-block bounds-checked loop) and before
//! [`crate::neon_fill`]. Disable with `TRUST_CG_DISABLE_PASSES=neon_bitrev`.
//!
//! ## Why this is SOUND
//!
//! The transform is **purely additive**: it inserts a NEON main loop in front of
//! the scalar loop and NEVER edits the scalar loop's instructions (including its
//! bounds checks). The scalar loop is therefore correct by construction; only the
//! inserted vector loop needs justifying.
//!
//! * **The vector loop reproduces EXACTLY the loop's observable effect.** The
//!   recognizer proves the loop body's ONLY memory effect is a single
//!   `StrbRI` writing `reverse8(a[iv])` to `out[iv]`, its ONLY read is the single
//!   `LdrbRI` of `a[iv]`, and there is no other store / load / call / atomic
//!   (whitelisted body ops) — so replacing iterations `[0, V)` with the vector
//!   loop drops NOTHING. The store is proven to dominate the latch (executed once
//!   per completed iteration) and the load to dominate the store.
//! * **In bounds.** The vector header enters the body only while
//!   `iv <u N - (WIDTH-1)` (`N` the single constant loop bound, `WIDTH = 64`), so
//!   every processed index `iv .. iv+63` is `<u N` — an index the scalar loop,
//!   guarded by the same `iv <u N`, also accesses. The vector index set
//!   `[0, V)` (`V` a multiple of 64, `V <= N`) is a SUBSET of the scalar's
//!   `[0, N)`, all of which the (correct) scalar program accesses without
//!   trapping — hence in bounds — and the untouched scalar loop resumes at `iv=V`
//!   to write the disjoint tail `[V, N)`. `out[0..N)` is written exactly once.
//! * **The per-lane term equals the scalar term.** For a byte `b in [0,255]`,
//!   `RBIT.16B` computes `reverse8(b)` in each lane (the FAITHFUL proof above),
//!   IDENTICAL to the scalar `bitmanip_reverse_bits(n=8)` ladder the recognizer
//!   exact-matched. `LDP`/`STP` move contiguous bytes and `RBIT` is per-byte, so
//!   `out[iv+j] = reverse8(a[iv+j])` for every `j in 0..64`.
//! * **The induction is the ONLY loop-carried register** (the crate's one
//!   loop-state contract, [`crate::loop_contract`]). The vector loop steps
//!   `iv` by `WIDTH` and executes NONE of the scalar body's other register
//!   updates, so a second loop-carried value (a stealth accumulator
//!   `acc += f(i)` in the latch, or any body register live out of the loop)
//!   would silently lose every contribution from the vectorized prefix
//!   `[0, V)`. The contract refuses any register other than `iv` that is live
//!   into the header or an exit; [`loop_defs_are_unique`] separately gives the
//!   ladder matcher one definition per loop register. Otherwise the loop stays
//!   scalar.
//! * **No store aliasing.** The store base `out` and the load base `a` are each
//!   proven to be the address of a DISTINCT stack slot (`AddPCRel(sp,
//!   StackSlot(s))` with `s_out != s_a`). Distinct stack slots occupy
//!   NON-OVERLAPPING frame ranges (`trust-cg-codegen::frame::stack_slot_frame_offsets`
//!   lays each fixed slot out in its own downward-growing, aligned byte range), so
//!   `out` and `a` provably never alias: the vector writes to `out` cannot clobber
//!   the `a` bytes the vector (or the scalar tail) later reads. If EITHER base is
//!   not a distinct-slot `AddPCRel`, or they share a slot (the in-place
//!   `a[i]=reverse(a[i])` self-map and any two derived pointers into ONE buffer —
//!   the overlapping-at-an-offset adversary), distinctness is NOT proven and the
//!   loop is left ENTIRELY scalar. Fail-closed beats miscompile.
//!
//! If ANY premise is unprovable (non-`.16B`/non-8-bit reversal, a partial or
//! permuted ladder, a stencil `a[i±k]`, a non-constant or `< WIDTH` bound, a
//! second store/load/call, a base not rooted at a distinct stack slot, a bound
//! guard not materializable in 16 bits, a second loop-carried register) the loop
//! stays scalar.

use crate::candidate::{alloc, commit, emit, emit_before, insert_new_blocks_before, splice_edge};
use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use crate::loop_contract::{ExitPlan, GuardBound, Handoff, InductionGuards, LoopLocality};
use crate::mach_util::{branch_targets, copied_const, copy_like, strip_copies};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachOperand, RegClass, StackSlotId, VReg,
};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Q registers per NEON iteration (`RBIT.16B` x `UNROLL_Q`), matching LLVM -O3's
/// 64-byte/iter `ldp q,q / rbit.16b x4 / stp q,q` shape.
const UNROLL_Q: usize = 4;
/// Bytes per 128-bit Q register.
const LANES_PER_Q: i64 = 16;
/// Bytes processed per NEON iteration (`UNROLL_Q * LANES_PER_Q` == 64).
const WIDTH: i64 = UNROLL_Q as i64 * LANES_PER_Q;
/// NEON arrangement operand code for `.16B` (`RBIT Vd.16B, Vn.16B`).
const ARR_B16: i64 = 1;
/// AArch64 condition code for unsigned lower (`LO`) — the `usize` `iv <u N`
/// counted-loop guard.
const CC_LO: i64 = 3;
/// The largest constant loop bound whose vector guard `N - (WIDTH-1)` still fits
/// a single 16-bit `Movz` immediate. Larger `N` BAILS (stays scalar) — a sound,
/// conservative limit that keeps the guard materialization to the proven
/// single-`Movz` form.
const MAX_BOUND: i64 = 0xffff + (WIDTH - 1);

// ---------------------------------------------------------------------------
// Pass
// ---------------------------------------------------------------------------

/// The `neon-bitrev` machine pass.
#[derive(Default)]
pub struct NeonBitrevPass {
    fired: usize,
}

impl NeonBitrevPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }
    /// Loops vectorized in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for NeonBitrevPass {
    fn name(&self) -> &str {
        "neon-bitrev"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &dom, &loops)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loops = analyses.loop_analysis(func).clone();
        let changed = {
            let dom = analyses.domtree(func);
            self.run_core(func, dom, &loops)
        };
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

impl NeonBitrevPass {
    fn run_core(&mut self, func: &mut MachFunction, dom: &DomTree, loops: &LoopAnalysis) -> bool {
        self.fired = 0;
        // Recognize read-only first; applying a plan only ADDS blocks (never
        // renumbers existing ids or edits other loops), so recognized data for
        // other loops stays valid.
        let mut plans = Vec::new();
        let def_map = build_def_map(func);
        for lp in loops.all_loops() {
            // Innermost only: no other loop's header lies inside this body.
            let is_innermost = loops
                .all_loops()
                .all(|other| other.header == lp.header || !lp.body.contains(&other.header));
            if !is_innermost {
                continue;
            }
            if let Some(rec) =
                Recognized::recognize(func, dom, &def_map, lp.header, lp.latch, &lp.body)
            {
                plans.push(rec);
            }
        }
        let mut changed = false;
        for rec in plans {
            if apply(func, &rec) {
                self.fired += 1;
                changed = true;
            }
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

struct Recognized {
    header: BlockId,
    preheader: BlockId,
    preheader_term: InstId,
    /// The `Gpr64` induction (`iv += 1`).
    iv: VReg,
    /// The single constant loop bound `N` (`iv <u N`), also every `a[i]`/`out[i]`
    /// bounds-check limit — so `iv <u N` proves both accesses in bounds.
    bound: i64,
    /// Loop-invariant base pointer of the input array `a` (a distinct stack slot).
    load_base: VReg,
    /// Loop-invariant base pointer of the output array `out` (a distinct stack
    /// slot, `!= load_base`'s slot).
    store_base: VReg,
    /// The loop-state contract (`crate::loop_contract`) passed for
    /// `[iv]`. The plan cannot be built without it.
    _locality: LoopLocality,
}

impl Recognized {
    fn recognize(
        func: &MachFunction,
        dom: &DomTree,
        def: &HashMap<u32, InstId>,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        macro_rules! bail {
            ($($t:tt)*) => {{
                return None;
            }};
        }
        if header == latch || body.is_empty() {
            bail!("degenerate loop");
        }
        // `def` is supplied by the caller, built ONCE per recognition sweep.
        // Measured at 99.1% of this pass (110.3ms of 111.3ms, many_fns n=200)
        // when it was rebuilt inside every per-loop attempt.

        // Whitelist every opcode in the loop body (rules out calls / atomics /
        // division / any unmodeled effect) and count the memory ops: EXACTLY one
        // byte load and one byte store, nothing else that reads or writes memory.
        let mut loop_insts = HashSet::default();
        let mut load_id: Option<InstId> = None;
        let mut store_id: Option<InstId> = None;
        for &b in body {
            for &id in &func.block(b).insts {
                let op = func.inst(id).opcode;
                if !allowed_loop_op(op) {
                    bail!("disallowed body op {:?}", op);
                }
                match op {
                    AArch64Opcode::LdrbRI => {
                        if load_id.is_some() {
                            bail!("more than one LdrbRI");
                        }
                        load_id = Some(id);
                    }
                    AArch64Opcode::StrbRI => {
                        if store_id.is_some() {
                            bail!("more than one StrbRI");
                        }
                        store_id = Some(id);
                    }
                    _ => {}
                }
                loop_insts.insert(id);
            }
        }
        let (Some(load_id), Some(store_id)) = (load_id, store_id) else {
            bail!("need exactly one LdrbRI and one StrbRI");
        };

        // Preheader: the single non-latch predecessor of the header.
        let hpreds = &func.block(header).preds;
        if hpreds.len() != 2 || !hpreds.contains(&latch) {
            bail!("header preds != {{latch, preheader}}: {:?}", hpreds);
        }
        let preheader = *hpreds.iter().find(|&&b| b != latch)?;
        let Some(&preheader_term) = func
            .block(preheader)
            .insts
            .iter()
            .rev()
            .find(|&&id| branch_targets(func.inst(id)).contains(&header))
        else {
            bail!("no preheader->header branch");
        };

        // The `Gpr64` induction: a latch writeback `d = MovR/Copy(AddRI(d, 1))`
        // or `d = MovR(AddRR(d, 1))`.
        let mut iv = None;
        for &id in &func.block(latch).insts {
            let Some((d, s)) = copy_like(func.inst(id)) else {
                continue;
            };
            let Some(&sdef) = def.get(&s.id) else {
                continue;
            };
            let si = func.inst(sdef);
            if si.opcode == AArch64Opcode::AddRI
                && si.operands.len() == 3
                && si.operands[1].as_vreg() == Some(d)
                && si.operands[2].as_imm() == Some(1)
            {
                iv = Some(d);
            } else if si.opcode == AArch64Opcode::AddRR && si.operands.len() == 3 {
                let a = si.operands[1].as_vreg()?;
                let b = si.operands[2].as_vreg()?;
                if (a == d && copied_const(func, def, b) == Some(1))
                    || (b == d && copied_const(func, def, a) == Some(1))
                {
                    iv = Some(d);
                }
            }
        }
        let Some(iv) = iv else {
            bail!("no +1 iv writeback in latch");
        };
        if iv.class != RegClass::Gpr64 {
            bail!("iv class not Gpr64 ({:?})", iv.class);
        }

        // The single constant bound `N`: every `iv`-relative compare in the loop
        // (the `iv <u N` continue test AND the `a[i]`/`out[i]` bounds tests) must
        // agree on ONE constant. A compare whose LHS is not the iv is unexpected
        // (fail closed).
        let mut bound: Option<i64> = None;
        for &b in body {
            for &id in &func.block(b).insts {
                let inst = func.inst(id);
                let n = match inst.opcode {
                    AArch64Opcode::CmpRR if inst.operands.len() == 2 => {
                        let x = inst.operands[0].as_vreg()?;
                        if !same_as_iv(func, def, x, iv) {
                            bail!("cmp lhs not iv");
                        }
                        let Some(n) = copied_const(func, def, inst.operands[1].as_vreg()?) else {
                            bail!("cmp bound not constant");
                        };
                        n
                    }
                    AArch64Opcode::CmpRI if inst.operands.len() == 2 => {
                        let x = inst.operands[0].as_vreg()?;
                        if !same_as_iv(func, def, x, iv) {
                            bail!("cmpri lhs not iv");
                        }
                        inst.operands[1].as_imm()?
                    }
                    _ => continue,
                };
                match bound {
                    Some(prev) if prev != n => bail!("bound {} disagrees with {}", n, prev),
                    _ => bound = Some(n),
                }
            }
        }
        let Some(bound) = bound else {
            bail!("no constant iv bound");
        };
        if bound < WIDTH {
            bail!("bound {} < WIDTH {}", bound, WIDTH);
        }
        if bound > MAX_BOUND {
            bail!(
                "bound {} > MAX_BOUND {} (guard not 16-bit)",
                bound,
                MAX_BOUND
            );
        }

        // --- The STORE: `StrbRI [value, addr, #0]`, addr = loop-invariant
        // `store_base + iv`, store_base a distinct stack slot.
        let store = func.inst(store_id);
        if store.operands.len() != 3 || store.operands[2].as_imm() != Some(0) {
            bail!("store not [val, addr, #0]");
        }
        let store_val = store.operands[0].as_vreg()?;
        let store_addr = store.operands[1].as_vreg()?;
        let (store_base, s_slot) = resolve_indexed_base(func, dom, def, body, store_addr, iv)?;

        // --- The LOAD: `LdrbRI [dst, addr, #0]`, addr = `load_base + iv`,
        // load_base a distinct stack slot.
        let load = func.inst(load_id);
        if load.operands.len() != 3 || load.operands[2].as_imm() != Some(0) {
            bail!("load not [dst, addr, #0]");
        }
        let load_addr = load.operands[1].as_vreg()?;
        let (load_base, l_slot) = resolve_indexed_base(func, dom, def, body, load_addr, iv)?;

        // Distinctness: the two arrays MUST be distinct stack slots. Same slot
        // (in-place self-map, or two pointers into one buffer) is NOT proven
        // disjoint — fail closed.
        if s_slot == l_slot {
            bail!("store and load share stack slot {:?}", s_slot);
        }

        // --- The stored value must be EXACTLY reverse8 of the loaded byte.
        // Peel the output normalization (`Uxtb` and/or `AndRI(_, 255)` — no-ops
        // on the low byte `StrbRI` stores) down to the OR-tree root, then match
        // the 8-term isolate/shift ladder, then verify its common byte source is
        // the loaded byte (zero-extended, optionally masked `& 255`).
        let or_root = peel_to_or_root(func, def, store_val)?;
        let byte_src = match_reverse_ladder(func, def, &loop_insts, or_root)?;
        let ladder_load = resolve_ladder_byte_load(func, def, byte_src)?;
        if ladder_load != load_id {
            bail!("ladder byte source is not the recognized load");
        }

        // --- LOCALITY: the induction is the ONLY loop-carried or live-out
        // register (the crate's one loop-state contract,
        // `crate::loop_contract`). The vector loop replaces whole iterations
        // WITHOUT executing any of the scalar body's register updates — it
        // steps only `iv`. A second accumulator `acc += f(i)` would read 0
        // contributions from `[0, V)`.
        if !loop_defs_are_unique(func, &loop_insts, iv) {
            bail!("a loop-defined register has a second definition");
        }
        // The vector exit falls into the scalar header, which must therefore
        // be the loop test: its one exit leaves exactly when `iv >=u N`. The
        // loop's other exits must be bounds checks the contract admits by its
        // own rule (`iv` against a bound of at least `N`).
        let is_iv = |v: VReg| same_as_iv(func, def, v, iv);
        let is_bound = |guard: GuardBound| match guard {
            GuardBound::Imm(n) => n == bound,
            GuardBound::Reg(r) => copied_const(func, def, r) == Some(bound),
        };
        let covers_loop_bound = |guard: GuardBound| match guard {
            GuardBound::Imm(n) => (n as u64) >= (bound as u64),
            GuardBound::Reg(r) => {
                copied_const(func, def, r).is_some_and(|n| (n as u64) >= (bound as u64))
            }
        };
        let Some(exits) =
            ExitPlan::unsigned_loop_test(func, body.iter().copied(), header, &is_iv, &is_bound)
        else {
            bail!("the header is not an `iv <u N` test with one exit");
        };
        let exits = exits.and_induction_guards(
            func,
            body.iter().copied(),
            header,
            &InductionGuards {
                iv,
                at_most_iv: &is_iv,
                covers_loop_bound: &covers_loop_bound,
            },
        );
        let locality = match LoopLocality::check(
            func,
            body.iter().copied(),
            header,
            &exits,
            Handoff::HeaderOrExit,
            &[iv],
        ) {
            Ok(locality) => locality,
            Err(_escape) => bail!("loop state escapes: {:?}", _escape),
        };

        // --- Dominance: the store executes once per completed iteration (its
        // block dominates the latch), and the load precedes the store.
        let store_block = block_of_inst(func, store_id)?;
        let load_block = block_of_inst(func, load_id)?;
        if !body.contains(&store_block) || !body.contains(&load_block) {
            bail!("load/store not in loop body");
        }
        if !dom.dominates(store_block, latch) {
            bail!("store does not dominate latch");
        }
        if !dom.dominates(load_block, store_block) {
            bail!("load does not dominate store");
        }

        Some(Recognized {
            _locality: locality,
            header,
            preheader,
            preheader_term,
            iv,
            bound,
            load_base,
            store_base,
        })
    }
}

/// The ladder matcher's premise: every register a loop instruction defines,
/// other than `iv`, has exactly ONE definition in the whole function, and it is
/// in the loop. The recognizer walks `def` maps (`peel_to_or_root`,
/// `match_reverse_ladder`), which name one defining instruction per register;
/// a second definition, in the loop or outside it, would make the walked value
/// ambiguous.
///
/// This is dataflow exactness for the matcher, not the loop-state rule. Whether
/// a skipped iteration's register update is observable is the crate's one
/// loop-state contract ([`crate::loop_contract`]), asked separately. With
/// unique definitions, that contract also refuses the shapes this gate used to
/// refuse by structure: a self-use or a use not dominated by its definition is
/// live into the header, and a use after the loop is live into an exit.
fn loop_defs_are_unique(func: &MachFunction, loop_insts: &HashSet<InstId>, iv: VReg) -> bool {
    // `effects::for_each_inst_def` is the COMPLETE def oracle: besides the
    // usual operand-0 result it names the second destination of a paired load,
    // a post-index writeback base, and the LSE read-modify-write result at
    // operand 1. Missing a def here could leave an ambiguous register
    // unchecked; an extra def candidate can only cause a bail.
    let mut loop_defs: HashSet<u32> = HashSet::default();
    for &id in loop_insts {
        crate::effects::for_each_inst_def(func.inst(id), |v| {
            loop_defs.insert(v.id);
        });
    }
    loop_defs.remove(&iv.id);
    let mut def_counts: HashMap<u32, usize> = HashMap::default();
    for block in &func.blocks {
        for &id in &block.insts {
            crate::effects::for_each_inst_def(func.inst(id), |v| {
                if loop_defs.contains(&v.id) {
                    *def_counts.entry(v.id).or_insert(0) += 1;
                }
            });
        }
    }
    loop_defs
        .iter()
        .all(|rid| def_counts.get(rid).copied() == Some(1))
}

/// Resolve `addr` (a byte-access address) to `(base, slot)` where
/// `addr == base + iv` (same-index, unit byte stride), `base` is loop-invariant
/// and roots at `AddPCRel(sp, StackSlot(slot))`. Fail-closed on any other shape
/// (a stencil `a[i±k]`, a non-iv index, a derived/non-stack base).
fn resolve_indexed_base(
    func: &MachFunction,
    dom: &DomTree,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    addr: VReg,
    iv: VReg,
) -> Option<(VReg, StackSlotId)> {
    let a = strip_copies(func, def, addr);
    let &adef = def.get(&a.id)?;
    let inst = func.inst(adef);
    if inst.opcode != AArch64Opcode::AddRR || inst.operands.len() != 3 {
        return None;
    }
    let x = inst.operands[1].as_vreg()?;
    let y = inst.operands[2].as_vreg()?;
    // Exactly one operand is the iv; the other is the loop-invariant base.
    let base = if same_as_iv(func, def, x, iv) {
        y
    } else if same_as_iv(func, def, y, iv) {
        x
    } else {
        return None;
    };
    let slot = resolve_stack_slot(func, dom, def, body, base)?;
    Some((strip_copies(func, def, base), slot))
}

/// Resolve `base` to the `StackSlotId` it addresses: loop-invariant (defined
/// outside the loop body) and rooted at `AddPCRel(_, StackSlot(slot))`.
fn resolve_stack_slot(
    func: &MachFunction,
    _dom: &DomTree,
    def: &HashMap<u32, InstId>,
    body: &HashSet<BlockId>,
    base: VReg,
) -> Option<StackSlotId> {
    let b = strip_copies(func, def, base);
    let &bdef = def.get(&b.id)?;
    // Loop-invariant: the base's definition is outside the loop body.
    if let Some(bl) = block_of_inst(func, bdef)
        && body.contains(&bl)
    {
        return None;
    }
    let inst = func.inst(bdef);
    if inst.opcode != AArch64Opcode::AddPCRel {
        return None;
    }
    inst.operands.iter().find_map(|op| match op {
        MachOperand::StackSlot(s) => Some(*s),
        _ => None,
    })
}

/// Peel a stored byte value down to the OR-tree root: strip copies, an optional
/// `Uxtb`, an optional `AndRI(_, 255)` — all no-ops on the low 8 bits that
/// `StrbRI` writes — and require an `OrrRR` root.
fn peel_to_or_root(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    store_val: VReg,
) -> Option<VReg> {
    let mut v = strip_copies(func, def, store_val);
    // Optional Uxtb (Gpr32 result of the ladder truncation).
    if let Some(&d) = def.get(&v.id)
        && func.inst(d).opcode == AArch64Opcode::Uxtb
        && func.inst(d).operands.len() == 2
    {
        v = strip_copies(func, def, func.inst(d).operands[1].as_vreg()?);
    }
    // Optional final `& 255` mask (bitmanip_mask_n).
    if let Some(x) = peel_and255(func, def, v) {
        v = x;
    }
    let &d = def.get(&v.id)?;
    if func.inst(d).opcode == AArch64Opcode::OrrRR {
        Some(v)
    } else {
        None
    }
}

/// If `v` is defined by `AndRI(x, 255)`, return `strip_copies(x)`.
fn peel_and255(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg) -> Option<VReg> {
    let &d = def.get(&v.id)?;
    let inst = func.inst(d);
    if inst.opcode == AArch64Opcode::AndRI
        && inst.operands.len() == 3
        && inst.operands[2].as_imm() == Some(255)
    {
        Some(strip_copies(func, def, inst.operands[1].as_vreg()?))
    } else {
        None
    }
}

/// Match the EXACT `bitmanip_reverse_bits(n=8)` OR-tree rooted at `or_root`:
/// exactly 8 leaves, each `LslRI`/`LsrRI` of an `AndRI(byte, 1<<i)` that places
/// bit `i` at mirror position `7-i`, covering every `i in 0..8` once, all
/// sourced from ONE common `byte` value. Returns that common `byte` source.
fn match_reverse_ladder(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    or_root: VReg,
) -> Option<VReg> {
    let mut leaves = Vec::new();
    if !collect_or_leaves(func, def, loop_insts, or_root, &mut leaves, 0) {
        return None;
    }
    if leaves.len() != 8 {
        return None;
    }
    let mut seen_bits = [false; 8];
    let mut byte_src: Option<VReg> = None;
    for leaf in leaves {
        let (bit, src) = classify_leaf(func, def, loop_insts, leaf)?;
        if seen_bits[bit as usize] {
            return None; // duplicate bit index — not a permutation
        }
        seen_bits[bit as usize] = true;
        match byte_src {
            Some(prev) if prev != src => return None, // leaves from different sources
            _ => byte_src = Some(src),
        }
    }
    if !seen_bits.iter().all(|&b| b) {
        return None; // not all 8 bits covered
    }
    byte_src
}

/// Recursively split `OrrRR` nodes (each defined in the loop) into their two
/// operands; a non-`OrrRR` value is a leaf. Bounded depth (the 8-leaf tree is at
/// most 8 deep).
fn collect_or_leaves(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    v: VReg,
    out: &mut Vec<VReg>,
    depth: u32,
) -> bool {
    if depth > 16 {
        return false;
    }
    if let Some(&d) = def.get(&v.id)
        && loop_insts.contains(&d)
    {
        let inst = func.inst(d);
        if inst.opcode == AArch64Opcode::OrrRR && inst.operands.len() == 3 {
            let (Some(a), Some(b)) = (inst.operands[1].as_vreg(), inst.operands[2].as_vreg())
            else {
                return false;
            };
            return collect_or_leaves(func, def, loop_insts, a, out, depth + 1)
                && collect_or_leaves(func, def, loop_insts, b, out, depth + 1);
        }
    }
    out.push(v);
    true
}

/// Classify a ladder leaf `LslRI/LsrRI(AndRI(byte, 1<<i), sh)` that moves bit `i`
/// to bit `7-i`. Returns `(i, byte)`. The shift direction and amount are checked
/// to EXACTLY match the mirror map (`sh = 7-2i` left for `i<4`, `sh = 2i-7` right
/// for `i>=4`), and the isolate mask must be `1<<i` for that same `i`.
fn classify_leaf(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    loop_insts: &HashSet<InstId>,
    leaf: VReg,
) -> Option<(u32, VReg)> {
    let &d = def.get(&leaf.id)?;
    if !loop_insts.contains(&d) {
        return None;
    }
    let inst = func.inst(d);
    if inst.operands.len() != 3 {
        return None;
    }
    let sh = inst.operands[2].as_imm()?;
    let and_v = inst.operands[1].as_vreg()?;
    // Expected bit index from the shift, per direction.
    let bit = match inst.opcode {
        // Left shift moves bit i UP to 7-i: 7-i = i+sh => i = (7-sh)/2, i in 0..4.
        AArch64Opcode::LslRI => {
            if !(1..=7).contains(&sh) || (7 - sh) % 2 != 0 {
                return None;
            }
            let i = (7 - sh) / 2;
            if !(0..4).contains(&i) {
                return None;
            }
            i as u32
        }
        // Right shift moves bit i DOWN to 7-i: 7-i = i-sh => i = (7+sh)/2, i in 4..8.
        AArch64Opcode::LsrRI => {
            if !(1..=7).contains(&sh) || (7 + sh) % 2 != 0 {
                return None;
            }
            let i = (7 + sh) / 2;
            if !(4..8).contains(&i) {
                return None;
            }
            i as u32
        }
        _ => return None,
    };
    // The isolate: AndRI(byte, 1<<bit).
    let &ad = def.get(&and_v.id)?;
    if !loop_insts.contains(&ad) {
        return None;
    }
    let ai = func.inst(ad);
    if ai.opcode != AArch64Opcode::AndRI || ai.operands.len() != 3 {
        return None;
    }
    if ai.operands[2].as_imm()? != (1i64 << bit) {
        return None;
    }
    let byte = strip_copies(func, def, ai.operands[1].as_vreg()?);
    Some((bit, byte))
}

/// Resolve the ladder's common byte source to the `InstId` of the `LdrbRI` it
/// loads: `byte -> (optional AndRI(_,255)) -> Uxtb(load_dst) -> LdrbRI`.
fn resolve_ladder_byte_load(
    func: &MachFunction,
    def: &HashMap<u32, InstId>,
    byte_src: VReg,
) -> Option<InstId> {
    let mut v = strip_copies(func, def, byte_src);
    if let Some(x) = peel_and255(func, def, v) {
        v = x;
    }
    let &d = def.get(&v.id)?;
    let inst = func.inst(d);
    if inst.opcode != AArch64Opcode::Uxtb || inst.operands.len() != 2 {
        return None;
    }
    let src = strip_copies(func, def, inst.operands[1].as_vreg()?);
    let &ld = def.get(&src.id)?;
    if func.inst(ld).opcode == AArch64Opcode::LdrbRI {
        Some(ld)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

fn apply(func: &mut MachFunction, rec: &Recognized) -> bool {
    commit(func, |candidate| apply_candidate(candidate, rec))
}

fn apply_candidate(func: &mut MachFunction, rec: &Recognized) -> Option<()> {
    // IDEMPOTENCE: never vectorize the remainder loop of a loop this pass
    // already vectorized (see `crate::vector_remainder`).
    if crate::vector_remainder::iv_is_vector_advanced_upstream(
        func,
        &crate::fast_hash::FxHashSet::default(),
        rec.preheader,
        rec.iv,
    ) {
        return None;
    }
    let vh = func.try_create_block()?;
    let vb = func.try_create_block()?;
    let vl = func.try_create_block()?;
    let vx = func.try_create_block()?;
    insert_new_blocks_before(func, rec.header, &[vh, vb, vl, vx])?;
    // Internal edges among the fresh blocks only; the preheader redirect is
    // deferred to the COMMIT so a lowering failure cannot break the CFG.
    func.add_edge(vh, vb);
    func.add_edge(vh, vx);
    func.add_edge(vb, vl);
    func.add_edge(vl, vh);

    let pre = rec.preheader_term;

    // main_bound = N - (WIDTH-1) (const, in `1..=0xffff` by the recognizer's
    // `WIDTH <= N <= MAX_BOUND` gate, so a single 16-bit Movz is exact).
    let main_bound = alloc(func, RegClass::Gpr64)?;
    emit_before(
        func,
        pre,
        AArch64Opcode::Movz,
        vec![vreg(main_bound), imm(rec.bound - (WIDTH - 1))],
    )?;

    // --- Vector header: unsigned `iv <u main_bound` => the whole 64-byte block
    // `iv .. iv+63` is `<u N` (in bounds). Both operands are non-negative and
    // `< 2^63`, so unsigned is exact.
    emit(
        func,
        vh,
        AArch64Opcode::CmpRR,
        vec![vreg(rec.iv), vreg(main_bound)],
    )?;
    emit(func, vh, AArch64Opcode::BCond, vec![imm(CC_LO), block(vb)])?;
    emit(func, vh, AArch64Opcode::B, vec![block(vx)])?;

    // --- Vector body: fresh post-index load/store pointers `base + iv` (iv is
    // the loop's current index; the latch advances it by WIDTH). All 64 input
    // bytes are LOADED before any store; the load and store pointers are distinct
    // registers over distinct (proven-disjoint) stack slots.
    let lp = alloc(func, RegClass::Gpr64)?;
    emit(
        func,
        vb,
        AArch64Opcode::AddRR,
        vec![vreg(lp), vreg(rec.load_base), vreg(rec.iv)],
    )?;
    let mut qs: Vec<VReg> = Vec::with_capacity(UNROLL_Q);
    for _pair in 0..UNROLL_Q / 2 {
        let q0 = alloc(func, RegClass::Fpr128)?;
        let q1 = alloc(func, RegClass::Fpr128)?;
        emit(
            func,
            vb,
            AArch64Opcode::NeonLdpQPost,
            vec![vreg(q0), vreg(q1), vreg(lp), imm(32)],
        )?;
        qs.push(q0);
        qs.push(q1);
    }
    // Per-byte reverse each Q with the FAITHFULLY-PROVEN `RBIT.16B`.
    let mut rs: Vec<VReg> = Vec::with_capacity(UNROLL_Q);
    for &q in &qs {
        let r = alloc(func, RegClass::Fpr128)?;
        emit(
            func,
            vb,
            AArch64Opcode::NeonRbitV,
            vec![vreg(r), vreg(q), imm(ARR_B16)],
        )?;
        rs.push(r);
    }
    let sp = alloc(func, RegClass::Gpr64)?;
    emit(
        func,
        vb,
        AArch64Opcode::AddRR,
        vec![vreg(sp), vreg(rec.store_base), vreg(rec.iv)],
    )?;
    let mut k = 0;
    while k + 1 < UNROLL_Q {
        emit(
            func,
            vb,
            AArch64Opcode::NeonStpQPost,
            vec![vreg(rs[k]), vreg(rs[k + 1]), vreg(sp), imm(32)],
        )?;
        k += 2;
    }
    emit(func, vb, AArch64Opcode::B, vec![block(vl)])?;

    // --- Vector latch: step iv by WIDTH (mutates the SAME iv the scalar loop
    // reads), then re-test the header.
    emit(
        func,
        vl,
        AArch64Opcode::AddRI,
        vec![vreg(rec.iv), vreg(rec.iv), imm(WIDTH)],
    )?;
    emit(func, vl, AArch64Opcode::B, vec![block(vh)])?;

    // --- Vector exit: a map has no accumulator — fall straight into the
    // untouched scalar loop (which finishes the `< WIDTH` tail at `iv = V`).
    emit(func, vx, AArch64Opcode::B, vec![block(rec.header)])?;

    // --- COMMIT: splice the fresh blocks in front of the scalar loop.
    splice_edge(func, rec.preheader, rec.preheader_term, rec.header, vh)?;
    func.add_edge(vx, rec.header);
    Some(())
}

// ---------------------------------------------------------------------------
// Local operand/recognition helpers; checked mutation lives in candidate.rs
// ---------------------------------------------------------------------------

fn vreg(v: VReg) -> MachOperand {
    MachOperand::VReg(v)
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn block(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}

/// Body opcode whitelist: pure ALU / moves / the counted-loop compares & branches
/// / the byte load & store / the sign-extend and bounds-check carriers. Any op
/// NOT here (a call, atomic, second store, division, unmodeled effect) BAILS.
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | SubRR
            | SubRI
            | AndRR
            | AndRI
            | OrrRR
            | OrrRI
            | EorRR
            | LslRI
            | LsrRI
            | AsrRI
            | Movz
            | Movk
            | Movn
            | MovR
            | Copy
            | CmpRR
            | CmpRI
            | BCond
            | B
            | Uxtb
            | Uxth
            | Uxtw
            | Sxtw
            | LdrbRI
            | StrbRI
            | TrapBoundsCheckExact
    )
}

fn same_as_iv(func: &MachFunction, def: &HashMap<u32, InstId>, v: VReg, iv: VReg) -> bool {
    strip_copies(func, def, v) == strip_copies(func, def, iv)
}

/// Def map (`vreg id -> defining InstId`) over instructions still ATTACHED to a
/// block (skips arena-retained detached instructions, which would shadow real
/// reaching defs).
/// DIAGNOSTIC (default off, `TCG_TIME_BOI=1`): accumulated time and call count,
/// so this helper's share of the pass is measured rather than assumed.
pub(crate) static BITREV_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static BITREV_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn build_def_map(func: &MachFunction) -> HashMap<u32, InstId> {
    if crate::neon_array::boi_timing_enabled() {
        let t = std::time::Instant::now();
        let r = build_def_map_inner(func);
        BITREV_NANOS.fetch_add(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        BITREV_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return r;
    }
    build_def_map_inner(func)
}

fn build_def_map_inner(func: &MachFunction) -> HashMap<u32, InstId> {
    crate::effects::build_reaching_def_map(func)
}

fn block_of_inst(func: &MachFunction, target: InstId) -> Option<BlockId> {
    for (idx, blk) in func.blocks.iter().enumerate() {
        if blk.insts.contains(&target) {
            return u32::try_from(idx).ok().map(BlockId);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::MachInst;
    use trust_cg_ir::Signature;

    fn g32(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }
    fn g64(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }
    fn i(x: i64) -> MachOperand {
        MachOperand::Imm(x)
    }
    fn b(x: BlockId) -> MachOperand {
        MachOperand::Block(x)
    }
    fn slot(x: u32) -> MachOperand {
        MachOperand::StackSlot(StackSlotId(x))
    }
    fn count(func: &MachFunction, op: AArch64Opcode) -> usize {
        func.blocks
            .iter()
            .flat_map(|blk| blk.insts.iter().copied())
            .filter(|&id| func.inst(id).opcode == op)
            .count()
    }

    /// Build `for iv in 0..256 { out[iv] = reverse8(a[iv]) }` in the EXACT shape
    /// the recognizer matches: `out` = StackSlot(0), `a` = StackSlot(1), the
    /// `bitmanip_reverse_bits(n=8)` isolate/shift/OR ladder, one `LdrbRI`, one
    /// `StrbRI`, and a `+1` induction writeback in the latch.
    ///
    /// `carried`: when true, add a SECOND loop-carried value — an accumulator
    /// `acc = acc + iv` written back in the latch and initialized outside the
    /// loop. The vector loop never executes it, so vectorizing would drop every
    /// contribution from the vectorized prefix.
    fn build_bitrev_loop(carried: bool) -> MachFunction {
        use AArch64Opcode::*;
        let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let header = func.create_block();
        let body = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();
        let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
            let id = func.push_inst(MachInst::new(op, ops));
            func.append_inst(blk, id);
        };

        // Preheader: the two distinct stack-slot bases, the bound, iv = 0.
        push(&mut func, bb0, AddPCRel, vec![g64(100), slot(0)]); // out
        push(&mut func, bb0, AddPCRel, vec![g64(101), slot(1)]); // a
        push(&mut func, bb0, Movz, vec![g64(102), i(256)]); // N
        push(&mut func, bb0, Movz, vec![g64(1), i(0)]); // iv
        if carried {
            push(&mut func, bb0, Movz, vec![g64(70), i(0)]); // acc
        }
        push(&mut func, bb0, B, vec![b(header)]);

        // Header: `iv <u N`.
        push(&mut func, header, CmpRR, vec![g64(1), g64(102)]);
        push(&mut func, header, BCond, vec![i(CC_LO), b(body)]);
        push(&mut func, header, B, vec![b(exit)]);

        // Body: load a[iv], the 8-term reverse ladder, store out[iv].
        push(&mut func, body, AddRR, vec![g64(10), g64(101), g64(1)]);
        push(&mut func, body, LdrbRI, vec![g32(11), g64(10), i(0)]);
        push(&mut func, body, Uxtb, vec![g32(12), g32(11)]);
        for bit in 0..8u32 {
            push(
                &mut func,
                body,
                AndRI,
                vec![g32(20 + bit), g32(12), i(1i64 << bit)],
            );
            // bit `i` lands at mirror position `7-i`.
            let (op, sh) = if bit < 4 {
                (LslRI, 7 - 2 * bit as i64)
            } else {
                (LsrRI, 2 * bit as i64 - 7)
            };
            push(
                &mut func,
                body,
                op,
                vec![g32(30 + bit), g32(20 + bit), i(sh)],
            );
        }
        push(&mut func, body, OrrRR, vec![g32(40), g32(30), g32(31)]);
        for k in 0..6u32 {
            push(
                &mut func,
                body,
                OrrRR,
                vec![g32(41 + k), g32(40 + k), g32(32 + k)],
            );
        }
        push(&mut func, body, AddRR, vec![g64(50), g64(100), g64(1)]);
        push(&mut func, body, StrbRI, vec![g32(46), g64(50), i(0)]);
        push(&mut func, body, B, vec![b(latch)]);

        // Latch: iv += 1 (and, for `carried`, acc += iv).
        push(&mut func, latch, AddRI, vec![g64(60), g64(1), i(1)]);
        push(&mut func, latch, MovR, vec![g64(1), g64(60)]);
        if carried {
            push(&mut func, latch, AddRR, vec![g64(71), g64(70), g64(1)]);
            push(&mut func, latch, MovR, vec![g64(70), g64(71)]);
        }
        push(&mut func, latch, B, vec![b(header)]);
        push(&mut func, exit, Ret, vec![]);

        func.add_edge(bb0, header);
        func.add_edge(header, body);
        func.add_edge(header, exit);
        func.add_edge(body, latch);
        func.add_edge(latch, header);
        func.next_vreg = 512;
        func
    }

    fn candidate_boundary_fixture() -> MachFunction {
        build_bitrev_loop(false)
    }

    fn candidate_boundary_plan(func: &MachFunction) -> Recognized {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        let def = build_def_map(func);
        loops
            .all_loops()
            .find_map(|lp| Recognized::recognize(func, &dom, &def, lp.header, lp.latch, &lp.body))
            .expect("unmodified control must be recognized")
    }

    fn candidate_boundary_refusal(func: &mut MachFunction, rec: &Recognized) {
        let before = format!("{func:?}");
        assert!(!apply(func, rec));
        assert_eq!(
            format!("{func:?}"),
            before,
            "refusal must preserve the whole function"
        );
    }

    #[test]
    fn candidate_boundary_early_exhaustion() {
        let mut func = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&func);
        // Arm the boundary after immutable recognition; not a frontend repro.
        func.next_vreg = u32::MAX;
        candidate_boundary_refusal(&mut func, &rec);
    }

    #[test]
    fn candidate_boundary_late_exhaustion() {
        let mut func = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&func);
        // Arm the boundary after immutable recognition; not a frontend repro.
        func.next_vreg = u32::MAX - 4;
        candidate_boundary_refusal(&mut func, &rec);
    }

    #[test]
    fn candidate_boundary_metadata_exhaustion() {
        let mut func = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&func);
        // Arm the boundary after immutable recognition; not a frontend repro.
        func.noalias_params.push(u32::MAX);
        candidate_boundary_refusal(&mut func, &rec);
    }

    #[test]
    fn candidate_boundary_splice_refusal() {
        let mut func = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&func);
        // Arm the boundary after immutable recognition; not a frontend repro.
        func.inst_mut(rec.preheader_term).operands.clear();
        candidate_boundary_refusal(&mut func, &rec);
    }

    #[test]
    fn candidate_boundary_missing_setup() {
        let mut func = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&func);
        // Arm the boundary after immutable recognition; not a frontend repro.
        for block in &mut func.blocks {
            block.insts.retain(|id| *id != rec.preheader_term);
        }
        candidate_boundary_refusal(&mut func, &rec);
    }

    #[test]
    fn candidate_boundary_missing_layout() {
        let mut func = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&func);
        // Arm the boundary after immutable recognition; not a frontend repro.
        func.block_order.retain(|id| *id != rec.header);
        candidate_boundary_refusal(&mut func, &rec);
    }

    #[test]
    fn candidate_boundary_success_snapshot() {
        let mut func = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&func);
        assert!(apply(&mut func, &rec));
        println!("CANDIDATE_SNAPSHOT: {func:?}");
    }

    #[test]
    fn candidate_boundary_public_entry_points_preserve_refusal() {
        let mut control = candidate_boundary_fixture();
        assert!(NeonBitrevPass::new().run(&mut control));
        let mut func = candidate_boundary_fixture();
        func.next_vreg = u32::MAX;
        let before = format!("{func:?}");
        let mut pass = NeonBitrevPass::new();
        let mut analyses = AnalysisCache::new();
        assert!(!pass.run(&mut func));
        assert!(!pass.run_with_analyses(&mut func, &mut analyses));
        assert_eq!(pass.fired(), 0);
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn candidate_boundary_sparse_ids_include_detached_and_noalias() {
        let mut func = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&func);
        let old_ids: HashSet<_> = func
            .insts
            .iter()
            .flat_map(|inst| &inst.operands)
            .filter_map(|op| op.as_vreg().map(|reg| reg.id))
            .collect();
        func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::VReg(VReg::new(1_000_000_000, RegClass::Gpr64))],
        ));
        func.noalias_params.push(1_000_000_007);
        func.next_vreg = 0;
        let old_len = func.insts.len();
        assert!(apply(&mut func, &rec));
        let fresh: Vec<_> = func.insts[old_len..]
            .iter()
            .flat_map(|inst| &inst.operands)
            .filter_map(|op| op.as_vreg().map(|reg| reg.id))
            .filter(|id| !old_ids.contains(id))
            .collect();
        assert!(!fresh.is_empty());
        assert!(fresh.iter().all(|id| *id > 1_000_000_007));
        assert!(func.next_vreg > 1_000_000_007);
    }

    #[test]
    fn candidate_boundary_last_representable_range_preserves_construction() {
        let original = candidate_boundary_fixture();
        let rec = candidate_boundary_plan(&original);
        let mut ordinary = original.clone();
        ordinary.try_sync_vreg_counter().unwrap();
        let first = ordinary.next_vreg;
        assert!(apply(&mut ordinary, &rec));
        let count = ordinary.next_vreg - first;
        assert!(count > 1);
        let mut boundary = original.clone();
        let boundary_first = u32::MAX - count;
        boundary.next_vreg = boundary_first;
        assert!(apply(&mut boundary, &rec));
        assert_eq!(boundary.next_vreg, u32::MAX);
        for inst in &mut boundary.insts[original.insts.len()..] {
            for operand in &mut inst.operands {
                if let MachOperand::VReg(reg) = operand
                    && reg.id >= boundary_first
                {
                    reg.id = first + (reg.id - boundary_first);
                }
            }
        }
        boundary.next_vreg = ordinary.next_vreg;
        assert_eq!(format!("{boundary:?}"), format!("{ordinary:?}"));
    }

    #[test]
    fn vectorizes_canonical_byte_reverse_map() {
        let mut func = build_bitrev_loop(false);
        let mut pass = NeonBitrevPass::new();
        assert!(pass.run(&mut func), "canonical bitrev map should vectorize");
        assert_eq!(pass.fired(), 1);
        assert_eq!(
            count(&func, AArch64Opcode::NeonRbitV),
            UNROLL_Q,
            "one RBIT.16B per Q register"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), UNROLL_Q / 2);
        assert_eq!(count(&func, AArch64Opcode::NeonStpQPost), UNROLL_Q / 2);
    }

    #[test]
    fn bails_on_second_loop_carried_value() {
        // The map is byte-for-byte identical; the ONLY difference is an
        // accumulator threaded through the latch. The vector loop steps `iv`
        // alone, so vectorizing would silently drop the accumulator's updates
        // for every vectorized iteration. Fail closed.
        let mut func = build_bitrev_loop(true);
        let before = func.blocks.len();
        let mut pass = NeonBitrevPass::new();
        assert!(
            !pass.run(&mut func),
            "a second loop-carried value must BAIL (its updates would be dropped)"
        );
        assert_eq!(pass.fired(), 0);
        assert_eq!(count(&func, AArch64Opcode::NeonRbitV), 0);
        assert_eq!(func.blocks.len(), before, "no blocks added");
    }

    /// IDEMPOTENCE (the neon-bytesum / neon-fill bug class of 2026-08-27: a
    /// vectorizer that keeps the scalar loop as the remainder and then
    /// recognizes that remainder again on the next fixpoint iteration). After
    /// the first firing, further runs must change nothing.
    #[test]
    fn second_run_is_a_no_op() {
        let mut func = build_bitrev_loop(false);
        assert!(NeonBitrevPass::new().run(&mut func), "first run must fire");
        let (insts, blocks) = (func.insts.len(), func.blocks.len());
        for again in 2..=4 {
            assert!(
                !NeonBitrevPass::new().run(&mut func),
                "run {again}: re-fired on its own output"
            );
            assert_eq!(func.insts.len(), insts, "run {again} added instructions");
            assert_eq!(func.blocks.len(), blocks, "run {again} added blocks");
        }
    }

    /// A body register defined once in the loop and read after it (the last
    /// reversed byte, `last = out[i]`) is live out: the vector loop never
    /// writes it, so an empty remainder leaves it stale. Its single definition
    /// passes `loop_defs_are_unique`; only the loop-state contract refuses it.
    #[test]
    fn bails_when_a_body_register_is_read_after_the_loop() {
        let mut func = build_bitrev_loop(false);
        let exit = BlockId(4);
        let read = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![g32(90), g32(46)]));
        func.block_mut(exit).insts.insert(0, read);
        let mut pass = NeonBitrevPass::new();
        assert!(
            !pass.run(&mut func),
            "a register live out of the loop must BAIL (the vector loop never writes it)"
        );
        assert_eq!(count(&func, AArch64Opcode::NeonRbitV), 0);
    }
}
