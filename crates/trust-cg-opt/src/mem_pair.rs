//! AArch64 load/store PAIR formation (`LDP`/`STP`).
//!
//! clang pairs adjacent same-base consecutive-offset loads/stores into `LDP`/
//! `STP` (two registers moved per instruction); trust-cg's existing
//! `addr_mode` pairing is GPR64-only AND requires an address-computation chain,
//! so plain double/float loads-stores (the FP cluster — matmul_f64, the flops
//! family) stay scalar. This pass pairs adjacent consecutive accesses and
//! also uses bounded windows for load hoisting and store sinking. Windowed
//! motion checks numeric register dependencies, ordinary effects/metadata and
//! memory barriers. GPR stores may cross another plain store only when the
//! same dynamic base and checked immediate byte ranges establish disjointness;
//! distinct symbol strings and unqualified origin claims confer no permission.
//!
//! Runs AFTER the instruction scheduler (so adjacency reflects the near-final
//! order) but BEFORE register allocation, so the always-on regalloc translation
//! validator checks every pair it forms. Register-pressure spills scalarize a
//! pair back to two accesses via the `LdpRI`/`StpRI` spill materialization —
//! under one NON-OBVIOUS CONTRACT with that lowering (the fc_c8 wrong-value
//! class, fixed in eafc04f1): an `LdpRI` whose two GPR defs are BOTH spilled
//! while its base stays in a real register must be SPLIT into two independent
//! `ldr X16, [base,#off]; str X16 -> slot` sequences
//! (`materialize_spilled_load_pair`, trust-cg-codegen/src/pipeline.rs), never
//! lowered as `ldp x16, x17, [base]` holding TWO live values in the IP-scratch
//! pool at once: the frame-index eliminator borrows the OTHER IP scratch to
//! materialize far (`< -256`) spill-slot addresses and would clobber the
//! still-live second lane. trust-cg-codegen/src/frame.rs enforces this
//! fail-closed (`scratch_live_after` liveness guard), so a regression is a
//! named panic, not a silent miscompile.
//!
//! Per-pass bisect: `TRUST_CG_DISABLE_PASSES=mempair`.

use crate::effects::{
    aarch64_for_each_def_position, inst_clobbers_vreg_id, is_load_acquire, is_removable,
    opcode_effect,
};
use crate::fast_hash::FxHashMap as HashMap;
use crate::pass_manager::MachinePass;
use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap, RegClass,
    VReg,
};

/// How far ahead the windowed load pairing looks for a partner load. Loads the
/// scheduler spread apart (matmul's row loads, interleaved with the FMADDs that
/// consume them) sit within a handful of instructions; bounded to keep the scan
/// linear.
const LOAD_PAIR_WINDOW: usize = 24;

/// LDP/STP pair-formation pass. See the module docs.
pub struct MemPairFormation;

impl MachinePass for MemPairFormation {
    fn name(&self) -> &str {
        "mem-pair-formation"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_mem_pair(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_mem_pair(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_mem_pair(func, Some(provenance))
    }
}

fn ordinary_metadata(inst: &MachInst) -> bool {
    inst.flags == inst.opcode.default_flags()
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
        && inst.proof.is_none()
}

/// Only ordinary, encodable virtual scalar accesses may lose arena state.
/// Source locations and immutable lowering sidecars remain history; custom
/// effects or proof metadata cannot be erased by replacing the access.
fn pairable_scalar(inst: &MachInst, next_vreg: u32) -> bool {
    if pair_opcode(inst.opcode).is_none() || !ordinary_metadata(inst) {
        return false;
    }
    let [
        MachOperand::VReg(data),
        MachOperand::VReg(base),
        MachOperand::Imm(offset),
    ] = inst.operands.as_slice()
    else {
        return false;
    };
    let Some(size) = access_size(data.class) else {
        return false;
    };
    data.id < next_vreg
        && base.id < next_vreg
        && base.class == RegClass::Gpr64
        && ((-256..=255).contains(offset) || is_encodable_single_offset(*offset, size))
}

/// The existing ordinary AddRI shape usable as a register-materialized base.
/// Ownership collection and fold recognition must use the same eligibility.
fn ordinary_addri_base(inst: &MachInst, next_vreg: u32) -> Option<(VReg, VReg, i64)> {
    if inst.opcode != AArch64Opcode::AddRI || !ordinary_metadata(inst) {
        return None;
    }
    let [
        MachOperand::VReg(dst),
        MachOperand::VReg(root),
        MachOperand::Imm(k),
    ] = inst.operands.as_slice()
    else {
        return None;
    };
    (root != dst
        && root.class == RegClass::Gpr64
        && dst.class == RegClass::Gpr64
        && root.id < next_vreg
        && dst.id < next_vreg
        && (0..=4095).contains(k))
    .then_some((*dst, *root, *k))
}

/// Only potentially rewritten layout IDs need ownership storage. References
/// in EVERY block still count, including blocks omitted from layout. Counts
/// saturate at two: one means unique, two means an unsupported shared input.
fn candidate_ownership(func: &MachFunction) -> HashMap<InstId, u8> {
    let mut candidates = HashMap::default();
    for block_id in &func.block_order {
        for &id in &func.block(*block_id).insts {
            let inst = func.inst(id);
            if pairable_scalar(inst, func.next_vreg)
                || ordinary_addri_base(inst, func.next_vreg).is_some()
            {
                candidates.entry(id).or_insert(0u8);
            }
        }
    }
    for block in &func.blocks {
        for &id in &block.insts {
            if let Some(references) = candidates.get_mut(&id) {
                *references = references.saturating_add(1).min(2);
            }
        }
    }
    candidates
}

fn pair_at(
    func: &MachFunction,
    first: InstId,
    second: InstId,
    ownership: &HashMap<InstId, u8>,
) -> Option<MachInst> {
    if ownership.get(&first) != Some(&1) || ownership.get(&second) != Some(&1) {
        return None;
    }
    try_form_pair(func.inst(first), func.inst(second), func.next_vreg)
}

/// Access size in bytes for the register class of a scalar load/store's data
/// operand — the required consecutive-offset delta and the pair-offset scale.
fn access_size(class: RegClass) -> Option<i64> {
    match class {
        RegClass::Gpr32 | RegClass::Fpr32 => Some(4),
        RegClass::Gpr64 | RegClass::Fpr64 => Some(8),
        RegClass::Fpr128 => Some(16),
        _ => None,
    }
}

/// True for the floating-point/SIMD register classes. The `AddRI` base
/// fold-back and store-sink extension is deliberately scoped to FP data: it
/// targets the `(real, imag)` complex-array access pattern (adjacent f64
/// components addressed through separate `add` bases) that clang keeps on one
/// base. Integer/pointer loops are typically latency-bound pointer chases where
/// folding a base can lengthen the critical loop (measured: Treesort), so they
/// are left untouched.
fn is_fp_class(class: RegClass) -> bool {
    matches!(class, RegClass::Fpr32 | RegClass::Fpr64 | RegClass::Fpr128)
}

/// The pair opcode for a scalar unsigned-offset load/store, if pairable.
fn pair_opcode(single: AArch64Opcode) -> Option<AArch64Opcode> {
    match single {
        AArch64Opcode::LdrRI => Some(AArch64Opcode::LdpRI),
        AArch64Opcode::StrRI => Some(AArch64Opcode::StpRI),
        _ => None,
    }
}

/// The `LDP`/`STP` signed scaled-imm7 offset field: `off` must be a multiple of
/// the access size and `off/size` must fit `[-64, 63]`.
fn is_encodable_pair_offset(offset: i64, size: i64) -> bool {
    offset % size == 0 && (-64..=63).contains(&(offset / size))
}

/// A non-negative, size-aligned offset that fits the scalar unsigned-offset
/// `LDR`/`STR` immediate (`off/size` in `[0, 4095]`). The base-resolution
/// fold-back (below) must keep the rewritten single access encodable even if it
/// never goes on to pair, so this is a conservative fail-closed gate.
fn is_encodable_single_offset(offset: i64, size: i64) -> bool {
    offset >= 0 && offset % size == 0 && (0..=4095).contains(&(offset / size))
}

/// If `a` (at `p`) and `b` (at `p+1`) are two adjacent same-opcode
/// `LdrRI`/`StrRI` to the SAME vreg base at consecutive offsets of the same
/// register class, build the fused `LdpRI`/`StpRI`. The lower-offset access is
/// placed first (matching `LDP/STP Rt1,Rt2,[base,#lo]`). Fail-closed on any
/// deviation.
fn try_form_pair(a: &MachInst, b: &MachInst, next_vreg: u32) -> Option<MachInst> {
    if a.opcode != b.opcode || !pairable_scalar(a, next_vreg) || !pairable_scalar(b, next_vreg) {
        return None;
    }
    let pair_op = pair_opcode(a.opcode)?;
    if a.operands.len() != 3 || b.operands.len() != 3 {
        return None;
    }

    // Data register (operand 0): both same class.
    let data_a = a.operands[0].as_vreg()?;
    let data_b = b.operands[0].as_vreg()?;
    if data_a.class != data_b.class {
        return None;
    }
    let size = access_size(data_a.class)?;

    // Base register (operand 1): identical vreg (a `Special`/`SP` base — spill /
    // frame access — has no `as_vreg`, so those are left untouched).
    let base = a.operands[1].as_vreg()?;
    if b.operands[1].as_vreg()? != base {
        return None;
    }

    // Offsets (operand 2): consecutive. Order the pair lower-offset-first.
    let off_a = a.operands[2].as_imm()?;
    let off_b = b.operands[2].as_imm()?;
    let (lo_off, lo_data, hi_data) = if off_b == off_a.checked_add(size)? {
        (off_a, data_a, data_b)
    } else if off_a == off_b.checked_add(size)? {
        (off_b, data_b, data_a)
    } else {
        return None;
    };
    if !is_encodable_pair_offset(lo_off, size) {
        return None;
    }

    // `LDP` into two registers requires them DISTINCT (same-reg is CONSTRAINED
    // UNPREDICTABLE) and neither equal to the base (the address register). Stores
    // read their sources, so no such constraint.
    // Numeric virtual IDs name global slots; a conflicting W/X class view
    // cannot turn a destination/base identity into a distinct register.
    if pair_op == AArch64Opcode::LdpRI
        && (lo_data.id == hi_data.id || lo_data.id == base.id || hi_data.id == base.id)
    {
        return None;
    }

    let mut pair = MachInst::new(
        pair_op,
        vec![
            MachOperand::VReg(lo_data),
            MachOperand::VReg(hi_data),
            MachOperand::VReg(base),
            MachOperand::Imm(lo_off),
        ],
    );
    pair.source_loc = a.source_loc;
    Some(pair)
}

/// A byte range `[start, end)` written by a scalar store to `base`, tagged with
/// the store's block position (`pos`, its index in the block's inst list). The
/// position lets the load-pair hazard guard tell a within-iteration forward (a
/// store EARLIER in the block) from a WAR write that only follows the load.
#[derive(Clone, Copy)]
struct StoreRange {
    base: VReg,
    start: i64,
    end: i64,
    pos: usize,
}

/// Byte width written by a scalar base+immediate store, or `None` if `inst` is
/// not one (the transfer register's class fixes the width for `StrRI`).
fn store_access_size(inst: &MachInst) -> Option<i64> {
    match inst.opcode {
        AArch64Opcode::StrbRI => Some(1),
        AArch64Opcode::StrhRI => Some(2),
        AArch64Opcode::StrRI => access_size(inst.operands.first()?.as_vreg()?.class),
        _ => None,
    }
}

/// Collect the byte ranges written by same-base scalar RI stores in a block.
/// Used to veto LOAD-pair formation that would straddle a store (below).
fn collect_store_ranges(func: &MachFunction, insts: &[InstId]) -> Vec<StoreRange> {
    let mut ranges = Vec::new();
    for (pos, &id) in insts.iter().enumerate() {
        let inst = func.inst(id);
        let Some(size) = store_access_size(inst) else {
            continue;
        };
        let (Some(base), Some(off)) = (
            inst.operands.get(1).and_then(|o| o.as_vreg()),
            inst.operands.get(2).and_then(|o| o.as_imm()),
        ) else {
            continue;
        };
        let Some(end) = off.checked_add(size) else {
            continue;
        };
        ranges.push(StoreRange {
            base,
            start: off,
            end,
            pos,
        });
    }
    ranges
}

/// Whether forming this LOAD pair (anchored at block position `anchor`) would
/// create a store-to-load forwarding hazard: the pair reads the 2×`size`-byte
/// range `[lo_off, lo_off + 2*size)`, and some store to the SAME base vreg in
/// the block overlaps it. A wider `LDP` cannot forward from a narrower
/// overlapping store on Apple arm64 — it stalls until the store drains — so two
/// scalar loads (one of which exactly matches the store and forwards cleanly)
/// are faster, and we veto the pair.
///
/// A same-base overlapping store can only FEED this load (the stall) if it is
/// dynamically earlier:
/// - within the iteration, a store at an EARLIER block position; or
/// - across the backedge, when the shared base is loop-INVARIANT so the previous
///   iteration wrote the identical address.
///
/// When `base_is_block_local` (the base is recomputed inside this block, i.e.
/// loop-variant — the shape the `AddRI` base fold-back exposes, e.g. the FFT
/// butterfly's `a + j*8`), every iteration targets a fresh address, so only an
/// EARLIER-in-block store aliases; a store that merely follows the load is a WAR
/// write and forwards nothing. Otherwise (base possibly loop-invariant, or
/// fold-back disabled) any overlap conservatively vetoes.
///
/// Store pairs are unaffected (a wider store forwards fine to a contained
/// narrower load). Only same-base, definitely-aliasing stores veto; unknown-base
/// stores never do (fewer pairs = always correct, a pure conservative narrowing).
///
/// Kill switch: `TCG_NO_MEM_PAIR_HAZARD_GUARD` (re-enables aggressive pairing).
fn load_pair_store_hazard(
    pair: &MachInst,
    store_ranges: &[StoreRange],
    anchor: usize,
    base_is_block_local: bool,
) -> bool {
    if pair.opcode != AArch64Opcode::LdpRI {
        return false;
    }
    let Some(size) = pair
        .operands
        .first()
        .and_then(|o| o.as_vreg())
        .and_then(|v| access_size(v.class))
    else {
        return false;
    };
    let Some(base) = pair.operands.get(2).and_then(|o| o.as_vreg()) else {
        return false;
    };
    let Some(lo_off) = pair.operands.get(3).and_then(|o| o.as_imm()) else {
        return false;
    };
    let Some(end) = lo_off.checked_add(2 * size) else {
        return false;
    };
    store_ranges.iter().any(|r| {
        if r.base != base || !(r.start < end && lo_off < r.end) {
            return false;
        }
        // Overlapping same-base store. Loop-variant base ⇒ only an
        // earlier-in-block store can forward into this load; loop-invariant (or
        // fold-back off) ⇒ conservatively veto on any overlap.
        !base_is_block_local || r.pos < anchor
    })
}

/// True if any operand names the same storage ID as `v`. W/X views differ
/// in class, not identity; moving a load across either view changes its use.
fn operand_refs(inst: &MachInst, v: VReg) -> bool {
    inst.operands
        .iter()
        .any(|o| o.as_vreg().is_some_and(|r| r.id == v.id))
}

/// True if no later plain load may be hoisted above `inst`. A memory write,
/// call, barrier (`Dmb`/`Dsb`/`Isb`) or volatile access (`writes_memory()`:
/// effect `Store`/`Call`) may change the loaded slot or order the load. A
/// load-acquire ([`is_load_acquire`]) writes nothing — its effect class is
/// only `Load` — but acquire semantics order every LATER access after it:
/// hoisting a plain load above one (`ldr; ldar; ldr` -> `ldp; ldar`) lets the
/// load return a value older than the one the acquire synchronizes with.
/// Every other `Load`-class opcode is a plain (non-ordering) load.
fn blocks_load_hoist(inst: &MachInst) -> bool {
    !ordinary_metadata(inst)
        || opcode_effect(inst.opcode).writes_memory()
        || is_load_acquire(inst.opcode)
}

/// Whether a later load may be hoisted above `inst` with respect to control
/// and ordering: `inst` neither ends or diverts execution (a call, branch,
/// trap carrier, `BRK` or other terminator: the load would run where the
/// input never ran it, ahead of the very bounds or null check guarding it)
/// nor carries an ordering side effect (a barrier). `HAS_SIDE_EFFECTS` on a
/// memory-pure flag setter only marks its NZCV write, which a load does not
/// touch.
fn load_may_cross(inst: &MachInst) -> bool {
    use trust_cg_ir::InstFlags;
    let flags = inst.flags.union(inst.opcode.default_flags());
    if flags.contains(InstFlags::IS_CALL)
        || flags.contains(InstFlags::IS_BRANCH)
        || flags.contains(InstFlags::IS_TERMINATOR)
        || inst.opcode == AArch64Opcode::Brk
    {
        return false;
    }
    let effect = opcode_effect(inst.opcode);
    !flags.contains(InstFlags::HAS_SIDE_EFFECTS)
        || (effect.is_pure() && crate::effects::writes_flags(inst.opcode))
}

/// Every instruction strictly between positions `i` and `j` (in `old`) must be
/// safe to hoist the load at `j` above: it must NOT write memory / call /
/// carry acquire ordering ([`blocks_load_hoist`]), NOT end or divert execution
/// or order memory ([`load_may_cross`]: a trap carrier between the loads is
/// the second load's bounds check), NOT redefine the `base` address register,
/// and NOT reference `moved_dst` (the moved load's destination — a read would
/// see a changed value, a write would be clobbered by the moved def).
/// Reads/writes of the OTHER (stationary, position-`i`) destination are fine.
fn gap_is_hoist_safe(
    func: &MachFunction,
    old: &[InstId],
    i: usize,
    j: usize,
    base: VReg,
    moved_dst: VReg,
) -> bool {
    for &id in &old[i + 1..j] {
        let inst = func.inst(id);
        if blocks_load_hoist(inst) || !load_may_cross(inst) {
            return false;
        }
        if inst_clobbers_vreg_id(inst, base.id) {
            return false;
        }
        if operand_refs(inst, moved_dst) {
            return false;
        }
    }
    true
}

/// Find a partner `LdrRI` at `j > i` (within the window, not already consumed)
/// that pairs with the load at `old[i]` AND whose whole gap is hoist-safe. A
/// memory write / call / load-acquire / trap or branch / base redefinition
/// between halts the scan (nothing past it is reachable).
fn find_windowed_load_partner(
    func: &MachFunction,
    old: &[InstId],
    i: usize,
    consumed: &std::collections::HashSet<usize>,
    ownership: &HashMap<InstId, u8>,
) -> Option<(usize, MachInst)> {
    let a = func.inst(old[i]);
    if a.opcode != AArch64Opcode::LdrRI || ownership.get(&old[i]) != Some(&1) {
        return None; // stores are handled by the strictly-adjacent path only
    }
    let base = a.operands.get(1)?.as_vreg()?;
    let end = (i + 1 + LOAD_PAIR_WINDOW).min(old.len());
    for (j, &inst_id) in old.iter().enumerate().take(end).skip(i + 1) {
        let inst_j = func.inst(inst_id);
        if !consumed.contains(&j)
            && let (Some(moved_dst), Some(pair)) = (
                inst_j.operands.first().and_then(|o| o.as_vreg()),
                pair_at(func, old[i], inst_id, ownership),
            )
            && gap_is_hoist_safe(func, old, i, j, base, moved_dst)
        {
            return Some((j, pair));
        }
        // A barrier (store/call/load-acquire/trap/ordering access) or a base
        // redefinition at `j` means no later instruction can be hoisted over
        // it to `i`; stop scanning.
        if blocks_load_hoist(inst_j)
            || !load_may_cross(inst_j)
            || inst_clobbers_vreg_id(inst_j, base.id)
        {
            break;
        }
    }
    None
}

/// A vreg whose UNIQUE block definition is `AddRI Rd, root, #k` (with `root !=
/// Rd`) — a register-materialized base the fold-back can express as `root + k`.
#[derive(Clone, Copy)]
struct AddRiBase {
    root: VReg,
    k: i64,
    pos: usize,
}

/// Per-block dataflow the `AddRI` base fold-back needs.
struct BlockDefs {
    /// vreg id → ascending block positions at which it is WRITTEN. Uses the
    /// full operand-role table, so secondary defs (`LdpRI` op1, pre/post-index
    /// base write-back, LSE `op1`, …) count too. A base with no entry here is a
    /// block live-in (possibly loop-invariant).
    def_pos: HashMap<u32, Vec<usize>>,
    /// vreg id → its single `AddRI(root, k)` definition (see [`AddRiBase`]).
    addri: HashMap<u32, AddRiBase>,
}

impl BlockDefs {
    /// Is `v` written anywhere in this block? (loop-variant / block-local)
    fn is_block_local(&self, v: VReg) -> bool {
        self.def_pos.contains_key(&v.id)
    }

    /// True if `root` is (re)defined at some position in `(lo, hi]` — i.e. its
    /// value at `hi` may differ from its value at `lo`. The closed upper bound
    /// also rejects the self-clobber case where the access at `hi` itself writes
    /// `root` (e.g. a GPR load into its own base register).
    fn redefined_between(&self, root: VReg, lo: usize, hi: usize) -> bool {
        self.def_pos
            .get(&root.id)
            .is_some_and(|positions| positions.iter().any(|&q| q > lo && q <= hi))
    }
}

/// Analyze one block's vreg definitions and single-def `AddRI` bases.
fn analyze_block_defs(func: &MachFunction, old: &[InstId]) -> BlockDefs {
    let mut def_pos: HashMap<u32, Vec<usize>> = HashMap::default();
    for (p, &id) in old.iter().enumerate() {
        let inst = func.inst(id);
        aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
            if let Some(v) = inst.operands[pos].as_vreg() {
                def_pos.entry(v.id).or_default().push(p);
            }
        });
    }
    let mut addri: HashMap<u32, AddRiBase> = HashMap::default();
    for (p, &id) in old.iter().enumerate() {
        let inst = func.inst(id);
        let Some((dst, root, k)) = ordinary_addri_base(inst, func.next_vreg) else {
            continue;
        };
        // `root == dst` would be a self-referential fold; and only accept when
        // this AddRI is the SOLE def of `dst` in the block (so `dst` provably
        // equals `root + k` at every in-block use).
        if def_pos
            .get(&dst.id)
            .is_some_and(|v| v.len() == 1 && v[0] == p)
        {
            addri.insert(dst.id, AddRiBase { root, k, pos: p });
        }
    }
    BlockDefs { def_pos, addri }
}

/// Fold register-materialized bases back onto their root. For each scalar
/// `LdrRI`/`StrRI` whose base vreg `vB` has a single-def `AddRI(root, k)` that
/// dominates it with `root` unchanged in between, rewrite the access to
/// `[root, #off + k]` — the IDENTICAL effective address (`(root + k) + off ==
/// root + (off + k)` since `root` is stable across the interval). This exposes
/// the shared `root` base to the pairing scan below, so consecutive
/// `(real, imag)` complex components that tcg addressed through two separate
/// `add` bases — where clang keeps one base with `#0`/`#8` — fuse into
/// `LDP`/`STP`. Any `AddRI` left dead by the fold is removed by post-RA
/// dead-def elimination. Fail-closed on a non-dominating/redefined root or an
/// offset that would not stay encodable.
fn resolve_ri_bases(
    func: &mut MachFunction,
    old: &[InstId],
    defs: &BlockDefs,
    ownership: &HashMap<InstId, u8>,
) -> bool {
    let mut changed = false;
    for (p, &id) in old.iter().enumerate() {
        let inst = func.inst(id);
        if ownership.get(&id) != Some(&1) || !pairable_scalar(inst, func.next_vreg) {
            continue;
        }
        let (Some(data), Some(base), Some(off)) = (
            inst.operands[0].as_vreg(),
            inst.operands[1].as_vreg(),
            inst.operands[2].as_imm(),
        ) else {
            continue;
        };
        let Some(size) = access_size(data.class) else {
            continue;
        };
        if !is_fp_class(data.class) {
            continue; // FP complex-array pattern only (see `is_fp_class`)
        }
        let Some(ab) = defs.addri.get(&base.id).copied() else {
            continue;
        };
        // The AddRI must dominate this access (its unique def precedes it) and
        // `root` must be unchanged from the AddRI through the access.
        if ab.pos >= p
            || ownership.get(&old[ab.pos]) != Some(&1)
            || defs.redefined_between(ab.root, ab.pos, p)
        {
            continue;
        }
        let Some(new_off) = off.checked_add(ab.k) else {
            continue;
        };
        if !is_encodable_single_offset(new_off, size) {
            continue;
        }
        let m = func.inst_mut(id);
        m.operands[1] = MachOperand::VReg(ab.root);
        m.operands[2] = MachOperand::Imm(new_off);
        changed = true;
    }
    changed
}

/// How far the store-sink scan looks ahead for a consecutive partner store to
/// fuse a `STR` into an `STP`. The scan stops at the first motion barrier;
/// GPR stores also cross same-base disjoint immediate stores. This bound keeps
/// the scan linear regardless of the number of pure operations in a block.
const STORE_SINK_WINDOW: usize = 24;

/// Cross-store integer sink kill switch: `TCG_NO_MEM_PAIR_XSTORE=1` disables
/// the GPR store-sink-across-disjoint-store extension (byte-identical to the
/// FP-only sink behavior).
fn xstore_sink_enabled() -> bool {
    std::env::var_os("TCG_NO_MEM_PAIR_XSTORE").is_none()
}

/// True when a plain immediate gap store cannot overlap the sunk store's
/// access. Both use the SAME full-width base value: the scan refuses every
/// numeric-ID redefinition before reaching this operation. Checked static
/// byte intervals are then disjoint without an object-origin assumption.
///
/// Different symbol spellings, additive roots and source `inbounds`/`noalias`
/// claims do not authenticate distinct allocations at this stage. Register-
/// offset, ordered, pair and write-back stores therefore fail this rule closed.
fn provably_disjoint_gap_store(s: &MachInst, a_base: VReg, a_off: i64, a_size: i64) -> bool {
    if !matches!(
        s.opcode,
        AArch64Opcode::StrRI | AArch64Opcode::StrbRI | AArch64Opcode::StrhRI
    ) {
        return false;
    }
    let [
        MachOperand::VReg(_),
        MachOperand::VReg(base),
        MachOperand::Imm(s_off),
    ] = s.operands.as_slice()
    else {
        return false;
    };
    if *base != a_base {
        return false;
    }
    let Some(s_size) = store_access_size(s) else {
        return false;
    };
    let (Some(a_end), Some(s_end)) = (a_off.checked_add(a_size), s_off.checked_add(s_size)) else {
        return false;
    };
    s_end <= a_off || a_end <= *s_off
}

/// A write through ANY modeled definition clobbers the numeric storage ID,
/// including W/X views and secondary defs. Keep the shared role visitor
/// authoritative instead of comparing exact typed carriers locally.
fn inst_defs_vreg(inst: &MachInst, v: VReg) -> bool {
    inst_clobbers_vreg_id(inst, v.id)
}

/// Find a later `StrRI` at `j > i` (within the window, not consumed) that pairs
/// with the store at `old[i]` and can absorb it by SINKING the earlier store
/// DOWN to `j`. The later store's data is typically computed between the two
/// stores (the FFT butterfly interleaves `fadd`/`fmul` with the write-backs), so
/// the pair must land at `j` (hoisting the partner UP is impossible — its value
/// is not yet live at `i`). Sinking is sound only across MEMORY-PURE ops that
/// leave the sunk store's data/base intact: a delayed write is unobservable when
/// nothing in the gap reads or writes memory. The first op that is not pure (or
/// clobbers data/base) halts the scan — a store may not cross an
/// aliasing/ordered access. Returns `(j, stp)` for emission at `j`'s position.
fn find_sink_store_partner(
    func: &MachFunction,
    old: &[InstId],
    i: usize,
    consumed: &std::collections::HashSet<usize>,
    gpr_sink_enabled: bool,
    ownership: &HashMap<InstId, u8>,
) -> Option<(usize, MachInst)> {
    let a = func.inst(old[i]);
    if a.opcode != AArch64Opcode::StrRI || ownership.get(&old[i]) != Some(&1) {
        return None; // loads use the windowed-hoist path; only StrRI sinks
    }
    let data = a.operands.first()?.as_vreg()?;
    // FP keeps its pure-computation-gap behavior. GPR admission is a policy
    // bit, not optional provenance: safe pure gaps and checked same-base
    // disjoint ranges require no function-wide name-root maps.
    let is_fp = is_fp_class(data.class);
    if !is_fp && !gpr_sink_enabled {
        return None;
    }
    let base = a.operands.get(1)?.as_vreg()?;
    let a_off = a.operands.get(2)?.as_imm()?;
    let a_size = access_size(data.class)?;
    let end = (i + 1 + STORE_SINK_WINDOW).min(old.len());
    for (j, &inst_id) in old.iter().enumerate().take(end).skip(i + 1) {
        let inst_j = func.inst(inst_id);
        // The partner store (checked before the purity gate below, since a store
        // is itself non-pure): the whole gap `(i, j)` already passed the
        // pure + no-clobber test in the earlier iterations.
        if !consumed.contains(&j)
            && let Some(stp) = pair_at(func, old[i], inst_id, ownership)
        {
            return Some((j, stp));
        }
        // Otherwise the earlier store can only sink across an op that is fully
        // side-effect-free AND leaves its data/base registers intact; anything
        // else halts the scan. `is_removable` = memory-pure with no flag writes
        // and, crucially, NO trap: a trap that fires would abort before the sunk
        // store ran, so the delayed write must never cross one. The GPR path
        // additionally admits a PROVABLY-DISJOINT plain store in the gap
        // (`provably_disjoint_gap_store` — SAME-base disjoint ranges only):
        // delaying the sunk write past a
        // write it cannot overlap leaves every later read and the final
        // memory state unchanged.
        let gap_ok = if !ordinary_metadata(inst_j) {
            false
        } else if is_removable(inst_j.opcode) {
            true
        } else if !is_fp {
            provably_disjoint_gap_store(inst_j, base, a_off, a_size)
        } else {
            false
        };
        if !gap_ok || inst_defs_vreg(inst_j, data) || inst_defs_vreg(inst_j, base) {
            break;
        }
    }
    None
}

fn run_mem_pair(func: &mut MachFunction, provenance: Option<&mut ProvenanceMap>) -> bool {
    // Exact no-work prefilter: fold-back also requires one of these ordinary
    // scalar accesses. Pure/no-admitted-access functions need no ownership or
    // address-provenance census.
    if !func
        .block_order
        .iter()
        .flat_map(|id| func.block(*id).insts.iter())
        .any(|&id| pairable_scalar(func.inst(id), func.next_vreg))
    {
        return false;
    }
    let ownership = candidate_ownership(func);
    let hazard_guard = crate::env_lock::var_os("TCG_NO_MEM_PAIR_HAZARD_GUARD").is_none();
    // `AddRI` base fold-back (folds `vB = add root,#k` bases onto `root`) plus
    // the loop-variant-base hazard exception it needs to let the resulting load
    // pairs form.
    // Capture GPR sink policy once. The admitted pure-gap and same-base range
    // cases need no global definition maps or unqualified symbol-root facts.
    // `TCG_NO_MEM_PAIR_XSTORE=1` retains the existing FP-only sink behavior.
    let gpr_sink_enabled = xstore_sink_enabled();
    let mut changed = false;
    let mut retired = Vec::new();
    let mut merges = Vec::new();
    for block_id in func.block_order.clone() {
        let old = func.blocks[block_id.0 as usize].insts.clone();
        // Fold register-materialized bases back onto their root FIRST, so the
        // store-range collection and pairing scan below observe canonical bases.
        let defs = analyze_block_defs(func, &old);
        if resolve_ri_bases(func, &old, &defs, &ownership) {
            changed = true;
        }
        // Same-base store byte-ranges in this block; used to veto LOAD-pair
        // formation that would straddle a store (forwarding-stall hazard).
        let store_ranges = if hazard_guard {
            collect_store_ranges(func, &old)
        } else {
            Vec::new()
        };
        // Is a formed pair's base recomputed inside this block (loop-variant)?
        // Only then does the hazard guard admit stores that merely follow. Scoped
        // to FP pairs (the fold-back's domain); integer pairs keep the strict
        // guard so this extension never perturbs latency-bound integer loops.
        let base_is_block_local = |pair: &MachInst| -> bool {
            let is_fp = pair
                .operands
                .first()
                .and_then(|o| o.as_vreg())
                .is_some_and(|d| is_fp_class(d.class));
            is_fp
                && pair
                    .operands
                    .get(2)
                    .and_then(|o| o.as_vreg())
                    .is_some_and(|base| defs.is_block_local(base))
        };
        let mut consumed: std::collections::HashSet<usize> = std::collections::HashSet::new();
        // Store-sink landings: `pending_stp[j]` is the `STP` that replaces the
        // partner store at position `j`, absorbing an earlier store sunk down to
        // it. Emitted when the scan reaches `j` (checked before `consumed`).
        let mut pending_stp: std::collections::HashMap<usize, (MachInst, [InstId; 2])> =
            std::collections::HashMap::new();
        let mut new_insts = Vec::with_capacity(old.len());
        for i in 0..old.len() {
            if let Some((stp, sources)) = pending_stp.remove(&i) {
                let id = func.push_inst(stp);
                new_insts.push(id);
                retired.extend(sources);
                if provenance.is_some() {
                    merges.push((sources, id));
                }
                changed = true;
                continue; // a sunk store pair lands here
            }
            if consumed.contains(&i) {
                continue; // already fused as a partner
            }
            // 1) Strictly-adjacent fusion (loads OR stores): zero instructions
            // between, so trivially safe.
            if i + 1 < old.len()
                && !consumed.contains(&(i + 1))
                && let Some(pair) = pair_at(func, old[i], old[i + 1], &ownership)
                && !load_pair_store_hazard(&pair, &store_ranges, i, base_is_block_local(&pair))
            {
                let id = func.push_inst(pair);
                new_insts.push(id);
                let sources = [old[i], old[i + 1]];
                retired.extend(sources);
                if provenance.is_some() {
                    merges.push((sources, id));
                }
                consumed.insert(i + 1);
                changed = true;
                continue;
            }
            // 2) Windowed LOAD fusion: hoist a later same-base consecutive load
            // up to `i` when the whole gap is hoist-safe.
            if let Some((j, pair)) =
                find_windowed_load_partner(func, &old, i, &consumed, &ownership)
                && !load_pair_store_hazard(&pair, &store_ranges, i, base_is_block_local(&pair))
            {
                let id = func.push_inst(pair);
                new_insts.push(id);
                let sources = [old[i], old[j]];
                retired.extend(sources);
                if provenance.is_some() {
                    merges.push((sources, id));
                }
                consumed.insert(j);
                changed = true;
                continue;
            }
            // 3) Windowed STORE fusion: sink this store DOWN to a later
            // consecutive partner across a memory-pure gap. The pair is emitted
            // at the partner's position (`pending_stp`), so drop `old[i]` here.
            // Gated with the base fold-back it complements (butterfly write-back
            // pairing). Load hazard guard is irrelevant to store pairs.
            if let Some((j, stp)) =
                find_sink_store_partner(func, &old, i, &consumed, gpr_sink_enabled, &ownership)
            {
                pending_stp.insert(j, (stp, [old[i], old[j]]));
                consumed.insert(j);
                changed = true;
                continue;
            }
            new_insts.push(old[i]);
        }
        func.blocks[block_id.0 as usize].insts = new_insts;
    }
    // Only IDs actually replaced by this run are candidates. The shared
    // helper checks EVERY remaining block reference before making a stable
    // arena slot inert; unrelated or still-linked instructions stay intact.
    crate::retirement::retire_unlinked_before(func, &retired, |unlinked| {
        if let Some(provenance) = provenance {
            let pass = PassId::new("mem-pair-formation");
            for (sources, merged) in merges {
                let (consumed, live): (&[InstId], &[InstId]) = match (
                    unlinked.contains(&sources[0]),
                    unlinked.contains(&sources[1]),
                ) {
                    (true, true) => (&sources, &[]),
                    (true, false) => (&sources[..1], &sources[1..]),
                    (false, true) => (&sources[1..], &sources[..1]),
                    (false, false) => (&[], &sources),
                };
                if live.is_empty() {
                    provenance.record_merge(consumed, merged, pass.clone());
                } else {
                    provenance.record_merge_with_live_sources(consumed, live, merged, pass.clone());
                }
            }
        }
    });
    changed
}

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "mem_pair_retirement_tests.rs"]
mod retirement_tests;
