// trust-cg-verify/post_ra_captured_spec.rs - TV-5 Stage A captured-spec value-flow check
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-5 **Stage A**: captured-spec value-flow validation of the post-fixup
//! x86-64 coalescing window (`[TCG-POST-RA-SPEC-WARN]`).
//!
//! # What this closes
//!
//! TV-5 v1 ([`crate::post_ra_dataflow`]) validates TIED-operand value routing
//! plus CFG lane-aware call/flags-clobber discipline on the final stream, but
//! documents two misses: wrong-value routing at NON-tied use slots (exactly
//! what a coalescer bug produces — a bad rename of a plain read) and memory
//! dataflow. Stage A closes the non-tied register half with a captured spec:
//!
//! * **Capture** the instruction stream right after `fixup_two_address` (the
//!   verified-faithful stream — every later value-routing mutation in the
//!   window is the `MovRR` coalescer).
//! * **Check** right after the coalescer: per block, symbolically execute BOTH
//!   streams with one shared, hash-consed term algebra anchored at opaque
//!   `BlockIn{loc, lane}` leaves, and require
//!   (a) equal ordered **event** sequences — every non-copy instruction is an
//!   event keyed by opcode + non-register operand structure + the exact
//!   input value terms it consumes (stores, call argument terms, and
//!   terminator flag consumers are therefore all covered), and
//!   (b) equal **exit terms** at every location the SPEC has live-out
//!   (spec-side lane liveness; the final stream may legitimately differ
//!   at dead locations, e.g. a deleted copy's target).
//!
//! Register identity is deliberately EXCLUDED from term keys (operand tags
//! collapse every register to `Reg`; definition terms are keyed by the
//! producing operation + def ordinal, never the destination location), so a
//! value-faithful rename produces IDENTICAL terms while any wrong-source
//! rename, deleted load-bearing copy, or non-commutative operand swap
//! diverges.
//!
//! IMPURE operations additionally carry an **impurity nonce**: every op whose
//! result is not a pure function of its input value terms — any call, any
//! memory-VALUE read (`MovRM`-class loads, RIP-relative loads, folded
//! memory-operand ALU/`Div`/`Idiv` forms, `Pop`'s implicit stack read), and
//! every atomic/interlocked op — is keyed by its ordinal position in the
//! block's EVENT sequence. Twin impure ops (two loads from one address across
//! an intervening store; two identical-argument calls to an impure function)
//! therefore never intern to one term, and a wrong-source rename between the
//! twins' result registers is refuted: the registers-only closure includes
//! twin-impure-op discrimination. The nonce is sound between the two streams
//! because copies are NON-events — a legitimate copy deletion never shifts an
//! event ordinal — and the spec and final streams number events identically
//! because check (a) and the exit-term check both already require equal
//! ordered event sequences (any inserted, deleted, or reordered event refutes
//! the stream on its own before a nonce could misalign). Pure
//! register-to-register/immediate ops keep identity-free keys, preserving the
//! core design property above exactly where value equality IS structural.
//!
//! # False-positive design points (each pinned by a unit test)
//!
//! * Deleted dead copies: exit terms are compared only at SPEC-side live-out
//!   lanes, and the spec-side liveness use/kill sets are pointwise no coarser
//!   than the coalescer's own conservative liveness (so a location the
//!   coalescer proved dead is never compared).
//! * Instruction indexes shift when a copy is deleted: no term is keyed by an
//!   instruction index — operation terms are structural, and `MovRR32`
//!   zero-extended upper lanes are the shared constant `Zero`, not a fresh
//!   per-site definition.
//! * `fixup_two_address`'s scratch-repair triangle: definition terms use the
//!   def ORDINAL within the instruction, never the destination register, so
//!   re-routing a result through a scratch keeps terms identical.
//! * Commutative operand swaps: for the verify-owned mirror of codegen's
//!   `is_x86_commutative_two_address_rr`, the two register value groups are
//!   sorted before keying (pinned against drift by a codegen-side test).
//! * The `xor r,r`/`pxor x,x` zero idiom: v1's classifier models the idiom as
//!   a pure def (no reads), so a rename that turns `xor a, a, b` (where `b`
//!   provably held `a`'s value) into the idiom form is normalized — equal
//!   input groups on XOR collapse to the same zero-result event.
//!
//! # Documented Stage A misses (sound to skip; never a false-positive source)
//!
//! * Memory VALUE dataflow: no memory cells are tracked, so a load's result
//!   term does not model WHICH stored value it observes. Loads are keyed by
//!   their address terms PLUS the impurity nonce, so two loads from one
//!   address are distinct instances (twin-load conflation across a store is
//!   CLOSED); stores are fully evented, so store ordering/content/addresses
//!   are compared. What remains open is only value flow THROUGH memory (e.g.
//!   proving a reload returns the just-stored value) — sound to skip: the
//!   checker never equates two memory-derived values unless they are the
//!   same instance.
//! * Cross-block value routing is compared only through block-exit terms at
//!   spec-live-out locations (the coalescer is block-local by construction).
//!
//! # Enforcement
//!
//! Stage A ships WARN-only: [`X86_POST_RA_SPEC_DEFAULT`] is `Warn`; a mismatch
//! records a greppable `[TCG-POST-RA-SPEC-WARN]` line plus a process-wide
//! counter and never fails the compile. `TCG_POST_RA_SPEC=off|warn|enforce`
//! selects the mode; the differential corpus decides promotion to enforce.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use trust_cg_ir::regs::VReg;
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_ir::x86_64_regs::{
    RAX, RDX, X86_CALLER_SAVED_GPRS, X86PReg, XMM0, XMM1, x86_preg_name,
};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{X86CallAbi, X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::post_ra_dataflow::{
    FLAGS_LOC, GPR_LANE_MASK, InstAccess, NUM_LOCS, SYMBOLIC_LANES, WINDOWS_X64_CALLER_SAVED_GPRS,
    XMM_LANE_MASK, classify_x86_post_ra_inst, loc_of, low_bits_lane_mask,
};
use crate::post_regalloc_recheck::PostRegallocRecheckMode;

/// Number of tracked arithmetic flag lanes (CF/PF/AF/ZF/SF/OF as bits 0..=5 of
/// the v1 `FlagMask` layout, stored in lanes 0..=5 of the `FLAGS_LOC` row).
const FLAG_LANES: usize = 6;
const FLAGS_ALL_LANES: u16 = (1 << FLAG_LANES) - 1;

// ---------------------------------------------------------------------------
// Violations
// ---------------------------------------------------------------------------

/// Which captured-spec value-flow property broke.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostRaSpecViolationKind {
    /// The final stream's block set / order / successor lists differ from the
    /// captured spec — the coalescing window must never restructure the CFG.
    BlockStructureMismatch,
    /// The ordered per-block event sequences diverge: some non-copy
    /// instruction consumes different value terms (or different instructions
    /// execute) in the final stream than the captured spec.
    EventStreamMismatch,
    /// A block-exit location the SPEC holds live-out carries a different
    /// value term in the final stream (a deleted or misrouted edge commit).
    LiveOutValueMismatch,
}

impl PostRaSpecViolationKind {
    /// Greppable tag for the diagnostic line.
    pub fn tag(self) -> &'static str {
        match self {
            Self::BlockStructureMismatch => "block-structure-mismatch",
            Self::EventStreamMismatch => "event-stream-mismatch",
            Self::LiveOutValueMismatch => "live-out-value-mismatch",
        }
    }
}

/// A single captured-spec violation. Under `Enforce` any one of these fails
/// the function's compile closed; under the default `Warn` it is telemetry.
#[derive(Debug, Clone)]
pub struct PostRaSpecViolation {
    /// Which property broke.
    pub kind: PostRaSpecViolationKind,
    /// Human-readable diagnostic (block, event index, opcodes, locations).
    pub detail: String,
}

// ---------------------------------------------------------------------------
// Mode + telemetry
// ---------------------------------------------------------------------------

/// Default mode for Stage A: WARN-only rollout. The corpus decides promotion.
pub const X86_POST_RA_SPEC_DEFAULT: PostRegallocRecheckMode = PostRegallocRecheckMode::Warn;

/// Parse a `TCG_POST_RA_SPEC` value; anything unrecognized keeps the default.
pub fn parse_post_ra_spec_mode(raw: Option<&str>) -> PostRegallocRecheckMode {
    match raw.map(|s| s.trim().to_ascii_lowercase()).as_deref() {
        Some("off") => PostRegallocRecheckMode::Off,
        Some("warn") => PostRegallocRecheckMode::Warn,
        Some("enforce") => PostRegallocRecheckMode::Enforce,
        _ => X86_POST_RA_SPEC_DEFAULT,
    }
}

/// Resolve the active mode from `TCG_POST_RA_SPEC` (default WARN).
pub fn post_ra_spec_mode() -> PostRegallocRecheckMode {
    parse_post_ra_spec_mode(std::env::var("TCG_POST_RA_SPEC").ok().as_deref())
}

/// Process-wide count of captured-spec violations observed (warn or enforce).
static SPEC_HITS: AtomicU64 = AtomicU64::new(0);

/// Total captured-spec violations observed by this process.
pub fn post_ra_spec_hit_count() -> u64 {
    SPEC_HITS.load(Ordering::Relaxed)
}

/// Record one violation: bump the counter and print a greppable line.
fn record(arch: &str, function_name: &str, kind_tag: &str, detail: &str, failing: bool) {
    SPEC_HITS.fetch_add(1, Ordering::Relaxed);
    let tag = if failing {
        "[TCG-POST-RA-SPEC-FAIL]"
    } else {
        "[TCG-POST-RA-SPEC-WARN]"
    };
    eprintln!("{tag} arch={arch} fn={function_name} kind={kind_tag}: {detail}");
}

// ---------------------------------------------------------------------------
// Capture
// ---------------------------------------------------------------------------

struct SpecBlock {
    insts: Vec<X86ISelInst>,
    successors: Vec<Block>,
}

/// The captured post-`fixup_two_address` stream: the value-routing spec the
/// coalesced final stream is checked against.
pub struct X86PostFixupSpec {
    name: String,
    block_order: Vec<Block>,
    blocks: HashMap<Block, SpecBlock>,
}

/// Capture the post-fixup stream as the coalescing-window spec. Returns
/// `None` when the mode is `Off` (zero work). The caller is responsible for
/// skipping capture when the window is empty (O0 / coalescer kill-switch).
pub fn capture_x86_post_fixup_spec(func: &X86ISelFunction) -> Option<X86PostFixupSpec> {
    if post_ra_spec_mode() == PostRegallocRecheckMode::Off {
        return None;
    }
    let mut blocks = HashMap::with_capacity(func.block_order.len());
    for block_id in &func.block_order {
        if let Some(block) = func.blocks.get(block_id) {
            blocks.insert(
                *block_id,
                SpecBlock {
                    insts: block.insts.clone(),
                    successors: block.successors.clone(),
                },
            );
        }
    }
    Some(X86PostFixupSpec {
        name: func.name.clone(),
        block_order: func.block_order.clone(),
        blocks,
    })
}

// ---------------------------------------------------------------------------
// Verify-owned commutativity mirror
// ---------------------------------------------------------------------------

/// Verify-side mirror of codegen's `is_x86_commutative_two_address_rr`
/// (pipeline.rs), byte-for-byte membership. Pinned against drift by
/// `post_ra_spec_commutative_mirror_pinned` here and by a codegen-side test
/// comparing it to the codegen function directly. Only opcodes in this set
/// have their two register input groups canonically sorted, so mirror UNDER-
/// inclusion can only make the check stricter, never unsound.
pub fn post_ra_spec_commutative_two_address_rr(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        AddRR
            | AndRR
            | OrRR
            | XorRR
            | ImulRR
            | Addsd
            | Mulsd
            | Andpd
            | Addss
            | Mulss
            | Andps
            | Pand
            | Por
            | Pxor
            | Pcmpeqb
            | Pcmpeqw
            | Pcmpeqd
            | Paddb
            | Paddw
            | Paddd
            | Paddq
            | Pmullw
            | Pmuludq
            | Pmulld
            | Pcmpeqq
            | Addps
            | Mulps
            | Addpd
            | Mulpd
    )
}

// ---------------------------------------------------------------------------
// Hash-consed term algebra
// ---------------------------------------------------------------------------

type TermId = u32;

/// Non-register operand structure, with every register collapsed to [`Reg`]:
/// a value-faithful rename must not perturb an operation's key.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum OperandTag {
    Reg,
    Imm(i64),
    FImm(u64),
    BlockRef(u32),
    Cond(X86CondCode),
    Symbol(String),
    Slot(u32),
    Pool(usize),
    JumpTable(u32),
    Mem {
        base: Box<OperandTag>,
        disp: i32,
    },
    Sib {
        base: Box<OperandTag>,
        index: Box<OperandTag>,
        scale: u8,
        disp: i32,
    },
}

fn operand_tag(op: &X86ISelOperand) -> OperandTag {
    match op {
        X86ISelOperand::VReg(_) | X86ISelOperand::PReg(_) => OperandTag::Reg,
        X86ISelOperand::Imm(v) => OperandTag::Imm(*v),
        X86ISelOperand::FImm(f) => OperandTag::FImm(f.to_bits()),
        X86ISelOperand::Block(b) => OperandTag::BlockRef(b.0),
        X86ISelOperand::CondCode(cc) => OperandTag::Cond(*cc),
        X86ISelOperand::Symbol(s) => OperandTag::Symbol(s.clone()),
        X86ISelOperand::StackSlot(slot) => OperandTag::Slot(*slot),
        X86ISelOperand::ConstPoolEntry(idx) => OperandTag::Pool(*idx),
        X86ISelOperand::JumpTableIndex(idx) => OperandTag::JumpTable(*idx),
        X86ISelOperand::MemAddr { base, disp } => OperandTag::Mem {
            base: Box::new(operand_tag(base)),
            disp: *disp,
        },
        X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } => OperandTag::Sib {
            base: Box::new(operand_tag(base)),
            index: Box::new(operand_tag(index)),
            scale: *scale,
            disp: *disp,
        },
    }
}

/// A hash-consed symbolic value/operation term. NO variant is keyed by an
/// instruction index or a definition location: keys are fully structural so
/// copy deletions (index shifts) and value-faithful renames leave every term
/// identical between the spec and the final stream.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TermNode {
    /// Opaque block-entry value of one byte lane of one location.
    BlockIn { loc: u8, lane: u8 },
    /// The architectural constant zero byte (e.g. `MovRR32` upper lanes and
    /// the XOR zero idiom's result).
    Zero,
    /// One executed non-copy operation: opcode + non-register operand
    /// structure + the exact input value terms consumed (canonicalized), plus
    /// a call's declared result metadata. IMPURE operations (calls, memory
    /// reads, atomics — see [`op_requires_impurity_nonce`]) also carry their
    /// per-block event ordinal, so twin impure ops never intern to one term;
    /// pure ops keep `None` (identity-free keys, the core design property).
    Op {
        opcode: X86Opcode,
        tags: Vec<OperandTag>,
        inputs: Vec<TermId>,
        call_results_meta: Vec<(u8, u16)>,
        impurity_nonce: Option<u32>,
    },
    /// One byte lane of the `ordinal`-th definition of operation `op`. The
    /// destination LOCATION is deliberately not part of the key.
    Proj { op: TermId, ordinal: u8, lane: u8 },
    /// One byte lane clobbered (not meaningfully defined) by call `op`. The
    /// clobbered location set is ABI-fixed, so keying by location is stable.
    Clobber { op: TermId, loc: u8, lane: u8 },
    /// One arithmetic flag defined by operation `op`.
    FlagDef { op: TermId, flag: u8 },
    /// One arithmetic flag made architecturally undefined by operation `op`.
    FlagUndef { op: TermId, flag: u8 },
    /// One arithmetic flag that operation `op` may leave undefined on a
    /// value-dependent path while preserving `old` on another.
    FlagMay { op: TermId, flag: u8, old: TermId },
}

#[derive(Default)]
struct TermTable {
    ids: HashMap<TermNode, TermId>,
}

impl TermTable {
    fn intern(&mut self, node: TermNode) -> TermId {
        let next = self.ids.len() as TermId;
        *self.ids.entry(node).or_insert(next)
    }
}

/// Per-block symbolic state: one term per byte lane per location. The
/// `FLAGS_LOC` row carries the six flag lanes in lanes 0..=5.
type LaneTermState = [[TermId; SYMBOLIC_LANES]; NUM_LOCS];

/// Per-location lane masks (liveness sets; flags in row `FLAGS_LOC`).
type LaneMaskSet = [u16; NUM_LOCS];

fn block_entry_state(table: &mut TermTable) -> LaneTermState {
    let mut state = [[0 as TermId; SYMBOLIC_LANES]; NUM_LOCS];
    for (loc, row) in state.iter_mut().enumerate() {
        for (lane, cell) in row.iter_mut().enumerate() {
            *cell = table.intern(TermNode::BlockIn {
                loc: loc as u8,
                lane: lane as u8,
            });
        }
    }
    state
}

// ---------------------------------------------------------------------------
// Per-instruction use/def lane sets (spec-side liveness)
// ---------------------------------------------------------------------------

/// Exact lanes this instruction reads / definitely overwrites, in the same
/// access model the executor uses. The USE set is pointwise no coarser than
/// the coalescer's `x86_inst_gpr64_use_roots` model at GPR-root granularity
/// (so spec-side live-out can never exceed the liveness the coalescer's own
/// deletions were justified against), and the DEF (kill) set is pointwise no
/// finer than its full-kill set.
fn inst_lane_uses_defs(
    inst: &X86ISelInst,
    acc: &InstAccess,
    call_abi: X86CallAbi,
) -> (LaneMaskSet, LaneMaskSet) {
    let mut uses: LaneMaskSet = [0; NUM_LOCS];
    let mut defs: LaneMaskSet = [0; NUM_LOCS];

    for read in &acc.lane_reads {
        uses[read.loc as usize] |= read.mask;
    }
    uses[FLAGS_LOC as usize] |= acc.flags_use_mask & FLAGS_ALL_LANES;
    if inst.flags.is_return() {
        for (reg, mask) in return_value_reads() {
            if let Some(loc) = loc_of(reg) {
                uses[loc as usize] |= mask;
            }
        }
    }

    if let Some(copy) = acc.lane_copy {
        defs[copy.dst as usize] |= copy.write_mask;
    } else if let Some((a, b)) = acc.xchg {
        defs[a as usize] |= XMM_LANE_MASK;
        defs[b as usize] |= XMM_LANE_MASK;
    } else {
        for def in &acc.lane_defs {
            defs[def.loc as usize] |= def.mask;
        }
    }
    if let Some(results) = &acc.call_result_locs {
        for reg in caller_saved_gprs(call_abi) {
            if let Some(loc) = loc_of(*reg) {
                defs[loc as usize] |= GPR_LANE_MASK;
            }
        }
        for xmm in 0..caller_saved_xmm_count(call_abi) {
            if let Some(loc) = loc_of(X86PReg::new(64 + xmm)) {
                defs[loc as usize] |= XMM_LANE_MASK;
            }
        }
        defs[FLAGS_LOC as usize] |= FLAGS_ALL_LANES;
        for result in results {
            defs[result.loc as usize] |= low_bits_lane_mask(result.defined_bits);
        }
    }
    defs[FLAGS_LOC as usize] |= (acc.flags_def_mask | acc.flags_undef_mask) & FLAGS_ALL_LANES;
    // flags_may_undef preserves on some path: never a kill.

    (uses, defs)
}

fn caller_saved_gprs(call_abi: X86CallAbi) -> &'static [X86PReg] {
    match call_abi {
        X86CallAbi::SystemV => &X86_CALLER_SAVED_GPRS,
        X86CallAbi::WindowsX64 => &WINDOWS_X64_CALLER_SAVED_GPRS,
    }
}

fn caller_saved_xmm_count(call_abi: X86CallAbi) -> u16 {
    match call_abi {
        X86CallAbi::SystemV => 16,
        X86CallAbi::WindowsX64 => 6,
    }
}

/// ABI return-value registers read at a `Ret` event. The coalescer treats
/// calls/returns as hard barriers and models RAX/RDX as implicit return uses,
/// so these terms are provably preserved by every sound coalescer action —
/// eventing them closes deleted return-value copies without any FP exposure.
fn return_value_reads() -> [(X86PReg, u16); 4] {
    [
        (RAX, GPR_LANE_MASK),
        (RDX, GPR_LANE_MASK),
        (XMM0, XMM_LANE_MASK),
        (XMM1, XMM_LANE_MASK),
    ]
}

// ---------------------------------------------------------------------------
// Spec-side lane liveness (backward may-analysis over the captured CFG)
// ---------------------------------------------------------------------------

fn spec_live_out(
    spec: &X86PostFixupSpec,
    accs: &HashMap<Block, Vec<InstAccess>>,
    call_abi: X86CallAbi,
) -> Option<HashMap<Block, LaneMaskSet>> {
    // Per-block gen (use-before-kill) / kill summaries.
    let mut block_use: HashMap<Block, LaneMaskSet> = HashMap::new();
    let mut block_def: HashMap<Block, LaneMaskSet> = HashMap::new();
    for block_id in &spec.block_order {
        let (mut use_b, mut def_b): (LaneMaskSet, LaneMaskSet) = ([0; NUM_LOCS], [0; NUM_LOCS]);
        if let (Some(block), Some(block_accs)) = (spec.blocks.get(block_id), accs.get(block_id)) {
            for (inst, acc) in block.insts.iter().zip(block_accs) {
                let (uses, defs) = inst_lane_uses_defs(inst, acc, call_abi);
                for loc in 0..NUM_LOCS {
                    use_b[loc] |= uses[loc] & !def_b[loc];
                    def_b[loc] |= defs[loc];
                }
            }
        }
        block_use.insert(*block_id, use_b);
        block_def.insert(*block_id, def_b);
    }

    let mut live_in: HashMap<Block, LaneMaskSet> = spec
        .block_order
        .iter()
        .map(|b| (*b, [0; NUM_LOCS]))
        .collect();

    let mut changed = true;
    let mut sweeps = 0usize;
    let cap = spec.block_order.len().saturating_mul(4).max(16);
    while changed && sweeps < cap {
        changed = false;
        sweeps += 1;
        for block_id in spec.block_order.iter().rev() {
            let mut out: LaneMaskSet = [0; NUM_LOCS];
            if let Some(block) = spec.blocks.get(block_id) {
                for succ in &block.successors {
                    if let Some(s_in) = live_in.get(succ) {
                        for loc in 0..NUM_LOCS {
                            out[loc] |= s_in[loc];
                        }
                    }
                }
            }
            let use_b = &block_use[block_id];
            let def_b = &block_def[block_id];
            let mut new_in: LaneMaskSet = [0; NUM_LOCS];
            for loc in 0..NUM_LOCS {
                new_in[loc] = use_b[loc] | (out[loc] & !def_b[loc]);
            }
            let entry = live_in.get_mut(block_id).expect("seeded above");
            if *entry != new_in {
                *entry = new_in;
                changed = true;
            }
        }
    }
    // FAIL-OPEN on non-convergence (should be unreachable for a monotone
    // fixpoint under this cap): exit-term comparison is skipped rather than
    // risking an over-approximate live set flagging a sound deletion. The
    // event-stream comparison still runs at full strength.
    if changed {
        return None;
    }

    let mut live_out: HashMap<Block, LaneMaskSet> = HashMap::new();
    for block_id in &spec.block_order {
        let mut out: LaneMaskSet = [0; NUM_LOCS];
        if let Some(block) = spec.blocks.get(block_id) {
            for succ in &block.successors {
                if let Some(s_in) = live_in.get(succ) {
                    for loc in 0..NUM_LOCS {
                        out[loc] |= s_in[loc];
                    }
                }
            }
        }
        live_out.insert(*block_id, out);
    }
    Some(live_out)
}

// ---------------------------------------------------------------------------
// Per-block symbolic execution
// ---------------------------------------------------------------------------

struct BlockRun {
    /// Interned `Op` term per non-copy instruction, in stream order.
    events: Vec<TermId>,
    /// `(instruction index, opcode)` per event, for diagnostics.
    event_sites: Vec<(usize, X86Opcode)>,
    /// Lane terms at block exit.
    exit: LaneTermState,
}

/// True when the instruction has any memory-shaped operand (used to restrict
/// commutative-group sorting and idiom normalization to pure register forms).
fn has_memory_operand(inst: &X86ISelInst) -> bool {
    inst.operands.iter().any(|op| {
        matches!(
            op,
            X86ISelOperand::MemAddr { .. }
                | X86ISelOperand::SibMemAddr { .. }
                | X86ISelOperand::StackSlot(_)
                | X86ISelOperand::ConstPoolEntry(_)
        )
    })
}

/// Impure-instance discrimination (the impurity nonce; see the module doc):
/// `true` when the operation's result is NOT a pure function of its input
/// value terms, so its `Op` term must be keyed by its per-block event ordinal
/// — otherwise twin impure ops (two loads from one address across an
/// intervening store; two identical-argument calls to an impure function)
/// intern to one term and a wrong-source rename between their result
/// registers would pass both checks.
///
/// Derived from the same access-model classification the executor uses:
///
/// * any call — [`InstAccess::call_result_locs`] is `Some` (the classifier
///   schema-requires this for `Call`/`CallR`/`CallM`, so every call-like op
///   is covered);
/// * every atomic/interlocked op (`Cmpxchg`, the CAS-loop pseudos, and the
///   memory form of `Xchg`; the register-register `Xchg` is a pure swap);
/// * every memory-VALUE read: the explicit memory-form loads (including the
///   RIP-relative static loads, whose `Symbol` operand is not memory-shaped),
///   `Pop`'s implicit `[rsp]` read, and — conservative default — ANY other
///   opcode carrying a memory-shaped operand (folded RM ALU forms, RM
///   compares, memory-operand `Div`/`Idiv`/`Mul`, memory-source
///   converts/extends, ...). Const-pool reads ride along: immutable, so the
///   nonce is merely stricter than necessary, never unsound. The explicit
///   `false` arms are exactly the shapes whose memory-shaped operand is never
///   a value READ: stores (memory written; the value and address registers
///   are read) and the `Lea` family (address arithmetic only).
///
/// Over-inclusion cannot create a false positive in this window: the nonce is
/// the event ordinal, identical in both streams whenever the event sequences
/// align (copies are non-events). Pure register/immediate ops keep
/// identity-free keys — the renamed-but-equal-flow design property.
fn op_requires_impurity_nonce(inst: &X86ISelInst, acc: &InstAccess) -> bool {
    use X86Opcode::*;
    if acc.call_result_locs.is_some() {
        return true;
    }
    match inst.opcode {
        // Atomics / interlocked: the memory forms read AND publish memory.
        Cmpxchg | AtomicRmwCasLoop | AtomicRmwCasLoop8 | AtomicRmwCasLoop16 => true,
        Xchg => has_memory_operand(inst),
        // Explicit memory-form loads + Pop's implicit stack read.
        MovRM8 | MovRM16 | MovRM32 | MovRM | MovRMSib | MovRM32Sib | MovsdRM | MovssRM
        | MovdquRM | MovdqaRM | MovRipRel | MovssRipRel | MovsdRipRel | Pop => true,
        // Memory-shaped operand but never a memory VALUE read.
        MovMR8 | MovMR16 | MovMR32 | MovMR | MovMRSib | MovMR32Sib | MovsdMR | MovssMR
        | MovdquMR | MovdqaMR | Lea | LeaSib | LeaRip => false,
        // Conservative default: any other memory-shaped operand is read as a
        // value; pure register/immediate forms stay identity-free.
        _ => has_memory_operand(inst),
    }
}

/// Gather the terms of the lanes named by one lane-read access, ascending.
fn read_group(state: &LaneTermState, loc: u8, mask: u16) -> Vec<TermId> {
    (0..SYMBOLIC_LANES)
        .filter(|lane| mask & (1u16 << lane) != 0)
        .map(|lane| state[loc as usize][lane])
        .collect()
}

fn exec_block(
    insts: &[X86ISelInst],
    accs: &[InstAccess],
    table: &mut TermTable,
    call_abi: X86CallAbi,
) -> BlockRun {
    let mut state = block_entry_state(table);
    let mut events = Vec::new();
    let mut event_sites = Vec::new();

    for (idx, (inst, acc)) in insts.iter().zip(accs).enumerate() {
        // --- Sym-propagating copies: pure term routing, exempt from the
        // event stream (the coalescer deletes exactly these). ---
        if let Some(copy) = acc.lane_copy {
            let source = state[copy.src as usize];
            for lane in 0..SYMBOLIC_LANES {
                let bit = 1u16 << lane;
                if copy.write_mask & bit == 0 {
                    continue;
                }
                state[copy.dst as usize][lane] = if copy.read_mask & bit != 0 {
                    source[lane]
                } else {
                    // MovRR32 upper lanes: the architectural constant zero —
                    // shared, index-free, identical in both streams.
                    table.intern(TermNode::Zero)
                };
            }
            continue;
        }

        // --- Canonical input term vector. ---
        let groups: Vec<Vec<TermId>> = acc
            .lane_reads
            .iter()
            .map(|read| read_group(&state, read.loc, read.mask))
            .collect();

        // XOR zero idiom normalization: v1 classifies `xor r,r,r`/`pxor x,x`
        // as a pure def (no reads). A sound rename can turn `xor a, a, b`
        // (where b's terms equal a's) INTO that shape, so the general form
        // with term-equal input groups must collapse to the same event and
        // the same constant-zero result.
        let register_form = !has_memory_operand(inst);
        let idiomable = matches!(inst.opcode, X86Opcode::XorRR | X86Opcode::Pxor);
        let classified_idiom = idiomable
            && acc.lane_reads.is_empty()
            && acc.xchg.is_none()
            && !acc.lane_defs.is_empty();
        let semantic_idiom = idiomable
            && register_form
            && groups.len() == 2
            && acc.lane_reads[0].mask == acc.lane_reads[1].mask
            && groups[0] == groups[1];
        let zero_result = classified_idiom || semantic_idiom;

        let mut inputs: Vec<TermId> = Vec::new();
        if !zero_result {
            let sortable = post_ra_spec_commutative_two_address_rr(inst.opcode)
                && register_form
                && groups.len() == 2
                && acc.lane_reads[0].mask == acc.lane_reads[1].mask
                && acc.flags_use_mask == 0;
            if sortable && groups[1] < groups[0] {
                inputs.extend(&groups[1]);
                inputs.extend(&groups[0]);
            } else {
                for group in &groups {
                    inputs.extend(group);
                }
            }
        }
        for (flag, &term) in state[FLAGS_LOC as usize]
            .iter()
            .take(FLAG_LANES)
            .enumerate()
        {
            if acc.flags_use_mask & (1u16 << flag) != 0 {
                inputs.push(term);
            }
        }
        if inst.flags.is_return() {
            for (reg, mask) in return_value_reads() {
                if let Some(loc) = loc_of(reg) {
                    inputs.extend(read_group(&state, loc, mask));
                }
            }
        }

        let tags: Vec<OperandTag> = inst.operands.iter().map(operand_tag).collect();
        let call_results_meta: Vec<(u8, u16)> = acc
            .call_result_locs
            .as_ref()
            .map(|results| results.iter().map(|r| (r.loc, r.defined_bits)).collect())
            .unwrap_or_default();
        let op = table.intern(TermNode::Op {
            opcode: inst.opcode,
            tags,
            inputs,
            call_results_meta,
            // The impurity nonce: this event's ordinal in the block's event
            // sequence (`events.len()` BEFORE pushing). Copies are non-events,
            // so a legitimate copy deletion never shifts it.
            impurity_nonce: op_requires_impurity_nonce(inst, acc).then_some(events.len() as u32),
        });
        events.push(op);
        event_sites.push((idx, inst.opcode));

        // --- Effects. ---
        if let Some((a, b)) = acc.xchg {
            state.swap(a as usize, b as usize);
        } else {
            for (ordinal, def) in acc.lane_defs.iter().enumerate() {
                for (lane, term) in state[def.loc as usize].iter_mut().enumerate() {
                    if def.mask & (1u16 << lane) != 0 {
                        *term = if zero_result {
                            table.intern(TermNode::Zero)
                        } else {
                            table.intern(TermNode::Proj {
                                op,
                                ordinal: ordinal as u8,
                                lane: lane as u8,
                            })
                        };
                    }
                }
            }
        }

        if let Some(results) = &acc.call_result_locs {
            for reg in caller_saved_gprs(call_abi) {
                if let Some(loc) = loc_of(*reg) {
                    for (lane, term) in state[loc as usize].iter_mut().enumerate() {
                        if GPR_LANE_MASK & (1u16 << lane) != 0 {
                            *term = table.intern(TermNode::Clobber {
                                op,
                                loc,
                                lane: lane as u8,
                            });
                        }
                    }
                }
            }
            for xmm in 0..caller_saved_xmm_count(call_abi) {
                if let Some(loc) = loc_of(X86PReg::new(64 + xmm)) {
                    for (lane, term) in state[loc as usize].iter_mut().enumerate() {
                        *term = table.intern(TermNode::Clobber {
                            op,
                            loc,
                            lane: lane as u8,
                        });
                    }
                }
            }
            for (flag, term) in state[FLAGS_LOC as usize]
                .iter_mut()
                .take(FLAG_LANES)
                .enumerate()
            {
                *term = table.intern(TermNode::Clobber {
                    op,
                    loc: FLAGS_LOC,
                    lane: flag as u8,
                });
            }
            let base_ordinal = acc.lane_defs.len();
            for (ri, result) in results.iter().enumerate() {
                let mask = low_bits_lane_mask(result.defined_bits);
                for (lane, term) in state[result.loc as usize].iter_mut().enumerate() {
                    if mask & (1u16 << lane) != 0 {
                        *term = table.intern(TermNode::Proj {
                            op,
                            ordinal: (base_ordinal + ri) as u8,
                            lane: lane as u8,
                        });
                    }
                }
            }
        } else {
            for (flag, term) in state[FLAGS_LOC as usize]
                .iter_mut()
                .take(FLAG_LANES)
                .enumerate()
            {
                let bit = 1u16 << flag;
                if acc.flags_def_mask & bit != 0 {
                    *term = table.intern(TermNode::FlagDef {
                        op,
                        flag: flag as u8,
                    });
                } else if acc.flags_undef_mask & bit != 0 {
                    *term = table.intern(TermNode::FlagUndef {
                        op,
                        flag: flag as u8,
                    });
                } else if acc.flags_may_undef_mask & bit != 0 {
                    let old = *term;
                    *term = table.intern(TermNode::FlagMay {
                        op,
                        flag: flag as u8,
                        old,
                    });
                }
            }
        }
    }

    BlockRun {
        events,
        event_sites,
        exit: state,
    }
}

// ---------------------------------------------------------------------------
// The pure check
// ---------------------------------------------------------------------------

fn loc_name(loc: u8) -> String {
    if loc < 16 {
        x86_preg_name(X86PReg::new(loc as u16)).to_string()
    } else if loc < 32 {
        x86_preg_name(X86PReg::new(64 + (loc as u16 - 16))).to_string()
    } else {
        "eflags".to_string()
    }
}

/// Classify every instruction of every block; `None` when any instruction is
/// outside the access model or carries an unallocated `VReg` — those are
/// TV-5 v1's (enforced) jurisdiction, and Stage A skips rather than guessing.
fn classify_stream<'s>(
    block_order: &[Block],
    get_insts: impl Fn(&Block) -> Option<&'s [X86ISelInst]>,
    alloc: &HashMap<VReg, X86PReg>,
    call_abi: X86CallAbi,
) -> Option<HashMap<Block, Vec<InstAccess>>> {
    let mut out = HashMap::new();
    for block_id in block_order {
        let Some(insts) = get_insts(block_id) else {
            out.insert(*block_id, Vec::new());
            continue;
        };
        let mut accs = Vec::with_capacity(insts.len());
        for inst in insts {
            let acc = classify_x86_post_ra_inst(inst, alloc, call_abi).ok()?;
            if !acc.unallocated.is_empty() {
                return None;
            }
            accs.push(acc);
        }
        out.insert(*block_id, accs);
    }
    Some(out)
}

/// Pure captured-spec comparison: symbolic dual execution + event/exit-term
/// equivalence. Returns every violation found (empty on a sound stream).
pub fn check_x86_captured_spec(
    spec: &X86PostFixupSpec,
    final_func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
    call_abi: X86CallAbi,
) -> Vec<PostRaSpecViolation> {
    let mut violations = Vec::new();

    // (1) CFG structure must be untouched by the coalescing window.
    if spec.block_order != final_func.block_order {
        violations.push(PostRaSpecViolation {
            kind: PostRaSpecViolationKind::BlockStructureMismatch,
            detail: format!(
                "fn `{}`: block order changed across the post-fixup coalescing window \
                 (spec {} blocks, final {})",
                spec.name,
                spec.block_order.len(),
                final_func.block_order.len()
            ),
        });
        return violations;
    }
    for block_id in &spec.block_order {
        let spec_succ = spec.blocks.get(block_id).map(|b| &b.successors);
        let final_succ = final_func.blocks.get(block_id).map(|b| &b.successors);
        if spec_succ != final_succ {
            violations.push(PostRaSpecViolation {
                kind: PostRaSpecViolationKind::BlockStructureMismatch,
                detail: format!(
                    "fn `{}` block {}: successor list changed across the coalescing window",
                    spec.name, block_id.0
                ),
            });
            return violations;
        }
    }

    // (2) Classify both streams; shapes outside the model are v1's enforced
    // jurisdiction — Stage A skips (never guesses an access set).
    let Some(spec_accs) = classify_stream(
        &spec.block_order,
        |b| spec.blocks.get(b).map(|blk| blk.insts.as_slice()),
        alloc,
        call_abi,
    ) else {
        return violations;
    };
    let Some(final_accs) = classify_stream(
        &spec.block_order,
        |b| final_func.blocks.get(b).map(|blk| blk.insts.as_slice()),
        alloc,
        call_abi,
    ) else {
        return violations;
    };

    // (3) Spec-side lane liveness for the exit-term comparison.
    let live_out = spec_live_out(spec, &spec_accs, call_abi);

    // (4) Dual symbolic execution per block over ONE shared term table.
    let mut table = TermTable::default();
    let empty: [X86ISelInst; 0] = [];
    for block_id in &spec.block_order {
        let spec_insts: &[X86ISelInst] = spec
            .blocks
            .get(block_id)
            .map(|b| b.insts.as_slice())
            .unwrap_or(&empty);
        let final_insts: &[X86ISelInst] = final_func
            .blocks
            .get(block_id)
            .map(|b| b.insts.as_slice())
            .unwrap_or(&empty);
        let spec_run = exec_block(spec_insts, &spec_accs[block_id], &mut table, call_abi);
        let final_run = exec_block(final_insts, &final_accs[block_id], &mut table, call_abi);

        // (4a) Ordered event equivalence.
        let mut events_diverged = false;
        let common = spec_run.events.len().min(final_run.events.len());
        for k in 0..common {
            if spec_run.events[k] != final_run.events[k] {
                let (si, sop) = spec_run.event_sites[k];
                let (fi, fop) = final_run.event_sites[k];
                violations.push(PostRaSpecViolation {
                    kind: PostRaSpecViolationKind::EventStreamMismatch,
                    detail: format!(
                        "fn `{}` block {} event #{k}: spec inst #{si} ({sop:?}) and final inst \
                         #{fi} ({fop:?}) consume different value terms — a post-fixup transform \
                         re-routed a non-tied read to a different value (deleted load-bearing \
                         copy, wrong-source rename, or non-commutative operand swap)",
                        spec.name, block_id.0
                    ),
                });
                events_diverged = true;
                break;
            }
        }
        if !events_diverged && spec_run.events.len() != final_run.events.len() {
            let (extra_idx, extra_op) = if spec_run.events.len() > final_run.events.len() {
                spec_run.event_sites[common]
            } else {
                final_run.event_sites[common]
            };
            violations.push(PostRaSpecViolation {
                kind: PostRaSpecViolationKind::EventStreamMismatch,
                detail: format!(
                    "fn `{}` block {}: event count changed across the coalescing window \
                     (spec {}, final {}; first unmatched inst #{extra_idx} {extra_op:?}) — \
                     only sym-propagating copies may be inserted or deleted",
                    spec.name,
                    block_id.0,
                    spec_run.events.len(),
                    final_run.events.len()
                ),
            });
            events_diverged = true;
        }

        // (4b) Exit terms at spec-live-out lanes. Skipped when the event
        // streams already diverged (downstream terms would only echo the
        // same root cause) or when liveness failed to converge (fail-open).
        if events_diverged {
            continue;
        }
        if let Some(live_out) = &live_out {
            let live = &live_out[block_id];
            for (loc, &mask) in live.iter().enumerate() {
                if mask == 0 {
                    continue;
                }
                for lane in 0..SYMBOLIC_LANES {
                    if mask & (1u16 << lane) == 0 {
                        continue;
                    }
                    if spec_run.exit[loc][lane] != final_run.exit[loc][lane] {
                        violations.push(PostRaSpecViolation {
                            kind: PostRaSpecViolationKind::LiveOutValueMismatch,
                            detail: format!(
                                "fn `{}` block {}: live-out byte lane {lane} of {} exits the \
                                 block with a different value term than the captured spec — a \
                                 deleted copy dropped an edge commit the successors consume",
                                spec.name,
                                block_id.0,
                                loc_name(loc as u8)
                            ),
                        });
                    }
                }
            }
        }
    }

    violations
}

// ---------------------------------------------------------------------------
// Driver (mode + telemetry)
// ---------------------------------------------------------------------------

/// Stage A driver with an explicit mode (testable without process env).
///
/// * `Off` → `None` immediately (zero work).
/// * Every violation is recorded (`[TCG-POST-RA-SPEC-WARN]`/`-FAIL` line +
///   process-wide counter) regardless of mode.
/// * Only in `Enforce` mode is the first violation returned to the caller.
pub fn evaluate_x86_captured_spec_with_mode(
    spec: &X86PostFixupSpec,
    final_func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
    arch: &str,
    call_abi: X86CallAbi,
    mode: PostRegallocRecheckMode,
) -> Option<PostRaSpecViolation> {
    if mode == PostRegallocRecheckMode::Off {
        return None;
    }
    let violations = check_x86_captured_spec(spec, final_func, alloc, call_abi);
    let failing = mode == PostRegallocRecheckMode::Enforce;
    for violation in &violations {
        record(
            arch,
            &spec.name,
            violation.kind.tag(),
            &violation.detail,
            failing,
        );
    }
    if failing {
        violations.into_iter().next()
    } else {
        None
    }
}

/// Stage A driver: resolve the mode from `TCG_POST_RA_SPEC` (default WARN).
pub fn evaluate_x86_captured_spec(
    spec: &X86PostFixupSpec,
    final_func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
    arch: &str,
    call_abi: X86CallAbi,
) -> Option<PostRaSpecViolation> {
    evaluate_x86_captured_spec_with_mode(
        spec,
        final_func,
        alloc,
        arch,
        call_abi,
        post_ra_spec_mode(),
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;
    use trust_cg_ir::x86_64_regs::{EAX, EDX, R8, R9, R10, RBP, RBX, RCX};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::types::Type;
    use trust_cg_lower::x86_64_isel::X86CallResultReg;

    /// Serializes tests that assert on the process-wide SPEC_HITS counter.
    static COUNTER_LOCK: Mutex<()> = Mutex::new(());

    fn counter_guard() -> std::sync::MutexGuard<'static, ()> {
        COUNTER_LOCK.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn p(reg: X86PReg) -> X86ISelOperand {
        X86ISelOperand::PReg(reg)
    }

    fn imm(value: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(value)
    }

    fn mem(base: X86PReg, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(p(base)),
            disp,
        }
    }

    fn inst(opcode: X86Opcode, operands: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(opcode, operands)
    }

    fn x86_func(name: &str, insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            name.to_string(),
            Signature {
                params: vec![Type::I64],
                returns: vec![],
            },
        );
        let block = Block(0);
        func.ensure_block(block);
        func.blocks.get_mut(&block).unwrap().insts.extend(insts);
        func
    }

    fn x86_cfg_func(name: &str, blocks: Vec<(Vec<X86ISelInst>, Vec<u32>)>) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            name.to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        for idx in 0..blocks.len() {
            func.ensure_block(Block(idx as u32));
        }
        for (idx, (insts, successors)) in blocks.into_iter().enumerate() {
            let block = func.blocks.get_mut(&Block(idx as u32)).unwrap();
            block.insts = insts;
            block.successors = successors.into_iter().map(Block).collect();
        }
        func
    }

    fn capture(func: &X86ISelFunction) -> X86PostFixupSpec {
        capture_x86_post_fixup_spec(func).expect("default mode is WARN, capture must run")
    }

    fn check(spec: &X86PostFixupSpec, final_func: &X86ISelFunction) -> Vec<PostRaSpecViolation> {
        check_x86_captured_spec(spec, final_func, &HashMap::new(), X86CallAbi::SystemV)
    }

    fn assert_clean(spec: &X86PostFixupSpec, final_func: &X86ISelFunction) {
        let violations = check(spec, final_func);
        assert!(
            violations.is_empty(),
            "sound stream must not be flagged: {violations:?}"
        );
    }

    fn assert_kind(
        spec: &X86PostFixupSpec,
        final_func: &X86ISelFunction,
        kind: PostRaSpecViolationKind,
    ) {
        let violations = check(spec, final_func);
        assert!(
            violations.iter().any(|v| v.kind == kind),
            "expected {kind:?}, got: {violations:?}"
        );
    }

    // ===================================================================
    // GREEN: sound streams (identical or value-faithfully coalesced)
    // ===================================================================

    #[test]
    fn identical_streams_pass() {
        let build = || {
            x86_func(
                "same",
                vec![
                    inst(X86Opcode::MovRI, vec![p(RAX), imm(7)]),
                    inst(X86Opcode::MovRR, vec![p(RCX), p(RAX)]),
                    inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RBX)]),
                    inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                    inst(X86Opcode::Ret, vec![]),
                ],
            )
        };
        let spec = capture(&build());
        assert_clean(&spec, &build());
    }

    #[test]
    fn legit_coalesce_delete_and_rename_passes() {
        // spec:  movq r8 <- rbx ; addq rcx += r8 ; store rcx ; ret
        // final: (copy deleted)  addq rcx += rbx ; store rcx ; ret
        // The renamed read consumes the SAME BlockIn(rbx) terms; r8 is dead
        // at exit (nothing reads it downstream), so no comparison happens
        // there.
        let spec_func = x86_func(
            "coalesce_ok",
            vec![
                inst(X86Opcode::MovRR, vec![p(R8), p(RBX)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(R8)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "coalesce_ok",
            vec![
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RBX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_clean(&spec, &final_func);
    }

    #[test]
    fn legit_coalesce_ghost_rename_at_tied_site_passes() {
        // The ghost operand (operands[1]) of the downstream tied site is
        // renamed in lockstep with the real read — Tag::Reg elides register
        // identity and the ghost carries no input term, so the event is
        // unchanged.
        let spec_func = x86_func(
            "ghost_rename",
            vec![
                inst(X86Opcode::MovRR, vec![p(R8), p(RBX)]),
                inst(X86Opcode::MovRR, vec![p(RCX), p(R8)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(R8), p(RDX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "ghost_rename",
            vec![
                inst(X86Opcode::MovRR, vec![p(RCX), p(RBX)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(RBX), p(RDX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_clean(&spec, &final_func);
    }

    #[test]
    fn scratch_repair_triangle_survives_upstream_deletion() {
        // A deleted+renamed copy UPSTREAM of a fixup scratch-repair triangle
        // shifts every instruction index; terms are structural (def-ordinal,
        // not location or index), so the triangle still matches.
        let triangle = |rhs: X86PReg| {
            vec![
                inst(X86Opcode::MovRR, vec![p(R10), p(RCX)]),
                inst(X86Opcode::SubRR, vec![p(R10), p(R10), p(rhs)]),
                inst(X86Opcode::MovRR, vec![p(RAX), p(R10)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -16), p(RAX)]),
                inst(X86Opcode::Ret, vec![]),
            ]
        };
        let mut spec_insts = vec![
            inst(X86Opcode::MovRR, vec![p(R8), p(RBX)]),
            inst(X86Opcode::AddRR, vec![p(R9), p(R9), p(R8)]),
        ];
        spec_insts.extend(triangle(R9));
        let mut final_insts = vec![inst(X86Opcode::AddRR, vec![p(R9), p(R9), p(RBX)])];
        final_insts.extend(triangle(R9));
        let spec = capture(&x86_func("triangle", spec_insts));
        assert_clean(&spec, &x86_func("triangle", final_insts));
    }

    #[test]
    fn commutative_swap_passes() {
        // rcx = rax + rbx, computed with swapped copy source and operand
        // order: value-identical under the commutativity mirror.
        let spec_func = x86_func(
            "comm",
            vec![
                inst(X86Opcode::MovRR, vec![p(RCX), p(RAX)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RBX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "comm",
            vec![
                inst(X86Opcode::MovRR, vec![p(RCX), p(RBX)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RAX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_clean(&spec, &final_func);
    }

    #[test]
    fn movrr32_zero_extension_stable_across_index_shift() {
        // MovRR32 upper lanes are the shared constant Zero, not a fresh
        // per-index def: an upstream deletion (index shift) must not perturb
        // the zero-extended exit terms of a live-out register.
        let tail = vec![
            inst(X86Opcode::MovRR32, vec![p(EAX), p(EDX)]),
            inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RAX)]),
            inst(X86Opcode::Ret, vec![]),
        ];
        let mut spec_insts = vec![
            inst(X86Opcode::MovRR, vec![p(R8), p(RBX)]),
            inst(X86Opcode::AddRR, vec![p(R9), p(R9), p(R8)]),
        ];
        spec_insts.extend(tail.clone());
        let mut final_insts = vec![inst(X86Opcode::AddRR, vec![p(R9), p(R9), p(RBX)])];
        final_insts.extend(tail);
        let spec = capture(&x86_func("zext", spec_insts));
        assert_clean(&spec, &x86_func("zext", final_insts));
    }

    #[test]
    fn xor_zero_idiom_normalization_passes() {
        // A sound rename can rewrite `xor rax, rax, r8` (r8 provably holds
        // rax's value via the deleted copy) into the zero idiom
        // `xor rax, rax, rax`; both must produce the same zero event/result.
        // (The copy target is a non-return register: a return-register copy
        // before `ret` is a barrier the coalescer must never delete, and the
        // Ret event's return-value reads would rightly refute it.)
        let spec_func = x86_func(
            "xor_idiom",
            vec![
                inst(X86Opcode::MovRR, vec![p(R8), p(RAX)]),
                inst(X86Opcode::XorRR, vec![p(RAX), p(RAX), p(R8)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RAX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "xor_idiom",
            vec![
                inst(X86Opcode::XorRR, vec![p(RAX), p(RAX), p(RAX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RAX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_clean(&spec, &final_func);
    }

    #[test]
    fn dead_copy_deletion_before_full_redef_passes() {
        // spec: movq r8 <- rbx (dead: nothing reads r8 before its full
        // redefinition) — deleting it must not trip the exit comparison.
        let spec_func = x86_func(
            "dead_copy",
            vec![
                inst(X86Opcode::MovRR, vec![p(R8), p(RBX)]),
                inst(X86Opcode::MovRI, vec![p(R8), imm(42)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(R8)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "dead_copy",
            vec![
                inst(X86Opcode::MovRI, vec![p(R8), imm(42)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(R8)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_clean(&spec, &final_func);
    }

    #[test]
    fn cross_block_live_copy_kept_passes_and_flags_route_through_cfg() {
        // Two blocks, a conditional consumer downstream, streams identical:
        // the CFG walk must stay clean (flags + branch events compared).
        let build = || {
            x86_cfg_func(
                "cfg",
                vec![
                    (
                        vec![
                            inst(X86Opcode::MovRR, vec![p(RCX), p(RBX)]),
                            inst(X86Opcode::CmpRI, vec![p(RCX), imm(0)]),
                            inst(
                                X86Opcode::Jcc,
                                vec![
                                    X86ISelOperand::CondCode(X86CondCode::E),
                                    X86ISelOperand::Block(Block(1)),
                                ],
                            ),
                        ],
                        vec![1],
                    ),
                    (
                        vec![
                            inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                            inst(X86Opcode::Ret, vec![]),
                        ],
                        vec![],
                    ),
                ],
            )
        };
        let spec = capture(&build());
        assert_clean(&spec, &build());
    }

    // ===================================================================
    // RED: value-routing corruption (warn recorded)
    // ===================================================================

    #[test]
    fn deleted_load_bearing_copy_refuted() {
        // The empirically-proven class: the copy is deleted but the
        // downstream read is NOT renamed — it now consumes BlockIn(rax)
        // instead of BlockIn(rbx).
        let spec_func = x86_func(
            "bad_delete",
            vec![
                inst(X86Opcode::MovRR, vec![p(RAX), p(RBX)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RAX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "bad_delete",
            vec![
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RAX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_kind(
            &spec,
            &final_func,
            PostRaSpecViolationKind::EventStreamMismatch,
        );
    }

    #[test]
    fn wrong_source_rename_refuted() {
        // The copy is deleted and the read renamed — to the WRONG register.
        let spec_func = x86_func(
            "bad_rename",
            vec![
                inst(X86Opcode::MovRR, vec![p(R8), p(RBX)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(R8)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "bad_rename",
            vec![
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RDX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_kind(
            &spec,
            &final_func,
            PostRaSpecViolationKind::EventStreamMismatch,
        );
    }

    #[test]
    fn twin_loads_across_store_wrong_rename_refuted() {
        // Instance-conflation hole (adversarial review): two `MovRM` loads
        // from ONE address with an intervening store hold DIFFERENT values.
        // Without the impurity nonce both loads interned to one Op term (keys
        // carry only opcode + tags + address terms), their result Projs
        // conflated, and renaming the Add's use onto the STALE first load's
        // destination passed both checks. The nonce (per-block event ordinal)
        // makes the twins distinct instances.
        let spec_func = x86_func(
            "twin_loads",
            vec![
                inst(X86Opcode::MovRM, vec![p(R8), mem(RBP, -8)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::MovRM, vec![p(R9), mem(RBP, -8)]),
                inst(X86Opcode::MovRR, vec![p(R10), p(R9)]),
                inst(X86Opcode::AddRR, vec![p(RDX), p(RDX), p(R10)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -16), p(RDX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let wrong = x86_func(
            "twin_loads",
            vec![
                inst(X86Opcode::MovRM, vec![p(R8), mem(RBP, -8)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::MovRM, vec![p(R9), mem(RBP, -8)]),
                // Copy deleted; the use renamed to the STALE first load.
                inst(X86Opcode::AddRR, vec![p(RDX), p(RDX), p(R8)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -16), p(RDX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_kind(&spec, &wrong, PostRaSpecViolationKind::EventStreamMismatch);

        // RED under Enforce; warn-recorded (never failing) under Warn.
        {
            let _guard = counter_guard();
            let enforced = evaluate_x86_captured_spec_with_mode(
                &spec,
                &wrong,
                &HashMap::new(),
                "x86_64",
                X86CallAbi::SystemV,
                PostRegallocRecheckMode::Enforce,
            );
            assert_eq!(
                enforced.map(|v| v.kind),
                Some(PostRaSpecViolationKind::EventStreamMismatch)
            );
            let before = post_ra_spec_hit_count();
            let warned = evaluate_x86_captured_spec_with_mode(
                &spec,
                &wrong,
                &HashMap::new(),
                "x86_64",
                X86CallAbi::SystemV,
                PostRegallocRecheckMode::Warn,
            );
            assert!(warned.is_none(), "warn mode must never fail the compile");
            assert!(
                post_ra_spec_hit_count() > before,
                "warn mode must still record telemetry"
            );
        }

        // GREEN twin: the LEGITIMATE rename onto the SECOND load's
        // destination consumes the same instance — must still pass.
        let legit = x86_func(
            "twin_loads",
            vec![
                inst(X86Opcode::MovRM, vec![p(R8), mem(RBP, -8)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::MovRM, vec![p(R9), mem(RBP, -8)]),
                inst(X86Opcode::AddRR, vec![p(RDX), p(RDX), p(R9)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -16), p(RDX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        assert_clean(&spec, &legit);
    }

    #[test]
    fn twin_calls_wrong_result_rename_refuted() {
        // Instance-conflation hole, call flavor: two calls with IDENTICAL
        // argument terms to an impure function return different values.
        // Without the nonce the two call Op terms — and so their RAX result
        // Proj terms — conflated, so routing call #2's consumer onto a
        // register holding call #1's result passed. The nonce separates the
        // instances.
        let call = || {
            inst(
                X86Opcode::Call,
                vec![X86ISelOperand::Symbol("f".to_string())],
            )
            .with_call_result_regs(vec![X86CallResultReg::new(RAX, 64)])
        };
        let spec_func = x86_func(
            "twin_calls",
            vec![
                call(),
                // Stash result #1 in a callee-saved register.
                inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)]),
                call(),
                inst(X86Opcode::MovRR, vec![p(RCX), p(RAX)]),
                inst(X86Opcode::AddRR, vec![p(RDX), p(RDX), p(RCX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RDX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -16), p(RBX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let wrong = x86_func(
            "twin_calls",
            vec![
                call(),
                inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)]),
                call(),
                // Copy deleted; call #2's consumer renamed onto RBX — which
                // holds call #1's result.
                inst(X86Opcode::AddRR, vec![p(RDX), p(RDX), p(RBX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RDX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -16), p(RBX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_kind(&spec, &wrong, PostRaSpecViolationKind::EventStreamMismatch);

        // RED under Enforce; warn-recorded (never failing) under Warn.
        {
            let _guard = counter_guard();
            let enforced = evaluate_x86_captured_spec_with_mode(
                &spec,
                &wrong,
                &HashMap::new(),
                "x86_64",
                X86CallAbi::SystemV,
                PostRegallocRecheckMode::Enforce,
            );
            assert_eq!(
                enforced.map(|v| v.kind),
                Some(PostRaSpecViolationKind::EventStreamMismatch)
            );
            let before = post_ra_spec_hit_count();
            let warned = evaluate_x86_captured_spec_with_mode(
                &spec,
                &wrong,
                &HashMap::new(),
                "x86_64",
                X86CallAbi::SystemV,
                PostRegallocRecheckMode::Warn,
            );
            assert!(warned.is_none(), "warn mode must never fail the compile");
            assert!(
                post_ra_spec_hit_count() > before,
                "warn mode must still record telemetry"
            );
        }

        // Legitimate routing: rename onto the copy's SOURCE — RAX still
        // holds call #2's result at the Add — must still pass.
        let legit = x86_func(
            "twin_calls",
            vec![
                call(),
                inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)]),
                call(),
                inst(X86Opcode::AddRR, vec![p(RDX), p(RDX), p(RAX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RDX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -16), p(RBX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        assert_clean(&spec, &legit);
    }

    #[test]
    fn noncommutative_swap_refuted() {
        // rcx = rax - rbx vs rcx = rbx - rax: SubRR is NOT in the
        // commutativity mirror, so the swapped input groups must diverge.
        let spec_func = x86_func(
            "bad_swap",
            vec![
                inst(X86Opcode::MovRR, vec![p(RCX), p(RAX)]),
                inst(X86Opcode::SubRR, vec![p(RCX), p(RCX), p(RBX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "bad_swap",
            vec![
                inst(X86Opcode::MovRR, vec![p(RCX), p(RBX)]),
                inst(X86Opcode::SubRR, vec![p(RCX), p(RCX), p(RAX)]),
                inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        assert_kind(
            &spec,
            &final_func,
            PostRaSpecViolationKind::EventStreamMismatch,
        );
    }

    #[test]
    fn deleted_return_value_copy_refuted() {
        // Deleting the copy that populates RAX before `ret` must diverge the
        // Ret event's return-register input terms.
        let spec_func = x86_func(
            "ret_copy",
            vec![
                inst(X86Opcode::MovRR, vec![p(RAX), p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func("ret_copy", vec![inst(X86Opcode::Ret, vec![])]);
        let spec = capture(&spec_func);
        assert_kind(
            &spec,
            &final_func,
            PostRaSpecViolationKind::EventStreamMismatch,
        );
    }

    #[test]
    fn deleted_cross_block_edge_commit_refuted() {
        // The copy's destination IS live-out (a successor stores it): the
        // deletion drops an edge commit → LiveOutValueMismatch.
        let blocks = |entry_insts: Vec<X86ISelInst>| {
            x86_cfg_func(
                "edge_commit",
                vec![
                    (entry_insts, vec![1]),
                    (
                        vec![
                            inst(X86Opcode::MovMR, vec![mem(RBP, -8), p(R8)]),
                            inst(X86Opcode::Ret, vec![]),
                        ],
                        vec![],
                    ),
                ],
            )
        };
        let spec_func = blocks(vec![
            inst(X86Opcode::MovRR, vec![p(R8), p(RBX)]),
            inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
        ]);
        let final_func = blocks(vec![inst(
            X86Opcode::Jmp,
            vec![X86ISelOperand::Block(Block(1))],
        )]);
        let spec = capture(&spec_func);
        assert_kind(
            &spec,
            &final_func,
            PostRaSpecViolationKind::LiveOutValueMismatch,
        );
    }

    #[test]
    fn changed_successor_list_refuted() {
        let build = |succs: Vec<u32>| {
            x86_cfg_func(
                "succs",
                vec![
                    (
                        vec![inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))])],
                        succs,
                    ),
                    (vec![inst(X86Opcode::Ret, vec![])], vec![]),
                ],
            )
        };
        let spec = capture(&build(vec![1]));
        assert_kind(
            &spec,
            &build(vec![]),
            PostRaSpecViolationKind::BlockStructureMismatch,
        );
    }

    // ===================================================================
    // Mirror drift pin + mode machinery + telemetry
    // ===================================================================

    /// PINNED (mirror drift): the exact member set of the verify-side
    /// commutativity mirror. If codegen's `is_x86_commutative_two_address_rr`
    /// gains/loses an opcode, update BOTH functions and this list (the
    /// codegen-side companion test compares the two functions directly).
    #[test]
    fn post_ra_spec_commutative_mirror_pinned() {
        use X86Opcode::*;
        let commutative = [
            AddRR, AndRR, OrRR, XorRR, ImulRR, Addsd, Mulsd, Andpd, Addss, Mulss, Andps, Pand, Por,
            Pxor, Pcmpeqb, Pcmpeqw, Pcmpeqd, Paddb, Paddw, Paddd, Paddq, Pmullw, Pmuludq, Pmulld,
            Pcmpeqq, Addps, Mulps, Addpd, Mulpd,
        ];
        for op in commutative {
            assert!(
                post_ra_spec_commutative_two_address_rr(op),
                "{op:?} must be in the commutativity mirror"
            );
        }
        // Non-commutative controls: subtraction/division/shift/compare
        // family members that share the two-address shape.
        let non_commutative = [
            SubRR, AdcRR, SbbRR, Subsd, Divsd, Subss, Divss, Pandn, Psubb, Psubw, Psubd, Psubq,
            Punpcklbw, Punpckldq, Packuswb, Punpckhbw, Punpcklqdq, Pcmpgtb, Pcmpgtw, Pcmpgtd,
            Pcmpgtq, Subps, Divps, Subpd, Divpd, Minsd, Maxsd, Minss, Maxss, Cmpsd, Cmpss,
        ];
        for op in non_commutative {
            assert!(
                !post_ra_spec_commutative_two_address_rr(op),
                "{op:?} must NOT be in the commutativity mirror"
            );
        }
    }

    #[test]
    fn mode_parsing_defaults_to_warn() {
        assert_eq!(parse_post_ra_spec_mode(None), PostRegallocRecheckMode::Warn);
        assert_eq!(
            parse_post_ra_spec_mode(Some("off")),
            PostRegallocRecheckMode::Off
        );
        assert_eq!(
            parse_post_ra_spec_mode(Some("warn")),
            PostRegallocRecheckMode::Warn
        );
        assert_eq!(
            parse_post_ra_spec_mode(Some("enforce")),
            PostRegallocRecheckMode::Enforce
        );
        assert_eq!(
            parse_post_ra_spec_mode(Some("bogus")),
            PostRegallocRecheckMode::Warn
        );
        assert_eq!(
            parse_post_ra_spec_mode(Some(" ENFORCE ")),
            PostRegallocRecheckMode::Enforce
        );
    }

    #[test]
    fn warn_mode_records_but_never_fails() {
        let _guard = counter_guard();
        let spec_func = x86_func(
            "warn_only",
            vec![
                inst(X86Opcode::MovRR, vec![p(RAX), p(RBX)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RAX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "warn_only",
            vec![
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RAX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        let before = post_ra_spec_hit_count();
        let outcome = evaluate_x86_captured_spec_with_mode(
            &spec,
            &final_func,
            &HashMap::new(),
            "x86_64",
            X86CallAbi::SystemV,
            PostRegallocRecheckMode::Warn,
        );
        assert!(outcome.is_none(), "warn mode must never fail the compile");
        assert!(
            post_ra_spec_hit_count() > before,
            "warn mode must still record telemetry"
        );
    }

    #[test]
    fn enforce_mode_returns_first_violation() {
        let _guard = counter_guard();
        let spec_func = x86_func(
            "enforced",
            vec![
                inst(X86Opcode::MovRR, vec![p(RAX), p(RBX)]),
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RAX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let final_func = x86_func(
            "enforced",
            vec![
                inst(X86Opcode::AddRR, vec![p(RCX), p(RCX), p(RAX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let spec = capture(&spec_func);
        let outcome = evaluate_x86_captured_spec_with_mode(
            &spec,
            &final_func,
            &HashMap::new(),
            "x86_64",
            X86CallAbi::SystemV,
            PostRegallocRecheckMode::Enforce,
        );
        assert_eq!(
            outcome.map(|v| v.kind),
            Some(PostRaSpecViolationKind::EventStreamMismatch)
        );
    }

    #[test]
    fn clean_streams_do_not_bump_the_counter() {
        let _guard = counter_guard();
        let build = || {
            x86_func(
                "clean",
                vec![
                    inst(X86Opcode::MovRI, vec![p(RAX), imm(1)]),
                    inst(X86Opcode::Ret, vec![]),
                ],
            )
        };
        let spec = capture(&build());
        let before = post_ra_spec_hit_count();
        let outcome = evaluate_x86_captured_spec_with_mode(
            &spec,
            &build(),
            &HashMap::new(),
            "x86_64",
            X86CallAbi::SystemV,
            PostRegallocRecheckMode::Warn,
        );
        assert!(outcome.is_none());
        assert_eq!(post_ra_spec_hit_count(), before);
    }
}
