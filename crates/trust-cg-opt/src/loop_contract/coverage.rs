// trust-cg-opt - The loop-state contract's ITERATION-COVERAGE clause
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Iteration coverage
//!
//! The third clause of the loop-state contract (see the parent module):
//!
//! > 3. **iterations**: the new code and the scalar remainder together run
//! >    exactly the iterations the scalar loop runs: each execution of a block
//! >    the rewrite names runs the `width` iterations it claims, the scalar
//! >    remainder runs the rest, and control leaves where, and with the
//! >    reproduced registers the scalar loop leaves with.
//!
//! [`check_coverage`] decides it once, for both machine IRs, by RUNNING the
//! two functions' control on the values that decide it. Each IR describes its
//! instructions as [`TripEffect`]s; an instruction it does not model is a
//! [`TripEffect::Clobber`] of what it writes. From the scalar loop's
//! preheader both the original function and the rewritten one are executed,
//! but only their TRIP SLICE: every register a branch or conditional-trap
//! condition depends on, closed over both functions (for a trap whose test
//! the model does not compute, [`TripCond::Unknown`], the operands its
//! adapter names, [`UnknownTest::Reads`]; one that names none reads nothing
//! the slice holds). The slice never includes memory, so a value loaded
//! inside a loop is unknown.
//!
//! **Inputs.** A slice register live into the preheader whose every reaching
//! definition is the same constant takes that constant. Any other one, and the
//! result of an unmodeled instruction in the preheader itself, is an INPUT,
//! run over [`SAMPLES`]: 0, 1, one short of, at, and one past every power of
//! two up to 1024, 48, 100 and 1000, and the 32- and 64-bit edges. Every
//! input combination is run when there are at most two inputs; a fixed,
//! deterministic selection otherwise (each input over every sample with the
//! others held at each of a few values, plus pairs). An input that is one
//! only because the operands a carrier names are read
//! ([`Input::carrier_only`]: without those reads it is outside the slice, or
//! read by nothing before the region writes it, so no modeled branch or trap
//! condition depends on it) does not count toward the two: the other inputs
//! take exactly the combinations they take without it, each of those runs
//! once for every combination of the carrier-only inputs over [`PIVOTS`],
//! and the combinations of all of them counted together run as well, so a
//! carrier-only input adds runs and never thins the others'. Past
//! [`CARRIER_COMBO_BUDGET`] crossed combinations the clause refuses
//! undecided. The trip count `N` of a
//! run is whatever the original function computes from its inputs, so `N`
//! ranges over 0, 1, `w - 1`, `w`, `w + 1`, multiples and non-multiples of
//! every power-of-two width and start offsets 0, 1 and odd. Both runs take
//! the same input for an unmodeled preheader result only when the rewritten
//! preheader begins with the scalar preheader's instructions
//! ([`LoopStateView::same_inst`]) up to the last that writes a slice
//! register unmodeled, so that each one reads the same registers and memory
//! in both; otherwise the rewritten run takes those results as unknown.
//!
//! **Counting.** An ITERATION of the scalar loop is an entry into its header,
//! except a final entry from which control leaves through the loop test the
//! plan names when that test is in the header and the header is not its own
//! latch (a top-tested loop runs its test once more than its body). In the
//! rewritten function, an entry into a block the rewrite names
//! ([`Lanes::blocks`]) counts that block's `width`, so a rewrite names the
//! block a trip passes only once it has run its iterations (a vector loop's
//! latch, not its body, when the body can give control back to the scalar
//! loop at the trip's start); and, when the scalar loop is kept as the
//! remainder ([`Remainder::ScalarLoop`]), its iterations count by the same
//! rule. That rule is exact only for the scalar loop itself entered at its
//! header, so with that remainder every block of the loop must be unchanged
//! (the same instructions, [`LoopStateView::same_inst`], and layout
//! successor) and every transfer into it from outside it must go to the
//! header; otherwise the clause refuses undecided.
//! Coverage holds for a run when both functions leave the region by the same
//! edge target, or both stop the same way (a return, a trap, an indirect
//! branch or a tail call, [`StopKind`]), the counts agree, and every
//! reproduced register (`carried`) the slice holds has the same value at the
//! exit.
//!
//! **Undecided conditions.** A branch whose condition is unknown (it reads a
//! loaded value, or one an unmodeled instruction wrote) and one of whose
//! sides leaves the region is a DATA EXIT, and a conditional trap whose
//! condition is unknown is one too: the run assumes it not taken, so the
//! clause states coverage only for the runs in which no data exit fires. The
//! scalar run may assume this of an exit of the scalar loop, which the control
//! clause accounts for (a full unroll's scope, [`CoveredLoop::unrolled`], is
//! not minted by that clause: there the unroll's recognizer keeps every exit
//! in each copy); it refuses a data exit of the preheader. The rewritten run
//! may assume it only of an exit that stands for one the scalar run assumed
//! on the same inputs: its branch or trap is TIED to the scalar one (the same
//! instruction, [`LoopStateView::same_inst`], in the same block of the scalar
//! loop, kept or rewritten in place, or in a block the rewrite names as a
//! copy of that block, [`Lanes::copies`], its block operands read as the
//! blocks they copy), and a branch leaves to the same block. Ties are one to
//! one: in each such block, the deciding instructions of one text stand, in
//! order, for those of that text in the scalar block, and only when there are
//! equally many, so a new exit of the text of the scalar loop's own (a flag
//! reader's `b.ne early`, whose text names its condition code and target but
//! not the compare behind it, or a `cbnz` reusing the scalar exit's register)
//! ties neither. A trap whose test the model does not compute
//! ([`TripCond::Unknown`]) is never assumed by the rewritten run when that run
//! knows every operand its adapter names (each in the slice): its outcome is
//! fixed by those values, so it stands for no trap of the scalar loop. Any
//! other data exit is one only the new code has, which nothing accounts for,
//! and the clause refuses undecided. A branch with both
//! sides in the region is explored both ways, and EVERY resulting run must
//! cover; the original function must reach one outcome for each input, or the
//! clause refuses. Two runs that reach a block in the same state (the same
//! counts included) are merged; so that a merge never drops a run that comes
//! back to its own state and never leaves, every cycle of each region a run
//! can reach must pass a counted block (or the counted scalar header), or the
//! clause refuses undecided.
//!
//! **Long loops.** A loop that runs many iterations along one path, with the
//! slice advancing by the same amount each time, is advanced in one step: the
//! iteration is re-executed in an affine domain (each value `base + j *
//! delta`), which proves the path, the advance and every decision on the path
//! for `j` up to an exact bound (linear compares within their no-wrap range,
//! equality modulo the width). A loop the domain cannot describe is stepped,
//! within a budget; an exhausted budget refuses.
//!
//! **Evidence rung.** The check runs in the compiler, on the rewritten code,
//! before it is published; a refusal keeps the scalar loop. It is a decision
//! for the inputs it runs, not for all inputs: a sampled run is test-rung
//! evidence, and two inputs the program can only hold together (a bound and
//! its scaled copy) are sampled independently, which refuses, never admits.
//! The semantics of each modeled instruction are this module's and its two
//! IR adapters'; an instruction they misdescribe is a wrong verdict. What each
//! counted block does with its `width` iterations (memory, lanes) is the
//! pass's premise, as in the other clauses. So is the undecided value a tied
//! data exit decides on: that it is the value the scalar exit decides on in
//! the iteration it stands for, whatever computes it (loads, unmodeled
//! instructions, and the modeled compare or operands beside them, which the
//! tie does not compare), so that it fires in the iteration the scalar one
//! would (the claim the plan makes for that exit, `and_reproduces`; for a
//! full unroll, its recognizer's; that a named copy is a copy of its block is
//! the pass's as well). The clause checks the tie, not that value.

use std::collections::VecDeque;
use std::fmt::Debug;
use std::hash::Hash;

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use trust_cg_ir::X86CondCode;

use super::{CoveredLoop, LoopStateView};

/// A register as the coverage clause names it: its number. Every class of a
/// number is one register; a read takes the low `width` bits of the value.
pub(crate) type RegId = u32;

/// An operand of a [`TripOp`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TripOperand {
    /// The low `width` bits of register `id`.
    Reg { id: RegId, width: u8 },
    /// An immediate (already sign- or zero-extended by the adapter).
    Imm(u64),
}

/// A two-operand integer operation, computed at the destination's width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TripBin {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    /// `a & !b`
    AndNot,
    /// `a | !b`
    OrNot,
    /// `a << (b % width)`
    Shl,
    /// `a >> (b % width)` (logical)
    LShr,
    /// `a >> (b % width)` (arithmetic)
    AShr,
    /// Rotate right by `b % width`.
    Ror,
    /// Unsigned division; division by zero gives 0 (AArch64 `UDIV`).
    UDiv,
    /// Signed division truncating; by zero gives 0, `MIN / -1` gives `MIN`.
    SDiv,
}

/// What a `Select` does to its second arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SelectPost {
    /// `cond ? a : b`
    Plain,
    /// `cond ? a : b + 1` (`CSINC`)
    Inc,
    /// `cond ? a : !b` (`CSINV`)
    Inv,
    /// `cond ? a : -b` (`CSNEG`)
    Neg,
}

/// The value an instruction writes to a register.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TripOp {
    Copy(TripOperand),
    Bin(TripBin, TripOperand, TripOperand),
    /// `a OP (b SHIFT amount)`, the shift at the destination's width.
    BinShifted {
        op: TripBin,
        a: TripOperand,
        b: TripOperand,
        shift: TripBin,
        amount: u8,
    },
    /// `a * b + c`
    MulAdd(TripOperand, TripOperand, TripOperand),
    /// `c - a * b`
    MulSub(TripOperand, TripOperand, TripOperand),
    Neg(TripOperand),
    /// The low `from` bits of `src`, sign- or zero-extended.
    Ext {
        signed: bool,
        from: u8,
        src: TripOperand,
    },
    /// `old` with bits `shift..shift + 16` replaced by `imm` (`MOVK`).
    Insert16 {
        old: TripOperand,
        imm: u16,
        shift: u8,
    },
    Select {
        cond: TripCond,
        then: TripOperand,
        otherwise: TripOperand,
        post: SelectPost,
    },
    /// 1 when `cond` holds, else 0.
    SetCond(TripCond),
    /// `old` with its low byte replaced by 1 when `cond` holds, else 0
    /// (x86 `SETcc`).
    SetLow8 {
        old: TripOperand,
        cond: TripCond,
    },
}

/// How the flags were last written.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum FlagOp {
    /// `a - b` (AArch64 `SUBS`/`CMP`, x86 `SUB`/`CMP`).
    Sub,
    /// `a + b` (AArch64 `ADDS`/`CMN`, x86 `ADD`).
    Add,
    /// `a & b` (AArch64 `ANDS`/`TST`, x86 `AND`/`TEST`; carry and overflow
    /// clear).
    And,
}

/// A branch, select or trap condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TripCond {
    /// An AArch64 4-bit condition encoding on NZCV.
    Arm(u8),
    /// An x86 condition code on RFLAGS.
    X86(X86CondCode),
    /// `op == 0`
    Zero(TripOperand),
    /// `op != 0`
    NonZero(TripOperand),
    /// Bit `bit` of `op` is clear.
    BitClear(TripOperand, u8),
    /// Bit `bit` of `op` is set.
    BitSet(TripOperand, u8),
    /// A condition the model does not compute (a conditional trap whose test
    /// it does not describe), reading what [`UnknownTest`] says.
    Unknown(UnknownTest),
}

/// What the test of a [`TripCond::Unknown`] condition reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum UnknownTest {
    /// These operands and nothing else (an unused slot is `None`): the test
    /// is a function of their values, which the model does not compute.
    Reads([Option<TripOperand>; 2]),
    /// Something the adapter does not name as an operand.
    Unnamed,
}

/// One effect of an instruction on what the coverage clause tracks, in
/// program order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TripEffect<B> {
    /// Register `dst` takes `op`'s value at `width` bits, zero-extended.
    Set { dst: RegId, width: u8, op: TripOp },
    /// Register `dst` takes a value the model does not compute.
    Clobber(RegId),
    /// The flags take `op(a, b)` at `width` bits.
    Flags {
        op: FlagOp,
        a: TripOperand,
        b: TripOperand,
        width: u8,
    },
    /// The flags take a value the model does not compute.
    ClobberFlags,
    /// When `cond` holds control goes to `target`; otherwise it continues.
    Branch { cond: TripCond, target: B },
    /// Control goes to `target`.
    Jump(B),
    /// Control ends with no successor block, as `StopKind` says.
    Stop(StopKind),
    /// Control ends when `cond` holds (a conditional trap).
    StopIf(TripCond),
    /// A transfer the model does not describe: a run that reaches it is
    /// undecided.
    Opaque,
}

/// How control ends with no successor block. A return and a trap are
/// different outcomes: a rewrite that returns where the scalar loop traps is
/// refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum StopKind {
    /// A return.
    Return,
    /// A trap: an unconditional one, or a conditional trap whose condition
    /// holds.
    Trap,
    /// An indirect branch (its targets cannot be named).
    IndirectBranch,
    /// A tail call.
    TailCall,
}

/// How a rewrite counts the iterations its new code runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Lanes<B> {
    /// Blocks of the rewritten function, each with the number of scalar
    /// iterations one entry into it runs.
    pub(crate) blocks: Vec<(B, u64)>,
    /// Whether the scalar loop stays as the remainder.
    pub(crate) remainder: Remainder,
    /// Blocks of the rewritten function that copy a block of the scalar
    /// loop, as `(copy, original)`: a full unroll's per-iteration clones. An
    /// exit on undecided data in a copy may stand for the original's
    /// (see the module docs, "Undecided conditions"); nothing else reads it.
    pub(crate) copies: Vec<(B, B)>,
}

/// What runs the iterations the new code does not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Remainder {
    /// The scalar loop, unchanged: its iterations in the rewritten function
    /// count one each. Every block of it must hold the same instructions
    /// ([`LoopStateView::same_inst`]) and fall through to the same block as
    /// in the scalar function, and every transfer from outside it into it
    /// must enter at its header; the clause refuses otherwise.
    ScalarLoop,
    /// Nothing: the new code runs every iteration (an in-place vectorizer, a
    /// full unroll, a closed form).
    None,
}

/// How a run left the region.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum RunEnd<B> {
    /// Through an edge to `B`, a block outside the region.
    Leaves(B),
    /// With no successor block, as the kind says.
    Stops(StopKind),
}

/// The outcome of one run: how it left, how many scalar iterations it ran,
/// and the reproduced registers' values when it left (`None`: unknown).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Outcome<B> {
    pub(crate) end: RunEnd<B>,
    pub(crate) iterations: u128,
    pub(crate) carried: Vec<Option<u64>>,
}

/// Why the coverage clause refuses a rewrite.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CoverageEscape<B> {
    /// For these inputs the rewritten function's run differs from the scalar
    /// loop's.
    Mismatch {
        inputs: Vec<(RegId, u64)>,
        scalar: Outcome<B>,
        rewritten: Outcome<B>,
    },
    /// The clause could not decide: `why` names the reason (an exhausted
    /// budget, an undescribed transfer, a scalar loop whose trip count
    /// depends on data, a malformed request).
    Undecided { why: &'static str },
}

/// Evidence that a rewrite passed the iteration-coverage clause. Minted only
/// by [`check_coverage`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct IterationCoverage {
    _sealed: (),
}

/// The sample values of an input, before masking to its width. 0, 1, one
/// short of, at and one past every power of two up to 1024, 48, 100 and 1000,
/// and the 32- and 64-bit edges.
pub(crate) const SAMPLES: &[u64] = &[
    0,
    1,
    2,
    3,
    4,
    5,
    7,
    8,
    9,
    15,
    16,
    17,
    31,
    32,
    33,
    47,
    48,
    49,
    63,
    64,
    65,
    100,
    127,
    128,
    129,
    255,
    256,
    257,
    511,
    512,
    513,
    1000,
    1023,
    1024,
    1025,
    0x7fff_ffff,
    0x8000_0000,
    0xffff_ffff,
    0x1_0000_0000,
    0x7fff_ffff_ffff_ffff,
    0x8000_0000_0000_0000,
    u64::MAX - 1,
    u64::MAX,
];

/// The values the other inputs are held at while one input runs over every
/// sample, when there are more than two inputs, and the values each
/// carrier-only input ([`Input::carrier_only`]) runs over.
const PIVOTS: &[u64] = &[0, 1, 17, 64, 1000, u64::MAX];

/// Crossed input combinations one check may run when it has carrier-only
/// inputs ([`input_combos`]): every pair of two 64-bit inputs' samples
/// (1849) times one carrier-only input's six pivots (11094) fits; a second
/// carrier-only input beside them does not, and the check refuses
/// undecided.
const CARRIER_COMBO_BUDGET: usize = 12_000;

/// Block executions allowed for one run of one function.
const RUN_BUDGET: usize = 100_000;
/// Block executions allowed for one whole check.
const CHECK_BUDGET: usize = 6_000_000;
/// Simultaneous runs (forks on unknown conditions) allowed for one input.
const FORK_BUDGET: usize = 256;
/// Blocks one affine iteration may execute.
const AFFINE_BUDGET: usize = 512;

/// Check the iteration-coverage clause for a rewrite of the loop `scope`
/// names: `before` is the function the loop-state check admitted, `after` the
/// rewritten one, and `lanes` how the new code counts. See the module docs.
pub(crate) fn check_coverage<G: LoopStateView>(
    before: &G,
    after: &G,
    scope: &CoveredLoop<G::Block>,
    lanes: &Lanes<G::Block>,
) -> Result<IterationCoverage, CoverageEscape<G::Block>> {
    check_coverage_in(
        &CoverageFrame::new(before, after),
        before,
        after,
        scope,
        lanes,
    )
}

/// [`check_coverage`] under a `frame` built once for this `(before, after)`
/// pair, so the loops one candidate rewrites are each checked at the cost of
/// their own region, never of the whole function again.
pub(crate) fn check_coverage_in<G: LoopStateView>(
    frame: &CoverageFrame<G::Block>,
    before: &G,
    after: &G,
    scope: &CoveredLoop<G::Block>,
    lanes: &Lanes<G::Block>,
) -> Result<IterationCoverage, CoverageEscape<G::Block>> {
    Checker::new(frame, before, after, scope, lanes)?.run()
}

/// The whole-function facts every check of one `(before, after)` pair reads:
/// both layouts, their fall-through successors, and `before`'s predecessors.
pub(crate) struct CoverageFrame<B> {
    before_layout: HashSet<B>,
    after_layout: HashSet<B>,
    before_fall: HashMap<B, B>,
    after_fall: HashMap<B, B>,
    before_preds: HashMap<B, Vec<B>>,
}

impl<B: Copy + Eq + Hash> CoverageFrame<B> {
    pub(crate) fn new<G: LoopStateView<Block = B>>(before: &G, after: &G) -> Self {
        CoverageFrame {
            before_layout: before.layout_order().into_iter().collect(),
            after_layout: after.layout_order().into_iter().collect(),
            before_fall: layout_fall(before),
            after_fall: layout_fall(after),
            before_preds: predecessors(before),
        }
    }
}

/// `fall` restricted to `blocks`: the only entries a region reads.
fn region_fall<B: Copy + Eq + Hash>(fall: &HashMap<B, B>, blocks: &HashSet<B>) -> HashMap<B, B> {
    blocks
        .iter()
        .filter_map(|block| fall.get(block).map(|&next| (*block, next)))
        .collect()
}

/// Every block a run of `ir` from `entry` can enter while it stays in
/// `allowed`, `entry` included: by a CFG edge, a branch target or the layout
/// fall-through (the edges [`predecessors`] reads). A block it cannot enter
/// never takes part in a run, so a region needs no other block of `allowed`.
fn reachable_within<G: LoopStateView>(
    ir: &G,
    fall: &HashMap<G::Block, G::Block>,
    entry: G::Block,
    allowed: impl Fn(G::Block) -> bool,
) -> HashSet<G::Block> {
    let mut reached: HashSet<G::Block> = HashSet::default();
    let mut work = vec![entry];
    while let Some(block) = work.pop() {
        if !reached.insert(block) {
            continue;
        }
        let mut next = ir.successors(block);
        for index in 0..ir.inst_count(block) {
            next.extend(ir.branch_targets(block, index));
        }
        next.extend(fall.get(&block).copied());
        work.extend(
            next.into_iter()
                .filter(|&succ| allowed(succ) && !reached.contains(&succ)),
        );
    }
    reached
}

// ---------------------------------------------------------------------------
// The two regions
// ---------------------------------------------------------------------------

/// One function's region: its blocks, their slice effects, and how a run
/// counts iterations in it.
struct Region<B> {
    /// The preheader: where every run starts, and a block a run leaves the
    /// region by re-entering.
    entry: B,
    blocks: HashSet<B>,
    effects: HashMap<B, Vec<TripEffect<B>>>,
    /// For each effect of `effects`, the index of the instruction it
    /// describes in its block.
    origin: HashMap<B, Vec<usize>>,
    /// The layout successor of each block that does not end in a transfer.
    fall: HashMap<B, B>,
    /// Width counted per entry into a block.
    lane: HashMap<B, u64>,
    /// The scalar header whose entries count, and the loop test that ends an
    /// uncounted final entry (`None` when the header's entries do not count).
    scalar: Option<ScalarCount<B>>,
    /// Blocks a run may be accelerated at (targets of a DFS back edge).
    heads: HashSet<B>,
}

#[derive(Clone, Copy)]
struct ScalarCount<B> {
    header: B,
    /// The loop test `(from, to)`: a final header entry that leaves through
    /// it is not an iteration, when `top_tested`.
    test: (B, B),
    top_tested: bool,
}

fn layout_fall<G: LoopStateView>(ir: &G) -> HashMap<G::Block, G::Block> {
    let order = ir.layout_order();
    let mut fall = HashMap::default();
    for (index, &block) in order.iter().enumerate() {
        let count = ir.inst_count(block);
        let ends = count > 0
            && (ir.is_unconditional_branch(block, count - 1) || ir.is_return(block, count - 1));
        if !ends && let Some(&next) = order.get(index + 1) {
            fall.insert(block, next);
        }
    }
    fall
}

/// Each block's effects, in program order, and for each effect the index of
/// the instruction it describes.
#[allow(clippy::type_complexity)]
fn collect_effects<G: LoopStateView>(
    ir: &G,
    blocks: &HashSet<G::Block>,
) -> (
    HashMap<G::Block, Vec<TripEffect<G::Block>>>,
    HashMap<G::Block, Vec<usize>>,
) {
    let mut effects = HashMap::default();
    let mut origin = HashMap::default();
    let mut buffer = Vec::new();
    for &block in blocks {
        let mut list = Vec::new();
        let mut from = Vec::new();
        for index in 0..ir.inst_count(block) {
            buffer.clear();
            ir.trip_effects(block, index, &mut buffer);
            list.extend(buffer.iter().copied());
            from.extend(std::iter::repeat_n(index, buffer.len()));
        }
        effects.insert(block, list);
        origin.insert(block, from);
    }
    (effects, origin)
}

/// Whether instruction `index` of `block` decides control on a condition:
/// a branch or a conditional trap.
fn decides<G: LoopStateView>(ir: &G, block: G::Block, index: usize) -> bool {
    let mut buffer = Vec::new();
    ir.trip_effects(block, index, &mut buffer);
    buffer
        .iter()
        .any(|effect| matches!(effect, TripEffect::Branch { .. } | TripEffect::StopIf(_)))
}

fn operand_regs(operand: &TripOperand, out: &mut Vec<RegId>) {
    if let TripOperand::Reg { id, .. } = operand {
        out.push(*id);
    }
}

/// Which reads of a condition count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reading {
    /// Every register a condition reads, the operands a test the model does
    /// not compute names included: the trip slice the runs execute.
    All,
    /// Without the operands a test the model does not compute names: the
    /// reading that tells the inputs only a carrier reads from the others
    /// ([`Input::carrier_only`]).
    Modeled,
}

/// The trip slice under [`Reading::Modeled`]: the registers, and whether
/// the flags, a run would hold if no carrier's named operand were read.
struct ModeledSlice {
    regs: HashSet<RegId>,
    flags: bool,
}

fn cond_regs(cond: &TripCond, out: &mut Vec<RegId>, reading: Reading) -> bool {
    match cond {
        TripCond::Arm(_) | TripCond::X86(_) => true,
        // A test the model does not compute reads the operands its adapter
        // names, and they are in the slice like any condition's: a run knows
        // them wherever the model computes them, and a trap on values the
        // run knows is not undecided data (`unknown_test_on_known`). A test
        // that names none reads nothing the slice holds.
        TripCond::Unknown(UnknownTest::Reads(reads)) => {
            if reading == Reading::All {
                for operand in reads.iter().flatten() {
                    operand_regs(operand, out);
                }
            }
            false
        }
        TripCond::Unknown(UnknownTest::Unnamed) => false,
        TripCond::Zero(op)
        | TripCond::NonZero(op)
        | TripCond::BitClear(op, _)
        | TripCond::BitSet(op, _) => {
            operand_regs(op, out);
            false
        }
    }
}

/// The registers `op` reads, and whether it reads the flags.
fn op_reads(op: &TripOp, out: &mut Vec<RegId>, reading: Reading) -> bool {
    match op {
        TripOp::Copy(a) | TripOp::Neg(a) => {
            operand_regs(a, out);
            false
        }
        TripOp::Ext { src, .. } => {
            operand_regs(src, out);
            false
        }
        TripOp::Insert16 { old, .. } => {
            operand_regs(old, out);
            false
        }
        TripOp::Bin(_, a, b) | TripOp::BinShifted { a, b, .. } => {
            operand_regs(a, out);
            operand_regs(b, out);
            false
        }
        TripOp::MulAdd(a, b, c) | TripOp::MulSub(a, b, c) => {
            operand_regs(a, out);
            operand_regs(b, out);
            operand_regs(c, out);
            false
        }
        TripOp::Select {
            cond,
            then,
            otherwise,
            ..
        } => {
            operand_regs(then, out);
            operand_regs(otherwise, out);
            cond_regs(cond, out, reading)
        }
        TripOp::SetCond(cond) => cond_regs(cond, out, reading),
        TripOp::SetLow8 { old, cond } => {
            operand_regs(old, out);
            cond_regs(cond, out, reading)
        }
    }
}

/// The trip slice over all `effects`: the registers branch and trap
/// conditions, and the `seeds`, depend on under `reading`, and whether the
/// flags are in it. A slice under [`Reading::Modeled`] is a subset of the
/// one under [`Reading::All`] (fewer reads seed and close it).
fn trip_slice<B>(
    effects: &[&HashMap<B, Vec<TripEffect<B>>>],
    seeds: &[RegId],
    reading: Reading,
) -> (HashSet<RegId>, bool) {
    let mut slice: HashSet<RegId> = seeds.iter().copied().collect();
    let mut flags = false;
    let mut reads = Vec::new();
    for map in effects {
        for list in map.values() {
            for effect in list {
                match effect {
                    TripEffect::Branch { cond, .. } | TripEffect::StopIf(cond) => {
                        reads.clear();
                        flags |= cond_regs(cond, &mut reads, reading);
                        slice.extend(reads.iter().copied());
                    }
                    _ => {}
                }
            }
        }
    }
    loop {
        let mut changed = false;
        for map in effects {
            for list in map.values() {
                for effect in list {
                    reads.clear();
                    let feeds = match effect {
                        TripEffect::Set { dst, op, .. } if slice.contains(dst) => {
                            op_reads(op, &mut reads, reading)
                        }
                        TripEffect::Flags { a, b, .. } if flags => {
                            operand_regs(a, &mut reads);
                            operand_regs(b, &mut reads);
                            false
                        }
                        _ => continue,
                    };
                    if feeds && !flags {
                        flags = true;
                        changed = true;
                    }
                    for &reg in &reads {
                        changed |= slice.insert(reg);
                    }
                }
            }
        }
        if !changed {
            return (slice, flags);
        }
    }
}

/// Keep only the effects that touch the slice or decide control, each with
/// the index of its instruction (`origin`, parallel to `list`).
fn slice_effects<B: Copy>(
    list: &[TripEffect<B>],
    origin: &[usize],
    slice: &HashSet<RegId>,
    flags: bool,
) -> (Vec<TripEffect<B>>, Vec<usize>) {
    list.iter()
        .copied()
        .zip(origin.iter().copied())
        .filter(|(effect, _)| in_slice(effect, slice, flags))
        .unzip()
}

/// Whether [`slice_effects`] keeps `effect` for the slice `slice` (with the
/// flags when `flags`).
fn in_slice<B>(effect: &TripEffect<B>, slice: &HashSet<RegId>, flags: bool) -> bool {
    match effect {
        TripEffect::Set { dst, .. } | TripEffect::Clobber(dst) => slice.contains(dst),
        TripEffect::Flags { .. } | TripEffect::ClobberFlags => flags,
        TripEffect::Branch { .. }
        | TripEffect::Jump(_)
        | TripEffect::Stop(_)
        | TripEffect::StopIf(_)
        | TripEffect::Opaque => true,
    }
}

/// Blocks reached by a DFS back edge from `entry` inside `blocks`.
fn loop_heads<B: Copy + Eq + Hash>(
    entry: B,
    successors: impl Fn(B) -> Vec<B>,
    blocks: &HashSet<B>,
) -> HashSet<B> {
    let mut heads = HashSet::default();
    let mut on_stack: HashSet<B> = HashSet::default();
    let mut done: HashSet<B> = HashSet::default();
    let mut stack: Vec<(B, Vec<B>)> = vec![(entry, successors(entry))];
    on_stack.insert(entry);
    while let Some((block, pending)) = stack.last_mut() {
        if let Some(next) = pending.pop() {
            if !blocks.contains(&next) {
                continue;
            }
            if on_stack.contains(&next) {
                heads.insert(next);
            } else if !done.contains(&next) {
                on_stack.insert(next);
                let succs = successors(next);
                stack.push((next, succs));
            }
        } else {
            let block = *block;
            on_stack.remove(&block);
            done.insert(block);
            stack.pop();
        }
    }
    heads
}

/// Whether a cycle of `region`, among the blocks a run from its entry can
/// reach, passes no counted block: none whose entry adds lanes and not the
/// counted scalar header. Re-entering the entry leaves the region, so the
/// entry is never on a cycle. Every branch counts as taken both ways.
fn has_uncounted_cycle<B: Copy + Eq + Hash>(region: &Region<B>) -> bool {
    let successors = |block: B| -> Vec<B> {
        effect_successors(&region.effects, &region.fall, block)
            .into_iter()
            .filter(|next| region.blocks.contains(next) && *next != region.entry)
            .collect()
    };
    let counted = |block: B| {
        region.lane.contains_key(&block)
            || region.scalar.is_some_and(|scalar| scalar.header == block)
    };
    let mut reached: HashSet<B> = HashSet::default();
    let mut work = successors(region.entry);
    while let Some(block) = work.pop() {
        if reached.insert(block) {
            work.extend(successors(block));
        }
    }
    // Depth-first over the reached, uncounted blocks: an edge to a block
    // still on the stack closes a cycle.
    let mut on_stack: HashSet<B> = HashSet::default();
    let mut done: HashSet<B> = HashSet::default();
    for &root in &reached {
        if counted(root) || done.contains(&root) {
            continue;
        }
        let mut stack: Vec<(B, Vec<B>)> = vec![(root, successors(root))];
        on_stack.insert(root);
        while let Some((block, pending)) = stack.last_mut() {
            if let Some(next) = pending.pop() {
                if counted(next) || done.contains(&next) {
                    continue;
                }
                if on_stack.contains(&next) {
                    return true;
                }
                on_stack.insert(next);
                let succs = successors(next);
                stack.push((next, succs));
            } else {
                let block = *block;
                on_stack.remove(&block);
                done.insert(block);
                stack.pop();
            }
        }
    }
    false
}

/// Successor blocks named by a block's effects, and its fall-through.
fn effect_successors<B: Copy + Eq + Hash>(
    effects: &HashMap<B, Vec<TripEffect<B>>>,
    fall: &HashMap<B, B>,
    block: B,
) -> Vec<B> {
    let mut out = Vec::new();
    let mut ends = false;
    if let Some(list) = effects.get(&block) {
        for effect in list {
            match effect {
                TripEffect::Branch { target, .. } => out.push(*target),
                TripEffect::Jump(target) => {
                    out.push(*target);
                    ends = true;
                    break;
                }
                TripEffect::Stop(_) | TripEffect::Opaque => {
                    ends = true;
                    break;
                }
                _ => {}
            }
        }
    }
    if !ends && let Some(&next) = fall.get(&block) {
        out.push(next);
    }
    out
}

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

fn mask(width: u8) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn sign_extend(value: u64, from: u8) -> u64 {
    if from >= 64 {
        value
    } else if from == 0 {
        0
    } else {
        let shift = 64 - u32::from(from);
        (((value << shift) as i64) >> shift) as u64
    }
}

/// A known register value: the value (zero-extended from `width` bits) and
/// the width it was written at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Known {
    value: u64,
    width: u8,
}

/// The flags, as the operation that wrote them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FlagVal {
    op: FlagOp,
    a: u64,
    b: u64,
    width: u8,
}

/// NZCV and x86 CF of a flag write.
struct FlagBits {
    n: bool,
    z: bool,
    v: bool,
    /// AArch64 C: carry out of an add, NOT borrow of a subtract.
    c_arm: bool,
    /// x86 CF: carry out of an add, borrow of a subtract.
    cf_x86: bool,
}

impl FlagVal {
    fn bits(self) -> FlagBits {
        let m = mask(self.width);
        let (a, b) = (self.a & m, self.b & m);
        let sign = 1u64 << (self.width - 1);
        match self.op {
            FlagOp::Sub => {
                let r = a.wrapping_sub(b) & m;
                FlagBits {
                    n: r & sign != 0,
                    z: r == 0,
                    v: (a ^ b) & (a ^ r) & sign != 0,
                    c_arm: a >= b,
                    cf_x86: a < b,
                }
            }
            FlagOp::Add => {
                let r = a.wrapping_add(b) & m;
                let carry = (u128::from(a) + u128::from(b)) > u128::from(m);
                FlagBits {
                    n: r & sign != 0,
                    z: r == 0,
                    v: !(a ^ b) & (a ^ r) & sign != 0,
                    c_arm: carry,
                    cf_x86: carry,
                }
            }
            FlagOp::And => {
                let r = a & b;
                FlagBits {
                    n: r & sign != 0,
                    z: r == 0,
                    v: false,
                    c_arm: false,
                    cf_x86: false,
                }
            }
        }
    }
}

/// AArch64 `ConditionHolds` over a 4-bit encoding.
fn arm_holds(cc: u8, f: &FlagBits) -> Option<bool> {
    let base = match cc >> 1 {
        0 => f.z,
        1 => f.c_arm,
        2 => f.n,
        3 => f.v,
        4 => f.c_arm && !f.z,
        5 => f.n == f.v,
        6 => f.n == f.v && !f.z,
        7 => true,
        _ => return None,
    };
    Some(if cc & 1 == 1 && cc != 15 { !base } else { base })
}

fn x86_holds(cc: X86CondCode, f: &FlagBits) -> Option<bool> {
    use X86CondCode::*;
    Some(match cc {
        O => f.v,
        NO => !f.v,
        B => f.cf_x86,
        AE => !f.cf_x86,
        E => f.z,
        NE => !f.z,
        BE => f.cf_x86 || f.z,
        A => !f.cf_x86 && !f.z,
        S => f.n,
        NS => !f.n,
        L => f.n != f.v,
        GE => f.n == f.v,
        LE => f.z || f.n != f.v,
        G => !f.z && f.n == f.v,
        #[allow(unreachable_patterns)]
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Concrete runs
// ---------------------------------------------------------------------------

/// The state of one run: the slice registers (by slot) and the flags.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct State {
    regs: Vec<Option<Known>>,
    flags: Option<FlagVal>,
}

/// One run of one function.
#[derive(Debug, Clone)]
struct Run<B> {
    block: B,
    pos: usize,
    state: State,
    lanes: u128,
    entries: u128,
    /// The last edge the run took out of a block, for the final-entry rule.
    last_edge: Option<(B, B)>,
    /// A transfer this run has decided but not yet made (a fork's copy).
    goto: Option<B>,
    /// Inputs that come from the preheader's unmodeled instructions, not yet
    /// consumed by this run.
    pending: Vec<bool>,
    /// Recent entries into acceleration heads: `(head, state, lanes,
    /// entries)` of the previous two entries.
    history: Vec<(B, [HeadEntry; 2])>,
}

/// One recorded entry into an acceleration head: its state and lanes, and
/// the entry count.
type HeadEntry = Option<(State, u128, u128)>;

/// The slot table: slice registers in a fixed order.
struct Slots {
    index: HashMap<RegId, usize>,
    regs: Vec<RegId>,
}

impl Slots {
    fn of(&self, id: RegId) -> Option<usize> {
        self.index.get(&id).copied()
    }
}

fn read_operand(state: &State, slots: &Slots, operand: &TripOperand) -> Option<u64> {
    match *operand {
        TripOperand::Imm(value) => Some(value),
        TripOperand::Reg { id, width } => {
            let known = state.regs[slots.of(id)?]?;
            Some(known.value & mask(width))
        }
    }
}

fn eval_bin(op: TripBin, a: Option<u64>, b: Option<u64>, width: u8) -> Option<u64> {
    let m = mask(width);
    // An unknown operand decides nothing, except where the other one does.
    match (op, a, b) {
        (TripBin::And | TripBin::Mul, Some(0), _) | (TripBin::And | TripBin::Mul, _, Some(0)) => {
            return Some(0);
        }
        (TripBin::Or, Some(x), _) | (TripBin::Or, _, Some(x)) if x & m == m => return Some(m),
        _ => {}
    }
    let (a, b) = (a? & m, b? & m);
    let w = u32::from(width);
    Some(
        match op {
            TripBin::Add => a.wrapping_add(b),
            TripBin::Sub => a.wrapping_sub(b),
            TripBin::Mul => a.wrapping_mul(b),
            TripBin::And => a & b,
            TripBin::Or => a | b,
            TripBin::Xor => a ^ b,
            TripBin::AndNot => a & !b,
            TripBin::OrNot => a | !b,
            TripBin::Shl => a.wrapping_shl((b % u64::from(w)) as u32),
            TripBin::LShr => a.wrapping_shr((b % u64::from(w)) as u32),
            TripBin::AShr => {
                (sign_extend(a, width) as i64).wrapping_shr((b % u64::from(w)) as u32) as u64
            }
            TripBin::Ror => {
                let k = (b % u64::from(w)) as u32;
                if k == 0 { a } else { (a >> k) | (a << (w - k)) }
            }
            TripBin::UDiv => a.checked_div(b).unwrap_or(0),
            TripBin::SDiv => {
                let (x, y) = (sign_extend(a, width) as i64, sign_extend(b, width) as i64);
                if y == 0 { 0 } else { x.wrapping_div(y) as u64 }
            }
        } & m,
    )
}

fn eval_cond(state: &State, slots: &Slots, cond: &TripCond) -> Option<bool> {
    match cond {
        TripCond::Arm(cc) => arm_holds(*cc, &state.flags?.bits()),
        TripCond::X86(cc) => x86_holds(*cc, &state.flags?.bits()),
        TripCond::Zero(op) => Some(read_operand(state, slots, op)? == 0),
        TripCond::NonZero(op) => Some(read_operand(state, slots, op)? != 0),
        TripCond::BitClear(op, bit) => Some(read_operand(state, slots, op)? >> bit & 1 == 0),
        TripCond::BitSet(op, bit) => Some(read_operand(state, slots, op)? >> bit & 1 == 1),
        TripCond::Unknown(_) => None,
    }
}

/// Whether a run knows every value the test of `cond` reads, when the model
/// does not compute that test: its outcome is then fixed by values the run
/// holds, not by undecided data.
fn unknown_test_on_known(state: &State, slots: &Slots, cond: &TripCond) -> bool {
    match cond {
        TripCond::Unknown(UnknownTest::Reads(reads)) => reads
            .iter()
            .flatten()
            .all(|operand| read_operand(state, slots, operand).is_some()),
        _ => false,
    }
}

fn eval_op(state: &State, slots: &Slots, op: &TripOp, width: u8) -> Option<u64> {
    let m = mask(width);
    let read = |operand: &TripOperand| read_operand(state, slots, operand);
    match op {
        TripOp::Copy(a) => Some(read(a)? & m),
        TripOp::Bin(bin, a, b) => eval_bin(*bin, read(a), read(b), width),
        TripOp::BinShifted {
            op,
            a,
            b,
            shift,
            amount,
        } => {
            let shifted = eval_bin(*shift, read(b), Some(u64::from(*amount)), width);
            eval_bin(*op, read(a), shifted, width)
        }
        TripOp::MulAdd(a, b, c) => {
            let product = eval_bin(TripBin::Mul, read(a), read(b), width);
            eval_bin(TripBin::Add, product, read(c), width)
        }
        TripOp::MulSub(a, b, c) => {
            let product = eval_bin(TripBin::Mul, read(a), read(b), width);
            eval_bin(TripBin::Sub, read(c), product, width)
        }
        TripOp::Neg(a) => Some(read(a)?.wrapping_neg() & m),
        TripOp::Ext { signed, from, src } => {
            let low = read(src)? & mask(*from);
            Some(
                if *signed {
                    sign_extend(low, *from)
                } else {
                    low
                } & m,
            )
        }
        TripOp::Insert16 { old, imm, shift } => {
            let field = 0xffffu64 << shift;
            Some((read(old)? & !field | u64::from(*imm) << shift) & m)
        }
        TripOp::Select {
            cond,
            then,
            otherwise,
            post,
        } => {
            let other = |value: u64| match post {
                SelectPost::Plain => value,
                SelectPost::Inc => value.wrapping_add(1),
                SelectPost::Inv => !value,
                SelectPost::Neg => value.wrapping_neg(),
            } & m;
            match eval_cond(state, slots, cond) {
                Some(true) => Some(read(then)? & m),
                Some(false) => Some(other(read(otherwise)?)),
                None => {
                    let (t, o) = (read(then)? & m, other(read(otherwise)?));
                    (t == o).then_some(t)
                }
            }
        }
        TripOp::SetCond(cond) => eval_cond(state, slots, cond).map(u64::from),
        TripOp::SetLow8 { old, cond } => {
            let bit = u64::from(eval_cond(state, slots, cond)?);
            Some((read(old)? & !0xff | bit) & m)
        }
    }
}

// ---------------------------------------------------------------------------
// The affine domain (acceleration)
// ---------------------------------------------------------------------------

/// `base + j * delta` modulo `2^width`, for the iteration index `j`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Aff {
    base: u64,
    delta: u64,
    width: u8,
}

impl Aff {
    fn constant(value: u64, width: u8) -> Self {
        Aff {
            base: value & mask(width),
            delta: 0,
            width,
        }
    }

    fn varies(self) -> bool {
        self.delta & mask(self.width) != 0
    }

    fn at(self, width: u8) -> Self {
        Aff {
            base: self.base & mask(width),
            delta: self.delta & mask(width),
            width,
        }
    }
}

/// The affine iteration aborts: the domain cannot describe it.
struct Abort;

/// Number of leading `j >= 0` (at least 1) for which `x(j)` stays inside the
/// unsigned (`signed == false`) or signed range of `x.width` bits as a true
/// integer: `x(j) = X0 + j * DX` with `DX` the delta read as signed.
fn nowrap_keep(x: Aff, signed: bool) -> u128 {
    if !x.varies() {
        return u128::MAX;
    }
    let w = x.width;
    let x0: i128 = if signed {
        i128::from(sign_extend(x.base, w) as i64)
    } else {
        i128::from(x.base & mask(w))
    };
    let dx: i128 = i128::from(sign_extend(x.delta & mask(w), w) as i64);
    let (lo, hi): (i128, i128) = if signed {
        (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1)
    } else {
        (0, (1i128 << w) - 1)
    };
    let room = if dx > 0 { hi - x0 } else { x0 - lo };
    // j <= room / |dx| keeps x in range; that many plus j = 0.
    (room / dx.abs()) as u128 + 1
}

/// Leading `j` (at least 1) for which `cmp(x(j), y(j))` keeps its `j = 0`
/// value, for an order comparison `x < y` (`strict`) or `x <= y`, unsigned or
/// signed at `width` bits. Exact within both operands' no-wrap ranges; at the
/// end of a range it stops there.
fn order_keep(x: Aff, y: Aff, signed: bool) -> u128 {
    let w = x.width;
    let limit = nowrap_keep(x, signed).min(nowrap_keep(y, signed));
    let as_int = |a: Aff| -> (i128, i128) {
        let base = if signed {
            i128::from(sign_extend(a.base, w) as i64)
        } else {
            i128::from(a.base & mask(w))
        };
        (base, i128::from(sign_extend(a.delta & mask(w), w) as i64))
    };
    let (x0, dx) = as_int(x);
    let (y0, dy) = as_int(y);
    // f(j) = (x0 - y0) + j * s; the comparison is a sign test on f.
    let f0 = x0 - y0;
    let s = dx - dy;
    if s == 0 {
        return limit;
    }
    // Every order comparison is `f < c` or `f >= c` for c in {0, 1}, so the
    // first flip is where f crosses 0 or 1; the earlier one bounds both.
    let flip = |c: i128| -> u128 {
        // First j > 0 where (f(j) < c) differs from (f(0) < c).
        let below = f0 < c;
        if below == (s < 0) {
            // Moving away from c.
            return u128::MAX;
        }
        // below: need f0 + j*s >= c, s > 0: j >= (c - f0) / s.
        // above: need f0 + j*s < c, s < 0: j > (f0 - c) / |s|.
        let j = if below {
            (c - f0 + s - 1) / s
        } else {
            (f0 - c) / (-s) + 1
        };
        j.max(1) as u128
    };
    limit.min(flip(0)).min(flip(1))
}

/// Leading `j` (at least 1) for which `x(j) == y(j)` keeps its `j = 0` value,
/// modulo `2^width`.
fn eq_keep(x: Aff, y: Aff) -> u128 {
    let w = x.width;
    let m = mask(w);
    let s = x.delta.wrapping_sub(y.delta) & m;
    let gap = y.base.wrapping_sub(x.base) & m;
    if s == 0 {
        return u128::MAX;
    }
    if gap == 0 {
        // Equal now, unequal at j = 1.
        return 1;
    }
    // Smallest j > 0 with s * j == gap (mod 2^w).
    let t = s.trailing_zeros();
    if gap.trailing_zeros() < t {
        return u128::MAX;
    }
    let reduced_bits = u32::from(w) - t;
    let rm = if reduced_bits >= 64 {
        u64::MAX
    } else {
        (1u64 << reduced_bits) - 1
    };
    let s_odd = (s >> t) & rm;
    let g = (gap >> t) & rm;
    // Inverse of an odd number modulo 2^k by Newton iteration.
    let mut inv: u64 = 1;
    for _ in 0..6 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(s_odd.wrapping_mul(inv)));
    }
    let j = g.wrapping_mul(inv) & rm;
    if j == 0 {
        // Unreachable: gap != 0 modulo 2^w implies j != 0.
        return u128::MAX;
    }
    u128::from(j)
}

/// The relation a condition on `Sub` flags tests, as `(x, y)` order.
#[derive(Clone, Copy)]
enum Rel {
    Eq,
    /// `x < y` unsigned / signed.
    Lt(bool),
    /// `x <= y`.
    Le(bool),
    /// `x > y`.
    Gt(bool),
    /// `x >= y`.
    Ge(bool),
}

fn arm_rel(cc: u8) -> Option<Rel> {
    Some(match cc & !1 {
        0 => Rel::Eq,
        2 => Rel::Ge(false),
        8 => Rel::Gt(false),
        10 => Rel::Ge(true),
        12 => Rel::Gt(true),
        _ => return None,
    })
}

fn x86_rel(cc: X86CondCode) -> Option<Rel> {
    use X86CondCode::*;
    Some(match cc {
        E | NE => Rel::Eq,
        B => Rel::Lt(false),
        AE => Rel::Ge(false),
        A => Rel::Gt(false),
        BE => Rel::Le(false),
        L => Rel::Lt(true),
        GE => Rel::Ge(true),
        G => Rel::Gt(true),
        LE => Rel::Le(true),
        _ => return None,
    })
}

fn rel_keep(rel: Rel, x: Aff, y: Aff) -> u128 {
    match rel {
        Rel::Eq => eq_keep(x, y),
        Rel::Lt(s) | Rel::Ge(s) => order_keep(x, y, s),
        Rel::Gt(s) | Rel::Le(s) => order_keep(y, x, s),
    }
}

/// Abstract flags: the operation and its affine operands.
#[derive(Debug, Clone, Copy)]
struct AffFlags {
    op: FlagOp,
    a: Aff,
    b: Aff,
}

/// One thread of an affine iteration.
#[derive(Clone)]
struct AffThread<B> {
    block: B,
    pos: usize,
    regs: Vec<Option<Aff>>,
    /// `None` while the iteration has not written the flags (reading them
    /// then aborts).
    flags: Option<Option<AffFlags>>,
    lanes: u128,
    entries: u128,
    steps: usize,
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

/// An input of the runs: a slice register live into the preheader, or the
/// result of an unmodeled instruction of the preheader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Input {
    reg: RegId,
    width: u8,
    /// Whether it is set by a preheader `Clobber` (else: live in).
    clobbered: bool,
    /// Whether it is an input only because a carrier's named operands are
    /// read: under [`Reading::Modeled`] it is no input (outside that slice,
    /// or, live in, read by nothing before the region writes it). No modeled
    /// branch or trap condition depends on it. It never thins the other
    /// inputs' combinations ([`input_combos`]).
    carrier_only: bool,
}

struct Checker<'a, G: LoopStateView> {
    before: &'a G,
    after: &'a G,
    frame: &'a CoverageFrame<G::Block>,
    before_region: Region<G::Block>,
    after_region: Region<G::Block>,
    preheader: G::Block,
    slots: Slots,
    flags_in_slice: bool,
    carried: Vec<RegId>,
    /// Entry values: a constant, or an input index.
    entry: Vec<Option<EntryValue>>,
    inputs: Vec<Input>,
    /// Whether the rewritten run takes the preheader inputs (`clobbered`)
    /// the scalar run takes: only when its preheader computes them with the
    /// scalar preheader's instructions ([`Checker::resolve_entry`]).
    shared_preheader: bool,
    /// For each deciding instruction of the rewritten region in a scalar
    /// loop block or a copy of one, the one scalar loop instruction it
    /// stands for ([`tied_exits`]).
    ties: Ties<G::Block>,
    budget: usize,
    /// When the scalar loop stays as the remainder, unchanged: per slot, the
    /// width a hand-off must match it at (0: not compared), and whether the
    /// header reads the flags before writing them.
    sync_compare: Option<(Vec<u8>, bool)>,
}

#[derive(Debug, Clone, Copy)]
enum EntryValue {
    Constant(Known),
    Input(usize),
}

impl<'a, G: LoopStateView> Checker<'a, G> {
    fn new(
        frame: &'a CoverageFrame<G::Block>,
        before: &'a G,
        after: &'a G,
        scope: &CoveredLoop<G::Block>,
        lanes: &Lanes<G::Block>,
    ) -> Result<Self, CoverageEscape<G::Block>> {
        let undecided = |why| CoverageEscape::Undecided { why };
        let preheader = scope.preheader;
        let loop_blocks: HashSet<G::Block> = scope.blocks.iter().copied().collect();
        if loop_blocks.contains(&preheader) || !loop_blocks.contains(&scope.header) {
            return Err(undecided(
                "malformed scope: preheader inside, or header outside",
            ));
        }
        if !frame.before_layout.contains(&preheader) || !frame.after_layout.contains(&preheader) {
            return Err(undecided("the preheader is not in both functions"));
        }
        let mut before_blocks = loop_blocks.clone();
        before_blocks.insert(preheader);
        // The rewritten region: the preheader, the scalar loop's blocks, and
        // every block the rewrite added that a run from the preheader can
        // enter without leaving the region (blocks another rewrite of the
        // same candidate added are not this loop's).
        let mut after_blocks = before_blocks.clone();
        after_blocks.extend(reachable_within(
            after,
            &frame.after_fall,
            preheader,
            |block| before_blocks.contains(&block) || !frame.before_layout.contains(&block),
        ));
        for &(block, width) in &lanes.blocks {
            if !after_blocks.contains(&block) || width == 0 {
                return Err(undecided("a counted block is outside the rewritten region"));
            }
        }
        // A copy is a block the rewrite added, of one block of the scalar
        // loop. One that a run from the preheader cannot enter never runs.
        let mut copy_of: HashMap<G::Block, G::Block> = HashMap::default();
        for &(copy, original) in &lanes.copies {
            if before_blocks.contains(&copy)
                || !loop_blocks.contains(&original)
                || copy_of
                    .insert(copy, original)
                    .is_some_and(|o| o != original)
            {
                return Err(undecided(
                    "a named copy is not a new block copying one scalar loop block",
                ));
            }
        }
        copy_of.retain(|copy, _| after_blocks.contains(copy));

        let (before_all, before_origin) = collect_effects(before, &before_blocks);
        let (after_all, after_origin) = collect_effects(after, &after_blocks);
        if lanes.remainder == Remainder::ScalarLoop {
            // The remainder's iterations count by entries into the scalar
            // header, and its final entry is iteration-free only when it
            // leaves through the named test edge: both hold only for the
            // scalar loop itself, entered where it is entered. An edited
            // remainder (one that leaves the header by another edge skipped
            // an iteration unseen, or whose exit reads another value) and a
            // transfer into any other block of it (the body entered from new
            // code ran an iteration no header entry counted) are refused.
            // Unchanged is instruction for instruction: equal effects alone
            // would let one unmodeled instruction stand for another.
            let unchanged = loop_blocks.iter().all(|&block| {
                let count = before.inst_count(block);
                count == after.inst_count(block)
                    && (0..count)
                        .all(|index| after.same_inst(block, index, before, block, index, &|b| b))
                    && frame.before_fall.get(&block) == frame.after_fall.get(&block)
            });
            if !unchanged {
                return Err(undecided(
                    "the scalar remainder is not the scalar loop unchanged",
                ));
            }
            let after_fall = region_fall(&frame.after_fall, &after_blocks);
            for &block in after_blocks.iter().filter(|b| !loop_blocks.contains(b)) {
                let mut next = effect_successors(&after_all, &after_fall, block);
                for index in 0..after.inst_count(block) {
                    next.extend(after.branch_targets(block, index));
                }
                if next
                    .iter()
                    .any(|next| loop_blocks.contains(next) && *next != scope.header)
                {
                    return Err(undecided(
                        "new code enters the scalar remainder other than at its header",
                    ));
                }
            }
        }
        // The reproduced registers are compared at the exit when the slice
        // holds them (the induction does); they do not seed it, so an
        // accumulator updated under a data-dependent branch does not split
        // every iteration into two runs.
        let carried: Vec<RegId> = scope.carried.iter().map(|v| v.id).collect();
        let (slice, flags_in_slice) = trip_slice(&[&before_all, &after_all], &[], Reading::All);
        let (modeled, modeled_flags) =
            trip_slice(&[&before_all, &after_all], &[], Reading::Modeled);
        let modeled = ModeledSlice {
            regs: modeled,
            flags: modeled_flags,
        };

        let mut regs: Vec<RegId> = slice.iter().copied().collect();
        regs.sort_unstable();
        let index = regs.iter().enumerate().map(|(i, &r)| (r, i)).collect();
        let slots = Slots { index, regs };

        let (test_from, test_to) = scope.test;
        let header_self_loop = before.successors(scope.header).contains(&scope.header)
            || (0..before.inst_count(scope.header)).any(|i| {
                before
                    .branch_targets(scope.header, i)
                    .contains(&scope.header)
            });
        let count = ScalarCount {
            header: scope.header,
            test: (test_from, test_to),
            top_tested: test_from == scope.header && !header_self_loop,
        };

        let build = |frame_fall: &HashMap<G::Block, G::Block>,
                     blocks: HashSet<G::Block>,
                     all: HashMap<G::Block, Vec<TripEffect<G::Block>>>,
                     all_origin: HashMap<G::Block, Vec<usize>>,
                     lane: HashMap<G::Block, u64>,
                     scalar: Option<ScalarCount<G::Block>>| {
            let fall = region_fall(frame_fall, &blocks);
            let mut effects: HashMap<G::Block, Vec<TripEffect<G::Block>>> = HashMap::default();
            let mut origin: HashMap<G::Block, Vec<usize>> = HashMap::default();
            for (&block, list) in &all {
                let (kept, from) = slice_effects(list, &all_origin[&block], &slice, flags_in_slice);
                effects.insert(block, kept);
                origin.insert(block, from);
            }
            let heads = loop_heads(
                preheader,
                |block| effect_successors(&all, &fall, block),
                &blocks,
            );
            Region {
                entry: preheader,
                blocks,
                effects,
                origin,
                fall,
                lane,
                scalar,
                heads,
            }
        };
        let before_region = build(
            &frame.before_fall,
            before_blocks,
            before_all,
            before_origin,
            HashMap::default(),
            Some(count),
        );
        let lane: HashMap<G::Block, u64> = lanes.blocks.iter().copied().collect();
        let after_scalar = match lanes.remainder {
            Remainder::ScalarLoop => Some(count),
            Remainder::None => None,
        };
        let after_region = build(
            &frame.after_fall,
            after_blocks,
            after_all,
            after_origin,
            lane,
            after_scalar,
        );
        // A run that comes back to a block in a state it already had never
        // leaves, and the explorer's merge of equal states would drop it with
        // no outcome: a rewrite that hangs on some path would then be
        // admitted for want of a run to compare. A run's count of lanes and
        // scalar-header entries is in that state, so a run can return to one
        // of its own states only around a cycle that passes no counted block;
        // a region with such a cycle is refused undecided, and every merge
        // the explorer makes is then a join of two different runs.
        if has_uncounted_cycle(&before_region) || has_uncounted_cycle(&after_region) {
            return Err(undecided("a cycle of the region passes no counted block"));
        }

        let ties = tied_exits(before, after, &after_region, &loop_blocks, &copy_of);
        let mut checker = Checker {
            before,
            after,
            frame,
            before_region,
            after_region,
            preheader,
            slots,
            flags_in_slice,
            carried,
            entry: Vec::new(),
            inputs: Vec::new(),
            shared_preheader: false,
            ties,
            budget: CHECK_BUDGET,
            sync_compare: None,
        };
        checker.resolve_entry(&modeled);
        if lanes.remainder == Remainder::ScalarLoop {
            let mut compare = live_in(&checker.before_region, &checker.slots, scope.header, None);
            for &reg in &checker.carried {
                if let Some(slot) = checker.slots.of(reg) {
                    compare[slot] = 64;
                }
            }
            let flags_live = flags_live_at(&checker.before_region, scope.header);
            checker.sync_compare = Some((compare, flags_live));
        }
        Ok(checker)
    }

    /// Entry values of the slice: constants where every reaching definition
    /// outside the region agrees, inputs otherwise. An input is carrier-only
    /// ([`Input::carrier_only`]) when it would be none were the slice
    /// `modeled`.
    fn resolve_entry(&mut self, modeled: &ModeledSlice) {
        let live_before = live_in(&self.before_region, &self.slots, self.preheader, None);
        let live_after = live_in(&self.after_region, &self.slots, self.preheader, None);
        let modeled_before = live_in(
            &self.before_region,
            &self.slots,
            self.preheader,
            Some(modeled),
        );
        let modeled_after = live_in(
            &self.after_region,
            &self.slots,
            self.preheader,
            Some(modeled),
        );
        let mut entry = vec![None; self.slots.regs.len()];
        let mut inputs = Vec::new();
        let preds = &self.frame.before_preds;
        for slot in 0..self.slots.regs.len() {
            let reg = self.slots.regs[slot];
            let width = live_before[slot].max(live_after[slot]);
            if width == 0 {
                continue;
            }
            match reaching_constant(self.before, preds, self.preheader, reg, 4) {
                Some(known) => entry[slot] = Some(EntryValue::Constant(known)),
                None => {
                    entry[slot] = Some(EntryValue::Input(inputs.len()));
                    inputs.push(Input {
                        reg,
                        width,
                        clobbered: false,
                        carrier_only: !modeled.regs.contains(&reg)
                            || modeled_before[slot].max(modeled_after[slot]) == 0,
                    });
                }
            }
        }
        // Unmodeled results of the preheader's own instructions.
        if let Some(list) = self.before_region.effects.get(&self.preheader) {
            let mut seen: HashSet<RegId> = HashSet::default();
            for effect in list {
                if let TripEffect::Clobber(reg) = effect
                    && seen.insert(*reg)
                    && self.slots.of(*reg).is_some()
                {
                    inputs.push(Input {
                        reg: *reg,
                        width: 64,
                        clobbered: true,
                        carrier_only: !modeled.regs.contains(reg),
                    });
                }
            }
        }
        // One sampled value stands for an unmodeled preheader result in both
        // runs only when both preheaders compute it the same way: they agree
        // instruction for instruction up to the last one that writes a slice
        // register unmodeled, so each such instruction reads the same
        // registers and memory in both. Otherwise the rewritten run takes
        // those results as unknown.
        let last_unmodeled = |region: &Region<G::Block>| -> usize {
            let effects = &region.effects[&self.preheader];
            let origin = &region.origin[&self.preheader];
            effects
                .iter()
                .zip(origin)
                .filter(|(effect, _)| {
                    matches!(effect, TripEffect::Clobber(reg) if self.slots.of(*reg).is_some())
                })
                .map(|(_, &index)| index + 1)
                .max()
                .unwrap_or(0)
        };
        let prefix = last_unmodeled(&self.before_region).max(last_unmodeled(&self.after_region));
        self.shared_preheader = prefix <= self.before.inst_count(self.preheader)
            && prefix <= self.after.inst_count(self.preheader)
            && (0..prefix).all(|index| {
                self.after.same_inst(
                    self.preheader,
                    index,
                    self.before,
                    self.preheader,
                    index,
                    &|b| b,
                )
            });
        self.entry = entry;
        self.inputs = inputs;
    }

    fn run(mut self) -> Result<IterationCoverage, CoverageEscape<G::Block>> {
        let combos = input_combos(&self.inputs).map_err(|why| CoverageEscape::Undecided { why })?;
        let sync_compare = self.sync_compare.clone();
        for values in combos {
            let scalar_run = self.outcomes(&values, None, None)?;
            let [scalar] = scalar_run.outcomes.as_slice() else {
                return Err(CoverageEscape::Undecided {
                    why: "the scalar loop's trip count depends on data it loads",
                });
            };
            let sync = match (&scalar_run.trace, &sync_compare) {
                (Some(trace), Some((compare, flags_live))) => Some(HandOff {
                    trace,
                    outcome: scalar,
                    compare,
                    flags_live: *flags_live,
                }),
                _ => None,
            };
            let rewritten = self
                .outcomes(&values, sync, Some(&scalar_run.data_exits))?
                .outcomes;
            for outcome in rewritten {
                if outcome != *scalar {
                    return Err(CoverageEscape::Mismatch {
                        inputs: self
                            .inputs
                            .iter()
                            .zip(&values)
                            .map(|(input, &value)| (input.reg, value))
                            .collect(),
                        scalar: scalar.clone(),
                        rewritten: outcome,
                    });
                }
            }
        }
        Ok(IterationCoverage { _sealed: () })
    }

    /// Every outcome of one function from the preheader, for `values`: the
    /// scalar function's when `allowed` is `None`, with the trace of its
    /// header entries and the exits on undecided data it assumed not taken;
    /// else the rewritten function's, which may assume only the exits in
    /// `allowed`.
    fn outcomes(
        &mut self,
        values: &[u64],
        sync: Option<HandOff<'_, G::Block>>,
        allowed: Option<&HashSet<DataExit<G::Block>>>,
    ) -> Result<Explored<G::Block>, CoverageEscape<G::Block>> {
        let scalar = allowed.is_none();
        let region = if scalar {
            &self.before_region
        } else {
            &self.after_region
        };
        let mut regs = vec![None; self.slots.regs.len()];
        for (slot, entry) in self.entry.iter().enumerate() {
            regs[slot] = match entry {
                Some(EntryValue::Constant(known)) => Some(*known),
                Some(EntryValue::Input(index)) => {
                    let input = self.inputs[*index];
                    Some(Known {
                        value: values[*index] & mask(input.width),
                        width: input.width,
                    })
                }
                None => None,
            };
        }
        let shares = scalar || self.shared_preheader;
        let pending = self
            .inputs
            .iter()
            .map(|input| input.clobbered && shares)
            .collect();
        let start = Run {
            block: self.preheader,
            pos: 0,
            state: State { regs, flags: None },
            lanes: 0,
            entries: 0,
            last_edge: None,
            goto: None,
            pending,
            history: Vec::new(),
        };
        let mut ctx = RunCtx {
            slots: &self.slots,
            inputs: &self.inputs,
            values,
            carried: &self.carried,
            flags_in_slice: self.flags_in_slice,
            ties: &self.ties,
            trace: (scalar && self.sync_compare.is_some()).then(Trace::new),
            sync,
            data_exits: match allowed {
                Some(allowed) => DataExits::Allow(allowed),
                None => DataExits::Record(HashSet::default()),
            },
        };
        let outcomes = ctx.explore(region, start, &mut self.budget)?;
        Ok(Explored {
            outcomes,
            trace: ctx.trace,
            data_exits: match ctx.data_exits {
                DataExits::Record(seen) => seen,
                DataExits::Allow(_) => HashSet::default(),
            },
        })
    }
}

/// What exploring one function found.
struct Explored<B> {
    outcomes: Vec<Outcome<B>>,
    /// The scalar run's header entries, when the hand-off is checked.
    trace: Option<Trace>,
    /// The exits on undecided data the scalar run assumed not taken.
    data_exits: HashSet<DataExit<B>>,
}

/// An exit of the scalar loop a run assumes not taken because the model
/// cannot decide its condition (it reads a loaded or unmodeled value): the
/// scalar function's instruction that decides it, as the
/// [`super::LoopExit`] the control clause accounts for names it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct DataExit<B> {
    /// The scalar loop block and the index of the branch or conditional
    /// trap in it.
    at: (B, usize),
    /// Where a branch leaves to, a block outside the region; `None` for a
    /// conditional trap.
    to: Option<B>,
}

/// Each deciding instruction `(block, index)` of the rewritten region, with
/// the one scalar loop instruction it is tied to ([`tied_exits`]).
type Ties<B> = HashMap<(B, usize), (B, usize)>;

/// The exits on undecided data a run may assume not taken.
enum DataExits<'c, B> {
    /// The scalar run: any exit of the scalar loop (every one of which the
    /// control clause accounts for), recorded here; none of the preheader.
    Record(HashSet<DataExit<B>>),
    /// A rewritten run: only an exit of an instruction tied to one the
    /// scalar run assumed for the same inputs ([`tied_exits`]), to the same
    /// block. Any other is an exit only the new code has, which nothing
    /// accounts for.
    Allow(&'c HashSet<DataExit<B>>),
}

/// For each instruction of the rewritten region that decides control and
/// stands in a block of the scalar loop (kept, or rewritten in place) or a
/// copy of one the rewrite names, the one scalar loop instruction it stands
/// for, if any. Ties are one to one within each such block: its deciding
/// instructions of one text ([`LoopStateView::same_inst`], a copy's block
/// operands read as the blocks they copy) stand, in order, for the
/// deciding instructions of that text in the block it is or copies, and
/// only when the two blocks have equally many of them. A rewritten block
/// with one more of a text than the scalar block (a new exit beside the
/// scalar loop's own one, its compare or register behind it unseen), or
/// one fewer, ties none of that text: one rewritten exit stands for at most
/// one scalar exit, and each scalar exit is stood for at most once in place
/// and once in each copy. Its exits on undecided data stand for that
/// instruction's; an instruction with no tie has none to stand for.
fn tied_exits<G: LoopStateView>(
    before: &G,
    after: &G,
    after_region: &Region<G::Block>,
    loop_blocks: &HashSet<G::Block>,
    copy_of: &HashMap<G::Block, G::Block>,
) -> Ties<G::Block> {
    let original = |block: G::Block| copy_of.get(&block).copied().unwrap_or(block);
    let mut ties = HashMap::default();
    for &block in &after_region.blocks {
        let scalar = if loop_blocks.contains(&block) {
            block
        } else if let Some(&copied) = copy_of.get(&block) {
            copied
        } else {
            continue;
        };
        let candidates: Vec<usize> = (0..before.inst_count(scalar))
            .filter(|&index| decides(before, scalar, index))
            .collect();
        // Each text the rewritten block's deciding instructions share with
        // the scalar block's: the scalar instructions of that text and the
        // rewritten ones, each in block order. Two rewritten instructions
        // match the same scalar ones exactly when they have the same text.
        let mut texts: Vec<(Vec<usize>, Vec<usize>)> = Vec::new();
        for index in 0..after.inst_count(block) {
            if !decides(after, block, index) {
                continue;
            }
            let matching: Vec<usize> = candidates
                .iter()
                .copied()
                .filter(|&at| after.same_inst(block, index, before, scalar, at, &original))
                .collect();
            if matching.is_empty() {
                continue;
            }
            match texts
                .iter_mut()
                .find(|(scalar_at, _)| *scalar_at == matching)
            {
                Some((_, rewritten)) => rewritten.push(index),
                None => texts.push((matching, vec![index])),
            }
        }
        for (scalar_at, rewritten) in texts {
            if scalar_at.len() == rewritten.len() {
                for (index, at) in rewritten.into_iter().zip(scalar_at) {
                    ties.insert((block, index), (scalar, at));
                }
            }
        }
    }
    ties
}

/// Whether rewritten instruction `at` is tied to a scalar instruction whose
/// exit to `to` (a trap: `None`) the scalar run assumed not taken.
fn tied_to_assumed<B: Copy + Eq + Hash>(
    ties: &Ties<B>,
    scalar: &HashSet<DataExit<B>>,
    at: (B, usize),
    to: Option<B>,
) -> bool {
    ties.get(&at)
        .is_some_and(|&at| scalar.contains(&DataExit { at, to }))
}

/// Whether some path from the top of `block` reads the flags before the
/// region writes them.
fn flags_live_at<B: Copy + Eq + Hash>(region: &Region<B>, block: B) -> bool {
    let reads = |cond: &TripCond| matches!(cond, TripCond::Arm(_) | TripCond::X86(_));
    let mut seen: HashSet<B> = HashSet::default();
    let mut work = vec![block];
    while let Some(block) = work.pop() {
        if !region.blocks.contains(&block) || !seen.insert(block) {
            continue;
        }
        let mut written = false;
        for effect in region.effects.get(&block).into_iter().flatten() {
            let read = match effect {
                TripEffect::Branch { cond, .. } | TripEffect::StopIf(cond) => reads(cond),
                TripEffect::Set {
                    op:
                        TripOp::Select { cond, .. }
                        | TripOp::SetCond(cond)
                        | TripOp::SetLow8 { cond, .. },
                    ..
                } => reads(cond),
                _ => false,
            };
            if read {
                return true;
            }
            if matches!(effect, TripEffect::Flags { .. } | TripEffect::ClobberFlags) {
                written = true;
                break;
            }
        }
        if !written {
            work.extend(effect_successors(&region.effects, &region.fall, block));
        }
    }
    false
}

/// The inputs' value combinations a check runs. The inputs that are not
/// [`Input::carrier_only`] take exactly the combinations [`sampled_combos`]
/// gives them alone, as if the carrier-only ones were absent, and each of
/// those is run once for every combination of the carrier-only inputs over
/// [`PIVOTS`]. The combinations [`sampled_combos`] gives every input counted
/// together run as well. So a carrier-only input adds runs and never
/// replaces any: neither those the other inputs take without it, nor those
/// all of them take with it counted. More than [`CARRIER_COMBO_BUDGET`]
/// crossed combinations is an error (the check refuses undecided), never a
/// sparser selection.
fn input_combos(inputs: &[Input]) -> Result<Vec<Vec<u64>>, &'static str> {
    let (carrier, others): (Vec<usize>, Vec<usize>) =
        (0..inputs.len()).partition(|&i| inputs[i].carrier_only);
    if carrier.is_empty() {
        return Ok(sampled_combos(inputs));
    }
    let base: Vec<Input> = others.iter().map(|&i| inputs[i]).collect();
    let combos = sampled_combos(&base);
    let too_many = "the inputs only a carrier reads take the runs past their bound";
    // Every combination of the carrier-only inputs' pivots.
    let mut picks: Vec<Vec<u64>> = vec![Vec::new()];
    for &i in &carrier {
        let mut values: Vec<u64> = PIVOTS.iter().map(|&v| v & mask(inputs[i].width)).collect();
        values.sort_unstable();
        values.dedup();
        picks = picks
            .iter()
            .flat_map(|pick| {
                values.iter().map(move |&value| {
                    let mut next = pick.clone();
                    next.push(value);
                    next
                })
            })
            .collect();
        if picks.len().saturating_mul(combos.len()) > CARRIER_COMBO_BUDGET {
            return Err(too_many);
        }
    }
    let mut out = Vec::with_capacity(combos.len() * picks.len());
    for combo in &combos {
        for pick in &picks {
            let mut values = vec![0; inputs.len()];
            for (&i, &value) in others.iter().zip(combo) {
                values[i] = value;
            }
            for (&i, &value) in carrier.iter().zip(pick) {
                values[i] = value;
            }
            out.push(values);
        }
    }
    let mut seen: HashSet<Vec<u64>> = out.iter().cloned().collect();
    for combo in sampled_combos(inputs) {
        if seen.insert(combo.clone()) {
            out.push(combo);
        }
    }
    Ok(out)
}

/// Value combinations of `inputs`: every one when there are at most two,
/// else each input over every sample with the others at each of [`PIVOTS`],
/// plus every pair over a short list with the others at 0.
fn sampled_combos(inputs: &[Input]) -> Vec<Vec<u64>> {
    let values = |input: &Input| -> Vec<u64> {
        let mut out: Vec<u64> = SAMPLES.iter().map(|&v| v & mask(input.width)).collect();
        out.sort_unstable();
        out.dedup();
        out
    };
    match inputs {
        [] => vec![Vec::new()],
        [one] => values(one).into_iter().map(|v| vec![v]).collect(),
        [a, b] => {
            let (va, vb) = (values(a), values(b));
            let mut out = Vec::with_capacity(va.len() * vb.len());
            for &x in &va {
                for &y in &vb {
                    out.push(vec![x, y]);
                }
            }
            out
        }
        many => {
            let lists: Vec<Vec<u64>> = many.iter().map(values).collect();
            let mut out: Vec<Vec<u64>> = Vec::new();
            let mut seen: HashSet<Vec<u64>> = HashSet::default();
            let mut push = |combo: Vec<u64>| {
                if seen.insert(combo.clone()) {
                    out.push(combo);
                }
            };
            for (moving, list) in lists.iter().enumerate() {
                for &pivot in PIVOTS {
                    for &value in list {
                        let combo = many
                            .iter()
                            .enumerate()
                            .map(|(i, input)| {
                                if i == moving {
                                    value
                                } else {
                                    pivot & mask(input.width)
                                }
                            })
                            .collect();
                        push(combo);
                    }
                }
            }
            // Every pair over a short list, the others at 0.
            const PAIR: &[u64] = &[0, 1, 15, 16, 17, 64, 65, 1000];
            for i in 0..many.len() {
                for j in i + 1..many.len() {
                    for &x in PAIR {
                        for &y in PAIR {
                            let combo = many
                                .iter()
                                .enumerate()
                                .map(|(k, input)| {
                                    let value = if k == i {
                                        x
                                    } else if k == j {
                                        y
                                    } else {
                                        0
                                    };
                                    value & mask(input.width)
                                })
                                .collect();
                            push(combo);
                        }
                    }
                }
            }
            out
        }
    }
}

/// For each slot, the widest width at which a path from the top of `entry`
/// may read it before the region writes it (0: not live). With `modeled`,
/// as the region sliced to it would read it under [`Reading::Modeled`]: only
/// the effects that slice keeps ([`in_slice`]), and no operand a test the
/// model does not compute names.
fn live_in<B: Copy + Eq + Hash>(
    region: &Region<B>,
    slots: &Slots,
    entry: B,
    modeled: Option<&ModeledSlice>,
) -> Vec<u8> {
    // Backward fixpoint over the region's blocks.
    let n = slots.regs.len();
    let mut live: HashMap<B, Vec<u8>> = HashMap::default();
    let succs: HashMap<B, Vec<B>> = region
        .blocks
        .iter()
        .map(|&b| (b, effect_successors(&region.effects, &region.fall, b)))
        .collect();
    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 1000 {
        changed = false;
        rounds += 1;
        for &block in &region.blocks {
            let mut out = vec![0u8; n];
            for next in &succs[&block] {
                if let Some(l) = live.get(next) {
                    for (o, &x) in out.iter_mut().zip(l) {
                        *o = (*o).max(x);
                    }
                }
            }
            // Walk the block backward.
            let list = &region.effects[&block];
            let mut cur = out;
            for effect in list.iter().rev() {
                if modeled.is_some_and(|m| !in_slice(effect, &m.regs, m.flags)) {
                    continue;
                }
                let mut reads: Vec<(RegId, u8)> = Vec::new();
                let push_operand = |op: &TripOperand, reads: &mut Vec<(RegId, u8)>| {
                    if let TripOperand::Reg { id, width } = op {
                        reads.push((*id, *width));
                    }
                };
                let push_cond = |cond: &TripCond, reads: &mut Vec<(RegId, u8)>| match cond {
                    TripCond::Zero(op)
                    | TripCond::NonZero(op)
                    | TripCond::BitClear(op, _)
                    | TripCond::BitSet(op, _) => push_operand(op, reads),
                    // The operands a test the model does not compute names
                    // are read like any condition's: one live into the
                    // region is an input the run samples, and so knows.
                    // The modeled reading reads none, so that the inputs
                    // only they make are told from the others.
                    TripCond::Unknown(UnknownTest::Reads(operands)) if modeled.is_none() => {
                        for op in operands.iter().flatten() {
                            push_operand(op, reads);
                        }
                    }
                    TripCond::Arm(_) | TripCond::X86(_) | TripCond::Unknown(_) => {}
                };
                match effect {
                    TripEffect::Set { dst, op, .. } => {
                        if let Some(slot) = slots.of(*dst) {
                            cur[slot] = 0;
                        }
                        op_operand_widths(op, &mut reads);
                        if let TripOp::Select { cond, .. } | TripOp::SetCond(cond) = op {
                            push_cond(cond, &mut reads);
                        }
                    }
                    TripEffect::Clobber(dst) => {
                        if let Some(slot) = slots.of(*dst) {
                            cur[slot] = 0;
                        }
                    }
                    TripEffect::Flags { a, b, .. } => {
                        push_operand(a, &mut reads);
                        push_operand(b, &mut reads);
                    }
                    TripEffect::Branch { cond, .. } | TripEffect::StopIf(cond) => {
                        push_cond(cond, &mut reads)
                    }
                    _ => {}
                }
                for (id, width) in reads {
                    if let Some(slot) = slots.of(id) {
                        cur[slot] = cur[slot].max(width);
                    }
                }
            }
            if live.get(&block) != Some(&cur) {
                live.insert(block, cur);
                changed = true;
            }
        }
    }
    live.remove(&entry).unwrap_or_else(|| vec![0; n])
}

fn op_operand_widths(op: &TripOp, out: &mut Vec<(RegId, u8)>) {
    let mut push = |operand: &TripOperand| {
        if let TripOperand::Reg { id, width } = operand {
            out.push((*id, *width));
        }
    };
    match op {
        TripOp::Copy(a) | TripOp::Neg(a) => push(a),
        TripOp::Ext { src, .. } => push(src),
        TripOp::Insert16 { old, .. } => push(old),
        TripOp::Bin(_, a, b) | TripOp::BinShifted { a, b, .. } => {
            push(a);
            push(b);
        }
        TripOp::MulAdd(a, b, c) | TripOp::MulSub(a, b, c) => {
            push(a);
            push(b);
            push(c);
        }
        TripOp::Select {
            then, otherwise, ..
        } => {
            push(then);
            push(otherwise);
        }
        TripOp::SetCond(_) => {}
        TripOp::SetLow8 { old, .. } => push(old),
    }
}

/// The constant register `reg` holds at the top of `block`, when every
/// definition reaching it there is the same constant (through at most
/// `depth` copies or constant-operand instructions).
fn reaching_constant<G: LoopStateView>(
    ir: &G,
    preds: &HashMap<G::Block, Vec<G::Block>>,
    block: G::Block,
    reg: RegId,
    depth: u32,
) -> Option<Known> {
    if depth == 0 {
        return None;
    }
    let mut found: Option<Known> = None;
    let mut seen: HashSet<G::Block> = HashSet::default();
    let mut work: Vec<G::Block> = preds.get(&block).cloned().unwrap_or_default();
    if work.is_empty() {
        return None;
    }
    let mut buffer = Vec::new();
    while let Some(pred) = work.pop() {
        if !seen.insert(pred) {
            continue;
        }
        // The last write of `reg` in `pred`, if any.
        let mut def: Option<(usize, TripEffect<G::Block>)> = None;
        for index in (0..ir.inst_count(pred)).rev() {
            buffer.clear();
            ir.trip_effects(pred, index, &mut buffer);
            if let Some(effect) = buffer.iter().rev().find(|effect| {
                matches!(effect, TripEffect::Set { dst, .. } | TripEffect::Clobber(dst) if *dst == reg)
            }) {
                def = Some((index, *effect));
                break;
            }
            // Any other write of the register's number (an unmodeled one
            // is a Clobber, found above).
        }
        let value = match def {
            None => {
                let up = preds.get(&pred).cloned().unwrap_or_default();
                if up.is_empty() {
                    // Reaches the function entry undefined.
                    return None;
                }
                work.extend(up);
                continue;
            }
            Some((index, TripEffect::Set { width, op, .. })) => {
                constant_value(ir, preds, pred, index, &op, width, depth)?
            }
            Some(_) => return None,
        };
        match found {
            None => found = Some(value),
            Some(prev) if prev == value => {}
            Some(_) => return None,
        }
    }
    found
}

/// Evaluate `op` at instruction `index` of `block` when every register it
/// reads is a reaching constant there.
fn constant_value<G: LoopStateView>(
    ir: &G,
    preds: &HashMap<G::Block, Vec<G::Block>>,
    block: G::Block,
    index: usize,
    op: &TripOp,
    width: u8,
    depth: u32,
) -> Option<Known> {
    let mut ids = Vec::new();
    if op_reads(op, &mut ids, Reading::All) {
        return None;
    }
    let slots = Slots {
        index: ids.iter().enumerate().map(|(i, &r)| (r, i)).collect(),
        regs: ids.clone(),
    };
    let mut regs = Vec::with_capacity(ids.len());
    for &id in &ids {
        regs.push(Some(constant_at(ir, preds, block, index, id, depth - 1)?));
    }
    let state = State { regs, flags: None };
    let value = eval_op(&state, &slots, op, width)?;
    Some(Known { value, width })
}

/// The constant `reg` holds just before instruction `index` of `block`.
fn constant_at<G: LoopStateView>(
    ir: &G,
    preds: &HashMap<G::Block, Vec<G::Block>>,
    block: G::Block,
    index: usize,
    reg: RegId,
    depth: u32,
) -> Option<Known> {
    if depth == 0 {
        return None;
    }
    let mut buffer = Vec::new();
    for at in (0..index).rev() {
        buffer.clear();
        ir.trip_effects(block, at, &mut buffer);
        if let Some(effect) = buffer.iter().rev().find(|effect| {
            matches!(effect, TripEffect::Set { dst, .. } | TripEffect::Clobber(dst) if *dst == reg)
        }) {
            return match *effect {
                TripEffect::Set { width, op, .. } => {
                    constant_value(ir, preds, block, at, &op, width, depth)
                }
                _ => None,
            };
        }
    }
    reaching_constant(ir, preds, block, reg, depth)
}

fn predecessors<G: LoopStateView>(ir: &G) -> HashMap<G::Block, Vec<G::Block>> {
    let fall = layout_fall(ir);
    let mut preds: HashMap<G::Block, Vec<G::Block>> = HashMap::default();
    for block in ir.layout_order() {
        let mut succs = ir.successors(block);
        for index in 0..ir.inst_count(block) {
            succs.extend(ir.branch_targets(block, index));
        }
        succs.extend(fall.get(&block).copied());
        succs.sort_by_key(|&b| ir.block_index(b));
        succs.dedup();
        for succ in succs {
            preds.entry(succ).or_default().push(block);
        }
    }
    preds
}

// ---------------------------------------------------------------------------
// Exploring one function
// ---------------------------------------------------------------------------

struct RunCtx<'c, B> {
    slots: &'c Slots,
    inputs: &'c [Input],
    values: &'c [u64],
    carried: &'c [RegId],
    flags_in_slice: bool,
    /// The rewritten region's deciding instructions tied to the scalar
    /// loop's ([`tied_exits`]).
    ties: &'c Ties<B>,
    /// The scalar run records its header entries here.
    trace: Option<Trace>,
    /// A rewritten run checks its hand-off to the scalar loop against this.
    sync: Option<HandOff<'c, B>>,
    /// The exits on undecided data the run may assume not taken.
    data_exits: DataExits<'c, B>,
}

/// The registers the scalar run recorded at one header entry, and its flags
/// when recorded.
type Recorded = (Vec<Option<Known>>, Option<Option<FlagVal>>);

/// The scalar run's state at each entry into the scalar header, by entry
/// number (the first entry is 1).
struct Trace {
    segments: Vec<Segment>,
    /// The last entry number recorded.
    last: u128,
    /// False when the entries are not one run's in order (a run that forked
    /// and did not merge, or an acceleration elsewhere skipped entries).
    linear: bool,
}

enum Segment {
    One {
        at: u128,
        regs: Vec<Option<Known>>,
        flags: Option<FlagVal>,
    },
    /// Entries `at + j` for `j` in `1..=count`: `base + j * delta`.
    Run {
        at: u128,
        count: u128,
        base: Vec<Option<Known>>,
        delta: Vec<Option<u64>>,
    },
}

impl Trace {
    fn new() -> Self {
        Trace {
            segments: Vec::new(),
            last: 0,
            linear: true,
        }
    }

    fn one(&mut self, at: u128, state: &State) {
        if at <= self.last {
            self.linear = false;
            return;
        }
        self.last = at;
        self.segments.push(Segment::One {
            at,
            regs: state.regs.clone(),
            flags: state.flags,
        });
    }

    fn run(&mut self, at: u128, count: u128, base: &[Option<Known>], delta: &[Option<u64>]) {
        if at != self.last {
            self.linear = false;
            return;
        }
        self.last = at + count;
        self.segments.push(Segment::Run {
            at,
            count,
            base: base.to_vec(),
            delta: delta.to_vec(),
        });
    }

    /// The registers at entry `entry`, and the flags when recorded.
    fn lookup(&self, entry: u128) -> Option<Recorded> {
        if !self.linear {
            return None;
        }
        for segment in &self.segments {
            match segment {
                Segment::One { at, regs, flags } if *at == entry => {
                    return Some((regs.clone(), Some(*flags)));
                }
                Segment::Run {
                    at,
                    count,
                    base,
                    delta,
                } if *at < entry && entry <= at + count => {
                    let steps = ((entry - at) % (1u128 << 64)) as u64;
                    let regs = base
                        .iter()
                        .zip(delta)
                        .map(|(value, d)| match (value, d) {
                            (Some(known), Some(d)) => Some(Known {
                                value: known.value.wrapping_add(d.wrapping_mul(steps))
                                    & mask(known.width),
                                width: known.width,
                            }),
                            _ => None,
                        })
                        .collect();
                    return Some((regs, None));
                }
                _ => {}
            }
        }
        None
    }
}

/// What a rewritten run's hand-off to the scalar loop must match.
struct HandOff<'c, B> {
    trace: &'c Trace,
    outcome: &'c Outcome<B>,
    /// Per slot: the widest width the scalar loop reads it at before
    /// writing it, or that the exit compares (0: neither).
    compare: &'c [u8],
    /// Whether the scalar header reads the flags before writing them.
    flags_live: bool,
}

/// What executing the rest of a block did.
enum Step<B> {
    /// Control enters `B` (inside or outside the region).
    Goto(B),
    /// The run stops.
    Stop(StopKind),
    /// An unknown branch with both sides in the region: this run continues
    /// past it, and a copy takes it to `B`.
    Fork(B),
    Undecided(&'static str),
}

impl<B: Copy + Eq + Hash + Debug> RunCtx<'_, B> {
    fn explore(
        &mut self,
        region: &Region<B>,
        start: Run<B>,
        budget: &mut usize,
    ) -> Result<Vec<Outcome<B>>, CoverageEscape<B>> {
        let undecided = |why| CoverageEscape::Undecided { why };
        let mut outcomes: Vec<Outcome<B>> = Vec::new();
        let mut queue: VecDeque<Run<B>> = VecDeque::new();
        let mut seen: HashSet<(B, State, u128, u128)> = HashSet::default();
        queue.push_back(start);
        let mut steps = 0usize;
        while let Some(mut run) = queue.pop_front() {
            loop {
                if *budget == 0 {
                    return Err(undecided("the coverage check's budget is exhausted"));
                }
                *budget -= 1;
                steps += 1;
                if steps > RUN_BUDGET {
                    return Err(undecided("a run exceeded its budget"));
                }
                let step = match run.goto.take() {
                    Some(next) => Step::Goto(next),
                    None => self.execute(region, &mut run),
                };
                match step {
                    Step::Undecided(why) => return Err(undecided(why)),
                    Step::Stop(kind) => {
                        outcomes.push(self.outcome(region, &run, RunEnd::Stops(kind)));
                        break;
                    }
                    Step::Fork(target) => {
                        if queue.len() >= FORK_BUDGET {
                            return Err(undecided("too many runs fork on unknown conditions"));
                        }
                        let mut other = run.clone();
                        other.goto = Some(target);
                        other.history.clear();
                        run.history.clear();
                        queue.push_back(other);
                    }
                    Step::Goto(next) => {
                        run.last_edge = Some((run.block, next));
                        if !region.blocks.contains(&next) || next == region.entry {
                            outcomes.push(self.outcome(region, &run, RunEnd::Leaves(next)));
                            break;
                        }
                        run.block = next;
                        run.pos = 0;
                        if let Some(width) = region.lane.get(&next) {
                            run.lanes += u128::from(*width);
                        }
                        if let Some(scalar) = region.scalar
                            && scalar.header == next
                        {
                            run.entries += 1;
                            if let Some(trace) = self.trace.as_mut() {
                                trace.one(run.entries, &run.state);
                            }
                            if run.entries == 1 && self.in_sync(&run) {
                                // The hand-off is the scalar run's own state at
                                // the next iteration, so the unchanged scalar loop
                                // runs exactly the scalar run's remaining ones.
                                let outcome = self.sync.as_ref().map(|sync| sync.outcome.clone());
                                outcomes.extend(outcome);
                                break;
                            }
                        }
                        if !seen.insert((next, run.state.clone(), run.lanes, run.entries)) {
                            // Another run reached this point in this state:
                            // its future is this one's. (Not this run's own
                            // past: every cycle of the region passes a counted
                            // block, `has_uncounted_cycle`.)
                            break;
                        }
                        if region.heads.contains(&next) {
                            self.accelerate(region, &mut run);
                        }
                    }
                }
            }
        }
        let mut unique: Vec<Outcome<B>> = Vec::new();
        for outcome in outcomes {
            if !unique.contains(&outcome) {
                unique.push(outcome);
            }
        }
        Ok(unique)
    }

    /// Whether `run`, entering the scalar header for the first time after
    /// `run.lanes` iterations of new code, holds the scalar run's state at
    /// its entry `lanes + 1` in every register the scalar loop reads before
    /// writing it, every reproduced register, and the flags if the header
    /// reads them.
    fn in_sync(&self, run: &Run<B>) -> bool {
        let Some(sync) = &self.sync else {
            return false;
        };
        let Some((regs, flags)) = sync.trace.lookup(run.lanes + 1) else {
            return false;
        };
        let registers = sync.compare.iter().enumerate().all(|(slot, &width)| {
            width == 0
                || match (run.state.regs[slot], regs[slot]) {
                    (Some(a), Some(b)) => a.value & mask(width) == b.value & mask(width),
                    _ => false,
                }
        });
        let flags = !sync.flags_live
            || matches!(flags, Some(recorded) if recorded.is_some() && recorded == run.state.flags);
        registers && flags
    }

    fn outcome(&self, region: &Region<B>, run: &Run<B>, end: RunEnd<B>) -> Outcome<B> {
        let mut iterations = run.lanes;
        if let Some(scalar) = region.scalar {
            let mut count = run.entries;
            if scalar.top_tested && count > 0 && run.last_edge == Some(scalar.test) {
                count -= 1;
            }
            iterations += count;
        }
        let carried = self
            .carried
            .iter()
            .map(|&reg| {
                self.slots
                    .of(reg)
                    .and_then(|slot| run.state.regs[slot])
                    .map(|known| known.value)
            })
            .collect();
        Outcome {
            end,
            iterations,
            carried,
        }
    }

    /// Execute `run` from its position to the end of its block or the first
    /// transfer.
    fn execute(&mut self, region: &Region<B>, run: &mut Run<B>) -> Step<B> {
        let Some(list) = region.effects.get(&run.block) else {
            return Step::Undecided("a run reached a block with no effects");
        };
        while let Some(effect) = list.get(run.pos) {
            run.pos += 1;
            match *effect {
                TripEffect::Set { dst, width, op } => {
                    if let Some(slot) = self.slots.of(dst) {
                        let value = eval_op(&run.state, self.slots, &op, width);
                        run.state.regs[slot] = value.map(|value| Known { value, width });
                    }
                }
                TripEffect::Clobber(dst) => {
                    if let Some(slot) = self.slots.of(dst) {
                        run.state.regs[slot] = self.clobber(run, dst);
                    }
                }
                TripEffect::Flags { op, a, b, width } => {
                    if self.flags_in_slice {
                        run.state.flags = match (
                            read_operand(&run.state, self.slots, &a),
                            read_operand(&run.state, self.slots, &b),
                        ) {
                            (Some(a), Some(b)) => Some(FlagVal { op, a, b, width }),
                            _ => None,
                        };
                    }
                }
                TripEffect::ClobberFlags => run.state.flags = None,
                TripEffect::Branch { cond, target } => {
                    match eval_cond(&run.state, self.slots, &cond) {
                        Some(true) => return Step::Goto(target),
                        Some(false) => {}
                        None => {
                            let at = (run.block, region.origin[&run.block][run.pos - 1]);
                            match unknown_branch(region, list, run.pos, run.block, target) {
                                Unknown::Stay(exit) => {
                                    if let Err(why) =
                                        self.assume_not_taken(region, at, Some(exit), false)
                                    {
                                        return Step::Undecided(why);
                                    }
                                }
                                Unknown::Take(exit) => {
                                    if let Err(why) =
                                        self.assume_not_taken(region, at, Some(exit), false)
                                    {
                                        return Step::Undecided(why);
                                    }
                                    return Step::Goto(target);
                                }
                                Unknown::Both => return Step::Fork(target),
                            }
                        }
                    }
                }
                TripEffect::Jump(target) => return Step::Goto(target),
                TripEffect::Stop(kind) => return Step::Stop(kind),
                TripEffect::StopIf(cond) => match eval_cond(&run.state, self.slots, &cond) {
                    Some(true) => return Step::Stop(StopKind::Trap),
                    Some(false) => {}
                    None => {
                        let at = (run.block, region.origin[&run.block][run.pos - 1]);
                        let known = unknown_test_on_known(&run.state, self.slots, &cond);
                        if let Err(why) = self.assume_not_taken(region, at, None, known) {
                            return Step::Undecided(why);
                        }
                    }
                },
                TripEffect::Opaque => {
                    return Step::Undecided("a run reached an undescribed transfer");
                }
            }
        }
        match region.fall.get(&run.block) {
            Some(&next) => Step::Goto(next),
            None => Step::Undecided("a run fell off the end of the layout"),
        }
    }

    /// Assume the exit that instruction `at` decides on an undecided
    /// condition not taken: a branch to `to`, or a conditional trap (`None`).
    /// The run covers only what happens when no such exit fires. The scalar
    /// run records it; the preheader is not the scalar loop, and an exit of
    /// it is one the control clause does not account for. A rewritten run
    /// may assume it only of an instruction tied to one whose exit the scalar
    /// run assumed for the same inputs, to the same block, and never of a
    /// trap whose test the model does not compute but whose operands the run
    /// knows (`known_test`): that trap's outcome is fixed by those values,
    /// not by undecided data, and stands for no other trap.
    fn assume_not_taken(
        &mut self,
        region: &Region<B>,
        at: (B, usize),
        to: Option<B>,
        known_test: bool,
    ) -> Result<(), &'static str> {
        match &mut self.data_exits {
            DataExits::Record(seen) => {
                if at.0 == region.entry {
                    return Err(
                        "the preheader has an exit whose condition the model does not decide",
                    );
                }
                seen.insert(DataExit { at, to });
                Ok(())
            }
            DataExits::Allow(_) if known_test => Err(
                "the rewrite has a trap whose test the model does not compute on values it knows",
            ),
            DataExits::Allow(scalar) => {
                if tied_to_assumed(self.ties, scalar, at, to) {
                    Ok(())
                } else {
                    Err("the rewrite has an exit on undecided data the scalar loop does not have")
                }
            }
        }
    }

    /// Whether an affine iteration of this run may assume the exit `at`
    /// decides not taken, by [`RunCtx::assume_not_taken`]'s rule (the scalar
    /// run's are recorded once the iteration is used).
    fn may_assume(&self, at: (B, usize), to: Option<B>, known_test: bool) -> bool {
        match &self.data_exits {
            DataExits::Record(_) => true,
            DataExits::Allow(_) if known_test => false,
            DataExits::Allow(scalar) => tied_to_assumed(self.ties, scalar, at, to),
        }
    }

    /// The value an unmodeled write gives `reg`: a pending preheader input,
    /// else unknown.
    fn clobber(&self, run: &mut Run<B>, reg: RegId) -> Option<Known> {
        let index = self
            .inputs
            .iter()
            .position(|input| input.clobbered && input.reg == reg)?;
        if !run.pending[index] {
            return None;
        }
        run.pending[index] = false;
        Some(Known {
            value: self.values[index],
            width: 64,
        })
    }

    /// Try to advance `run`, just entered at acceleration head `run.block`,
    /// by many iterations at once.
    fn accelerate(&mut self, region: &Region<B>, run: &mut Run<B>) {
        #[cfg(test)]
        if tests::NO_ACCELERATION.with(std::cell::Cell::get) {
            return;
        }
        let head = run.block;
        let current = (run.state.clone(), run.lanes, run.entries);
        let slot = match run.history.iter().position(|(block, _)| *block == head) {
            Some(slot) => slot,
            None => {
                run.history.push((head, [None, None]));
                run.history.len() - 1
            }
        };
        let [first, second] = run.history[slot].1.clone();
        run.history[slot].1 = [second.clone(), Some(current.clone())];
        let (Some(s1), Some(s2)) = (first, second) else {
            return;
        };
        let Some(delta) = state_delta(&s1, &s2, &current) else {
            return;
        };
        let Some((jump, flags, exits)) = self.affine_iteration(region, run, &delta) else {
            return;
        };
        // `jump` iterations follow the steady path; the last one, `jump - 1`,
        // leaves the flags `flags` describes (unchanged when it writes none).
        if !(2..=(1u128 << 64)).contains(&jump) {
            return;
        }
        if let DataExits::Record(seen) = &mut self.data_exits {
            seen.extend(exits);
        }
        let steps = (jump % (1u128 << 64)) as u64;
        let (reg_delta, lane_delta, entry_delta) = &delta;
        if let Some(trace) = self.trace.as_mut() {
            // The scalar run's header entries this jump skips: recorded as
            // one affine run when the head is the header (one entry per
            // iteration), else the trace stops being usable.
            let at_header = region.scalar.is_some_and(|scalar| scalar.header == head);
            if at_header && *entry_delta == 1 {
                trace.run(run.entries, jump, &run.state.regs, reg_delta);
            } else if *entry_delta != 0 {
                trace.linear = false;
            }
        }
        for (slot, value) in run.state.regs.iter_mut().enumerate() {
            if let (Some(known), Some(d)) = (value.as_mut(), reg_delta[slot]) {
                known.value = known.value.wrapping_add(d.wrapping_mul(steps)) & mask(known.width);
            }
        }
        if let Some(flags) = flags {
            let last = steps.wrapping_sub(1);
            run.state.flags = flags.map(|flags| {
                let at = |a: Aff| a.base.wrapping_add(a.delta.wrapping_mul(last)) & mask(a.width);
                FlagVal {
                    op: flags.op,
                    a: at(flags.a),
                    b: at(flags.b),
                    width: flags.a.width,
                }
            });
        }
        run.lanes += jump * lane_delta;
        run.entries += jump * entry_delta;
        run.history.clear();
    }

    /// Execute one iteration from `run` (at its head, `j = 0`) in the affine
    /// domain with per-iteration advance `delta`. `Some((J, flags, exits))`:
    /// for every `j < J` the iteration takes the same decisions and advances
    /// the state by exactly `delta`; `flags` is what it leaves in the flags
    /// (`None`: it writes none); `exits` are the exits on undecided data it
    /// assumes not taken.
    #[allow(clippy::type_complexity)]
    fn affine_iteration(
        &self,
        region: &Region<B>,
        run: &Run<B>,
        delta: &(Vec<Option<u64>>, u128, u128),
    ) -> Option<(u128, Option<Option<AffFlags>>, Vec<DataExit<B>>)> {
        let head = run.block;
        let (reg_delta, lane_delta, entry_delta) = delta;
        let regs: Vec<Option<Aff>> = run
            .state
            .regs
            .iter()
            .zip(reg_delta)
            .map(|(value, d)| match (value, d) {
                (Some(known), Some(d)) => Some(Aff {
                    base: known.value,
                    delta: *d,
                    width: known.width,
                }),
                _ => None,
            })
            .collect();
        let start = AffThread {
            block: head,
            pos: 0,
            regs: regs.clone(),
            flags: None,
            lanes: 0,
            entries: 0,
            steps: 0,
        };
        let mut keep = u128::MAX;
        let mut pending = vec![start];
        let mut arrived: Vec<AffThread<B>> = Vec::new();
        let mut exits: Vec<DataExit<B>> = Vec::new();
        while let Some(mut thread) = pending.pop() {
            if pending.len() + arrived.len() > FORK_BUDGET {
                return None;
            }
            if !self
                .affine_thread(
                    region,
                    &mut thread,
                    &mut keep,
                    (&mut pending, &mut arrived, &mut exits),
                    head,
                )
                .ok()?
            {
                return None;
            }
        }
        if keep == u128::MAX || arrived.is_empty() {
            return None;
        }
        let final_flags = arrived[0].flags;
        for thread in &arrived {
            // Back at the head: the state must have advanced by exactly one
            // `delta`, and the counters by one iteration's.
            if thread.lanes != *lane_delta || thread.entries != *entry_delta {
                return None;
            }
            if !same_flags(thread.flags, final_flags) {
                return None;
            }
            for (slot, (out, input)) in thread.regs.iter().zip(&regs).enumerate() {
                match (out, input) {
                    (None, None) => {}
                    (Some(out), Some(input)) => {
                        let d = reg_delta[slot]?;
                        let m = mask(input.width);
                        if out.width != input.width
                            || out.base & m != input.base.wrapping_add(d) & m
                            || out.delta & m != d & m
                        {
                            return None;
                        }
                    }
                    _ => return None,
                }
            }
        }
        Some((keep, final_flags, exits))
    }

    /// Run one affine thread until it returns to `head` (pushed to
    /// `arrived`), forking copies onto `pending` and noting the exits on
    /// undecided data it assumes not taken in `exits`. `Ok(false)`: it left
    /// the iteration any other way, or assumed an exit this run may not, so
    /// the iteration is not steady.
    #[allow(clippy::type_complexity)]
    fn affine_thread(
        &self,
        region: &Region<B>,
        thread: &mut AffThread<B>,
        keep: &mut u128,
        (pending, arrived, exits): (
            &mut Vec<AffThread<B>>,
            &mut Vec<AffThread<B>>,
            &mut Vec<DataExit<B>>,
        ),
        head: B,
    ) -> Result<bool, Abort> {
        loop {
            let list = region.effects.get(&thread.block).ok_or(Abort)?;
            let mut next: Option<B> = None;
            while let Some(effect) = list.get(thread.pos) {
                thread.pos += 1;
                match *effect {
                    TripEffect::Set { dst, width, op } => {
                        if let Some(slot) = self.slots.of(dst) {
                            thread.regs[slot] = self.aff_op(thread, &op, width, keep)?;
                        }
                    }
                    TripEffect::Clobber(dst) => {
                        if let Some(slot) = self.slots.of(dst) {
                            thread.regs[slot] = None;
                        }
                    }
                    TripEffect::Flags { op, a, b, width } => {
                        if self.flags_in_slice {
                            let a = self.aff_operand(thread, &a, keep)?;
                            let b = self.aff_operand(thread, &b, keep)?;
                            thread.flags = Some(match (a, b) {
                                (Some(a), Some(b)) => Some(AffFlags {
                                    op,
                                    a: a.at(width),
                                    b: b.at(width),
                                }),
                                _ => None,
                            });
                        }
                    }
                    TripEffect::ClobberFlags => thread.flags = Some(None),
                    TripEffect::Branch { cond, target } => {
                        match self.aff_cond(thread, &cond, keep)? {
                            Some(true) => {
                                next = Some(target);
                                break;
                            }
                            Some(false) => {}
                            None => {
                                let at =
                                    (thread.block, region.origin[&thread.block][thread.pos - 1]);
                                match unknown_branch(region, list, thread.pos, thread.block, target)
                                {
                                    Unknown::Stay(exit) => {
                                        if !self.may_assume(at, Some(exit), false) {
                                            return Ok(false);
                                        }
                                        exits.push(DataExit { at, to: Some(exit) });
                                    }
                                    Unknown::Take(exit) => {
                                        if !self.may_assume(at, Some(exit), false) {
                                            return Ok(false);
                                        }
                                        exits.push(DataExit { at, to: Some(exit) });
                                        next = Some(target);
                                        break;
                                    }
                                    Unknown::Both => {
                                        let mut other = thread.clone();
                                        if !self.affine_enter(region, &mut other, target) {
                                            return Ok(false);
                                        }
                                        if target == head {
                                            arrived.push(other);
                                        } else {
                                            pending.push(other);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    TripEffect::Jump(target) => {
                        next = Some(target);
                        break;
                    }
                    TripEffect::Stop(_) | TripEffect::Opaque => return Ok(false),
                    TripEffect::StopIf(cond) => match self.aff_cond(thread, &cond, keep)? {
                        Some(true) => return Ok(false),
                        Some(false) => {}
                        None => {
                            // An undecided trap is not taken, as in a
                            // concrete run, under the same rule.
                            let at = (thread.block, region.origin[&thread.block][thread.pos - 1]);
                            if !self.may_assume(at, None, self.aff_test_on_known(thread, &cond)) {
                                return Ok(false);
                            }
                            exits.push(DataExit { at, to: None });
                        }
                    },
                }
            }
            let next = match next {
                Some(next) => next,
                None => *region.fall.get(&thread.block).ok_or(Abort)?,
            };
            if !self.affine_enter(region, thread, next) {
                return Ok(false);
            }
            if next == head {
                arrived.push(thread.clone());
                return Ok(true);
            }
        }
    }

    /// Move `thread` into block `next` and count it; `false` when that
    /// leaves the region or exceeds the iteration's budget.
    fn affine_enter(&self, region: &Region<B>, thread: &mut AffThread<B>, next: B) -> bool {
        thread.steps += 1;
        if thread.steps > AFFINE_BUDGET || !region.blocks.contains(&next) || next == region.entry {
            return false;
        }
        thread.block = next;
        thread.pos = 0;
        if let Some(width) = region.lane.get(&next) {
            thread.lanes += u128::from(*width);
        }
        if let Some(scalar) = region.scalar
            && scalar.header == next
        {
            thread.entries += 1;
        }
        true
    }

    fn aff_operand(
        &self,
        thread: &AffThread<B>,
        operand: &TripOperand,
        keep: &mut u128,
    ) -> Result<Option<Aff>, Abort> {
        match *operand {
            TripOperand::Imm(value) => Ok(Some(Aff::constant(value, 64))),
            TripOperand::Reg { id, width } => {
                let Some(slot) = self.slots.of(id) else {
                    return Ok(None);
                };
                let Some(value) = thread.regs[slot] else {
                    return Ok(None);
                };
                if width > value.width && value.varies() {
                    // A wider read zero-extends: affine while the value does
                    // not wrap at its own width.
                    *keep = (*keep).min(nowrap_keep(value, false));
                    let base = value.base & mask(value.width);
                    let delta = sign_extend(value.delta & mask(value.width), value.width);
                    return Ok(Some(Aff {
                        base,
                        delta: delta & mask(width),
                        width,
                    }));
                }
                Ok(Some(value.at(width)))
            }
        }
    }

    fn aff_op(
        &self,
        thread: &AffThread<B>,
        op: &TripOp,
        width: u8,
        keep: &mut u128,
    ) -> Result<Option<Aff>, Abort> {
        let operand = |o: &TripOperand, keep: &mut u128| -> Result<Option<Aff>, Abort> {
            Ok(self.aff_operand(thread, o, keep)?.map(|a| a.at(width)))
        };
        let m = mask(width);
        match op {
            TripOp::Copy(a) => operand(a, keep),
            TripOp::Bin(bin, a, b) => {
                let (a, b) = (operand(a, keep)?, operand(b, keep)?);
                aff_bin(*bin, a, b, width)
            }
            TripOp::BinShifted {
                op,
                a,
                b,
                shift,
                amount,
            } => {
                let (a, b) = (operand(a, keep)?, operand(b, keep)?);
                let amount = Some(Aff::constant(u64::from(*amount), width));
                let shifted = aff_bin(*shift, b, amount, width)?;
                aff_bin(*op, a, shifted, width)
            }
            TripOp::MulAdd(a, b, c) => {
                let product = aff_bin(TripBin::Mul, operand(a, keep)?, operand(b, keep)?, width)?;
                aff_bin(TripBin::Add, product, operand(c, keep)?, width)
            }
            TripOp::MulSub(a, b, c) => {
                let product = aff_bin(TripBin::Mul, operand(a, keep)?, operand(b, keep)?, width)?;
                aff_bin(TripBin::Sub, operand(c, keep)?, product, width)
            }
            TripOp::Neg(a) => Ok(operand(a, keep)?.map(|a| Aff {
                base: a.base.wrapping_neg() & m,
                delta: a.delta.wrapping_neg() & m,
                width,
            })),
            TripOp::Ext { signed, from, src } => {
                let Some(src) = self.aff_operand(thread, src, keep)? else {
                    return Ok(None);
                };
                let low = src.at(*from);
                if low.varies() {
                    *keep = (*keep).min(nowrap_keep(low, *signed));
                }
                let base = if *signed {
                    sign_extend(low.base, *from)
                } else {
                    low.base
                };
                let delta = sign_extend(low.delta, *from);
                Ok(Some(Aff {
                    base: base & m,
                    delta: delta & m,
                    width,
                }))
            }
            TripOp::Insert16 { old, imm, shift } => {
                let Some(old) = operand(old, keep)? else {
                    return Ok(None);
                };
                if old.varies() {
                    return Err(Abort);
                }
                let field = 0xffffu64 << shift;
                Ok(Some(Aff::constant(
                    (old.base & !field) | (u64::from(*imm) << shift),
                    width,
                )))
            }
            TripOp::Select {
                cond,
                then,
                otherwise,
                post,
            } => {
                let Some(chosen) = self.aff_cond(thread, cond, keep)? else {
                    // Unknown condition: known only if both arms agree for
                    // every j, which the domain does not track.
                    return Ok(None);
                };
                if chosen {
                    return operand(then, keep);
                }
                let Some(o) = operand(otherwise, keep)? else {
                    return Ok(None);
                };
                Ok(Some(match post {
                    SelectPost::Plain => o,
                    SelectPost::Inc => Aff {
                        base: o.base.wrapping_add(1) & m,
                        ..o
                    },
                    SelectPost::Inv => Aff {
                        base: !o.base & m,
                        delta: o.delta.wrapping_neg() & m,
                        width,
                    },
                    SelectPost::Neg => Aff {
                        base: o.base.wrapping_neg() & m,
                        delta: o.delta.wrapping_neg() & m,
                        width,
                    },
                }))
            }
            TripOp::SetCond(cond) => Ok(self
                .aff_cond(thread, cond, keep)?
                .map(|holds| Aff::constant(u64::from(holds), width))),
            TripOp::SetLow8 { old, cond } => {
                let Some(old) = operand(old, keep)? else {
                    return Ok(None);
                };
                if old.varies() {
                    return Err(Abort);
                }
                Ok(self
                    .aff_cond(thread, cond, keep)?
                    .map(|holds| Aff::constant(old.base & !0xff | u64::from(holds), width)))
            }
        }
    }

    /// A condition's value at `j = 0`, lowering `keep` to how many leading
    /// `j` keep it; `Ok(None)`: unknown.
    fn aff_cond(
        &self,
        thread: &AffThread<B>,
        cond: &TripCond,
        keep: &mut u128,
    ) -> Result<Option<bool>, Abort> {
        let flag_cond = |rel: Option<Rel>, keep: &mut u128| -> Result<Option<bool>, Abort> {
            // Reading flags the iteration has not written aborts.
            let flags = thread.flags.ok_or(Abort)?;
            let Some(flags) = flags else {
                return Ok(None);
            };
            let concrete = FlagVal {
                op: flags.op,
                a: flags.a.base,
                b: flags.b.base,
                width: flags.a.width,
            };
            let value = match cond {
                TripCond::Arm(cc) => arm_holds(*cc, &concrete.bits()),
                TripCond::X86(cc) => x86_holds(*cc, &concrete.bits()),
                _ => None,
            };
            let Some(value) = value else {
                return Ok(None);
            };
            if !flags.a.varies() && !flags.b.varies() {
                return Ok(Some(value));
            }
            match (flags.op, rel) {
                (FlagOp::Sub, Some(rel)) => {
                    *keep = (*keep).min(rel_keep(rel, flags.a, flags.b));
                    Ok(Some(value))
                }
                _ => Err(Abort),
            }
        };
        match cond {
            TripCond::Arm(cc) => {
                if *cc >> 1 == 7 {
                    return Ok(Some(true));
                }
                flag_cond(arm_rel(*cc), keep)
            }
            TripCond::X86(cc) => flag_cond(x86_rel(*cc), keep),
            TripCond::Zero(op) | TripCond::NonZero(op) => {
                let Some(x) = self.aff_operand(thread, op, keep)? else {
                    return Ok(None);
                };
                let zero = x.base & mask(x.width) == 0;
                if x.varies() {
                    *keep = (*keep).min(eq_keep(x, Aff::constant(0, x.width)));
                }
                Ok(Some(if matches!(cond, TripCond::Zero(_)) {
                    zero
                } else {
                    !zero
                }))
            }
            TripCond::BitClear(op, bit) | TripCond::BitSet(op, bit) => {
                let Some(x) = self.aff_operand(thread, op, keep)? else {
                    return Ok(None);
                };
                if x.varies() {
                    return Err(Abort);
                }
                let set = x.base >> bit & 1 == 1;
                Ok(Some(if matches!(cond, TripCond::BitSet(..)) {
                    set
                } else {
                    !set
                }))
            }
            TripCond::Unknown(_) => Ok(None),
        }
    }

    /// [`unknown_test_on_known`] in the affine domain: every value the test
    /// reads is known for every `j` of the iteration.
    fn aff_test_on_known(&self, thread: &AffThread<B>, cond: &TripCond) -> bool {
        match cond {
            TripCond::Unknown(UnknownTest::Reads(reads)) => {
                reads.iter().flatten().all(|operand| match *operand {
                    TripOperand::Imm(_) => true,
                    TripOperand::Reg { id, .. } => self
                        .slots
                        .of(id)
                        .is_some_and(|slot| thread.regs[slot].is_some()),
                })
            }
            _ => false,
        }
    }
}

fn same_flags(a: Option<Option<AffFlags>>, b: Option<Option<AffFlags>>) -> bool {
    match (a, b) {
        (None, None) | (Some(None), Some(None)) => true,
        (Some(Some(x)), Some(Some(y))) => x.op == y.op && x.a == y.a && x.b == y.b,
        _ => false,
    }
}

fn aff_bin(op: TripBin, a: Option<Aff>, b: Option<Aff>, width: u8) -> Result<Option<Aff>, Abort> {
    let m = mask(width);
    // The concrete absorbing rules first, so an unknown meets them the same
    // way it does in a concrete run.
    let zero = |x: &Option<Aff>| x.is_some_and(|x| !x.varies() && x.base & m == 0);
    let ones = |x: &Option<Aff>| x.is_some_and(|x| !x.varies() && x.base & m == m);
    match op {
        TripBin::And | TripBin::Mul if zero(&a) || zero(&b) => {
            return Ok(Some(Aff::constant(0, width)));
        }
        TripBin::Or if ones(&a) || ones(&b) => return Ok(Some(Aff::constant(m, width))),
        _ => {}
    }
    let (Some(a), Some(b)) = (a, b) else {
        return Ok(None);
    };
    let (a, b) = (a.at(width), b.at(width));
    if !a.varies() && !b.varies() {
        return Ok(eval_bin(op, Some(a.base), Some(b.base), width).map(|v| Aff::constant(v, width)));
    }
    Ok(Some(match op {
        TripBin::Add => Aff {
            base: a.base.wrapping_add(b.base) & m,
            delta: a.delta.wrapping_add(b.delta) & m,
            width,
        },
        TripBin::Sub => Aff {
            base: a.base.wrapping_sub(b.base) & m,
            delta: a.delta.wrapping_sub(b.delta) & m,
            width,
        },
        TripBin::Mul if !a.varies() => Aff {
            base: a.base.wrapping_mul(b.base) & m,
            delta: a.base.wrapping_mul(b.delta) & m,
            width,
        },
        TripBin::Mul if !b.varies() => Aff {
            base: b.base.wrapping_mul(a.base) & m,
            delta: b.base.wrapping_mul(a.delta) & m,
            width,
        },
        TripBin::Shl if !b.varies() => {
            let k = (b.base % u64::from(width)) as u32;
            Aff {
                base: a.base.wrapping_shl(k) & m,
                delta: a.delta.wrapping_shl(k) & m,
                width,
            }
        }
        _ => return Err(Abort),
    }))
}

/// The per-iteration advance of a run seen at three successive entries of
/// one head: every known register's wrapping delta (equal between the two
/// pairs, at an unchanged width and knownness), and the counters'.
#[allow(clippy::type_complexity)]
fn state_delta(
    s1: &(State, u128, u128),
    s2: &(State, u128, u128),
    s3: &(State, u128, u128),
) -> Option<(Vec<Option<u64>>, u128, u128)> {
    let mut deltas = Vec::with_capacity(s1.0.regs.len());
    for ((a, b), c) in s1.0.regs.iter().zip(&s2.0.regs).zip(&s3.0.regs) {
        match (a, b, c) {
            (None, None, None) => deltas.push(None),
            (Some(a), Some(b), Some(c)) if a.width == b.width && b.width == c.width => {
                let m = mask(a.width);
                let d1 = b.value.wrapping_sub(a.value) & m;
                let d2 = c.value.wrapping_sub(b.value) & m;
                if d1 != d2 {
                    return None;
                }
                deltas.push(Some(d1));
            }
            _ => return None,
        }
    }
    let lane = s2.1.checked_sub(s1.1)?;
    let entry = s2.2.checked_sub(s1.2)?;
    if s3.1.checked_sub(s2.1)? != lane || s3.2.checked_sub(s2.2)? != entry {
        return None;
    }
    Some((deltas, lane, entry))
}

/// How a run treats a branch whose condition it does not know.
enum Unknown<B> {
    /// The branch leaves the region for `B` and not taking it stays: a data
    /// exit, not taken.
    Stay(B),
    /// Not taking it leaves the region for `B` and taking it stays: a data
    /// exit, not taken.
    Take(B),
    /// Both sides stay (or both leave): explore both.
    Both,
}

fn unknown_branch<B: Copy + Eq + Hash>(
    region: &Region<B>,
    list: &[TripEffect<B>],
    pos: usize,
    block: B,
    target: B,
) -> Unknown<B> {
    let leaves = |b: B| !region.blocks.contains(&b) || b == region.entry;
    // Where control goes when the branch is not taken, if the rest of the
    // block decides it without another effect: a jump, or the fall-through.
    let not_taken = match list.get(pos) {
        Some(TripEffect::Jump(next)) => Some(*next),
        None => region.fall.get(&block).copied(),
        _ => None,
    };
    match (leaves(target), not_taken.filter(|&next| leaves(next))) {
        (true, None) => Unknown::Stay(target),
        (false, Some(exit)) => Unknown::Take(exit),
        _ => Unknown::Both,
    }
}

#[cfg(test)]
mod tests;
