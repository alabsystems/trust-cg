// trust-cg-opt - Scalar ILP unroll (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Scalar ILP unroll (`scalar-unroll`)
//!
//! A LATE machine pass for the load-bearing reduction loops that neither the
//! NEON vectorizers nor `reduction_split` can take, in two provably disjoint
//! modes:
//!
//! * **SPLIT mode** (integer multi-accumulator, the `reduction_split` transform
//!   for loops whose term LOADS memory): a latency-bound associative integer
//!   reduction `acc = acc <op> TERM(a[i], ...)`, `op ∈ {+, *, |, ^}`, is
//!   unrolled 4-wide with **4 independent accumulators** — one per residue
//!   class — breaking the loop-carried dependency chain so the CPU can keep 4
//!   `<op>`s in flight (`prod_i64`: the i64 multiply chain; table-xor: the CRC
//!   folding loop).
//!
//! * **SERIAL mode** (order-preserving unroll): a loop whose accumulator update
//!   is NOT reassociable — a float chain (`s += a[i]` on f32/f64) or a compound
//!   integer recurrence (`h = (h ^ b[i]) * P`, `c = tbl[(c^b[i])&255] ^ (c>>8)`)
//!   — is unrolled 4-wide with **one accumulator and the exact original
//!   operation order**: the unrolled body is four verbatim copies of the scalar
//!   body (iteration `i`, then `i+1`, `i+2`, `i+3`), so it computes
//!   **bit-identically** to four scalar iterations. The win is amortized loop
//!   overhead (1 compare + 1 branch + 1 induction update per 4 iterations) and
//!   4 independent, batchable address streams for the OoO core.
//!
//! Both modes are **purely additive** exactly like the NEON vectorizers: a
//! guarded 4-wide main loop is inserted IN FRONT of the scalar loop, which is
//! never edited and serves as the `< 4`-iteration tail (and as the whole loop
//! when the guard rejects). The scalar loop therefore stays correct by
//! construction; only the inserted main loop needs justifying.
//!
//! ## Why SPLIT mode is sound (the `reduction_split` regrouping argument)
//!
//! The scalar loop computes the left fold
//! `acc_init <op> T(i0) <op> T(i0+1) <op> ... <op> T(n-1)`. Two's-complement
//! integer **add and multiply are associative AND commutative** over `Z/2^w`,
//! as are bitwise **or** and **xor**, so ANY regrouping/reordering of the
//! `T(i)` terms yields a bit-for-bit identical result. Distributing the terms
//! across 4 accumulators by residue class (`acc_k` folds `T(i0+k), T(i0+k+4),
//! ...` starting from `identity`; `acc_0` starts from the live `acc` so the
//! initial value is preserved) and combining `(acc0 op acc1) op (acc2 op acc3)`
//! on exit is exactly such a regrouping — the identity proven once for all
//! inputs in `trust-cg-verify/src/reduction_split_proofs.rs` (this pass emits
//! the same shape with the same ops; float add/mul are NOT associative and are
//! never split — they take SERIAL mode). `AndRR` is excluded (all-ones identity
//! materialization out of scope), matching `reduction_split`.
//!
//! **Loads.** Unlike `reduction_split` (which BAILS on any load), the term may
//! read memory. This is sound for the same reason as `neon_array`: the loop
//! body contains **no store / call / atomic** (whitelist), so memory is
//! invariant across the loop and loads commute freely with each other; and the
//! entry guard admits the 4-wide body only when all four indices `iv..iv+3`
//! are `< n`, i.e. iterations the scalar loop itself would execute — so every
//! load the main loop performs (including data-dependent GATHER loads
//! `tbl[b[i]]`, whose addresses are pure functions of that lane's own loads)
//! is a load the original loop performs, at the same address, reading the same
//! value.
//!
//! SERIAL mode also generalizes from ONE accumulator to a `k`-variable
//! recurrence (`k ∈ 1..=MAX_ACCS` carried accumulators besides the induction):
//! iterative fib `a,b = b,a+b` (`k=2`), a tribonacci `a,b,c = b,c,a+b+c`
//! (`k=3`), and similar linear/compound recurrences clang's generic unroller
//! handles by renaming. These are loadless dependency chains no vectorizer or
//! `reduction_split` recognizes; unrolling amortizes the loop overhead and lets
//! the renamed carried-var copies vanish, exactly as clang does.
//!
//! ## Why SERIAL mode is sound (bit-identity by construction)
//!
//! The 4-wide body executes the EXACT instruction sequence of four consecutive
//! scalar iterations: lane `k` is the original body with `iv` renamed to `iv+k`
//! and every carried accumulator renamed to its value entering that lane (lane
//! 0 reads the live carried regs; lane `k` reads lane `k-1`'s freshly computed
//! next values). No operation is added, dropped, reordered across a lane
//! boundary, or reassociated — in particular every FP operation runs in the
//! original order with the original operands, so the result is **bit-identical**
//! (the differential harness enforces this). The guard (below) admits the body
//! only when all four iterations would run.
//!
//! SERIAL mode (only) also admits a STORE in the body to a loop-INVARIANT
//! address (the redundant `store *result` clang -O1 leaves in `*result +=
//! a[row][i]*b[i][column]`, FloatMM's inner product) — but NEVER one whose
//! stored VALUE is the induction variable, which fails closed (a store is the
//! only body instruction with a use at operand 0, and `apply`'s per-lane index
//! materialization reads uses from operand 1 onward). Verbatim replication is
//! bit-identical for a store exactly as for a compute op: each lane emits the
//! store in program order after its own compute, so the unrolled block is the
//! literal instruction stream of `k` consecutive scalar iterations — whatever
//! the later scheduler soundly does to the scalar loop, it does here. (SPLIT
//! mode, which reorders the term across accumulators, NEVER admits a store.)
//!
//! The `k`-var writebacks are advanced SIMULTANEOUSLY (all carried vars' next
//! values are read from one pre-update rename map, then assigned together),
//! which the scalar loop's SEQUENTIAL latch writebacks match **because every
//! carried var's next value is required to be a fresh body def** — a vreg
//! distinct from every carried dest, so no writeback can observe another's new
//! value (the `a = b; b = a` swap hazard is structurally excluded). Real
//! recurrences always satisfy this: the frontend breaks the parallel
//! shift-copies with temps, so each next value is a freshly computed temp.
//!
//! ## Bounds guards (identical to `neon_array`'s, with WIDTH = 4)
//!
//! * `Gpr32` induction: the preheader computes `main_bound = sxtw(n) - 3` in
//!   i64 (exact — both operands are in i32 range, so no wrap), and the main
//!   header tests `sxtw(iv) < main_bound`, i.e. `sxtw(iv) + 3 < sxtw(n)`: all
//!   four lane indices are `< n`, and `iv + k` cannot wrap i32.
//! * `Gpr64` induction: no sign-extension headroom exists, so a dedicated
//!   precheck runs once: `if n <s 4 skip` (covers `n <= 0` and negative-as-
//!   signed `n`); otherwise `main_bound = n - 3` is exact in `[1, 2^63-4]`,
//!   and the main header loops while `iv <u main_bound` (unsigned; both sides
//!   non-negative `< 2^63`, so it agrees with signed) — hence `iv+3 < n`
//!   wrap-free. On exit `iv <= n`, so the scalar tail sees a valid state.
//!   This is `neon_array::apply_i64`'s guard verbatim (see its module docs for
//!   the full argument), with 4 instead of 8.
//!
//! In both cases the redirect target after the main loop is the loop's
//! original entry test (the rotated guard block, or the top-tested header),
//! which re-tests `iv < n` — 0..3 remaining iterations run in the untouched
//! scalar loop.
//!
//! ## Fail-closed doctrine (BAIL preconditions)
//!
//! This pass runs on all code; anything not EXACTLY matching the recognized
//! shape is left untouched:
//!
//! * a 2-block `{header, latch}` loop in one of the two late canonical forms —
//!   ROTATED (`loop-latch-layout`'s guard + bottom-test) or TOP-TESTED — with
//!   the exact 3-inst test block `[CmpRR(iv, n); BCond(LT, ..); B(exit)]`
//!   (signed `<` counted loops only) and a single-pred preheader edge;
//! * every loop instruction on the whitelist (no call / atomic / division /
//!   flag-consumer beyond the loop test — and no `Csel`, whose flag dependency
//!   the cloner does not model). Immediate- AND register-offset loads are
//!   admitted (`AddrModeFormation` runs before this pass and folds an array
//!   index into a `LdrRO`); float↔int converts (`Scvtf`/`Ucvtf`) and `Fneg`
//!   are admitted (the flops polynomial kernels); a STORE is admitted only in
//!   SERIAL mode and only to a loop-invariant address (see above);
//! * `1 + k` loop-carried vars (copy-like writebacks in the latch): a `+1`
//!   induction plus `k ∈ 1..=MAX_ACCS` accumulators. Each carried var's next
//!   value MUST be a fresh body def (`>MAX_ACCS` accumulators, or a next value
//!   that is another carried var / the induction chain, BAILS);
//! * a closed-world body: every non-store body instruction defines a fresh
//!   vreg, reading only `{iv, carried accs, earlier body defs, loop
//!   invariants}`; a store reads those and has a loop-invariant address;
//! * a bounded body (`<= MAX_BODY` compute insts, or `<= MAX_BODY_FP` for a
//!   single-FP-accumulator reduction; `<= MAX_LOADS` loads). A single-INTEGER-
//!   accumulator loop must have at least one load (loadless integer single-acc
//!   reductions belong to `reduction_split` / `neon_reduce`); a single-FP
//!   accumulator (non-reassociable, no vector path) and a MULTI-var recurrence
//!   are admitted loadless;
//! * the loop bound is a live-in, OR a constant trust-cg rematerializes in-loop
//!   by a `Movz`/`Movn`/`Movk` chain (a large bound it did not hoist, e.g. the
//!   flops `m-1`); the chain is replicated to a fresh register in the guard;
//! * SPLIT mode requires exactly ONE accumulator, read exactly once, by an
//!   `{AddRR, MulRR, OrrRR, EorRR}` root, **and** a shape no vectorizer can
//!   take: an i64 multiply root (no NEON `MUL.2D` exists) or a data-dependent
//!   GATHER load in the term (NEON has no gathers). Affine single-op integer
//!   reductions (`s += a[i]`, i32 products, min/max, ...) are the NEON
//!   vectorizers' property and always BAIL here — placement after the
//!   vectorizers plus this shape gate means this pass can never steal a
//!   vectorizable loop, even at the O3 fixpoint;
//! * SERIAL mode fires on everything else non-reassociable: a single FPR/compound
//!   integer chain, or a `k`-var recurrence (`k >= 2`) — shapes every
//!   vectorizer and `reduction_split` reject by construction.
//!
//! ## Idempotence
//!
//! The inserted main loop is a 3-block loop (`{header, body, latch}`), so the
//! 2-block recognizer can never re-match it; the original loop's entry block
//! gains a second predecessor (guard-skip + main-loop exit), which the
//! single-pred entry check rejects — the same mechanism that keeps the NEON
//! passes off their own scalar tails. The transform is a fixpoint.
//!
//! Runs AFTER the NEON vectorizers and `reduction_split` (placement is part of
//! the ownership argument, like `ext-addr`) and BEFORE `ext-addr` /
//! `select-fuse` / the scheduler, so each unrolled lane's `Sxtw`/`Madd`/`LdrRI`
//! address chain is folded into one extended-register load by the very next
//! pass. Kill switch: `TRUST_CG_DISABLE_PASSES=scalar_unroll`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

use crate::dom::DomTree;
use crate::effects::{
    aarch64_for_each_def_position, aarch64_for_each_use_position, for_each_inst_def,
    inst_defines_vreg,
};
use crate::loops::LoopAnalysis;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Unroll factor: scalar iterations per main-loop iteration (and accumulator
/// count in SPLIT mode). The same 4-way ILP factor as `reduction_split` and
/// the NEON vectorizers' accumulator unroll.
const UNROLL: i64 = 4;
/// Max compute instructions in the loop body (register-pressure bound: SPLIT
/// mode materializes up to `UNROLL` copies of the body's live ranges; the
/// per-lane temporaries die at each lane's reduction root, so the concurrent
/// live set stays far below `UNROLL * MAX_BODY`). 10 admits the serial CRC
/// recurrence (9 body insts).
const MAX_BODY: usize = 10;
/// Larger body bound for a SINGLE FP-accumulator SERIAL reduction (`s +=
/// TERM(i)` with a long straight-line polynomial term, e.g. the flops
/// numerical-integration kernels). Such a term is a chain of `Fmul`/`Fmadd`
/// on short-lived temporaries that die at each step, so even unrolled `UNROLL`
/// wide the concurrent live set stays within the 32-register FP budget (clang
/// -O3 unrolls these same kernels 4-wide). Only SERIAL single-FP reductions
/// are admitted at this size; SPLIT / `k`-var recurrences keep `MAX_BODY`.
const MAX_BODY_FP: usize = 40;
/// Max loads in the loop body.
const MAX_LOADS: usize = 4;
/// Max loop-carried accumulators BEYOND the induction variable. SERIAL mode
/// generalizes to a `k`-var linear/compound recurrence (iterative fib has 2:
/// `a,b = b,a+b`; a tribonacci has 3): each of the `k` carried vars is threaded
/// through `UNROLL` verbatim lane copies via fresh vregs. Bounded to keep the
/// unrolled body's concurrent live set (≈ `k` carried values + per-lane temps)
/// within the register budget; `k > MAX_ACCS` BAILS.
const MAX_ACCS: usize = 4;
/// AArch64 condition-code encodings.
const CC_LT: i64 = 11; // signed <
const CC_LO: i64 = 3; // unsigned <
const CC_EQ: i64 = 0; // equal (clang-rotated header exit: leave when iv+1 == n)
const CC_GE: i64 = 10; // signed >= (clang-rotated header exit: leave when iv+1 >= n)

/// FULL-UNROLL bounds. When a SERIAL clang-rotated reduction has a COMPILE-TIME
/// constant trip in `[MIN_FULL, MAX_FULL]` AND every memory address is a proven
/// affine function of the induction variable with a constant coefficient, the
/// loop is fully unrolled straight-line: each copy's induction is a known
/// constant, so the per-lane index arithmetic (`mul iv,#s`; `madd iv,#s,base`)
/// FOLDS into a base+immediate `LdrRI [base, #imm]` — the invariant base is
/// hoisted ONCE and the iv-dependent part becomes a load immediate, exactly what
/// clang -O3 emits for the constant-trip inner product (Stanford/FloatMM).
/// Above `MAX_FULL` the loop keeps the 4-wide SERIAL unroll (e.g. the flops
/// kernels, trip in the millions). `MIN_FULL` keeps tiny loops on the 4-wide
/// path (full-unroll leaves ONE tail iteration in the untouched header, so it
/// only pays for itself once there are several folded copies).
const MIN_FULL: i64 = 4;
const MAX_FULL: i64 = 64;

/// The `scalar-unroll` machine pass.
#[derive(Default)]
pub struct ScalarUnrollPass {
    /// Number of loops unrolled in the last run (diagnostics/tests).
    fired: usize,
}

impl ScalarUnrollPass {
    pub fn new() -> Self {
        Self { fired: 0 }
    }

    /// Loops unrolled in the last `run`.
    pub fn fired(&self) -> usize {
        self.fired
    }
}

impl MachinePass for ScalarUnrollPass {
    fn name(&self) -> &str {
        "scalar-unroll"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        self.run_core(func, &loops)
    }

    // Share the AnalysisCache's CFG-derived LoopAnalysis instead of recomputing
    // it per pass (see NeonArrayPass). This recognizer needs only the loop
    // analysis (not the dominator tree). Sound + byte-identical: LoopAnalysis
    // depends only on the CFG, which the cache invalidates on any CFG change.
    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loops = analyses.loop_analysis(func).clone();
        let changed = self.run_core(func, &loops);
        // Invalidate the shared analyses on a FIRE (CFG mutated) so no downstream
        // pass reads a stale loop tree; zero cost in the no-fire hot path. See
        // NeonArrayPass::run_with_analyses.
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

impl ScalarUnrollPass {
    fn run_core(&mut self, func: &mut MachFunction, loops: &LoopAnalysis) -> bool {
        self.fired = 0;

        // Normalize constant-immediate trip guards back to the `CmpRR(iv, movz)`
        // shape the recognizer keys on (ISel's `CmpRI` fold otherwise silently
        // defeats full-unroll of the constant-trip serial reductions — the
        // matmul k-loop). Semantics-preserving; fail-closed. See the function.
        normalize_const_trip_guards(func, loops);

        // Recognize read-only first; applying a plan only ADDS blocks (never
        // renumbers existing block/inst ids or edits other loops' blocks), so
        // recognized data for other loops stays valid (neon_array's pattern).
        let mut plans = Vec::new();
        for lp in loops.all_loops() {
            if let Some(plan) = Plan::recognize(func, lp.header, lp.latch, &lp.body) {
                plans.push(plan);
            }
        }

        let dump = std::env::var("TRUST_CG_DUMP_SCALARUNROLL").is_ok();
        let mut changed = false;
        for plan in plans {
            if dump {
                let mode = match plan.mode {
                    Mode::Split { op, identity } => format!("split(op={op:?},id={identity})"),
                    Mode::Serial => "serial".to_string(),
                };
                let accs: Vec<VReg> = plan.accs.iter().map(|(a, _)| *a).collect();
                let full = match &plan.full_unroll {
                    Some(fu) => format!(
                        "FULL(trip={},init={},folds={})",
                        fu.trip,
                        fu.init,
                        fu.folds.len()
                    ),
                    None => "4-wide".to_string(),
                };
                eprintln!(
                    "[scalar-unroll] FIRE fn={} entry={:?} mode={} {} iv={:?} accs={:?}",
                    func.name, plan.entry, mode, full, plan.iv, accs
                );
            }
            apply(func, &plan);
            self.fired += 1;
            changed = true;
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// How the accumulator is advanced — selects the rewrite.
#[derive(Clone, Copy)]
enum Mode {
    /// `acc = op(acc, term)` with an associative+commutative integer `op`,
    /// term reads memory, and no vector path exists for the shape: unroll with
    /// `UNROLL` independent accumulators (identity-seeded) + balanced combine.
    Split { op: AArch64Opcode, identity: i64 },
    /// Non-reassociable chain: unroll 4x preserving the exact operation order
    /// with the single original accumulator.
    Serial,
}

/// A fully validated, unrollable reduction loop.
struct Plan {
    /// The loop's entry-test block (ROTATED: the guard; TOP-TESTED: the
    /// header). The preheader edge into it is redirected through the new main
    /// loop, and the main loop exits back into it (it re-tests `iv < n`).
    entry: BlockId,
    /// Single block branching into `entry` from outside the loop.
    preheader: BlockId,
    /// The `preheader` terminator targeting `entry`.
    preheader_term: InstId,
    /// Loop-carried `+1` induction register (`Gpr32` or `Gpr64`).
    iv: VReg,
    /// Loop-carried accumulators, each paired with the register holding its
    /// next value (the writeback source): a body def (`b = a+b`) or another
    /// carried var (`a = b`). SPLIT mode has exactly one; SERIAL mode has
    /// `1..=MAX_ACCS` — the `k` vars of a `k`-var recurrence.
    accs: Vec<(VReg, VReg)>,
    /// Loop bound register (`iv <s bound` counted loop). Normally defined
    /// OUTSIDE the loop; but a large constant bound trust-cg rematerializes
    /// in-loop is admitted via `bound_chain` (below).
    bound: VReg,
    /// If non-empty, `bound` is a CONSTANT rematerialized in-loop by this
    /// `Movz`/`Movn`/`Movk` chain (a loop bound trust-cg did not hoist).
    /// `apply` replicates the chain to a fresh register in the guard so the
    /// bounds test has a value available before the loop; bit-exact by
    /// replication, no value reconstruction. Empty ⇒ `bound` is a live-in.
    bound_chain: Vec<InstId>,
    /// Body compute instructions in execution order (no control, no
    /// writebacks, no induction increment).
    body: Vec<InstId>,
    mode: Mode,
    /// CLANG-ROTATED shape: `entry` is the loop HEADER itself, which runs the
    /// body UNCONDITIONALLY (the exit test lives at its END). Re-entering the
    /// header after the main loop is only safe when at least one tail iteration
    /// remains, so `apply` uses a tighter bounds guard (`main_bound = n - UNROLL`,
    /// precheck `n < UNROLL+1`) that leaves 1..=UNROLL tail iterations for the
    /// scalar loop. For the NATIVE/TOP-TESTED shapes (`entry` is a re-test
    /// guard/header that tolerates `iv == n`) this is `false` and the original
    /// looser guard (`main_bound = n - (UNROLL-1)`) is used.
    header_reentry: bool,
    /// When `Some`, the loop is a COMPILE-TIME constant-trip SERIAL reduction
    /// whose addresses fold to base+immediate loads: it is FULLY unrolled
    /// straight-line by `apply_full_unroll` (all but one iteration), instead of
    /// the 4-wide guarded `apply`. `None` ⇒ the ordinary 4-wide path runs.
    full_unroll: Option<FullUnroll>,
}

/// A single load whose address is a proven affine function of the induction
/// variable. Two source forms fold into this one model:
///
/// * register-offset `Ldr{,b,h}RO [ptr, offset]` — `address = ptr + offset`,
///   `offset = coeff*iv + REST` (`base = Some(ptr)`, `imm0 = 0`);
/// * immediate-offset `Ldr{,b,h}RI [addr, #imm0]` whose *whole* address `addr`
///   is itself affine in `iv` — `addr = coeff*iv + REST` (`base = None`). This
///   is the pointer-array shape `Ldr [Madd(iv, #scale, ptr), #imm0]` the matrix
///   inner product carries when `AddrModeFormation` did not split the index back
///   out into a register offset.
///
/// In both, `REST` is a loop-invariant register expression (the address/offset
/// evaluated at `iv==0`). Full-unroll hoists the base once — `base.map(ptr) +
/// REST` — and emits each copy `k` (iv the known constant `c`) as
/// `Ldr{,b,h}RI [base, #imm0 + coeff*c]`.
struct LoadFold {
    /// The original load instruction (`Ldr{,b,h}RO` or `Ldr{,b,h}RI`).
    load: InstId,
    /// The loaded destination register (its class picks the immediate scale).
    dst: VReg,
    /// The invariant base pointer (`Rn`) of a register-offset load, added to
    /// `REST` once to form the hoisted base. `None` for an immediate-offset load
    /// whose entire address is the affine `offset` (nothing extra to add).
    base: Option<VReg>,
    /// The affine register (`address = base + offset` for `RO`; the address
    /// register itself for `RI`); its affine coefficient of `iv` is `coeff`.
    /// Looked up in the slice clone to read `REST = offset@iv=0`.
    offset: VReg,
    /// The load's own immediate offset (`0` for a register-offset load; the
    /// `#imm` operand for an immediate-offset load). Folded into the per-copy
    /// immediate as `imm0 + coeff*(init + k)`.
    imm0: i64,
    /// Compile-time affine coefficient of `iv` in the offset. Per-copy immediate
    /// is `imm0 + coeff * (init + k)`.
    coeff: i64,
    /// Encoding scale (bytes) for the immediate form of this load width.
    scale: i64,
    /// Body instructions computing the offset (backward slice, stopping at
    /// `iv`/constants/invariants). Cloned ONCE with `iv->0` to materialize `REST`.
    slice: Vec<InstId>,
}

/// A validated full-unroll plan (see [`MIN_FULL`]/[`MAX_FULL`]).
struct FullUnroll {
    /// Compile-time trip count `T` (`bound - init`), in `[MIN_FULL, MAX_FULL]`.
    trip: i64,
    /// Compile-time initial value of the induction variable.
    init: i64,
    /// Every loop load, each proven foldable to a base+immediate form.
    folds: Vec<LoadFold>,
    /// Offset-slice instructions NOT emitted per copy (their value is folded
    /// into the load immediate); materialized once via the slice clone.
    skip: HashSet<InstId>,
    /// Whether any non-address body instruction reads `iv` directly (then each
    /// copy materialises `iv` as a constant register before cloning).
    iv_read_by_compute: bool,
}

/// Opcodes permitted anywhere in the loop. PURE compute + the recognized
/// loads + the loop control — anything else (stores, calls, atomics,
/// division, `Csel`/flag consumers, ...) BAILS.
fn allowed_loop_op(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        AddRR
            | AddRI
            | SubRR
            | SubRI
            | MulRR
            | Madd
            | AndRR
            | AndRI
            | OrrRR
            | OrrRI
            | EorRR
            | EorRI
            | LslRI
            | LsrRI
            | AsrRI
            | Movz
            | Movn
            | Movk
            | MovR
            | Copy
            | CmpRR
            | BCond
            | B
            | Sxtw
            | Uxtb
            | Sxtb
            | Uxth
            | Sxth
            | LdrRI
            | LdrbRI
            | LdrhRI
            | LdrRO
            | LdrbRO
            | LdrhRO
            | StrRI
            | StrbRI
            | StrhRI
            | StrRO
            | FaddRR
            | FsubRR
            | FmulRR
            | FmaddRR
            | FnegRR
            | ScvtfRR
            | UcvtfRR
            | FmovFprFpr
    )
}

/// Loads (immediate- or register-offset). `AddrModeFormation` runs BEFORE this
/// pass and folds an array index into a register-offset load, so the recognized
/// reduction loops carry `LdrRO`, not the raw `Sxtw/Madd/LdrRI` chain.
fn is_load(op: AArch64Opcode) -> bool {
    matches!(
        op,
        AArch64Opcode::LdrRI
            | AArch64Opcode::LdrbRI
            | AArch64Opcode::LdrhRI
            | AArch64Opcode::LdrRO
            | AArch64Opcode::LdrbRO
            | AArch64Opcode::LdrhRO
    )
}

/// Stores (immediate- or register-offset) permitted ONLY in SERIAL mode
/// (order-preserving verbatim replication). A store defines no vreg: operand 0
/// is the stored VALUE (a use), the remaining operands form the address. NEVER
/// permitted in SPLIT mode, which reorders the term across accumulators.
fn is_store(op: AArch64Opcode) -> bool {
    matches!(
        op,
        AArch64Opcode::StrRI | AArch64Opcode::StrbRI | AArch64Opcode::StrhRI | AArch64Opcode::StrRO
    )
}

fn vreg_of(op: &MachOperand) -> Option<VReg> {
    match op {
        MachOperand::VReg(v) => Some(*v),
        _ => None,
    }
}

fn imm_of(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::Imm(v) => Some(*v),
        _ => None,
    }
}

/// Copy idioms used for loop-carried writebacks: `MovR`/`Copy`/`FmovFprFpr`
/// (FP accumulators) and `AddRI(d, s, #0)`.
fn copy_like(inst: &MachInst) -> Option<(VReg, VReg)> {
    match inst.opcode {
        AArch64Opcode::MovR | AArch64Opcode::Copy | AArch64Opcode::FmovFprFpr
            if inst.operands.len() == 2 =>
        {
            Some((vreg_of(&inst.operands[0])?, vreg_of(&inst.operands[1])?))
        }
        AArch64Opcode::AddRI
            if inst.operands.len() == 3 && imm_of(&inst.operands[2]) == Some(0) =>
        {
            Some((vreg_of(&inst.operands[0])?, vreg_of(&inst.operands[1])?))
        }
        _ => None,
    }
}

/// Associative+commutative integer roots SPLIT mode may take, with the
/// identity each extra accumulator is seeded with (`reduction_split`'s family;
/// `AndRR` excluded — all-ones identity materialization out of scope).
fn assoc_int_identity(op: AArch64Opcode) -> Option<i64> {
    match op {
        AArch64Opcode::AddRR | AArch64Opcode::OrrRR | AArch64Opcode::EorRR => Some(0),
        AArch64Opcode::MulRR => Some(1),
        _ => None,
    }
}

/// The exact 3-instruction entry/exit test `[CmpRR(iv, bound); BCond(LT, t);
/// B(_)]` ⇒ `(iv, bound, t)`.
fn test_block_shape(func: &MachFunction, b: BlockId) -> Option<(VReg, VReg, BlockId)> {
    let insts = &func.block(b).insts;
    if insts.len() != 3 {
        return None;
    }
    let cmp = func.inst(insts[0]);
    let bcond = func.inst(insts[1]);
    let br = func.inst(insts[2]);
    if cmp.opcode != AArch64Opcode::CmpRR
        || bcond.opcode != AArch64Opcode::BCond
        || br.opcode != AArch64Opcode::B
    {
        return None;
    }
    if imm_of(&bcond.operands[0]) != Some(CC_LT) {
        return None; // signed `<` counted loops only
    }
    let iv = vreg_of(&cmp.operands[0])?;
    let bound = vreg_of(&cmp.operands[1])?;
    let target = match bcond.operands.get(1)? {
        MachOperand::Block(t) => *t,
        _ => return None,
    };
    Some((iv, bound, target))
}

/// CLANG-ROTATED (importer -O1, folded at O2): recognize the rotated loop whose
/// exit test lives at the END of the HEADER as
/// ```text
///   CmpRR(iv+1, bound)          ; the increment vs the bound
///   BCond(EQ|GE) -> <exit>      ; leave iff iv+1 reaches bound
///   B -> <latch>                ; else fall through to the writeback latch
/// ```
/// and whose LATCH is PURE loop-carried writebacks (`copy_like`, `d != s`)
/// followed by a single `B -> header`. Returns `(iv, bound)`.
///
/// This is the exact shape `neon_array::recognize_rotated_header_exit` accepts
/// for its (reassociation-sound) integer reductions, plus the latch-purity and
/// header-terminator checks. Because iv starts at 0 and steps +1, `iv+1` reaches
/// `bound` EXACTLY, so "leave when iv+1 (>)= bound" is the counted trip
/// `[0, bound)`. The un-reassociable FP chains (`s += a[i]*b[i]`, the `FmaddRR`
/// dot product) that hit this shape are the SERIAL-mode target: no vectorizer or
/// `reduction_split` can take them, and the header re-entry (with the tighter
/// guard in `apply`) preserves the exact scalar operation order — bit-identical.
///
/// Fail-closed: ANY deviation (other CC, non-adjacent compare, compared value
/// not the increment, exit target inside the loop, an effectful latch inst, a
/// header not falling through to the latch) returns `None`.
fn detect_clang_rotated(
    func: &MachFunction,
    header: BlockId,
    latch: BlockId,
    body: &HashSet<BlockId>,
) -> Option<(VReg, VReg)> {
    // -- Latch: exactly the loop-carried writebacks + ONE `B -> header`. The
    // sole non-`copy_like` inst must be that terminator branch (no store / cmp /
    // compute), and it must be the LAST inst (writebacks precede it).
    let linsts = func.block(latch).insts.clone();
    let non_copy: Vec<InstId> = linsts
        .iter()
        .copied()
        .filter(|&id| copy_like(func.inst(id)).is_none())
        .collect();
    if non_copy.len() != 1 || func.inst(non_copy[0]).opcode != AArch64Opcode::B {
        return None;
    }
    if *linsts.last()? != non_copy[0] {
        return None;
    }
    if !matches!(func.inst(non_copy[0]).operands.first(), Some(MachOperand::Block(t)) if *t == header)
    {
        return None;
    }
    if func.block(latch).succs != vec![header] {
        return None;
    }

    // -- Header exit test at its END: find the conditional branch LEAVING the
    // loop; it must be `BCond(EQ|GE) -> <exit outside body>`, with the header's
    // last inst an unconditional `B -> latch` (the fall-through continuation).
    let hinsts = &func.block(header).insts;
    let p = hinsts.iter().position(|&id| {
        let i = func.inst(id);
        i.opcode == AArch64Opcode::BCond && branch_targets(i).iter().any(|t| !body.contains(t))
    })?;
    if p < 1 {
        return None;
    }
    let bcond = func.inst(hinsts[p]);
    let cc = imm_of(&bcond.operands[0])?;
    if cc != CC_EQ && cc != CC_GE {
        return None;
    }
    match bcond.operands.get(1) {
        Some(MachOperand::Block(t)) if !body.contains(t) => {}
        _ => return None,
    }
    let last = func.inst(*hinsts.last()?);
    if last.opcode != AArch64Opcode::B
        || !matches!(last.operands.first(), Some(MachOperand::Block(t)) if *t == latch)
    {
        return None;
    }

    // -- Flag producer: the `CmpRR(iv+1, bound)` IMMEDIATELY before the BCond
    // (no intervening flag clobber). The compared value is the STEP `iv+1`, so
    // `iv` is the latch writeback whose SOURCE is that value.
    let cmp = func.inst(hinsts[p - 1]);
    if cmp.opcode != AArch64Opcode::CmpRR {
        return None;
    }
    let iv_src = vreg_of(&cmp.operands[0])?;
    let bound = vreg_of(&cmp.operands[1])?;
    let iv = linsts
        .iter()
        .filter_map(|&id| copy_like(func.inst(id)))
        .find(|(_, s)| *s == iv_src)
        .map(|(d, _)| d)?;
    Some((iv, bound))
}

/// ISel (`dc5916e`, `select_cmp`) folds a constant loop-trip compare
/// `icmp <cc> iv, C` (with `C ∈ [0, 4095]`) directly into `CmpRI iv, #C`, which
/// removes the materialized `Movz`-bound + `CmpRR` shape that
/// [`detect_clang_rotated`] keys on. That silently DEFEATS the full-unroll of
/// the importer's constant-trip SERIAL reductions — most visibly the matmul
/// inner product (`icmp eq i64 %k, 10`), whose rolled k-loop is a ~2x
/// regression versus the fully-unrolled (folded `LdrRI`) form. This locates a
/// header trip-guard `CmpRI(iv, #imm)` in the exact clang-rotated shape and,
/// when the immediate is an unroll-eligible constant with a clean unique
/// preheader, [`normalize_const_trip_guards`] rewrites it back to
/// `CmpRR(iv, movz)` with the `Movz` HOISTED into the preheader — a
/// loop-invariant live-in, so no per-iteration cost, exactly the pre-fold shape
/// `clang -O1` produced. The rewrite is semantics-preserving: `CmpRI Rn, #imm`
/// is bit-for-bit `CmpRR Rn, Rm` with `Rm` holding `#imm` (ISel's own fold
/// invariant, `cmp_imm12_fold`), and `Movz` of an `imm ∈ [MIN_FULL, MAX_FULL]`
/// materializes exactly that value.
///
/// Returns `(cmp_inst, imm, iv_class, preheader_terminator)`. Fail-closed on any
/// deviation (non-`CmpRI` guard, out-of-window immediate, non-GPR induction, no
/// unique preheader, preheader not ending in an unconditional branch to the
/// header) — the guard keeps its `CmpRI` (and any `#0`/CBZ fusions) untouched.
fn find_const_trip_cmpri_guard(
    func: &MachFunction,
    header: BlockId,
    body: &HashSet<BlockId>,
    preheader: BlockId,
) -> Option<(InstId, i64, RegClass, InstId)> {
    let hinsts = &func.block(header).insts;
    // The header's loop-leaving conditional branch (a target outside the body).
    let p = hinsts.iter().position(|&id| {
        let i = func.inst(id);
        i.opcode == AArch64Opcode::BCond && branch_targets(i).iter().any(|t| !body.contains(t))
    })?;
    if p < 1 {
        return None;
    }
    // Its flag producer must be an immediate compare against a constant trip.
    // The window is `[MIN_FULL, 0xFFF]`: the ceiling is the `CmpRI` imm12 range
    // (so it covers EVERY constant `select_cmp` could have folded — both the
    // full-unroll band `<= MAX_FULL` and the larger 4-wide-serial band, each of
    // which the fold would otherwise strand rolled); the floor keeps `#0` (the
    // CBZ case) and sub-unroll trips on their `CmpRI` (nothing to gain, and the
    // CBZ/immediate benefit is preserved).
    let cmp_id = hinsts[p - 1];
    let cmp = func.inst(cmp_id);
    if cmp.opcode != AArch64Opcode::CmpRI || cmp.operands.len() != 2 {
        return None;
    }
    let iv_step = vreg_of(&cmp.operands[0])?;
    let imm_val = imm_of(&cmp.operands[1])?;
    if !(MIN_FULL..=0xFFF).contains(&imm_val) {
        return None;
    }
    if !matches!(iv_step.class, RegClass::Gpr32 | RegClass::Gpr64) {
        return None;
    }
    // Insert the hoisted `Movz` at the loop PREHEADER (the header's unique
    // predecessor outside the loop — `LoopAnalysis::preheader`), which dominates
    // the header and is loop-invariant. It may be a plain preheader ending in an
    // unconditional `B` (matrix's reduction, or a constant-trip map's direct
    // entry) OR a rotated entry GUARD (`cmp/bcond/b`); either way the constant is
    // materialized once before the loop. Insert before the preheader's UNIQUE
    // branch into the header.
    if preheader == header || body.contains(&preheader) {
        return None;
    }
    let targeting: Vec<InstId> = func
        .block(preheader)
        .insts
        .iter()
        .copied()
        .filter(|&id| branch_targets(func.inst(id)).contains(&header))
        .collect();
    if targeting.len() != 1 {
        return None;
    }
    Some((cmp_id, imm_val, iv_step.class, targeting[0]))
}

/// Rewrite every recognized constant-trip `CmpRI` header guard back to
/// `CmpRR(iv, movz)` with the `Movz` hoisted into the preheader. See
/// [`find_const_trip_cmpri_guard`] for the shape and soundness argument. Runs
/// BEFORE recognition so the recognizer/`apply` machinery is entirely unchanged;
/// mutating an operand + adding a loop-invariant preheader def preserves the
/// loop tree (no block add/remove, no edge change).
pub(crate) fn normalize_const_trip_guards(func: &mut MachFunction, loops: &LoopAnalysis) -> bool {
    let edits: Vec<(InstId, i64, RegClass, InstId)> = loops
        .all_loops()
        .filter_map(|lp| find_const_trip_cmpri_guard(func, lp.header, &lp.body, lp.preheader?))
        .collect();
    let changed = !edits.is_empty();
    for (cmp_id, imm_val, class, pre_term) in edits {
        let tmp = alloc(func, class);
        emit_before(
            func,
            pre_term,
            AArch64Opcode::Movz,
            vec![vreg(tmp), imm(imm_val)],
        );
        let inst = func.inst_mut(cmp_id);
        inst.opcode = AArch64Opcode::CmpRR;
        inst.operands[1] = vreg(tmp);
    }
    changed
}

/// Standalone early pass: `normalize_const_trip_guards` as its own pipeline
/// pass so EVERY constant-trip recognizer (the NEON vectorizers, the unrollers)
/// sees the `CmpRR(iv, movz)` shape instead of ISel's folded `CmpRI` — otherwise
/// `dc5916e`'s `cmp_imm12_fold` silently defeats them (the matmul full-unroll AND
/// the constant-trip FP maps like `dt`). Semantics-preserving; runs before the
/// vectorization/unroll block.
pub struct ConstTripGuardNormalize;

impl MachinePass for ConstTripGuardNormalize {
    fn name(&self) -> &str {
        "const-trip-guard-normalize"
    }

    fn run(&mut self, _func: &mut MachFunction) -> bool {
        false // needs loop analysis; see run_with_analyses
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loops = analyses.loop_analysis(func).clone();
        let changed = normalize_const_trip_guards(func, &loops);
        if changed {
            analyses.invalidate();
        }
        changed
    }
}

impl Plan {
    fn recognize(
        func: &MachFunction,
        header: BlockId,
        latch: BlockId,
        body: &HashSet<BlockId>,
    ) -> Option<Self> {
        // A 2-block {header, latch} loop (necessarily innermost).
        if header == latch || body.len() != 2 || !body.contains(&header) || !body.contains(&latch) {
            return None;
        }

        // Whitelist every opcode in the loop — no call/atomic/etc.
        for &b in [header, latch].iter() {
            for &id in &func.block(b).insts {
                if !allowed_loop_op(func.inst(id).opcode) {
                    return None;
                }
            }
        }

        // -- Classify the loop form and locate the entry test. --------------
        //
        // ROTATED (`loop-latch-layout` output): guard outside the loop holds
        // the entry test; the latch bottom-tests `[wb, wb, CmpRR, BCond(LT,
        // header)]` with a fallthrough exit; the header is the straight-line
        // body ending in `B latch`.
        //
        // TOP-TESTED: the header IS the 3-inst test `[CmpRR, BCond(LT, latch),
        // B exit]`; the latch is the body + writebacks ending in `B header`.
        //
        // CLANG-ROTATED (importer): the exit test lives at the END of the HEADER
        // (`CmpRR(iv+1, bound); BCond(EQ|GE) -> exit; B -> latch`) and the latch
        // is PURE writebacks + `B -> header`. `entry` is the header itself, so
        // `apply` uses the tighter guard (`header_reentry`) that leaves >= 1 tail
        // iteration — re-entering the unconditional-body header stays in bounds.
        let (entry, rotated, header_reentry, iv, bound) = if let Some((iv, bound, t)) =
            test_block_shape(func, header)
            && t == latch
        {
            // TOP-TESTED. Header preds must be exactly {preheader, latch};
            // the latch's only successor is the header (single back-edge);
            // the exit continuation must be outside the loop.
            let hpreds = &func.block(header).preds;
            if hpreds.len() != 2 || !hpreds.contains(&latch) {
                return None;
            }
            if func.block(latch).succs != vec![header] {
                return None;
            }
            let exit = match func.inst(func.block(header).insts[2]).operands.first() {
                Some(MachOperand::Block(t)) => *t,
                _ => return None,
            };
            if body.contains(&exit) {
                return None;
            }
            (header, false, false, iv, bound)
        } else if let Some((iv, bound)) = detect_clang_rotated(func, header, latch, body) {
            // CLANG-ROTATED: entry is the header (unconditional body); the tighter
            // guard leaves >= 1 tail iteration. The header's single external pred
            // (its preheader) and the writeback/body/mode structure are validated
            // by the generic machinery below (control_tail = 1, like TOP-TESTED).
            (header, false, true, iv, bound)
        } else {
            // ROTATED: latch = [wb, ..., wb, CmpRR, BCond(LT, header)] — the
            // `k+1` carried-var writebacks (iv + `k` accumulators) followed by
            // the bottom test — 2 succs {header, exit}; header body ends `B
            // latch` (only succ); the guard outside repeats the exact same
            // test. The CmpRR/BCond are the LAST two insts (≥ 2 writebacks
            // precede them, so len ≥ 4); their operands and the writeback
            // count are validated below.
            let linsts = func.block(latch).insts.clone();
            if linsts.len() < 4 {
                return None;
            }
            let cmp = func.inst(linsts[linsts.len() - 2]);
            let bcond = func.inst(linsts[linsts.len() - 1]);
            if cmp.opcode != AArch64Opcode::CmpRR || bcond.opcode != AArch64Opcode::BCond {
                return None;
            }
            if imm_of(&bcond.operands[0]) != Some(CC_LT) {
                return None;
            }
            if !matches!(bcond.operands.get(1), Some(MachOperand::Block(t)) if *t == header) {
                return None;
            }
            let iv = vreg_of(&cmp.operands[0])?;
            let bound = vreg_of(&cmp.operands[1])?;
            if func.block(latch).succs.len() != 2 || func.block(header).succs != vec![latch] {
                return None;
            }
            let exit = *func.block(latch).succs.iter().find(|&&s| s != header)?;
            // The guard: the header's unique non-latch predecessor, with the
            // EXACT same test (same iv/bound, LT, into the header) — jumping
            // back into it after the main loop must re-dispatch the tail and
            // nothing else (3 insts, no defs), and its exit continuation must
            // be the SAME block the latch exits to (otherwise handing the
            // "loop done" state to the guard's exit path could diverge from
            // the original, which always leaves a running loop via the latch).
            let hpreds = &func.block(header).preds;
            if hpreds.len() != 2 || !hpreds.contains(&latch) {
                return None;
            }
            let guard = *hpreds.iter().find(|&&b| b != latch)?;
            if body.contains(&guard) || exit == guard || body.contains(&exit) {
                return None;
            }
            let (giv, gbound, gt) = test_block_shape(func, guard)?;
            if giv != iv || gbound != bound || gt != header {
                return None;
            }
            let gexit = match func.inst(func.block(guard).insts[2]).operands.first() {
                Some(MachOperand::Block(t)) => *t,
                _ => return None,
            };
            if gexit != exit {
                return None;
            }
            (guard, true, false, iv, bound)
        };

        // -- Preheader: single pred of the entry block from outside the loop,
        // with exactly ONE branch targeting it (the redirect point).
        let epreds: Vec<BlockId> = func
            .block(entry)
            .preds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if epreds.len() != 1 {
            return None;
        }
        let preheader = epreds[0];
        if preheader == entry || body.contains(&preheader) {
            return None;
        }
        let targeting: Vec<InstId> = func
            .block(preheader)
            .insts
            .iter()
            .copied()
            .filter(|&id| branch_targets(func.inst(id)).contains(&entry))
            .collect();
        if targeting.len() != 1 {
            return None;
        }
        let preheader_term = targeting[0];

        // -- Loop-carried vars: the `+1` induction plus `1..=MAX_ACCS`
        // accumulators — `num_wb ∈ 2..=1+MAX_ACCS` copy-like writebacks that
        // are the MAXIMAL TRAILING RUN of copy-like (`d != s`) insts
        // immediately before the latch's control tail. Collecting the trailing
        // run (rather than every copy-like inst in the latch) keeps shift
        // TEMPS — `t = x` copies the frontend emits earlier in a top-tested
        // latch to break parallel copies, separated from the writebacks by the
        // iv increment or other compute — in the body where they belong. The
        // writebacks being LAST guarantees no body instruction observes a
        // written-back value.
        let wb_insts = func.block(latch).insts.clone();
        let control_tail = if rotated { 2 } else { 1 }; // Cmp+BCond | B
        let n = wb_insts.len();
        if n < 2 + control_tail {
            return None;
        }
        let mut writebacks: Vec<(VReg, VReg, InstId)> = Vec::new();
        let mut idx = n - control_tail;
        while idx > 0 {
            match copy_like(func.inst(wb_insts[idx - 1])) {
                Some((d, s)) if d != s => {
                    writebacks.push((d, s, wb_insts[idx - 1]));
                    idx -= 1;
                }
                _ => break,
            }
        }
        writebacks.reverse(); // restore latch order
        let num_wb = writebacks.len();
        if !(2..=1 + MAX_ACCS).contains(&num_wb) {
            return None;
        }
        let wb_ids: Vec<InstId> = writebacks.iter().map(|w| w.2).collect();

        // Classify: the `iv` writeback vs. the accumulator writebacks.
        let iv_src = writebacks
            .iter()
            .find(|(d, _, _)| *d == iv)
            .map(|(_, s, _)| *s)?;
        let accs: Vec<(VReg, VReg)> = writebacks
            .iter()
            .filter(|(d, _, _)| *d != iv)
            .map(|(d, s, _)| (*d, *s))
            .collect();
        if accs.len() != num_wb - 1 {
            return None; // `iv` was not written exactly once among the writebacks
        }
        // Carried accumulators must be distinct and alias neither iv nor bound.
        let mut acc_ids: HashSet<u32> = HashSet::new();
        for (a, _) in &accs {
            if *a == iv || *a == bound || !acc_ids.insert(a.id) {
                return None;
            }
        }
        if iv == bound {
            return None;
        }
        if !matches!(iv.class, RegClass::Gpr32 | RegClass::Gpr64) || bound.class != iv.class {
            return None;
        }

        // -- Defs in the loop: every carried var written exactly once (its
        // writeback); every body def fresh (exactly one def, not iv/acc/bound).
        // `header ++ latch` is execution order in BOTH forms (rotated: body
        // block then writeback latch; top-tested: 3-inst test then body).
        let loop_inst_ids: Vec<InstId> = [header, latch]
            .iter()
            .flat_map(|&b| func.block(b).insts.iter().copied())
            .collect();
        let mut def_count: HashMap<u32, usize> = HashMap::new();
        for &id in &loop_inst_ids {
            let inst = func.inst(id);
            for_each_inst_def(inst, |d| {
                *def_count.entry(d.id).or_insert(0) += 1;
            });
        }
        if def_count.get(&iv.id) != Some(&1) {
            return None;
        }
        for (a, _) in &accs {
            if def_count.get(&a.id) != Some(&1) {
                return None;
            }
        }

        // -- Constant loop bound rematerialized IN the loop. A large bound
        // (e.g. the flops `m-1 = 3124999`) that trust-cg does not hoist appears
        // as a `Movz`/`Movn`/`Movk` constant chain writing `bound` in-place each
        // iteration. Such a bound is loop-INVARIANT in value: collect the chain
        // so `apply` can rebuild it in the guard by REPLICATING the same
        // instructions to a fresh register (bit-exact, no value reconstruction),
        // and exclude it from the body. If `bound` is defined in-loop by
        // anything else, it is a genuinely loop-variant bound: bail.
        let bound_chain: Vec<InstId> = if def_count.contains_key(&bound.id) {
            let chain: Vec<InstId> = loop_inst_ids
                .iter()
                .copied()
                .filter(|&id| inst_defines_vreg(func.inst(id), bound))
                .collect();
            let all_const = chain.iter().all(|&id| {
                let i = func.inst(id);
                matches!(
                    i.opcode,
                    AArch64Opcode::Movz | AArch64Opcode::Movn | AArch64Opcode::Movk
                ) && i
                    .operands
                    .iter()
                    .skip(1)
                    .all(|op| matches!(op, MachOperand::Imm(_)))
            });
            if !all_const {
                return None;
            }
            chain
        } else {
            Vec::new()
        };
        let bound_chain_set: HashSet<InstId> = bound_chain.iter().copied().collect();

        // -- Idempotence / own-output defense: the carried vars must have
        // EXACTLY ONE definition outside the loop (their preheader init). Any
        // additive loop transform — this pass's main loop (`iv += 4` in its
        // latch, the accumulator writeback/combine in its body/exit) and every
        // NEON vectorizer's — adds a second outside def, so a transformed
        // loop's scalar tail is structurally rejected here forever, at any
        // O3 fixpoint iteration, independent of what later cleanups do to the
        // main loop's shape.
        let loop_set: HashSet<InstId> = loop_inst_ids.iter().copied().collect();
        let carried_regs: Vec<VReg> = std::iter::once(iv)
            .chain(accs.iter().map(|(a, _)| *a))
            .collect();
        for &carried in &carried_regs {
            let outside_defs = func
                .block_order
                .iter()
                .flat_map(|&b| func.block(b).insts.iter().copied())
                .filter(|&iid| {
                    !loop_set.contains(&iid) && inst_defines_vreg(func.inst(iid), carried)
                })
                .count();
            if outside_defs != 1 {
                return None;
            }
        }

        // -- Body slice: everything but control / writebacks / iv increment,
        // in execution order. (ROTATED executes body_block then wb_block;
        // TOP-TESTED's body and writebacks share one block. Iterating
        // body_block then wb_block is execution order in both.)
        let mut iv_inc: Option<InstId> = None;
        let mut body_insts: Vec<InstId> = Vec::new();
        for &id in &loop_inst_ids {
            let inst = func.inst(id);
            if matches!(
                inst.opcode,
                AArch64Opcode::CmpRR | AArch64Opcode::BCond | AArch64Opcode::B
            ) || wb_ids.contains(&id)
                || bound_chain_set.contains(&id)
            {
                continue;
            }
            // The `+1` induction increment: `iv_src = iv + 1`.
            if inst.operands.first().and_then(vreg_of) == Some(iv_src)
                && is_increment_by_one(func, &loop_inst_ids, inst, iv)
            {
                iv_inc = Some(id);
                continue;
            }
            body_insts.push(id);
        }
        iv_inc?;

        // -- Closed world: each body inst defines a fresh vreg and reads only
        // {iv, acc, earlier body defs, loop invariants}. Track loads and
        // whether any load address depends on another load (a GATHER).
        //
        // A single FP accumulator with a long straight-line polynomial term
        // (the flops numerical-integration kernels: `s += TERM(i)`) is admitted
        // at the larger `MAX_BODY_FP` bound; every other shape keeps `MAX_BODY`.
        let acc_is_fp =
            accs.len() == 1 && matches!(accs[0].0.class, RegClass::Fpr32 | RegClass::Fpr64);
        let max_body = if acc_is_fp { MAX_BODY_FP } else { MAX_BODY };
        if body_insts.is_empty() || body_insts.len() > max_body {
            return None;
        }
        let mut body_defs: HashSet<u32> = HashSet::new();
        let mut load_derived: HashSet<u32> = HashSet::new();
        let mut acc_reads = 0usize;
        let mut n_loads = 0usize;
        let mut has_gather = false;
        let mut has_store = false;
        for &id in &body_insts {
            let inst = func.inst(id);
            if is_store(inst.opcode) {
                // STORE (SERIAL-only): defines nothing — operand 0 is the stored
                // value, 1 the base, 2 the byte offset. Every vreg operand must
                // read {iv, acc, earlier body def, invariant}; the BASE must be
                // loop-INVARIANT (not iv / acc / a body def), so the address is
                // fixed across iterations — the reduction accumulator store
                // `str acc, [result]` (the redundant per-iteration store clang
                // -O1 leaves in `*result += a[i]*b[i]`). iv-indexed scatter
                // stores fail closed (verbatim replication would be sound, but
                // those belong to the memory-MAP vectorizers). Per-lane cloning
                // replicates the exact scalar store sequence — bit-identical —
                // and SPLIT is forbidden below whenever a store is present.
                has_store = true;
                for (idx, op) in inst.operands.iter().enumerate() {
                    if let Some(v) = vreg_of(op) {
                        if idx == 0 {
                            // Stored value: {acc, earlier body def, invariant}.
                            //
                            // The INDUCTION VARIABLE is explicitly NOT admitted
                            // here. A store is the only body instruction whose
                            // operand 0 is a USE, and `apply`'s per-lane index
                            // materialization decides whether the `iv+k` registers
                            // are needed by scanning `operands.iter().skip(1)`
                            // (correct for every def-first instruction, blind to a
                            // store's value operand). A loop whose ONLY read of
                            // `iv` is the stored value would therefore pass
                            // recognition with `body_uses_iv == false`, and all
                            // `UNROLL` lane clones would store the SAME `iv`
                            // instead of `iv, iv+1, ..., iv+UNROLL-1` — wrong code
                            // (the store address is loop-invariant, so the last
                            // lane's value is the observable one, and a non-
                            // `header_reentry` main loop can leave a ZERO-iteration
                            // scalar tail). Fail closed rather than widen the
                            // emitter: `iv`-valued stores are not a shape this pass
                            // needs.
                            if v == iv {
                                return None;
                            }
                            if acc_ids.contains(&v.id) {
                                acc_reads += 1;
                            } else if !body_defs.contains(&v.id) && def_count.contains_key(&v.id) {
                                return None; // value is a non-invariant that is not a body def
                            }
                        } else if def_count.contains_key(&v.id) {
                            // Address operand (base / index): must be loop-invariant
                            // (`def_count` holds every value defined inside the loop —
                            // iv, accumulators, and body defs).
                            return None;
                        }
                    }
                }
                continue;
            }
            let d = simple_body_def(inst)?;
            if def_count.get(&d.id) != Some(&1) || d == iv || acc_ids.contains(&d.id) || d == bound
            {
                return None;
            }
            let mut reads_load = false;
            for op in inst.operands.iter().skip(1) {
                if let Some(v) = vreg_of(op) {
                    if acc_ids.contains(&v.id) {
                        acc_reads += 1;
                    } else if v != iv && !body_defs.contains(&v.id) && def_count.contains_key(&v.id)
                    {
                        return None; // reads a non-invariant that is not an earlier body def
                    }
                    if load_derived.contains(&v.id) {
                        reads_load = true;
                    }
                }
            }
            if is_load(inst.opcode) {
                n_loads += 1;
                if reads_load {
                    has_gather = true;
                }
                load_derived.insert(d.id);
            } else if reads_load {
                load_derived.insert(d.id);
            }
            body_defs.insert(d.id);
        }
        if n_loads > MAX_LOADS {
            return None;
        }
        // A single-accumulator loadless INTEGER reduction belongs to
        // reduction_split / neon_reduce. A single-accumulator loadless FP
        // reduction (`s += poly(i)`, the flops kernels) is non-reassociable and
        // has no vector path, so no other pass takes it — admit it here. A
        // MULTI-var recurrence (iterative fib is loadless: `a,b = b,a+b`) is
        // likewise nobody else's.
        if n_loads == 0 && accs.len() == 1 && !acc_is_fp {
            return None;
        }

        // -- Accumulator next-values: EACH must be a fresh body def, never the
        // induction chain and never another carried var directly. This is the
        // soundness contract for the simultaneous writeback in `apply`:
        //
        // The scalar loop executes its latch writebacks SEQUENTIALLY (`a = sa;
        // b = sb; ...`); `apply` instead reads every source from one pre-update
        // rename map and assigns all carried vars at once. The two agree iff no
        // writeback source is a carried dest overwritten by an EARLIER
        // writeback (else sequential would read the new value, e.g. a direct
        // swap `a = b; b = a`). Requiring every source to be a body def — a
        // FRESH vreg distinct from every carried dest — makes that hazard
        // impossible, so sequential ≡ simultaneous and the unroll is
        // bit-identical by construction. Real recurrences always satisfy this:
        // the frontend breaks the parallel shift-copies of `a,b = b,a+b` with
        // temps (`t = b; ... a = t`), so each carried var's next value is a
        // freshly computed temp, not a live carried reg. (This subsumes the
        // single-accumulator `root` requirement below — its source is the
        // reduction root, always a body def.)
        for (_, src) in &accs {
            if !body_defs.contains(&src.id) {
                return None;
            }
        }

        // -- Mode selection. -------------------------------------------------
        //
        // SINGLE ACCUMULATOR:
        //   SPLIT — a single associative integer root reading `acc` exactly
        //   once, and ONLY when no vector path exists for the shape (i64
        //   multiply root: NEON has no MUL.2D; or a gather in the term: NEON
        //   has no gathers). Affine single-op shapes are vectorizer property:
        //   BAIL.
        //   SERIAL — a non-reassociable chain (FP accumulator or compound
        //   integer update): shapes no vectorizer or reduction_split takes.
        //
        // MULTIPLE ACCUMULATORS (k ∈ 2..=MAX_ACCS): a k-var linear/compound
        // recurrence — always SERIAL (verbatim, order-preserving, bit-identical
        // lane copies; zero reassociation). No vectorizer or reduction_split
        // recognizes a multi-carried-var recurrence, so this pass owns it.
        let mode = if accs.len() == 1 {
            let (acc, acc_src) = accs[0];
            // (The per-acc check above already forced `acc_src` to be a body
            // def: the sole accumulator's source cannot be itself — copy-like
            // writebacks require `d != s` — so it is not in `acc_ids`.)
            let root = *body_insts
                .iter()
                .find(|&&id| func.inst(id).operands.first().and_then(vreg_of) == Some(acc_src))?;
            let root_inst = func.inst(root);
            // A store in the loop forbids SPLIT (which reorders the term across
            // independent accumulators): force the order-preserving SERIAL path.
            let assoc_root = assoc_int_identity(root_inst.opcode)
                .filter(|_| !has_store)
                .and_then(|identity| {
                    if acc_reads != 1 || root_inst.operands.len() != 3 {
                        return None;
                    }
                    let a = vreg_of(&root_inst.operands[1])?;
                    let b = vreg_of(&root_inst.operands[2])?;
                    if a == acc || b == acc {
                        Some((root_inst.opcode, identity))
                    } else {
                        None
                    }
                });
            let is_fp_acc = matches!(acc.class, RegClass::Fpr32 | RegClass::Fpr64);
            match assoc_root {
                Some((op, identity)) => {
                    if is_fp_acc {
                        return None; // unreachable (assoc ops are integer) — fail closed
                    }
                    let no_vector_path =
                        (op == AArch64Opcode::MulRR && acc.class == RegClass::Gpr64) || has_gather;
                    if !no_vector_path {
                        return None; // vectorizer-owned affine shape: never steal
                    }
                    Mode::Split { op, identity }
                }
                None => {
                    if !is_fp_acc && acc_reads == 0 {
                        return None; // acc never read: not a reduction chain
                    }
                    Mode::Serial
                }
            }
        } else {
            // MULTIPLE ACCUMULATORS: always SERIAL. Every carried var's next
            // value is a fresh body def (enforced above), so the recurrence
            // does genuine work each iteration and the simultaneous writeback
            // is bit-identical to the scalar loop's sequential one.
            Mode::Serial
        };

        // FULL-UNROLL opportunity: a compile-time constant-trip SERIAL reduction
        // whose addresses fold to base+immediate loads. `None` (the common case)
        // ⇒ the ordinary 4-wide guarded unroll runs unchanged.
        let full_unroll = try_full_unroll(
            func,
            entry,
            header_reentry,
            iv,
            bound,
            &bound_chain,
            &body_insts,
            mode,
            &loop_set,
            &def_count,
            &acc_ids,
        );

        Some(Plan {
            entry,
            preheader,
            preheader_term,
            iv,
            accs,
            bound,
            bound_chain,
            body: body_insts,
            mode,
            header_reentry,
            full_unroll,
        })
    }
}

// ---------------------------------------------------------------------------
// Full-unroll recognition
// ---------------------------------------------------------------------------

/// The compile-time constant value of `v`, if it is defined by a single
/// `Movz`/`Movn` in the whole function (following `MovR`/`Copy`/`AddRI #0`
/// copy chains). Returns `None` on any ambiguity (multiple defs, non-constant
/// def, `Movk`). Only sound to call on values with a UNIQUE def.
fn const_val_of(func: &MachFunction, v: VReg) -> Option<i64> {
    const_val_rec(func, v, 0)
}

fn const_val_rec(func: &MachFunction, v: VReg, depth: u32) -> Option<i64> {
    if depth > 8 {
        return None;
    }
    let mut found: Option<i64> = None;
    for &b in &func.block_order {
        for &iid in &func.block(b).insts {
            let inst = func.inst(iid);
            if !inst_defines_vreg(inst, v) {
                continue;
            }
            // Second def of `v` ⇒ ambiguous ⇒ not a stable constant.
            if found.is_some() {
                return None;
            }
            found = Some(match inst.opcode {
                AArch64Opcode::Movz => {
                    let (dst, value) = crate::reaching_const::movz_value(inst)?;
                    if dst != v {
                        return None;
                    }
                    i64::try_from(value).ok()?
                }
                AArch64Opcode::MovR | AArch64Opcode::Copy => {
                    let s = vreg_of(&inst.operands[1])?;
                    const_val_rec(func, s, depth + 1)?
                }
                AArch64Opcode::AddRI if imm_of(&inst.operands[2]) == Some(0) => {
                    let s = vreg_of(&inst.operands[1])?;
                    const_val_rec(func, s, depth + 1)?
                }
                _ => return None,
            });
        }
    }
    found
}

/// The compile-time value of a carried variable's SINGLE definition OUTSIDE the
/// loop (its preheader init), if constant. `outside_defs == 1` is already an
/// enforced invariant of the recognizer, so this reads that one init.
fn outside_def_const(
    func: &MachFunction,
    carried: VReg,
    loop_set: &HashSet<InstId>,
) -> Option<i64> {
    let mut result: Option<i64> = None;
    for &b in &func.block_order {
        for &iid in &func.block(b).insts {
            if loop_set.contains(&iid) {
                continue;
            }
            let inst = func.inst(iid);
            if !inst_defines_vreg(inst, carried) {
                continue;
            }
            if result.is_some() {
                return None; // more than one outside def
            }
            result = Some(match inst.opcode {
                AArch64Opcode::Movz => {
                    let (dst, value) = crate::reaching_const::movz_value(inst)?;
                    if dst != carried {
                        return None;
                    }
                    i64::try_from(value).ok()?
                }
                AArch64Opcode::MovR | AArch64Opcode::Copy => {
                    const_val_of(func, vreg_of(&inst.operands[1])?)?
                }
                AArch64Opcode::AddRI if imm_of(&inst.operands[2]) == Some(0) => {
                    const_val_of(func, vreg_of(&inst.operands[1])?)?
                }
                _ => return None,
            });
        }
    }
    result
}

/// Byte scale (encoding stride) of a load's immediate-offset form, from the
/// destination register class. Matches `fp_mem_fields_from_preg_class` and the
/// GPR `sf` path in the encoder.
fn mem_scale_of(op: AArch64Opcode, dst: VReg) -> Option<i64> {
    use AArch64Opcode::*;
    match op {
        LdrbRO | LdrbRI => Some(1),
        LdrhRO | LdrhRI => Some(2),
        LdrRO | LdrRI => Some(match dst.class {
            RegClass::Fpr128 => 16,
            RegClass::Fpr64 | RegClass::Gpr64 => 8,
            RegClass::Fpr32 | RegClass::Gpr32 => 4,
            RegClass::Fpr16 => 2,
            _ => return None,
        }),
        _ => None,
    }
}

/// The immediate-offset opcode for a register-offset load (`Ldr{,b,h}RO ->
/// Ldr{,b,h}RI`).
fn ri_load_opcode(ro: AArch64Opcode) -> Option<AArch64Opcode> {
    Some(match ro {
        AArch64Opcode::LdrRO => AArch64Opcode::LdrRI,
        AArch64Opcode::LdrbRO => AArch64Opcode::LdrbRI,
        AArch64Opcode::LdrhRO => AArch64Opcode::LdrhRI,
        _ => return None,
    })
}

/// The per-copy immediate-offset opcode a fold emits: an `RO` load lowers to its
/// `RI` form; an `RI` load (whole-address affine fold) keeps its own opcode.
fn percopy_ri_opcode(op: AArch64Opcode) -> Option<AArch64Opcode> {
    match op {
        AArch64Opcode::LdrRI | AArch64Opcode::LdrbRI | AArch64Opcode::LdrhRI => Some(op),
        _ => ri_load_opcode(op),
    }
}

/// Whether `imm` encodes as a scaled unsigned (or small unscaled) load/store
/// offset — the `encode_load_store_auto` predicate.
fn imm_encodable(imm: i64, scale: i64) -> bool {
    (imm >= 0 && imm % scale == 0 && (imm / scale) <= 0xFFF) || (-256..=255).contains(&imm)
}

/// The compile-time affine coefficient of `iv` in `v`: `v == coeff*iv +
/// invariant`. Returns `None` if `v` is not affine in `iv` with a COMPILE-TIME
/// constant coefficient (a load result, a non-constant scale, `iv*iv`, an
/// accumulator, ...). `loop_def` maps every in-loop-defined vreg to its def.
fn iv_affine_coeff(
    func: &MachFunction,
    v: VReg,
    iv: VReg,
    loop_def: &HashMap<u32, InstId>,
    acc_ids: &HashSet<u32>,
    depth: u32,
) -> Option<i64> {
    if depth > 32 {
        return None;
    }
    if v == iv {
        return Some(1);
    }
    if acc_ids.contains(&v.id) {
        return None; // accumulator: loop-variant but not an affine function of iv
    }
    let Some(&def) = loop_def.get(&v.id) else {
        return Some(0); // defined outside the loop ⇒ invariant
    };
    let inst = func.inst(def);
    let rec = |x: VReg| iv_affine_coeff(func, x, iv, loop_def, acc_ids, depth + 1);
    use AArch64Opcode::*;
    match inst.opcode {
        Movz | Movn | Movk => Some(0),
        AddRR => Some(rec(vreg_of(&inst.operands[1])?)? + rec(vreg_of(&inst.operands[2])?)?),
        AddRI => rec(vreg_of(&inst.operands[1])?),
        SubRR => Some(rec(vreg_of(&inst.operands[1])?)? - rec(vreg_of(&inst.operands[2])?)?),
        SubRI => rec(vreg_of(&inst.operands[1])?),
        MulRR => {
            let a = vreg_of(&inst.operands[1])?;
            let b = vreg_of(&inst.operands[2])?;
            mul_coeff(func, a, b, iv, loop_def, acc_ids, depth)
        }
        Madd => {
            let a = vreg_of(&inst.operands[1])?;
            let b = vreg_of(&inst.operands[2])?;
            let addend = vreg_of(&inst.operands[3])?;
            Some(mul_coeff(func, a, b, iv, loop_def, acc_ids, depth)? + rec(addend)?)
        }
        LslRI => {
            let a = rec(vreg_of(&inst.operands[1])?)?;
            let sh = imm_of(&inst.operands[2])?;
            if !(0..=31).contains(&sh) {
                return None;
            }
            Some(a.checked_shl(sh as u32)?)
        }
        Sxtw | Uxtw => {
            // Only distributes for the base cases: the (non-negative, small)
            // induction itself, or an invariant. `iv` here is a 32-bit counter
            // sign/zero-extended to form a 64-bit index; extending `init+k`
            // (all in `[0, MAX_FULL)`) is identity, so the coefficient carries.
            let x = vreg_of(&inst.operands[1])?;
            if x == iv {
                Some(1)
            } else if rec(x)? == 0 {
                Some(0)
            } else {
                None
            }
        }
        _ => None, // loads, FP, shifts-right, byte-truncations, ... : not affine
    }
}

/// Affine coefficient of `iv` in `a*b`, requiring the non-iv factor to be a
/// COMPILE-TIME constant (else the coefficient is not a compile-time immediate).
fn mul_coeff(
    func: &MachFunction,
    a: VReg,
    b: VReg,
    iv: VReg,
    loop_def: &HashMap<u32, InstId>,
    acc_ids: &HashSet<u32>,
    depth: u32,
) -> Option<i64> {
    let ca = iv_affine_coeff(func, a, iv, loop_def, acc_ids, depth + 1)?;
    let cb = iv_affine_coeff(func, b, iv, loop_def, acc_ids, depth + 1)?;
    match (ca, cb) {
        (0, 0) => Some(0),
        (0, _) => Some(const_val_of(func, a)?.checked_mul(cb)?),
        (_, 0) => Some(const_val_of(func, b)?.checked_mul(ca)?),
        _ => None, // iv * iv
    }
}

/// Backward slice of body instructions computing `offset` (stopping at `iv`,
/// constants, and loop invariants). Appended to `out` (dedup); the caller
/// clones these (in body order) with `iv->0` to materialise `REST`.
fn collect_offset_slice(
    func: &MachFunction,
    offset: VReg,
    loop_def: &HashMap<u32, InstId>,
    out: &mut Vec<InstId>,
) {
    let Some(&def) = loop_def.get(&offset.id) else {
        return; // invariant / iv: not a slice member
    };
    if out.contains(&def) {
        return;
    }
    for op in func.inst(def).operands.iter().skip(1) {
        if let Some(v) = vreg_of(op) {
            collect_offset_slice(func, v, loop_def, out);
        }
    }
    out.push(def);
}

/// First-level in-loop LOADS the value `reg` transitively depends on: walk the
/// backward slice, treating any in-loop load as an opaque LEAF (do NOT descend
/// into its address). Appended to `out` (dedup). Used to recognize a two-level
/// gather's single row-pointer load and to reject deeper chains.
fn collect_inloop_loads(
    func: &MachFunction,
    reg: VReg,
    loop_def: &HashMap<u32, InstId>,
    out: &mut Vec<InstId>,
) {
    let Some(&def) = loop_def.get(&reg.id) else {
        return; // invariant / iv: not defined in the loop
    };
    if is_load(func.inst(def).opcode) {
        if !out.contains(&def) {
            out.push(def);
        }
        return; // leaf — the two-level bound is enforced against `def`'s address
    }
    for op in func.inst(def).operands.iter().skip(1) {
        if let Some(v) = vreg_of(op) {
            collect_inloop_loads(func, v, loop_def, out);
        }
    }
}

/// Whether load `id` is an admissible TWO-LEVEL AFFINE GATHER — the dependent
/// element load of `m2[k][j]`: its address depends on EXACTLY ONE in-loop
/// row-pointer load `R`, itself a proven full-width (8-byte) single-level affine
/// load with a truly loop-invariant base. Full-unroll then clones this load AND
/// its address arithmetic verbatim per copy, threading `R`'s materialized
/// per-copy value through the rename map — so no extra fold state is needed
/// here, only validation. Fail-closed on any miss.
///
/// Required:
/// * the loop body has NO stores — a store could clobber the row-pointer array
///   between iterations (the conservative bar the matrix k-loop clears);
/// * the address depends on exactly ONE in-loop load `R` (the row load);
/// * `R` produces a `Gpr64` pointer via a full-width `LdrRO`/`LdrRI`;
/// * `R`'s own address is single-level affine in `iv` with a loop-invariant
///   base — which also bounds the chain to TWO levels (`R` reads no in-loop
///   load, else its address would not be affine).
fn gather_admissible(
    func: &MachFunction,
    id: InstId,
    iv: VReg,
    loop_def: &HashMap<u32, InstId>,
    def_count: &HashMap<u32, usize>,
    acc_ids: &HashSet<u32>,
    loop_has_store: bool,
) -> bool {
    if loop_has_store {
        return false;
    }
    // In-loop loads reachable from EVERY address operand (operand 0 is the
    // loaded def): for an RO load that is base + offset; for an RI load the
    // single address register.
    let mut rows = Vec::new();
    for op in func.inst(id).operands.iter().skip(1) {
        if let Some(v) = vreg_of(op) {
            collect_inloop_loads(func, v, loop_def, &mut rows);
        }
    }
    if rows.len() != 1 {
        return false; // zero (single-level) or a deeper / multi-row gather
    }
    let row = func.inst(rows[0]);
    if !is_load(row.opcode) {
        return false;
    }
    // The row load must produce a full-width 8-byte pointer.
    let Some(row_dst) = vreg_of(&row.operands[0]) else {
        return false;
    };
    if row_dst.class != RegClass::Gpr64 || mem_scale_of(row.opcode, row_dst) != Some(8) {
        return false;
    }
    // The row load's own address must be single-level affine in iv with a
    // loop-invariant base (affine ⇒ it reads no load ⇒ two-level max).
    match row.opcode {
        AArch64Opcode::LdrRO => {
            let (Some(rbase), Some(roff)) = (vreg_of(&row.operands[1]), vreg_of(&row.operands[2]))
            else {
                return false;
            };
            if rbase == iv || def_count.contains_key(&rbase.id) {
                return false; // row base is not loop-invariant
            }
            iv_affine_coeff(func, roff, iv, loop_def, acc_ids, 0).is_some()
        }
        AArch64Opcode::LdrRI => {
            let Some(raddr) = vreg_of(&row.operands[1]) else {
                return false;
            };
            if raddr == iv {
                return false;
            }
            // A loop-invariant address, or a whole-address affine immediate load.
            !def_count.contains_key(&raddr.id)
                || iv_affine_coeff(func, raddr, iv, loop_def, acc_ids, 0).is_some()
        }
        _ => false,
    }
}

/// Try to build a full-unroll plan for a SERIAL clang-rotated constant-trip
/// reduction with foldable addresses. Returns `None` (keep the 4-wide path) on
/// ANY deviation — fail-closed.
#[allow(clippy::too_many_arguments)]
fn try_full_unroll(
    func: &MachFunction,
    entry: BlockId,
    header_reentry: bool,
    iv: VReg,
    bound: VReg,
    bound_chain: &[InstId],
    body: &[InstId],
    mode: Mode,
    loop_set: &HashSet<InstId>,
    def_count: &HashMap<u32, usize>,
    acc_ids: &HashSet<u32>,
) -> Option<FullUnroll> {
    // Only the SERIAL clang-rotated shape (the importer's constant-trip inner
    // reductions): `entry` IS the unconditional-body header, so re-entering it
    // for the single tail iteration runs exactly that iteration and exits
    // through the ORIGINAL (unchanged) exit path — live-outs correct by
    // construction. SPLIT (reordering) and non-reentry shapes keep 4-wide.
    if !header_reentry || !matches!(mode, Mode::Serial) {
        return None;
    }
    // A rematerialized-in-loop constant bound is not evaluated here (would risk
    // a wrong trip); such loops (flops) have trips far above MAX_FULL anyway.
    if !bound_chain.is_empty() {
        return None;
    }

    let init = outside_def_const(func, iv, loop_set)?;
    let bound_val = const_val_of(func, bound)?;
    if init < 0 {
        return None;
    }
    let trip = bound_val.checked_sub(init)?;
    if !(MIN_FULL..=MAX_FULL).contains(&trip) {
        return None;
    }

    // Exit relation must be EQ or GE (leave when `iv+1` reaches `bound`); with
    // `trip >= MIN_FULL` the body runs `init..bound-1`, so `trip = bound-init`
    // for both. Read the header's loop-leaving conditional branch.
    let exit_cc = func
        .block(entry)
        .insts
        .iter()
        .map(|&id| func.inst(id))
        .find(|i| i.opcode == AArch64Opcode::BCond)
        .and_then(|i| imm_of(&i.operands[0]))?;
    if exit_cc != CC_EQ && exit_cc != CC_GE {
        return None;
    }

    // Map every in-loop-defined vreg to its (single) def instruction.
    let mut loop_def: HashMap<u32, InstId> = HashMap::new();
    for &id in body {
        for_each_inst_def(func.inst(id), |d| {
            loop_def.insert(d.id, id);
        });
    }

    let mut folds: Vec<LoadFold> = Vec::new();
    let mut skip: HashSet<InstId> = HashSet::new();
    let mut iv_read_by_compute = false;

    // A store anywhere in the loop forbids admitting a two-level gather (it could
    // clobber the row-pointer array between iterations). Single-level folds are
    // unaffected (their base is loop-invariant, the store address recognizer-
    // enforced invariant): the matrix k-loop is store-free; FloatMM's store is
    // single-level only.
    let loop_has_store = body.iter().any(|&bid| is_store(func.inst(bid).opcode));

    for &id in body {
        let inst = func.inst(id);
        let op = inst.opcode;
        if is_store(op) {
            continue; // invariant address (recognizer-enforced); cloned as-is
        }
        if is_load(op) {
            let dst = vreg_of(&inst.operands[0])?;
            match op {
                AArch64Opcode::LdrRO | AArch64Opcode::LdrbRO | AArch64Opcode::LdrhRO => {
                    let base = vreg_of(&inst.operands[1])?;
                    let offset = vreg_of(&inst.operands[2])?;
                    if base == iv {
                        return None;
                    }
                    if def_count.contains_key(&base.id) {
                        // In-loop base ⇒ only a TWO-LEVEL GATHER (the base is the
                        // in-loop row-pointer load). Validate and clone verbatim
                        // (the row load's per-copy value threads through `map`).
                        if !gather_admissible(
                            func,
                            id,
                            iv,
                            &loop_def,
                            def_count,
                            acc_ids,
                            loop_has_store,
                        ) {
                            return None;
                        }
                        continue; // not folded, not skipped: cloned as-is
                    }
                    let coeff = iv_affine_coeff(func, offset, iv, &loop_def, acc_ids, 0)?;
                    let scale = mem_scale_of(op, dst)?;
                    let mut slice = Vec::new();
                    collect_offset_slice(func, offset, &loop_def, &mut slice);
                    for &s in &slice {
                        skip.insert(s);
                    }
                    folds.push(LoadFold {
                        load: id,
                        dst,
                        base: Some(base),
                        offset,
                        imm0: 0,
                        coeff,
                        scale,
                        slice,
                    });
                }
                AArch64Opcode::LdrRI | AArch64Opcode::LdrbRI | AArch64Opcode::LdrhRI => {
                    let addr = vreg_of(&inst.operands[1])?;
                    let imm0 = imm_of(&inst.operands[2])?;
                    if addr == iv {
                        return None;
                    }
                    if !def_count.contains_key(&addr.id) {
                        // Invariant address: cloned as-is (existing behavior).
                    } else if let Some(coeff) =
                        iv_affine_coeff(func, addr, iv, &loop_def, acc_ids, 0)
                    {
                        // The WHOLE address is affine in iv (the pointer-array
                        // `Ldr [Madd(iv, #scale, ptr), #imm0]` shape): fold like an
                        // RO load, with no separate base pointer to add.
                        let scale = mem_scale_of(op, dst)?;
                        let mut slice = Vec::new();
                        collect_offset_slice(func, addr, &loop_def, &mut slice);
                        for &s in &slice {
                            skip.insert(s);
                        }
                        folds.push(LoadFold {
                            load: id,
                            dst,
                            base: None,
                            offset: addr,
                            imm0,
                            coeff,
                            scale,
                            slice,
                        });
                    } else {
                        // Non-affine in-loop address ⇒ only a TWO-LEVEL GATHER
                        // (dependent element load off an in-loop row load).
                        if !gather_admissible(
                            func,
                            id,
                            iv,
                            &loop_def,
                            def_count,
                            acc_ids,
                            loop_has_store,
                        ) {
                            return None;
                        }
                        continue; // not folded, not skipped: cloned as-is
                    }
                }
                _ => return None,
            }
            continue;
        }
        // A compute instruction: it may read iv directly (then materialise iv).
        if inst.operands.iter().skip(1).any(|o| vreg_of(o) == Some(iv)) {
            iv_read_by_compute = true;
        }
    }

    // At least one address must actually depend on iv (else nothing to fold —
    // keep the 4-wide path).
    if !folds.iter().any(|f| f.coeff != 0) {
        return None;
    }

    // Every skipped slice value must be consumed ONLY by other slice
    // instructions or by the fold-loads it addresses — never by a compute /
    // store / clone-as-is load (which would still need the value). Fail-closed.
    let skip_defs: HashSet<u32> = skip
        .iter()
        .filter_map(|&s| {
            func.inst(s)
                .operands
                .first()
                .and_then(vreg_of)
                .map(|v| v.id)
        })
        .collect();
    let fold_ids: HashSet<InstId> = folds.iter().map(|f| f.load).collect();
    for &id in body {
        if skip.contains(&id) || fold_ids.contains(&id) {
            continue;
        }
        for op in func.inst(id).operands.iter().skip(1) {
            if let Some(v) = vreg_of(op)
                && skip_defs.contains(&v.id)
            {
                return None;
            }
        }
    }

    // Every folded copy's immediate must encode. Copies run `iv = init .. init +
    // trip - 2` (the last iteration stays in the header). Check that exact set.
    for f in &folds {
        for k in 0..(trip - 1) {
            let imm = f.imm0.checked_add(f.coeff.checked_mul(init + k)?)?;
            if !imm_encodable(imm, f.scale) {
                return None;
            }
        }
    }

    Some(FullUnroll {
        trip,
        init,
        folds,
        skip,
        iv_read_by_compute,
    })
}

/// `inst` computes `iv + 1`: `AddRI(_, iv, #1)` or `AddRR(_, iv, one)` /
/// `AddRR(_, one, iv)` with `one` a `Movz #1` defined OUTSIDE the loop.
fn is_increment_by_one(
    func: &MachFunction,
    loop_insts: &[InstId],
    inst: &MachInst,
    iv: VReg,
) -> bool {
    match inst.opcode {
        AArch64Opcode::AddRI => {
            inst.operands.len() == 3
                && vreg_of(&inst.operands[1]) == Some(iv)
                && imm_of(&inst.operands[2]) == Some(1)
        }
        AArch64Opcode::AddRR => {
            if inst.operands.len() != 3 {
                return false;
            }
            let a = vreg_of(&inst.operands[1]);
            let b = vreg_of(&inst.operands[2]);
            let other = if a == Some(iv) {
                b
            } else if b == Some(iv) {
                a
            } else {
                None
            };
            let Some(other) = other else { return false };
            is_movz_one_outside(func, loop_insts, other)
        }
        _ => false,
    }
}

/// `v` is defined by exactly one `Movz v, #1` (no shift) outside the loop.
fn is_movz_one_outside(func: &MachFunction, loop_insts: &[InstId], v: VReg) -> bool {
    let mut found = false;
    for &b in &func.block_order {
        for &id in &func.block(b).insts {
            let inst = func.inst(id);
            if !inst_defines_vreg(inst, v) {
                continue;
            }
            if loop_insts.contains(&id) {
                return false;
            }
            if inst.opcode != AArch64Opcode::Movz
                || inst.operands.len() != 2
                || imm_of(&inst.operands[1]) != Some(1)
            {
                return false;
            }
            if found {
                return false; // multiple defs
            }
            found = true;
        }
    }
    found
}

// ---------------------------------------------------------------------------
// Transformation
// ---------------------------------------------------------------------------

fn apply(func: &mut MachFunction, plan: &Plan) {
    // FULL-UNROLL: constant-trip SERIAL reduction with foldable addresses —
    // emit straight-line copies with base+immediate loads (see the module docs).
    if let Some(fu) = &plan.full_unroll {
        apply_full_unroll(func, plan, fu);
        return;
    }

    let is_i64 = plan.iv.class == RegClass::Gpr64;

    // Fresh blocks: [precheck (i64 only)] / main header / body / latch / exit.
    let pv = if is_i64 {
        Some(func.create_block())
    } else {
        None
    };
    let uh = func.create_block();
    let ub = func.create_block();
    let ul = func.create_block();
    let ux = func.create_block();
    let mut order: Vec<BlockId> = Vec::new();
    if let Some(pv) = pv {
        order.push(pv);
    }
    order.extend([uh, ub, ul, ux]);
    insert_new_blocks_before(func, plan.entry, &order);
    let first = order[0];

    // Internal edges among fresh blocks (edges into the existing `entry` are
    // safe to add now; the preheader redirect is the COMMIT below).
    if let Some(pv) = pv {
        func.add_edge(pv, uh);
        func.add_edge(pv, plan.entry);
    }
    func.add_edge(uh, ub);
    func.add_edge(uh, ux);
    func.add_edge(ub, ul);
    func.add_edge(ul, uh);

    let pre = plan.preheader_term;

    // --- Effective bound for the guard. Normally `plan.bound` is a loop
    // live-in; but when it is a constant rematerialized in-loop (`bound_chain`
    // non-empty, e.g. the flops `m-1`), the value is NOT available before the
    // loop, so REPLICATE the `Movz`/`Movn`/`Movk` chain to a fresh register in
    // the guard (i64: the precheck `pv`; i32: before the preheader terminator).
    // This is bit-exact by construction — the same instructions build the same
    // constant — with no value reconstruction. The scalar tail keeps its own
    // in-loop chain untouched.
    let eff_bound = if plan.bound_chain.is_empty() {
        plan.bound
    } else {
        let nb = alloc(func, plan.bound.class);
        for &cid in &plan.bound_chain {
            let opcode = func.inst(cid).opcode;
            let mut ops = func.inst(cid).operands.clone();
            ops[0] = vreg(nb); // rename the chain's dst: bound -> nb
            if let Some(pv) = pv {
                emit(func, pv, opcode, ops);
            } else {
                emit_before(func, pre, opcode, ops);
            }
        }
        nb
    };

    // --- SPLIT mode: seed the UNROLL-1 extra accumulators with the op
    // identity in the preheader (`acc` itself is accumulator 0, preserving a
    // non-zero initial value — the regrouping argument in the module docs).
    let extra_accs: Vec<VReg> = match plan.mode {
        Mode::Split { identity, .. } => (1..UNROLL)
            .map(|_| {
                let a = alloc(func, plan.accs[0].0.class);
                emit_before(func, pre, AArch64Opcode::Movz, vec![vreg(a), imm(identity)]);
                a
            })
            .collect(),
        Mode::Serial => Vec::new(),
    };

    // --- Bounds guard (neon_array's, WIDTH = UNROLL = 4; see module docs).
    //
    // NATIVE / TOP-TESTED (`entry` is a re-test guard/header that tolerates
    // `iv == n`): `main_bound = n - (UNROLL-1)`, precheck `n < UNROLL`, leaving
    // 0..=UNROLL-1 tail iterations.
    //
    // CLANG-ROTATED (`header_reentry`: `entry` IS the header, which runs the body
    // UNCONDITIONALLY): re-entering with `iv == n` would read `a[n]` out of
    // bounds, so the guard is tightened by ONE — `main_bound = n - UNROLL`,
    // precheck `n < UNROLL+1` — which forces `iv < n` on every exit from the main
    // loop (main-loop exit: `iv ∈ [n-UNROLL, n-1]`; precheck-skip: `iv == 0 < n`,
    // as the rotated preheader is only reached when `n > 0`). The scalar loop
    // then always runs 1..=UNROLL tail iterations and delivers the result through
    // the original (unchanged) header exit — no exit-value reconstruction needed.
    let (sub_imm, pre_imm) = if plan.header_reentry {
        (UNROLL, UNROLL + 1)
    } else {
        (UNROLL - 1, UNROLL)
    };
    let main_bound = alloc(func, RegClass::Gpr64);
    if let Some(pv) = pv {
        // i64: precheck `if n <s pre_imm skip`; `main_bound = n - sub_imm` exact
        // when taken; main loop tests UNSIGNED `iv <u main_bound`.
        emit(
            func,
            pv,
            AArch64Opcode::SubRI,
            vec![vreg(main_bound), vreg(eff_bound), imm(sub_imm)],
        );
        emit(
            func,
            pv,
            AArch64Opcode::CmpRI,
            vec![vreg(eff_bound), imm(pre_imm)],
        );
        emit(
            func,
            pv,
            AArch64Opcode::BCond,
            vec![imm(CC_LT), block(plan.entry)],
        );
        emit(func, pv, AArch64Opcode::B, vec![block(uh)]);
        emit(
            func,
            uh,
            AArch64Opcode::CmpRR,
            vec![vreg(plan.iv), vreg(main_bound)],
        );
        emit(func, uh, AArch64Opcode::BCond, vec![imm(CC_LO), block(ub)]);
        emit(func, uh, AArch64Opcode::B, vec![block(ux)]);
    } else {
        // i32: `main_bound = sxtw(n) - sub_imm` (exact in i64); test
        // `sxtw(iv) < main_bound`. The signed test naturally skips the main loop
        // for small `n` (no precheck needed): `main_bound <= 0 ⇒ sxtw(0) < it`
        // is false, so control falls straight to `entry` with `iv == 0`.
        let nb64 = alloc(func, RegClass::Gpr64);
        emit_before(
            func,
            pre,
            AArch64Opcode::Sxtw,
            vec![vreg(nb64), vreg(eff_bound)],
        );
        emit_before(
            func,
            pre,
            AArch64Opcode::SubRI,
            vec![vreg(main_bound), vreg(nb64), imm(sub_imm)],
        );
        let gi = alloc(func, RegClass::Gpr64);
        emit(func, uh, AArch64Opcode::Sxtw, vec![vreg(gi), vreg(plan.iv)]);
        emit(
            func,
            uh,
            AArch64Opcode::CmpRR,
            vec![vreg(gi), vreg(main_bound)],
        );
        emit(func, uh, AArch64Opcode::BCond, vec![imm(CC_LT), block(ub)]);
        emit(func, uh, AArch64Opcode::B, vec![block(ux)]);
    }

    // --- Main body: lane index registers `iv+k` (lane 0 uses `iv` itself;
    // wrap-free under the guard), then the four body copies. Only materialized
    // when the body actually reads `iv` — a loadless recurrence (iterative fib)
    // never indexes memory, so per-lane indices would be dead arithmetic (no
    // DCE runs after this pass at O2, so we must not emit it).
    let body_uses_iv = plan.body.iter().any(|&id| {
        func.inst(id)
            .operands
            .iter()
            .skip(1)
            .any(|op| vreg_of(op) == Some(plan.iv))
    });
    let mut lane_iv: Vec<VReg> = vec![plan.iv];
    for k in 1..UNROLL {
        if body_uses_iv {
            let ivk = alloc(func, plan.iv.class);
            emit(
                func,
                ub,
                AArch64Opcode::AddRI,
                vec![vreg(ivk), vreg(plan.iv), imm(k)],
            );
            lane_iv.push(ivk);
        } else {
            lane_iv.push(plan.iv); // unused by the clones; avoid dead adds
        }
    }

    match plan.mode {
        Mode::Split { op, .. } => {
            // Lane k folds into accumulator k: clone the body with
            // `iv -> iv+k` and the root's `acc` operand renamed to
            // accumulator k. Every clone defines a FRESH vreg; the carried
            // accumulators are advanced by `MovR acc_k, acc_next_k` writeback
            // copies at the block tail — the backend's copy-form loop
            // contract (`reduction_split`'s emitted shape), which the O3
            // fixpoint's scalar passes (GVN/copy-prop/DCE) are built around.
            // In-place redefinition of a carried GPR inside the loop is NOT
            // that shape and gets mis-numbered on re-runs.
            let (acc, acc_src) = plan.accs[0];
            let mut lane_next: Vec<(VReg, VReg)> = Vec::new();
            for k in 0..UNROLL as usize {
                let acc_k = if k == 0 { acc } else { extra_accs[k - 1] };
                let mut map: HashMap<u32, VReg> = HashMap::new();
                map.insert(plan.iv.id, lane_iv[k]);
                map.insert(acc.id, acc_k);
                for &id in &plan.body {
                    clone_inst(func, ub, id, &mut map);
                }
                lane_next.push((acc_k, *map.get(&acc_src.id).expect("root cloned")));
            }
            for &(acc_k, next) in &lane_next {
                emit(func, ub, AArch64Opcode::MovR, vec![vreg(acc_k), vreg(next)]);
            }
            emit(func, ub, AArch64Opcode::B, vec![block(ul)]);

            // Exit: balanced combine `acc = (acc0 op acc1) op (acc2 op acc3)`
            // through fresh temporaries + one writeback copy (copy-form).
            let a01 = alloc(func, acc.class);
            let a23 = alloc(func, acc.class);
            let tot = alloc(func, acc.class);
            emit(
                func,
                ux,
                op,
                vec![vreg(a01), vreg(acc), vreg(extra_accs[0])],
            );
            emit(
                func,
                ux,
                op,
                vec![vreg(a23), vreg(extra_accs[1]), vreg(extra_accs[2])],
            );
            emit(func, ux, op, vec![vreg(tot), vreg(a01), vreg(a23)]);
            emit(func, ux, AArch64Opcode::MovR, vec![vreg(acc), vreg(tot)]);
            emit(func, ux, AArch64Opcode::B, vec![block(plan.entry)]);
        }
        Mode::Serial => {
            // The `k` carried accumulators are threaded through `UNROLL`
            // verbatim lane copies. `prev[j]` holds carried var `j`'s value
            // entering a lane (lane 0 reads the live carried regs). Each lane:
            // clone the body ONCE with iv → iv+k and every carried var → its
            // `prev` value, then read off each var's NEXT value — its writeback
            // source, a body def, resolved through the SAME map to this lane's
            // fresh clone — and update all `prev` SIMULTANEOUSLY. Because every
            // source is a fresh clone (never a live carried reg — see the
            // recognizer's body-def contract), the simultaneous update equals
            // the scalar loop's sequential writebacks; the writebacks read
            // loop-top values exactly as `a,b = b,a+b` does. Every instruction
            // runs in the original order with the original operands:
            // bit-identical to `UNROLL` scalar iterations (module docs). k=1
            // reduces to the single-accumulator chain verbatim.
            let mut prev: Vec<VReg> = plan.accs.iter().map(|(a, _)| *a).collect();
            for &lane in lane_iv.iter().take(UNROLL as usize) {
                let mut map: HashMap<u32, VReg> = HashMap::new();
                map.insert(plan.iv.id, lane);
                for (j, (a, _)) in plan.accs.iter().enumerate() {
                    map.insert(a.id, prev[j]);
                }
                for &id in &plan.body {
                    clone_inst(func, ub, id, &mut map);
                }
                prev = plan
                    .accs
                    .iter()
                    .map(|(_, src)| *map.get(&src.id).unwrap_or(src))
                    .collect();
            }
            // One writeback per carried var (fresh distinct `prev` vregs —
            // order-free); copies that the O3 fixpoint / regalloc coalescing
            // fold away by renaming.
            for (j, (a, _)) in plan.accs.iter().enumerate() {
                let wb_op = if matches!(a.class, RegClass::Fpr32 | RegClass::Fpr64) {
                    AArch64Opcode::FmovFprFpr
                } else {
                    AArch64Opcode::MovR
                };
                emit(func, ub, wb_op, vec![vreg(*a), vreg(prev[j])]);
            }
            emit(func, ub, AArch64Opcode::B, vec![block(ul)]);
            emit(func, ux, AArch64Opcode::B, vec![block(plan.entry)]);
        }
    }

    // --- Main latch: advance the induction by UNROLL.
    emit(
        func,
        ul,
        AArch64Opcode::AddRI,
        vec![vreg(plan.iv), vreg(plan.iv), imm(UNROLL)],
    );
    emit(func, ul, AArch64Opcode::B, vec![block(uh)]);

    // --- COMMIT: redirect the single preheader edge through the main loop.
    let redirected = rewrite_block_target(func.inst_mut(plan.preheader_term), plan.entry, first);
    debug_assert!(redirected, "validated preheader branch targets entry");
    remove_cfg_edge(func, plan.preheader, plan.entry);
    func.add_edge(plan.preheader, first);
    func.add_edge(ux, plan.entry);
}

// ---------------------------------------------------------------------------
// Full-unroll transformation
// ---------------------------------------------------------------------------

/// Emit a non-negative compile-time constant into a fresh register of `class`
/// via `Movz` + `Movk` chunks (`Gpr32`: low 32 bits only). Bit-exact.
fn emit_const(func: &mut MachFunction, b: BlockId, class: RegClass, val: i64) -> VReg {
    debug_assert!(val >= 0, "emit_const expects a non-negative constant");
    let d = alloc(func, class);
    let uv = val as u64;
    emit(
        func,
        b,
        AArch64Opcode::Movz,
        vec![vreg(d), imm((uv & 0xFFFF) as i64)],
    );
    let shifts: &[i64] = if class == RegClass::Gpr64 {
        &[16, 32, 48]
    } else {
        &[16]
    };
    for &sh in shifts {
        let chunk = (uv >> sh) & 0xFFFF;
        if chunk != 0 {
            emit(
                func,
                b,
                AArch64Opcode::Movk,
                vec![vreg(d), imm(chunk as i64), imm(sh)],
            );
        }
    }
    d
}

/// FULL-UNROLL a constant-trip SERIAL reduction (see [`FullUnroll`]).
///
/// One fresh straight-line block `ub` replaces the preheader edge into the
/// loop. It runs the FIRST `trip-1` iterations verbatim, with the induction a
/// KNOWN constant per copy so each foldable load becomes `LdrRI [base, #imm]`
/// (the invariant base hoisted once). It then writes the carried accumulator(s)
/// and sets `iv = init + (trip-1)` and re-enters the ORIGINAL header, which runs
/// the FINAL iteration on its original code and exits through the unchanged exit
/// edge — so every loop live-out is produced by the original loop, unchanged.
///
/// Bit-identity: the fast path is `trip-1` verbatim copies of the scalar body
/// in iteration order feeding the single carried chain (NO reassociation — safe
/// for the FP accumulator), plus one original tail iteration. The folded loads
/// read the SAME addresses (`ptr + REST + iv*coeff`, with `base = ptr + REST`
/// hoisted and `iv` the copy's constant) and the stores replicate verbatim.
fn apply_full_unroll(func: &mut MachFunction, plan: &Plan, fu: &FullUnroll) {
    let iv = plan.iv;
    let ub = func.create_block();
    insert_new_blocks_before(func, plan.entry, &[ub]);

    // `iv -> 0` substitute for the slice clones that materialise each base.
    let zero = alloc(func, iv.class);
    emit(func, ub, AArch64Opcode::Movz, vec![vreg(zero), imm(0)]);

    // Hoist `base_L = base_L? + offset_L(iv=0)` for every foldable load, once, by
    // cloning the offset slice with `iv -> 0` (so the iv term vanishes and only
    // the invariant REST remains) and adding the invariant pointer (RO loads); an
    // RI load with no separate pointer (`base = None`) hoists its whole affine
    // address, so `offset(iv=0)` IS the base.
    let mut base_of: HashMap<InstId, VReg> = HashMap::new();
    for lf in &fu.folds {
        let mut smap: HashMap<u32, VReg> = HashMap::new();
        smap.insert(iv.id, zero);
        for &sid in &plan.body {
            if lf.slice.contains(&sid) {
                clone_inst(func, ub, sid, &mut smap);
            }
        }
        // `offset(iv=0)` is REST; with an empty slice (offset itself invariant)
        // it is the offset register directly.
        let off0 = *smap.get(&lf.offset.id).unwrap_or(&lf.offset);
        let base = match lf.base {
            Some(ptr) => {
                let b = alloc(func, RegClass::Gpr64);
                emit(
                    func,
                    ub,
                    AArch64Opcode::AddRR,
                    vec![vreg(b), vreg(ptr), vreg(off0)],
                );
                b
            }
            None => off0, // whole address hoisted: `off0` is the base
        };
        base_of.insert(lf.load, base);
    }

    // The `trip-1` fully-folded copies, threading the carried accumulator(s).
    let mut prev: Vec<VReg> = plan.accs.iter().map(|(a, _)| *a).collect();
    for k in 0..(fu.trip - 1) {
        let iv_val = fu.init + k;
        let mut map: HashMap<u32, VReg> = HashMap::new();
        for (j, (a, _)) in plan.accs.iter().enumerate() {
            map.insert(a.id, prev[j]);
        }
        if fu.iv_read_by_compute {
            let ivc = emit_const(func, ub, iv.class, iv_val);
            map.insert(iv.id, ivc);
        }
        for &bid in &plan.body {
            if fu.skip.contains(&bid) {
                continue; // offset arithmetic folded into the load immediate
            }
            if let Some(lf) = fu.folds.iter().find(|f| f.load == bid) {
                let base = base_of[&bid];
                let ri = percopy_ri_opcode(func.inst(bid).opcode).expect("validated load");
                let d = alloc(func, lf.dst.class);
                let off = lf.imm0 + lf.coeff * iv_val;
                emit(func, ub, ri, vec![vreg(d), vreg(base), imm(off)]);
                map.insert(lf.dst.id, d);
            } else {
                clone_inst(func, ub, bid, &mut map);
            }
        }
        prev = plan
            .accs
            .iter()
            .map(|(_, src)| *map.get(&src.id).unwrap_or(src))
            .collect();
    }

    // Carried-var writebacks entering the tail header: each accumulator gets its
    // value after `trip-1` iterations; the induction its constant `init+trip-1`.
    for (j, (a, _)) in plan.accs.iter().enumerate() {
        let wb = if matches!(a.class, RegClass::Fpr32 | RegClass::Fpr64) {
            AArch64Opcode::FmovFprFpr
        } else {
            AArch64Opcode::MovR
        };
        emit(func, ub, wb, vec![vreg(*a), vreg(prev[j])]);
    }
    let iv_final = emit_const(func, ub, iv.class, fu.init + (fu.trip - 1));
    emit(
        func,
        ub,
        AArch64Opcode::MovR,
        vec![vreg(iv), vreg(iv_final)],
    );
    emit(func, ub, AArch64Opcode::B, vec![block(plan.entry)]);

    // Local zero-fold of the fast path (see [`collapse_zero_ops`]): with
    // `init == 0` every hoisted fold base collapses to `0*scale + ptr = ptr`,
    // an irreducible `Madd`/`AddRR` that neither the post-scalar-unroll DCE nor
    // register coalescing can strip. Removing it here saves one materialised
    // zero + one ALU op per fold in the (i,j)-hot matmul preheader.
    collapse_zero_ops(func, ub);

    // COMMIT: redirect the single preheader edge through `ub`, which re-enters
    // the ORIGINAL header for the final iteration.
    let redirected = rewrite_block_target(func.inst_mut(plan.preheader_term), plan.entry, ub);
    debug_assert!(redirected, "validated preheader branch targets entry");
    remove_cfg_edge(func, plan.preheader, plan.entry);
    func.add_edge(plan.preheader, ub);
    func.add_edge(ub, plan.entry);
}

/// Fold the redundant zero arithmetic the fast-path emitter leaves in `ub` when
/// `init == 0` and forward the result WITHIN the straight-line block.
///
/// The base of every foldable load is materialised by cloning its offset slice
/// with `iv -> 0` (a fresh `Movz #0`). For the common `init == 0` counted loop
/// the slice collapses to `0*scale + ptr` — emitted as `Madd(zero, scale, ptr)`
/// (whole-address fold) or `AddRR(ptr, zero)` (separate-pointer fold). Both
/// equal `ptr` exactly, but neither is a copy, so the scheduler/DCE that follows
/// `scalar-unroll` and register coalescing all leave them in place: in the
/// Shootout `matrix` k-loop this is a live `mov xZ,#0; madd base,xZ,#scale,ptr`
/// per fold, re-executed on every `(i,j)` iteration.
///
/// This pass rewrites, in program order over `ub` only:
///   * `Madd(d, m1, m2, a)` with `m1` or `m2` a `ub`-local `Movz #0`  ⇒ `d ≡ a`,
///   * `AddRR(d, x, y)` with `x` or `y` a `ub`-local `Movz #0`        ⇒ `d ≡` other,
///     substituting `d` by its equal source in every later `ub` use and deleting the
///     folded instruction. `0*x + a == a` and `x + 0 == x` hold for all inputs, so
///     this is value-preserving; a def used OUTSIDE `ub` is never folded (its user
///     would lose its definition), keeping the rewrite block-local and sound. Any
///     `Movz #0` left unused is dropped last. The straight-line, single-entry shape
///     of `ub` (defs precede uses) makes one forward pass exact.
fn collapse_zero_ops(func: &mut MachFunction, ub: BlockId) {
    let insts: Vec<InstId> = func.block(ub).insts.clone();

    // `ub`-local registers proven to hold 0.
    let mut zero: HashSet<u32> = HashSet::new();
    for &id in &insts {
        let inst = func.inst(id);
        if let Some((d, 0)) = crate::reaching_const::movz_value(inst) {
            zero.insert(d.id);
        }
    }
    if zero.is_empty() {
        return;
    }

    // A def used anywhere OUTSIDE `ub` must keep its definition — folding it away
    // would orphan that external use. Collect those vreg ids once.
    let used_outside: HashSet<u32> = func
        .blocks
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != ub.0 as usize)
        .flat_map(|(_, b)| b.insts.iter())
        .flat_map(|&iid| func.inst(iid).operands.iter().skip(1))
        .filter_map(vreg_of)
        .map(|v| v.id)
        .collect();

    let mut subst: HashMap<u32, VReg> = HashMap::new();
    let mut remove: HashSet<InstId> = HashSet::new();

    for &id in &insts {
        // Resolve this instruction's use operands through prior substitutions.
        {
            let inst = func.inst_mut(id);
            for op in inst.operands.iter_mut().skip(1) {
                if let MachOperand::VReg(v) = op
                    && let Some(&r) = subst.get(&v.id)
                {
                    *v = r;
                }
            }
        }
        let inst = func.inst(id);
        let is_zero = |o: &MachOperand| vreg_of(o).is_some_and(|v| zero.contains(&v.id));
        // The equal source this op collapses to, if any.
        let equal_src = match inst.opcode {
            AArch64Opcode::Madd if is_zero(&inst.operands[1]) || is_zero(&inst.operands[2]) => {
                vreg_of(&inst.operands[3])
            }
            AArch64Opcode::AddRR if is_zero(&inst.operands[1]) => vreg_of(&inst.operands[2]),
            AArch64Opcode::AddRR if is_zero(&inst.operands[2]) => vreg_of(&inst.operands[1]),
            _ => None,
        };
        if let (Some(dst), Some(src)) = (vreg_of(&inst.operands[0]), equal_src)
            && !used_outside.contains(&dst.id)
        {
            // Operands are already resolved, so `src` is the canonical value.
            subst.insert(dst.id, src);
            remove.insert(id);
        }
    }

    if remove.is_empty() {
        return;
    }
    func.block_mut(ub).insts.retain(|id| !remove.contains(id));

    // Drop any `Movz #0` that has become dead (its only users were folded).
    let still_used: HashSet<u32> = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter())
        .flat_map(|&iid| func.inst(iid).operands.iter().skip(1))
        .filter_map(vreg_of)
        .map(|v| v.id)
        .collect();
    let dead_zero: HashSet<InstId> = func
        .block(ub)
        .insts
        .iter()
        .copied()
        .filter(|&id| {
            let inst = func.inst(id);
            crate::reaching_const::movz_value(inst).is_some_and(|(d, value)| {
                value == 0 && zero.contains(&d.id) && !still_used.contains(&d.id)
            })
        })
        .collect();
    func.block_mut(ub)
        .insts
        .retain(|id| !dead_zero.contains(id));
}

/// Clone body instruction `id` into `b`, remapping operand vregs through
/// `map` (invariants pass through) and allocating a fresh def, which is
/// recorded in `map`.
///
/// A STORE defines no vreg — EVERY operand (including operand 0, the stored
/// value) is a use — so it is cloned by remapping all operands, with no fresh
/// def allocated. This replicates the store verbatim in each lane (SERIAL
/// mode only), preserving the exact scalar store sequence.
fn clone_inst(func: &mut MachFunction, b: BlockId, id: InstId, map: &mut HashMap<u32, VReg>) {
    let inst = func.inst(id);
    let opcode = inst.opcode;
    if is_store(opcode) {
        let operands: Vec<MachOperand> = inst
            .operands
            .iter()
            .map(|op| match op {
                MachOperand::VReg(v) => MachOperand::VReg(*map.get(&v.id).unwrap_or(v)),
                other => other.clone(),
            })
            .collect();
        emit(func, b, opcode, operands);
        return;
    }
    let old_dst = inst
        .operands
        .first()
        .and_then(vreg_of)
        .expect("validated body def");
    let mut operands: Vec<MachOperand> = Vec::with_capacity(inst.operands.len());
    operands.push(MachOperand::Imm(0)); // placeholder for the def
    for op in inst.operands.iter().skip(1) {
        operands.push(match op {
            MachOperand::VReg(v) => MachOperand::VReg(*map.get(&v.id).unwrap_or(v)),
            other => other.clone(),
        });
    }
    let new_dst = alloc(func, old_dst.class);
    operands[0] = MachOperand::VReg(new_dst);
    map.insert(old_dst.id, new_dst);
    emit(func, b, opcode, operands);
}

// ---------------------------------------------------------------------------
// Small local IR helpers (kept file-local like the NEON passes')
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

fn emit(
    func: &mut MachFunction,
    b: BlockId,
    op: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> InstId {
    let id = func.push_inst(MachInst::new(op, operands));
    func.append_inst(b, id);
    id
}

fn emit_before(
    func: &mut MachFunction,
    before: InstId,
    op: AArch64Opcode,
    operands: Vec<MachOperand>,
) -> InstId {
    let id = func.push_inst(MachInst::new(op, operands));
    for blk in &mut func.blocks {
        if let Some(pos) = blk.insts.iter().position(|&x| x == before) {
            blk.insts.insert(pos, id);
            return id;
        }
    }
    id
}

fn alloc(func: &mut MachFunction, class: RegClass) -> VReg {
    // Allocate a vreg id strictly greater than every id currently in use so we
    // never alias an existing value.
    let max_existing = func
        .insts
        .iter()
        .flat_map(|inst| inst.operands.iter())
        .filter_map(vreg_of)
        .map(|v| v.id)
        .max()
        .unwrap_or(0);
    let mut id = func.alloc_vreg();
    while id <= max_existing {
        id = func.alloc_vreg();
    }
    VReg::new(id, class)
}

/// The sole untied operand-0 definition supported by the generic body cloner.
fn simple_body_def(inst: &MachInst) -> Option<VReg> {
    let mut defs = Vec::new();
    aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| defs.push(pos));
    if defs.as_slice() != [0] {
        return None;
    }
    let mut tied = false;
    aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
        if pos == 0 {
            tied = true;
        }
    });
    if tied {
        return None;
    }
    inst.operands.first().and_then(vreg_of)
}

fn branch_targets(inst: &MachInst) -> Vec<BlockId> {
    inst.operands
        .iter()
        .filter_map(|op| match op {
            MachOperand::Block(b) => Some(*b),
            _ => None,
        })
        .collect()
}

fn rewrite_block_target(inst: &mut MachInst, old: BlockId, new: BlockId) -> bool {
    let mut changed = false;
    for op in &mut inst.operands {
        if matches!(op, MachOperand::Block(b) if *b == old) {
            *op = MachOperand::Block(new);
            changed = true;
        }
    }
    changed
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&s| s != to);
    func.block_mut(to).preds.retain(|&p| p != from);
}

fn insert_new_blocks_before(func: &mut MachFunction, before: BlockId, new_blocks: &[BlockId]) {
    let mut reordered = Vec::with_capacity(func.block_order.len() + new_blocks.len());
    for &b in &func.block_order {
        if b == before {
            reordered.extend(new_blocks.iter().copied());
        }
        if !new_blocks.contains(&b) {
            reordered.push(b);
        }
    }
    func.block_order = reordered;
}

#[cfg(test)]
#[path = "scalar_unroll/tests.rs"]
mod tests;
