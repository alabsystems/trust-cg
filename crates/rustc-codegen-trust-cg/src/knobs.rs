// rustc_codegen_trust_cg/knobs.rs - tracked backend knobs (-Ztrust-ir-cg-args)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

//! The backend's operator knobs, read from a TRACKED compiler option instead of
//! the process environment.
//!
//! WHAT this replaces. Every knob below used to be a `TCG_*` / `TRUST_CG_*`
//! environment variable that the backend read, lazily, wherever it happened to
//! need it.
//!
//! WHY it moved. An environment variable is not part of the crate hash. A knob
//! that changes emitted code — or changes the evidence attached to it, which
//! `no-proof-certs` does — therefore makes incremental reuse and evidence
//! provenance LIE: two compilations with different knobs hash identically, so
//! one can be served from the other's cache, and an artifact can carry a
//! provenance record that does not describe how it was built. trustc refuses
//! the whole `TCG_`/`TRUST_CG_` prefix family for exactly that reason
//! (`rustc_session::config::UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES`), and points
//! the user at the tracked replacement. This module is the backend half of that
//! replacement: `-Ztrust-ir-cg-args` is `[TRACKED]` + `EvidenceControl`, so a
//! knob change changes the crate hash and is recorded where evidence is
//! recorded.
//!
//! HOW it is read. Installed in `CodegenBackend::init` into a process-wide
//! [`OnceLock`]; subsequent sessions must install an identical parsed map.
//! Nothing re-reads, so no code path can observe two different
//! values for one knob inside one compilation — which an environment read
//! could, through this workspace's thread-local override layer.
//!
//! FAIL-CLOSED argument:
//!
//! 1. **Unknown keys refuse.** A misspelled knob is a hard error that NAMES
//!    every accepted key (design principle 10: a refusal carries the fix, with
//!    options). Silently ignoring it would let an operator believe a gate is
//!    off — or on — when it is not.
//! 2. **Absent is the checked lane.** Every knob's default (the empty knob set)
//!    is the MORE checked behaviour: proof certificates on, the refinement
//!    solver on, unwind modelling on, no traces. So a backend that never
//!    reaches `install` — a non-rustc embedding, or a compiler too old to carry
//!    the option — runs the fully checked lane and claims nothing extra.
//! 3. **The knobs never widen what is admitted.** They select traces, opt-outs
//!    and resource budgets. None of them admits a MIR shape the default lane
//!    would refuse.
//! 4. **A value is READ, never merely counted as present.** Each knob declares
//!    a [`Shape`], the grammar is checked once at parse where a bad value is
//!    `fatal`, and the stored value is canonical. This is the fix for a
//!    measured fail-open: with values stored verbatim and booleans read as
//!    `raw(key).is_none()`, `no-proof-certs=0` — written to KEEP the proof
//!    certificates — turned the gate OFF, and `no-proof-certs=nope` did too.
//!    Booleans are read with [`is_enabled`] / [`is_disabled`]; `raw` remains
//!    only for the value-carrying knobs.
//! 5. **Conflicting reinstallation refuses.** A later compiler session cannot
//!    silently compile with the first session's different tracked policy.
//!
//! REACH, and where it stops. These are the BACKEND's knobs. Where a knob has
//! to be visible to a library crate the backend calls, the backend FORWARDS it
//! explicitly from `init` — `diag-json` and `bridge-coverage[-strict]` through
//! setters on `trust_cg_verify`, `max-parallelism` through the shared resource
//! leaf — because a library reading the environment for itself sees nothing:
//! trustc refuses the variable before the backend is even loaded.
//!
//! Two knobs are PARTIAL, and say so in their help text: `no-proof-cache` and
//! `refine-solver` were also read independently by `trust_cg_verify`'s verdict
//! cache, and this option does not restore those reads. That is not a
//! regression — under trustc those reads were already dead, before and after,
//! because the variable is refused — and it does not cost checking: both
//! variables asked `trust_cg_verify` to do LESS (skip the cache, decline the
//! solver), so a library that does not see them keeps its full behaviour. The
//! direction of a partial knob is what matters, and this one points at more
//! checking, never at a verdict the operator's setting would have withheld.

use std::collections::BTreeMap;
use std::sync::OnceLock;

/// One accepted knob: its key, the environment variable it replaces, the shape
/// of value it accepts, and the one-line help printed when a refusal has to list
/// the accepted keys.
struct Knob {
    /// The key as written in `-Ztrust-ir-cg-args`.
    key: &'static str,
    /// The `TCG_*` / `TRUST_CG_*` variable this knob replaces. Kept so a
    /// refusal can tell a reader who knows the old name what the new one is;
    /// the backend never reads it.
    legacy_env: &'static str,
    /// What values this knob accepts, and therefore what a bad one does.
    shape: Shape,
    /// What the knob does, in one line.
    help: &'static str,
}

/// The value grammar of a knob.
///
/// # Why this exists — a measured silent fail-open
///
/// Every knob used to be stored verbatim and every boolean knob was read as
/// PRESENCE (`raw(key).is_none()`), so `no-proof-certs=0` — which a reader
/// writes to mean "keep the certificates" — parsed fine, stored `"0"`, and then
/// counted as SET: the proof-certificate gate switched OFF under an argument
/// spelled to keep it on. The same shape applied to every other `no-*` gate
/// opt-out and every trace. A knob whose value is ignored is worse than one
/// that refuses, because the operator has written down an intention the build
/// silently contradicts.
///
/// The grammar is now declared per knob and checked ONCE, at parse, where the
/// `Session` is in hand and a bad value is `fatal` before any object is
/// written. Call sites read the CANONICAL form and can no longer disagree
/// about what a value means.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    /// A boolean. Accepted spellings, canonicalized to `"1"` / `"0"`:
    ///
    /// * bare (`no-proof-certs`), `=1`, `=true`, `=on`, `=yes`  -> `"1"`
    /// * `=0`, `=false`, `=off`, `=no`                          -> `"0"`
    ///
    /// Anything else is a fatal refusal naming every accepted spelling. Read
    /// with [`is_enabled`] (default-OFF knobs) or [`is_disabled`] (default-ON
    /// knobs, whose `=0` is the kill switch); never with `raw(..).is_some()`,
    /// which is the predicate this shape exists to retire.
    Boolean,
    /// Exactly one of a fixed set of spellings (`opt-level=0|1|2|3`).
    OneOf(&'static [&'static str]),
    /// A base-10 `usize`, zero included.
    Uint,
    /// An item count with an off switch: `0`/`off`/`false`/empty disable
    /// (canonical `"0"`); bare/`1`/`on`/`true` take the default count; any other
    /// value must be a base-10 `usize`. Canonicalized to a decimal string.
    Count {
        /// The count a bare / `on` spelling means.
        default: usize,
    },
    /// Free-form text (a filesystem path). Every value is meaningful, including
    /// the empty one, so there is nothing to check here.
    Free,
    /// The value grammar is checked AT THE READ SITE, which already refuses
    /// fail-closed and names the knob and the fix — the two execution resource
    /// budgets go through `parse_positive_usize_control` in
    /// `positive_usize_knob`. Re-checking here would duplicate a good refusal
    /// and move its wording; leaving it there keeps ONE authority per knob.
    CheckedAtUse,
}

/// Declare the accepted knobs ONCE.
///
/// The macro emits both the `pub(crate) const` every call site uses and the
/// `ACCEPTED` table the parser validates against, from the same line. That is
/// the point: a call site cannot name a key the table lacks (it would not
/// compile), and the table cannot accept a key no call site reads without the
/// declaration being visible here.
macro_rules! declare_knobs {
    ($($name:ident = $key:literal, $legacy:literal, $shape:expr, $help:literal;)*) => {
        $(
            #[doc = $help]
            #[doc = ""]
            #[doc = concat!("`-Ztrust-ir-cg-args=", $key, "` (was `", $legacy, "`).")]
            pub(crate) const $name: &str = $key;
        )*

        /// Every knob this backend accepts, in declaration order.
        const ACCEPTED: &[Knob] = &[
            $(Knob { key: $key, legacy_env: $legacy, shape: $shape, help: $help }),*
        ];
    };
}

declare_knobs! {
    // ---- evidence / gate opt-outs (these are why the option is EvidenceControl)
    NO_PROOF_CERTS = "no-proof-certs", "TCG_NO_PROOF_CERTS", Shape::Boolean,
        "skip the per-compile lowering proof certificates (weakens the evidence the artifact carries)";
    NO_PROOF_CACHE = "no-proof-cache", "TCG_NO_PROOF_CACHE", Shape::Boolean,
        "skip the solver-identity warm-up the verdict cache consumes (PARTIAL: the cache itself is trust-cg-verify's own switch, not reachable from here)";
    SOURCE_BOUND_NO_NEGATIVE_MEMO = "source-bound-no-negative-memo", "TCG_SOURCE_BOUND_NO_NEGATIVE_MEMO", Shape::Boolean,
        "bypass the source-bound negative memo: every source-bound theorem AY did not certify (x86-64 body and envelope, AArch64 frame and ALU) is solved again at every occurrence, and the memo is neither read nor written. The memo only withholds credit, so this can only cost time or let a retry certify";
    NO_IDENTITY_WARM = "no-identity-warm", "TCG_NO_IDENTITY_WARM", Shape::Boolean,
        "do not pre-hash the solver binary identity on a detached thread (A/B only; verdicts are identical)";
    NO_REPLAY_PREFETCH = "no-replay-prefetch", "TCG_NO_REPLAY_PREFETCH", Shape::Boolean,
        "neither read nor write this compile's certificate replay hint, so no stored certificate is replayed (and no resident solver started) before lowering asks for it (A/B only; every replay is the same full check either way and verdicts are identical)";
    DISABLE_UNWIND = "disable-unwind", "TCG_DISABLE_UNWIND", Shape::Boolean,
        "refuse crates that need unwind tables instead of modelling the cleanup edges";
    NO_VC_DIAMOND = "no-vc-diamond", "TCG_NO_VC_DIAMOND", Shape::Boolean,
        "do not model in-loop diamonds in the loop-threading VC (the loop then fails closed)";
    NO_SSA071_CELL_RETRY = "no-ssa071-cell-retry", "TCG_NO_SSA071_CELL_RETRY", Shape::Boolean,
        "do not re-lower a loop whose structural misthread the loop-threading VC declined with the flagged scalars in memory cells (the loop then fails closed)";
    NO_REFINE_BATCH = "no-refine-batch", "TCG_NO_REFINE_BATCH", Shape::Boolean,
        "discharge refinement obligations one at a time instead of batching them";
    NO_ASSUME_SCRATCH_ELIDE = "no-assume-scratch-elide", "TCG_NO_ASSUME_SCRATCH_ELIDE", Shape::Boolean,
        "keep scratch assumes the elider would drop";
    NO_HELPER_OVERLAP = "no-helper-overlap", "TCG_NO_HELPER_OVERLAP", Shape::Boolean,
        "do not overlap helper compilation with the main lowering";
    NO_ZERO_FILL_TRACK = "no-zero-fill-track", "TCG_NO_ZERO_FILL_TRACK", Shape::Boolean,
        "do not track zero-fill state across stores";
    NO_VEC_MINCAP = "no-vec-mincap", "TCG_NO_VEC_MINCAP", Shape::Boolean,
        "do not apply the Vec minimum-capacity model";
    NO_X86_FILL_MEMSET = "no-x86-fill-memset", "TCG_NO_X86_FILL_MEMSET", Shape::Boolean,
        "keep the inline MOVDQU store loop for large compile-time x86 fills instead of the `memset` libcall (a FailClosedAllowlisted call, not a proven instruction)";
    NO_X86_JUMP_TABLE = "no-x86-jump-table", "TCG_NO_X86_JUMP_TABLE", Shape::Boolean,
        "lower a dense x86 switch (>=4 arms, density > 0.4) through a binary-search compare tree instead of an indexed JUMP TABLE (the jump table is default-on since it was measured; this is the forensic opt-out)";
    X86_CSE_LOAD_TRANSPARENT = "x86-cse-load-transparent", "TCG_X86_CSE_LOAD_TRANSPARENT", Shape::Boolean,
        "stop treating a plain load as a hard barrier in x86 CSE -- every tracked expression is register-only, so no memory access can change one (DEFAULT OFF: it changes the pass's contract and fires on nothing in the ported corpus)";
    NO_LICM_OUTER_IV = "no-licm-outer-iv", "TCG_NO_X86_LICM_OUTER_IV", Shape::Boolean,
        "restore the refusal to treat a multi-def vreg with no in-loop definition as loop-invariant (DEFAULT ON since 2026-09-30). Hoisting an outer loop's induction-derived value out of an inner loop is the commonest invariant in nested code; it takes p4_matmul 1.0818 -> 1.0753 and changes 1 of 18 beat-llvm binaries, so the register-pressure hazard that kept it opt-in has nowhere else to bite";
    NO_X86_LEA_WRITEBACK_COLLAPSE = "no-x86-lea-writeback-collapse", "TCG_NO_X86_LEA_WRITEBACK_COLLAPSE", Shape::Boolean,
        "DISTINCT from `no-x86-lea-writeback`, which is the PEEPHOLE's fold; this one is the post-RA coalescer's collapse. Do NOT collapse a LEA that writes back to its own base into a self-writeback form. The collapse is DEFAULT ON since 2026-09-30. Its doc carried a flip criterion resting on p1_xorshift at 0.8535 ON/OFF and blocked by p7_sieve at 1.44x; the named blocker (no x86 loop-head aligner) is gone, and on re-measurement BOTH figures had expired -- p1 0.9996 -> 0.9998 and p7 0.7118 -> 0.7142, both inside their floors. The default flipped on a different, smaller basis: p2_collatz 1.0231 -> 1.0105 (a parity violation halved), against m2_call_heavy 0.7506 -> 0.7557 and p6_branch_match 0.9796 -> 0.9822, both of which stay below parity; suite max and geomean unchanged. This is the forensic opt-out";
    NO_X86_BRANCH_LAYOUT = "no-x86-branch-layout", "TCG_NO_BRANCH_LAYOUT", Shape::Boolean,
        "disable the whole OPT-8 x86 branch-layout pass (all four rules: latch, fallthrough, cold-trap inversion, loop-exit inversion, plus cold-arm sinking). DEFAULT ON. Until 2026-09-30 its only channel was the `TCG_NO_BRANCH_LAYOUT` env var, which trustc refuses, so the pass's whole contribution had never been measured through the bridge -- and it matters: one of its rules was worth 2.2% on the suite's worst program as soon as it became measurable";
    NO_X86_COLD_TRAP_LAYOUT = "no-x86-cold-trap-layout", "TCG_NO_X86_COLD_TRAP_LAYOUT", Shape::Boolean,
        "disable ONLY the cold-trap fall-through inversion (bounds/null/abort exits) inside the branch-layout pass, leaving its other rules on. DEFAULT ON, profile-free-correct. Previously env-only, so its individual contribution was unmeasurable through the bridge";
    NO_X86_LOOP_EXIT_LAYOUT = "no-x86-loop-exit-layout", "TCG_NO_X86_LOOP_EXIT_LAYOUT", Shape::Boolean,
        "disable ONLY the loop-exit fall-through inversion inside the branch-layout pass, leaving its other rules on. DEFAULT ON, profile-independent (loop membership is the hotness evidence). Previously env-only. NOTE it overlaps the fallthrough rule on a top-tested loop header, so isolating either one needs both switches";
    X86_COLD_ARM_SINK = "x86-cold-arm-sink", "TCG_X86_COLD_ARM_SINK", Shape::Boolean,
        "enable COLD-ARM SINKING in the branch-layout pass: move a call-bearing diamond arm past the loop span. DEFAULT OFF, awaiting the soak its own doc asks for -- \"After the paired A/B the intended flip shape is a `TCG_NO_X86_COLD_ARM_SINK` kill switch with the rule default-ON\". That A/B could never be run, because the opt-in's only channel was a `TCG_*` variable trustc refuses. It is the first `block_order` mutation in the x86 lane, and block layout is the one thing measured to move time on this host";
    NO_BRANCH_LAYOUT_FALLTHROUGH = "no-branch-layout-fallthrough", "TCG_NO_BRANCH_LAYOUT_FALLTHROUGH", Shape::Boolean,
        "restore the pre-2026-09-30 layout: do NOT invert `jcc T; jmp F` when T is the layout successor, so the trailing jmp keeps its bytes. The rule is DEFAULT ON since both recorded reasons for deferring it were refuted by measurement -- p6_branch_match's +4.3% (its dispatch is now a jump table, measured 0.9795 -> 0.9784, noise) and p7_sieve's +23.5% (measured 0.7354 -> 0.7210, i.e. 1.6% FASTER). It takes the suite's WORST program b1_mispredict from 1.1216 to 1.0971 and the geomean from 0.8409 to 0.8372. Known cost: h1_vec_push_sum regresses 2.4% (0.9768 -> 1.0009). This is the forensic opt-out";
    NO_X86_JCC_BRANCH_PAD = "no-x86-jcc-branch-pad", "TCG_NO_X86_JCC_BRANCH_PAD", Shape::Boolean,
        "suppress ONLY the per-branch JCC NOP padding, keeping the per-function 32-byte padding and the `__text` 32-byte section alignment that `no-x86-jcc-align` also disables. That knob toggles all THREE together and its own doc says an A/B of it measures the combined regime, not the padding bytes -- so the measured trade (p2_collatz -1.8%, b1_mispredict +1.1%) could never be attributed to a mechanism. This separates them. Padding is semantically neutral, so dropping it only forgoes the Intel Skylake erratum mitigation, which does not apply on an AMD host";
    NO_X86_JCC_ALIGN = "no-x86-jcc-align", "TCG_NO_X86_JCC_ALIGN", Shape::Boolean,
        "disable JCC-erratum branch padding AND its function/section alignment (A/B experiment; enabled by default; disabling it does not imply a speedup)";
    X86_COPYPROP_ALU = "x86-copyprop-alu", "TCG_X86_COPYPROP_ALU", Shape::Boolean,
        "copy-propagate into the operands of a value-producing ALU instruction (every x86 ALU op writes flags, and the flag barrier rescues only the value-free Cmp/Test forms, so this was blocked for ALL arithmetic; DEFAULT OFF -- it fires, removing 11 instructions from b1_mispredict, and measures 1.0106x SLOWER there)";
    TRACE_X86_RMW_FUSE = "trace-x86-rmw-fuse", "TCG_X86_RMW_FUSE_TRACE", Shape::Boolean,
        "name the condition each memory-destination RMW fusion candidate declines on. The pass has FIFTEEN decline points -- window purity before and after the ALU, the EA canonical-root redef scan, the `sdef` rule, both deadness scans, the proof admission gate -- and every one of them declined in SILENCE, so a lost fusion could not be attributed by reading the output. Found needed while diagnosing why b1_mispredict's `t[j] += acc` arm loses its fusion under the two-address expansion while its `t[j] ^= s` arm keeps it (diagnostics only, no codegen effect)";
    TRACE_PEEPHOLE_ENTRY = "trace-peephole-entry", "TCG_X86_TRACE_PEEPHOLE_ENTRY", Shape::Boolean,
        "dump each x86 function's blocks as the PEEPHOLE sees them, filling the gap between the two vectorizer-owned dump positions (diagnostics; no codegen effect)";
    X86_TEST_ELIDE = "x86-test-elide", "TCG_X86_TEST_ELIDE", Shape::Boolean,
        "delete a `test v,v` / `cmp v,0` whose ZF the nearest preceding ALU def of `v` already established, when every downstream flag reader needs only ZF (its own comment calls it opt-in for a staged rollout, and the rollout had no lever reachable through the bridge)";
    NO_X86_LEA_WRITEBACK = "no-x86-lea-writeback", "TCG_NO_X86_LEA_WRITEBACK", Shape::Boolean,
        "keep the non-destructive two-address increment expansion (`lea tmp,[base+k]` / `add tmp,base,k` plus a write-back copy) instead of collapsing it to an in-place add";
    NO_X86_RMW_FUSE_SDEF = "no-x86-rmw-fuse-sdef", "TCG_NO_X86_RMW_FUSE_SDEF", Shape::Boolean,
        "refuse the memory-destination RMW fusion when the fused register operand `s` is DEFINED between the load and the ALU, restoring the stricter pre-2026-09-29 window. The fused instruction is spliced at the STORE's position, so it reads `s` after any such def, and the W2 window already refuses a redef of `s` between the ALU and the store -- so the old refusal was stricter than the rewrite needs, and it is what declined b1_mispredict's hot loop";
    NO_X86_ADD_FUSE = "no-x86-add-fuse", "TCG_NO_X86_ADD_FUSE", Shape::Boolean,
        "keep a locally-dead 64-bit load and its consuming AddRR as two instructions instead of fusing them into the single memory-operand `AddRM`. The `ImulRR` arm of this fusion has been default-on since X9; `AddRM` is equally first-class (encoded, coverage-gated, flag-modelled, with labelled addressing proofs) but was never created by any peephole, which is why h3_box_leak spent two instructions where LLVM emits one";
    NO_X86_IFCONVERT = "no-x86-ifconvert", "TCG_NO_IFCONVERT", Shape::Boolean,
        "disable x86 if-conversion (DEFAULT ON). Its only channel was the raw env var, which `trustc` refuses, so this default-ON hot-loop-rewriting pass had never been A/B'd through the real driver. trust-cg has TWO default-on branch->cmov passes and NO cmov->branch pass, with no profitability term in either; LLVM deliberately pairs a generous converter with X86CmovConversion to undo it, so an unmeasured branch->cmov pass can be a silent LOSS";
    NO_X86_CMOV_SWAP = "no-x86-cmov-swap", "TCG_NO_X86_CMOV_SWAP", Shape::Boolean,
        "disable the branchless conditional-swap rewrite for sort inner loops (DEFAULT ON). Same reachability defect as no-x86-ifconvert: env-only, hence never measured through the bridge";
    NO_X86_BLOCK_MERGE = "no-x86-block-merge", "TCG_NO_X86_BLOCK_MERGE", Shape::Boolean,
        "disable x86 straight-line block merging (DEFAULT ON at O2/O3). Env-only until 2026-11-03, so the pass that makes the largest class of O2 body-theorem refusals (a machine block lowering a merged LIR chain) could not be A/B'd through the bridge";
    NO_X86_LOOP_ROTATE = "no-x86-loop-rotate", "TCG_NO_X86_ROTATE", Shape::Boolean,
        "disable x86 loop rotation / pure-test header jump threading (DEFAULT ON at O2/O3). Env-only until 2026-11-03";
    NO_X86_LICM_LOADS = "no-x86-licm-loads", "TCG_NO_LICM_LOADS", Shape::Boolean,
        "keep invariant stack-slot loads in their loops: x86 LICM runs only its pure-only tier, as at O1 (DEFAULT ON at O2/O3). Env-only until 2026-11-03";
    NO_X86_LICM = "no-x86-licm", "TCG_NO_X86_LICM", Shape::Boolean,
        "disable x86 loop-invariant code motion entirely, every tier (Region-LICM, the instruction and load tiers, the pure-call clusters) at every opt level (DEFAULT ON at O1+). A diagnostic knob: the O2 proof census uses it to measure which roots LICM's hoists decide";
    NO_X86_LOOP_UNROLL = "no-x86-loop-unroll", "TCG_NO_X86_UNROLL", Shape::Boolean,
        "disable the x86 full unroller of small constant-trip loops (DEFAULT ON at O2/O3 since fa7ee295a; its env opt-out was deleted). A diagnostic knob: the O2 proof census uses it to measure which roots unrolling decides";
    NO_X86_PURE_CALL_HOIST = "no-x86-pure-call-hoist", "TCG_NO_PURE_CALL_HOIST", Shape::Boolean,
        "keep every call to a proven-pure function where the source puts it: x86 LICM skips its pure-call cluster tier (DEFAULT ON wherever x86 LICM runs). The tier has no translation-validation net, and the fuzz/repros/purecall differential compiles each program with and without this knob; its env kill switch was deleted in 747cf19b4";
    NO_X86_RMW_FUSE = "no-x86-rmw-fuse", "TCG_NO_X86_RMW_FUSE", Shape::Boolean,
        "disable the x86 memory-destination read-modify-write fusion (load+op+store -> `op [m], r`; DEFAULT ON). Env-only until 2026-11-03";
    NO_X86_SROA = "no-x86-sroa", "TCG_NO_X86_SROA", Shape::Boolean,
        "disable x86 scalar replacement of non-escaped stack slots (DEFAULT ON at O2/O3). Env-only until 2026-11-03";
    X86_ROWREG_PACKED_MUL = "x86-rowreg-packed-mul", "TCG_X86_ROWREG_PACKED_MUL", Shape::Boolean,
        "use the packed PMULUDQ lo64 compose for the row-register tier's products instead of scalar IMUL + GPR<->XMM round trips. LLVM's p4_matmul is 36 PMULUDQ / 2 IMUL in 272 instructions where this backend's default is 36 IMUL / 12 PMULUDQ in 468, so the packed route is what LLVM does on this program";
    NO_X86_ROWREG_MEMORY_RMW = "no-x86-rowreg-memory-rmw", "TCG_NO_X86_ROWREG_MEMORY_RMW", Shape::Boolean,
        "disable the row-register tier's IN-MEMORY route and restore the XMM-accumulator route. The in-memory route is the default ONLY together with `no-proof-certs` (since 2026-11-14); with proof certificates on the XMM route is kept whatever this knob says, because the in-memory route has not been run under proof gating. The in-memory route updates the c row element by element (`mov`, `imul`, `add [mem], reg`) in the source loop's own order; on p4_matmul it measured 33.7 ms against 63.2 ms for the XMM scalar-IMUL route on an AMD Ryzen host (LLVM: 66.3 ms at O2, 32.4 ms at O3). `x86-rowreg-packed-mul` names an XMM route and therefore also selects one";
    NO_X86_XORSHIFT_DEMANDED_BITS = "no-x86-xorshift-demanded-bits", "TCG_NO_X86_XORSHIFT_DEMANDED_BITS", Shape::Boolean,
        "DISABLE the xorshift demanded-bits rewrite (DEFAULT ON since 2026-10-01: b1_mispredict 1.0959 -> 1.0260, ~60x its noise floor, all 18 programs MATCH, library/core at O3 unchanged). The rewrite lets a consumer that reads only bits [0,k) of `x ^ (x << k)` read `x` instead: shifting left by k cannot change bits below k, so the two agree there and the dependency chain feeding that consumer loses one shift-and-xor. The capability EXISTS in this repo as the AArch64 `xorshift_demanded_bits` (default-ON, credited -9ms of b1's 29ms gap there and independently reproduced at -11ms) and had NO x86 twin -- `x86_loop_top.rs` carried a comment naming it as missing. A direct port fires on nothing: AArch64's producer is one shift-fused `EorRRLsl` with both sources equal, while x86's is the PAIR `ShlRI`+`XorRR` whose operands do NOT match syntactically (b1's measured stream shifts v25 and xors v24, with `MovRR` copies between), and x86 ISel vregs are not SSA so single-def-ness must be checked where SSA gave the AArch64 twin it for free. This is a LATENCY lever, not an instruction-count one: it resolves b1's 50%-mispredicting branch one ALU op earlier";
    TRACE_X86_XORSHIFT_DEMANDED_BITS = "trace-x86-xorshift-demanded-bits", "TCG_X86_XORSHIFT_DB_TRACE", Shape::Boolean,
        "report each xorshift demanded-bits substitution and each consumer declined because its demanded bit range reaches the shift amount (diagnostics; no codegen effect)";
    X86_LOOP_TOP = "x86-loop-top", "TCG_X86_LOOP_TOP", Shape::Boolean,
        "place a two-arm in-loop diamond's LATCH immediately before its HEADER, so the backedge becomes a fall-through and the loop costs ONE taken branch per iteration instead of two (LLVM's `findBestLoopTopHelper` pattern 2, MachineBlockPlacement.cpp:2155-2167). b1_mispredict is the measured case: LLVM lays its loop out [even-arm, latch, header, odd-arm] and pays one taken branch on either path; this backend emits [header, arms, latch] and pays two. The pass re-inverts the latch's own branch pair, because `x86_branch_layout`'s default-ON latch rule puts the backedge on the CONDITIONAL branch -- the exact inverse of what the reorder needs -- so the two rules would otherwise fight on the same block (and at O3 they did, across FIXPOINT iterations, until the latch rule learned that an already-falling-through backedge costs nothing). DEFAULT OFF on a MEASUREMENT, not a guess: it delivers its claim -- b1 goes from two taken branches per iteration to LLVM's one, verified in the disassembly -- and is 4.7% SLOWER anyway (1.0942 -> 1.1453, floors 0.0003/0.0001), because the orientation flips cost 2 instructions (38 -> 40) and a saved taken branch on a perfectly predicted backedge is worth less than that. b1's gap is INSTRUCTION COUNT (38 vs LLVM 33), not branch count";
    TRACE_X86_LOOP_TOP = "trace-x86-loop-top", "TCG_X86_LOOP_TOP_TRACE", Shape::Boolean,
        "report every natural loop the loop-top reorder considers and name the gate each declined candidate fails (silence proves nothing)";
    X86_LATCH_DUP = "x86-latch-dup", "TCG_X86_LATCH_DUP", Shape::Boolean,
        "clone a small loop LATCH into the diamond arm that is not its layout predecessor, so each arm carries its own backedge -- the transform LLVM applies to b1_mispredict (its `main` has two backedges to two targets where this backend emits one). Ported gates: tail has >=2 successors, is a backedge target, <=4 instructions (LLVM's -O3 `TailDupPlacementAggressiveThreshold`), carries no proof obligation or call; every cloned arm is a single-successor unconditional-Jmp predecessor; and `dup + 1 <= succ_size` (LLVM's whole no-profile benefit rule). DEFAULT OFF pending measurement";
    X86_LOOP_SIMPLIFY = "x86-loop-simplify", "TCG_X86_LOOP_SIMPLIFY", Shape::Boolean,
        "insert a UNIQUE loop preheader for every natural loop header with more than one out-of-loop predecessor (LLVM's InsertPreheaderForLoop, preheader half). `find_preheader` requires exactly one non-loop predecessor, so a header fronted by a bounds-check diamond has NO preheader and every loop-consuming pass declines it for CFG shape; p4_matmul's k loop is that case and the tier it blocks keeps the matmul c row in XMM accumulators across the k loop. DEFAULT OFF: it creates blocks, which perturbs layout for every downstream pass";
    TRACE_X86_LOOP_SIMPLIFY = "trace-x86-loop-simplify", "TCG_X86_LOOP_SIMPLIFY_TRACE", Shape::Boolean,
        "report every natural loop's header, depth, out-of-loop predecessors and preheader, and each insertion";
    X86_LATCH_DUP_MAX_INSTS = "x86-latch-dup-max-insts", "TCG_X86_LATCH_DUP_MAX", Shape::Uint,
        "instruction budget for the cloned latch (DEFAULT 4 = LLVM's own post-RA value). At 4 the pass DECLINES b1_mispredict, whose latch is 9 instructions post-RA, so LLVM would decline it too; raising this is a NEW policy needing its own measurement, not a port";
    TRACE_X86_LATCH_DUP = "trace-x86-latch-dup", "TCG_X86_LATCH_DUP_TRACE", Shape::Boolean,
        "trace which loop latches the duplication pass declines and why (silence proves nothing; each decline names its failing gate)";
    X86_LATCH_WINDOW = "x86-latch-window", "TCG_X86_LATCH_WINDOW", Shape::Boolean,
        "let the latch-advance collapse reach ACROSS the loop's other carried copies (and accept the flag-neutral `Lea` spelling of the advance) instead of requiring advance/write-back/compare/branch to be adjacent; DEFAULT OFF on a MEASUREMENT -- it fires on 9 of 18 programs and is a net loss: b1_mispredict 0.39% faster but h3_box_leak 1.7% SLOWER, and h3 is itself still above LLVM";
    NO_X86_SIB_CROSSBLOCK_FLAGS = "no-x86-sib-crossblock-flags", "TCG_NO_X86_SIB_CROSSBLOCK_FLAGS", Shape::Boolean,
        "prove the scale-1 SIB index fold's flag-deadness with the BLOCK-LOCAL scan instead of the cross-block RFLAGS analysis (the isolating A/B lever for that widening; `no-x86-sib-scale1-fold` cannot isolate it, since it disables the whole fold)";
    NO_X86_SIB_SCALE1_FOLD = "no-x86-sib-scale1-fold", "TCG_NO_X86_SIB_SCALE1_FOLD", Shape::Boolean,
        "keep an explicit power-of-two stride multiply feeding a scale-1 SIB instead of folding it into the SIB scale field (the A/B lever for that fold)";
    NO_X86_BCE_EARLYCOPY = "no-x86-bce-earlycopy", "TCG_NO_X86_BCE_EARLYCOPY", Shape::Boolean,
        "disable ONLY the early-guard-copy arm of x86 bounds-check elimination (the shape where both compares read a copy of the loop IV), leaving the rest of the pass on";
    TRACE_X86_BCE = "trace-x86-bce", "TCG_X86_BCE_TRACE", Shape::Boolean,
        "print the CONDITION each bounds-check-elimination candidate declined on (the BRANCH-form path had no trace at all, and the carrier path's only trace was behind a TCG_* env var trustc refuses; diagnostics, no codegen effect)";
    X86_BCE_PTR_RELOAD = "x86-bce-ptr-reload", "TCG_X86_BCE_PTR_RELOAD", Shape::Boolean,
        "admit bounds-check elimination when the guard's and the check's lengths are loaded from the SAME POINTER at the same displacement with no store between (case 5 -- the owning-container shape once the header address is in a register, which the frame-resolving case 4 cannot classify); DEFAULT OFF because this pass removes bounds checks, so a new admission arm is measured before any default is considered";
    NO_X86_BCE_RELOAD = "no-x86-bce-reload", "TCG_NO_X86_BCE_RELOAD", Shape::Boolean,
        "disable ONLY the reloaded-length arm of x86 bounds-check elimination, leaving the rest of the pass on (the lever that isolates what that arm contributes; `no-x86-bce` cannot)";
    TRACE_VECTORIZE_BAIL = "trace-vectorize-bail", "TCG_DBG_REGARG", Shape::Boolean,
        "print the CONDITION each vectorizer recognizer bailed on, instead of only `DECLINED by every recognizer` (diagnostics; no codegen effect)";
    NO_X86_VECTORIZE = "no-x86-vectorize", "TCG_NO_VECTORIZE", Shape::Boolean,
        "disable the SSE2 integer vectorizer entirely (the backend's largest optimization; its NET per-program effect had no reachable lever through the bridge)";
    NO_X86_VECTORIZE_RAISE_SINK = "no-x86-vectorize-raise-sink", "TCG_NO_X86_VECTORIZE_RAISE_SINK", Shape::Boolean,
        "REFUSE to vectorize a loop whose guard failure edge lands in the faithful Rust panic raise, restoring the `[Ud2]`/`[Call abort, Ud2]`-only contract the vectorizer's trap-sink test used before upstream c876e3bd0 made `assert_panic::emit` the unconditional native sink. DEFAULT OFF, i.e. the raise IS admitted: all 10 trap-sink sites in x86_vectorize separately PROVE the guard cannot fail over the range the vector loop replaces -- via block_has_iv_bound_compare (\"provably never traps for iv in [0, n_trip)\"), via classify_guard_compare returning StaticOk or an Inv obligation recorded for the runtime check, or via a matched chase_below_branch guard -- so the edge is unreachable and what its sink contains cannot affect any execution. Admission is by SHAPE (no successors, exactly one call, terminated by Ud2, no stores), never by symbol, because the soundness argument never reads the symbol and matching a Rust mangled name would fail closed on any mangling change. This knob is the A/B lever for that admission and the only way to get the old refusal back";
    NO_X86_VECTORIZE_CONST_BOUND = "no-x86-vectorize-const-bound", "TCG_NO_X86_VECTORIZE_CONST_BOUND", Shape::Boolean,
        "REFUSE to prove a vectorizer CROSS-LENGTH bound discharged by the two bounds being the SAME IMMEDIATE. DEFAULT OFF, i.e. the proof IS used. The fixed-size-array dialect -- `while i < N { a[i] ... }` over `[T; N]` -- materializes N twice (MovRI for the loop test, MovRI for the bounds check), so the bounds are distinct vregs holding one compile-time constant. The existing same_ownlen_by_pointer_reload proves two LOADS read one address and declines that shape with its own self-contradictory message, `bound defs are not the same load opcode (MovRI vs MovRI)` -- the opcodes ARE the same, they are simply not loads; v1_saxpy, v2_memfill and v3_popcount are all const N = 4096 programs and all three died there. The immediate proof needs NO body-containment condition, and that is the point rather than an omission: the load proof must exclude a PREHEADER store separating the two loads (the committed refutation rejects_regarg_stale_preheader_length_reload), while no store can change a constant, so single-def-ness carries it instead. Fails closed on a non-immediate def, differing immediates, differing register classes, a proof carrier, a non-single-def bound, and any def of the same vreg ID in a DIFFERENT class (DefIndex counts are keyed by the full VReg, so single-def-ness alone does not exclude that alias). This knob is the A/B lever for the admission";
    NO_X86_VEC_ZERO_REMAINDER = "no-x86-vec-zero-remainder", "TCG_NO_X86_VEC_ZERO_REMAINDER", Shape::Boolean,
        "KEEP the scalar remainder loop of a vectorized loop even when it provably runs zero iterations. DEFAULT OFF, i.e. an empty remainder is not emitted: when the packed loop is entered with the counter at 0, steps by a constant and is guarded by a constant, its exit value is an exact integer; if that equals the loop's constant trip count and an exact evaluation of the scalar header's own instructions at that counter value (constants, copies, byte zero-extension, AND with an immediate, SETcc, compares; no memory access, no call) leaves the loop, the packed loop hands off to that exit and the unreachable scalar loop is deleted. Every other case keeps the remainder. Wired for the byte-sum / popcount-sum tier. This knob is the A/B lever for the handoff and restores the previous code";
    X86_TWOADDR_EXPAND = "x86-twoaddr-expand", "TCG_X86_TWOADDR_EXPAND", Shape::Boolean,
        "REGISTER the two-address pre-expansion pass in the x86 pipeline. DEFAULT OFF (default-on is refuted at three gate granularities: p7_sieve +43%, p8 +15%). This is the channel the pass was MISSING, not a new lever: the pipeline only constructed it when the `TCG_X86_TWOADDR_EXPAND` env var was set, and trustc refuses every `TCG_*` var, so through the bridge the pass was UNREACHABLE and its two tracked sub-knobs below measured byte-identical on every program because they configure a pass that was never in the schedule";
    X86_TWOADDR_COMMUTE = "x86-twoaddr-commute", "TCG_X86_TWOADDR_COMMUTE", Shape::Boolean,
        "in the two-address pre-expansion, when the LHS is NOT provably dead but the rhs IS and the operation is commutative, tie the destination to the dying rhs instead of declining. ADDITIVE: it fires only on candidates the pass already declines, so every candidate it acts on today keeps the un-commuted tie -- which is why it is not the variant the module doc refutes at +24% on p1, and p1_xorshift is byte-identical with it on";
    X86_TWOADDR_EXPAND_ALL = "x86-twoaddr-expand-all", "TCG_X86_TWOADDR_EXPAND_ALL", Shape::Boolean,
        "lift the two-address pre-expansion's LOOP-SCOPE CALL GATE and expand in every block, not only in loops that already pay call overhead. The gate exists because the pass measured p7_sieve +43% and p8 +15% on tight call-free loops; its own note kept the lift \"for future suite A/Bs\" but its only channel was a TCG_* env var trustc refuses, so that A/B had never been run through the bridge";
    X86_SAXPYQ_SCALAR_MUL = "x86-saxpyq-scalar-mul", "TCG_X86_SAXPYQ_SCALAR_MUL", Shape::Boolean,
        "compute the saxpy-Q row-register nest's lane products with two pipelined scalar IMULs plus a MOVQ/PUNPCKLQDQ pack instead of the PACKED PMULUDQ/PSLLQ/PSRLQ compose. The scalar route was DEFAULT ON until 2026-09-29 on a claim now WITHDRAWN: measured, the packed compose is 0.88% FASTER on p4_matmul (the only program where the tier fires) and LLVM itself emits the compose there";
    NO_X86_VEC_OWNLEN_RELOAD = "no-x86-vec-ownlen-reload", "TCG_NO_X86_VEC_OWNLEN_RELOAD", Shape::Boolean,
        "demand EXACT register identity for the reduction vectorizer's own-length rule instead of proving it for two loads from the SAME address in a write-free loop (the `while k < v.len()` shape over an owning `Vec`). DEFAULT ON since 2026-09-29; this is the forensic opt-out";
    NO_X86_VEC_BOUND_REMAT = "no-x86-vec-bound-remat", "TCG_NO_X86_VEC_BOUND_REMAT", Shape::Boolean,
        "keep the OLD refusal of a vectorizable reduction whose TRIP BOUND is a load in the loop header, instead of rematerializing the header's bound-computing prefix into fresh vregs in the vector preheader. DEFAULT ON since 2026-09-29 -- with the own-length proof and the post-SROA run it takes h1_vec_push_sum from 2.4890x to 1.0023x LLVM, a 2.63x speedup; this is the forensic opt-out";
    NO_X86_VEC_REGARG = "no-x86-vec-regarg", "TCG_NO_X86_VEC_REGARG", Shape::Boolean,
        "disable the reg-arg/saxpy-q reduction tier only, keeping the rest of the vectorizer (an attribution control; vector opcodes alone do not identify the recognizer)";
    NO_VECTORIZE_POST_SROA = "no-vectorize-post-sroa", "TCG_NO_VECTORIZE_POST_SROA", Shape::Boolean,
        "do NOT run the SSE2 integer vectorizer a second time after SROA, where an owning-container reduction first has a recognisable shape (its slice temp promoted, and the peephole not yet having re-spelled the header test or the element address). DEFAULT ON since 2026-09-29 -- it is what lets that shape reach the recognizers at all; this is the forensic opt-out";
    VECTORIZE_LATE = "vectorize-late", "TCG_VECTORIZE_LATE", Shape::Boolean,
        "additionally run the SSE2 integer vectorizer a second time after SROA/LICM/peephole/BCE, where an owning-container reduction first has a recognisable shape (DEFAULT OFF; A/B lever)";
    NO_X86_BCE = "no-x86-bce", "TCG_NO_X86_BCE", Shape::Boolean,
        "keep every x86 bounds check instead of eliding one a dominating identical compare proves dead (always correct, never faster; the A/B lever for a safety-critical pass)";

    // ---- refinement lane
    REFINE = "refine", "TCG_REFINE", Shape::Boolean,
        "emit per-rvalue refinement obligations";
    P3C_REFINE = "p3c-refine", "TCG_P3C_REFINE", Shape::Boolean,
        "emit per-rvalue refinement obligations (P3c spelling; same effect as `refine`)";
    REFINE_FAST = "refine-fast", "TCG_REFINE_FAST", Shape::Boolean,
        "use the fast refinement encoding";
    REFINE_SOLVER = "refine-solver", "TCG_REFINE_SOLVER", Shape::Boolean,
        "`refine-solver=0` opts the bridge's refinement lane out of the SMT solver (PARTIAL: trust-cg-verify's own opt-out is not reachable from here, so it keeps discharging)";

    // ---- codegen shape / batching
    BATCH_CGU = "batch-cgu", "TCG_BATCH_CGU", Shape::Boolean,
        "`batch-cgu=0` restores the legacy per-function compile loop (default: batched)";
    BATCH_PARALLEL = "batch-parallel", "TCG_BATCH_PARALLEL", Shape::Boolean,
        "`batch-parallel=0` compiles a batched CGU serially (default: parallel)";
    OPT_LEVEL = "opt-level", "TCG_OPT_LEVEL", Shape::OneOf(&["0", "1", "2", "3"]),
        "`opt-level=0|1|2|3` overrides the backend pass pipeline level (default: follow `-C opt-level`)";
    SLOT_ARRAY_MIN_LANES = "slot-array-min-lanes", "TCG_SLOT_ARRAY_MIN_LANES", Shape::Uint,
        "fewest lanes before a memory slot is spelled as an array rather than a tuple (default: 1)";
    ARTIFACT_CACHE_DIR = "artifact-cache-dir", "TCG_ARTIFACT_CACHE_DIR", Shape::Free,
        "directory for the AOT compile-artifact cache (a value containing whitespace cannot be spelled here)";
    DUMP_TRUST_IR = "dump-trust-ir", "TCG_DUMP_TRUST_IR", Shape::Free,
        "write every CGU's TrustIR module (the exact input of its object compile) as a binary container plus a JSON sidecar of the compile settings under this directory; changes no decision (a value containing whitespace cannot be spelled here)";
    DUMP_AARCH64_PREPARED = "dump-aarch64-prepared", "TCG_DUMP_AARCH64_PREPARED", Shape::Free,
        "write the admitted AArch64 module and its actual prepared LIR, machine, proof-context and frame diagnostics before certificate generation; untrusted snapshots grant no proof or encoding authority and change no verdict (a value containing whitespace cannot be spelled here)";

    // ---- resource budgets
    PROOF_WALK_WORKERS = "proof-walk-workers", "TCG_PROOF_WALK_WORKERS", Shape::CheckedAtUse,
        "positive worker count for the certificate walk's large-stack pool (default: 1)";
    MAX_PARALLELISM = "max-parallelism", "TRUST_CG_MAX_PARALLELISM", Shape::CheckedAtUse,
        "positive ceiling on Trust Codegen-owned CPU fanout";

    // ---- diagnostics that change no decision
    BRIDGE_NOTES = "bridge-notes", "TCG_BRIDGE_NOTES", Shape::Boolean,
        "print the bridge's development notes to stderr";
    SOLVE_TRACE = "solve-trace", "TCG_SOLVE_TRACE", Shape::Boolean,
        "print one line per SMT solve (obligation, wall time, query size) to stderr";
    BACKEDGE_TRACE = "backedge-trace", "TCG_BACKEDGE_TRACE", Shape::Boolean,
        "print both sides of every back-edge edge-equality obligation (the \
         structural-identity lane is an exact tree compare, so this names the \
         differing subterm behind a [TCG-SSA-071] refusal)";
    X86_BODY_TRACE = "x86-body-trace", "TCG_X86_BODY_TRACE", Shape::Boolean,
        "print one line per x86-64 function the source-bound body lane classifies (its refusal reason, or its bound rows and replay outcome) to stderr";
    X86_BODY_DUMP = "x86-body-dump", "TCG_X86_BODY_DUMP", Shape::Free,
        "directory to write the replayed SMT2 query of every x86-64 body theorem that does not replay Valid into (a value containing whitespace cannot be spelled here)";
    OPCODE_INVENTORY_TRACE = "opcode-inventory-trace", "TCG_TRACE_OPCODE_INVENTORY", Shape::Boolean,
        "print every function's emitted-opcode inventory census lines (one per row that blocks proof promotion, with its reason) to stderr";
    EH_OBLIGATION_TRACE = "eh-obligation-trace", "TCG_TRACE_EH_OBLIGATIONS", Shape::Boolean,
        "print the exception-table obligation report (functions, unwind points, invokes, landing pads) of every AArch64 Darwin object the emission gate decides to stderr";
    MEMORY_EFFECT_REPLAY = "memory-effect-replay", "TCG_MEMORY_EFFECT_REPLAY", Shape::Boolean,
        "replay every part of each uncredited AArch64 memory row's word-bound memory-effect decomposition live (AY, then Clean) and report how many parts have a Clean-checked certificate. Diagnostic: the decomposition is never proof credit, so the default skips the solve";
    DIAG_JSON = "diag-json", "TCG_DIAG_JSON", Shape::Boolean,
        "additionally emit one structured JSON object per fail-closed event";
    DIAG_DUMP = "diag-dump", "TCG_DIAG_DUMP", Shape::Boolean,
        "dump the offending trust-ir function on an SSA/loop-completeness refusal";
    DIAG_STMTS = "diag-stmts", "TCG_DIAG_STMTS", Shape::Boolean,
        "trace per-statement lowering decisions";
    BRIDGE_COVERAGE = "bridge-coverage", "TCG_BRIDGE_COVERAGE", Shape::Boolean,
        "print the per-function MIR-shape coverage manifest";
    BRIDGE_COVERAGE_STRICT = "bridge-coverage-strict", "TCG_BRIDGE_COVERAGE_STRICT", Shape::Boolean,
        "fail the compile closed on any unmodeled MIR shape (implies the manifest)";
    TIME = "time", "TCG_TIME", Shape::Boolean,
        "print backend phase timings";
    TIME_SWEEP = "time-sweep", "TCG_TIME_SWEEP", Shape::Boolean,
        "print proof-sweep timings";
    TIME_LOWER = "time-lower", "TCG_TIME_LOWER", Shape::Boolean,
        "print per-function lowering stage timings";
    TIME_CODEGEN = "time-codegen", "TCG_TIME_CODEGEN", Shape::Count { default: 10 },
        "`time-codegen[=N]` lists the N slowest mono items (default N: 10; `0`/`off`/`false` disables)";
    TRACE_VECTORIZE = "trace-vectorize", "TCG_TRACE_VECTORIZE", Shape::Boolean,
        "trace the x86 SSE2 vectorizer's per-loop accept/decline decisions";
    TRACE_VECTORIZE_DUMP = "trace-vectorize-dump", "TCG_TRACE_VECTORIZE_DUMP", Shape::Boolean,
        "dump every natural loop's raw post-ISel body for x86 vectorizer triage";
    NO_LICM_POINTER_LOADS = "no-licm-pointer-loads", "TCG_NO_LICM_POINTER_LOADS", Shape::Boolean,
        "disable LICM's POINTER-BASE invariant-load arm (DEFAULT ON since 2026-09-29: h3_box_leak hot loop 14 -> 10 insns, 6 -> 3 memory ops, 8.8% faster, 1.0954x -> 0.9993x LLVM; the old 1.46x-slower reading was on h1_vec_push_sum, which now vectorizes and is byte-identical under this arm)";
    NO_X86_AGREEING_LANE_POINTEE = "no-x86-agreeing-lane-pointee", "TCG_NO_X86_AGREEING_LANE_POINTEE", Shape::Boolean,
        "decline a `(*r).field...` thin-reference pointee that is an all-scalar-leaf struct/tuple whose DECLARATION-ORDER trust-ir lane offsets AGREE with rustc's field offsets at every field. Admitting it is address-neutral by construction (both models compute the same address, so there is no order to switch), and it closed the LAST `library/core` root at -Copt-level=3, `<VaListInner as Debug>::fmt`. This is the forensic opt-out";
    NO_X86_THIN_REF_AGGREGATE_ADDR = "no-x86-thin-ref-aggregate-addr", "TCG_NO_X86_THIN_REF_AGGREGATE_ADDR", Shape::Boolean,
        "restrict the ADDRESS-ONLY thin-reference-to-aggregate arm of `Rvalue::Ref` back to aarch64 Linux. That arm takes a memory-eligible pointee's field address WITHOUT asking for a scalar trust-ir leaf type; the fallback computes a leaf it then discards, and that query fails closed on an array-wrapping pointee (`&self.ip` where `ip: Ipv4Addr { octets: [u8; 4] }` in `<SocketAddrV4 as Display>::fmt`, and `[u8; 16]` for SocketAddrV6 -- two `library/core` roots). Admitted on x86-64 Linux since 2026-09-29 and on x86-64 macOS since 2026-09-30; this is the forensic opt-out";
    NO_X86_ENTRY_REF_FIELD_ADDR = "no-x86-entry-ref-field-addr", "TCG_NO_X86_ENTRY_REF_FIELD_ADDR", Shape::Boolean,
        "decline `*cell = &(*arg).f...` where `arg` is an untouched thin `&T`/`&mut T` entry argument and the stored value is the field's address `arg + layout offset` (restores the deref-store refusal `projected source's base is not a reference to a memory-eligible aggregate`: the one x86-64 macOS `library/core` lowering root, `<VaListInner as Debug>::fmt`, whose derived `&&self.reg_save_area` cells the field reference). This is the forensic opt-out";
    NO_X86_REF_REFERENT_CELL = "no-x86-ref-referent-cell", "TCG_NO_X86_REF_REFERENT_CELL", Shape::Boolean,
        "on x86-64, do NOT give a thin `&T` referent its own scalar cell when a `&raw` of it is taken (restores the pre-2026-09-29 refusal; the capability was gated to aarch64-linux with no stated reason and the gate cost four library/core roots at -Copt-level=3)";
    A64_LOOP_HEAD_ALIGN = "a64-loop-head-align", "TCG_LOOP_HEAD_ALIGN", Shape::Boolean,
        "on AArch64, restore the 32-byte innermost-loop-head NOP padding and 32-byte placement of loop-bearing functions (DEFAULT OFF since 2026-09-30: no measured runtime benefit, and 39.6 emitted bytes per beat-llvm corpus program on average, 0.951x -> 1.005x LLVM -O3 emitted-code geomean; this is the A/B lever that re-emits the previous layout)";
    NO_X86_LOOP_HEAD_ALIGN = "no-x86-loop-head-align", "TCG_NO_X86_LOOP_HEAD_ALIGN", Shape::Boolean,
        "disable the loop-head 64-byte containment aligner AND its 64-byte function/section alignment (DEFAULT ON; the pass can only see function-relative offsets, so the two must move together or the aligner targets the wrong grid)";
    X86_LOOP_ALIGN_SEAM_PAD = "x86-loop-align-seam-pad", "TCG_X86_LOOP_ALIGN_SEAM_PAD", Shape::Uint,
        "pad budget in bytes at a LIVE fall-through seam. DEFAULT is the same budget as at a dead seam (63); it WAS 0 = refuse until 2026-09-29, and that refusal is what measured 14.8% on h3_box_leak. Pass 0 to restore the refusal";
    X86_SROA_MULTI_BLOCK = "x86-sroa-multi-block", "TCG_X86_SROA_MULTI_BLOCK", Shape::Boolean,
        "enable the multi-BLOCK writer tier of x86 SROA (promote a stack slot written from more than one block). DEFAULT OFF and, until 2026-09-30, env-only and therefore never measured through the bridge";
    NO_CONST_ADDR_UNROLL = "no-const-addr-unroll", "TCG_NO_CONST_ADDR_UNROLL", Shape::Boolean,
        "disable const-address loop unrolling. DEFAULT ON and, until 2026-09-30, env-only. Unrolling a constant-trip inner loop DESTROYS the loop the vectorizer needs: p4_matmul with `get_unchecked` arrives at the vectorizer already unrolled by 24 (stride 0x18, 96 scalar imul, ZERO pmuludq) and loses 1.90x, where the checked build keeps an 8-element loop with 12 pmuludq";
    NO_PARTIAL_UNROLL = "no-partial-unroll", "TCG_NO_PARTIAL_UNROLL", Shape::Boolean,
        "disable PARTIAL loop unrolling. DEFAULT ON and, until 2026-09-30, env-only, so its interaction with the vectorizer could not be measured through the bridge";
    RUNTIME_PARTIAL_UNROLL = "runtime-partial-unroll", "TCG_RUNTIME_PARTIAL_UNROLL", Shape::Boolean,
        "enable runtime partial loop unrolling (trip count not known at compile time). DEFAULT OFF and, until 2026-09-30, env-only and therefore never measured through the bridge";
    X86_LICM_GUARDED_HOIST = "x86-licm-guarded-hoist", "TCG_X86_LICM_GUARDED_HOIST", Shape::Boolean,
        "enable the GUARDED-HOIST tier of x86 LICM. DEFAULT OFF and, until 2026-09-30, env-only and therefore never measured through the bridge";
    X86_BCE_CARRIER = "x86-bce-carrier", "TCG_X86_BCE_CARRIER", Shape::Boolean,
        "enable the CARRIER arm of x86 bounds-check elimination. DEFAULT OFF and, until 2026-09-30, env-only and therefore never measured through the bridge";
    AND_CMP_FUSE_RR = "and-cmp-fuse-rr", "TCG_AND_CMP_FUSE_RR", Shape::Boolean,
        "enable the register-register form of AND/CMP fusion. DEFAULT OFF and, until 2026-09-30, env-only and therefore never measured through the bridge";
    X86_SPILL_RELOAD_CSE_XBLOCK = "x86-spill-reload-cse-xblock", "TCG_SPILL_RELOAD_CSE_XBLOCK", Shape::Boolean,
        "enable the CROSS-BLOCK solve in spill/reload CSE, not just the block-local one. DEFAULT OFF and, until 2026-09-30, env-only and therefore never measured through the bridge. h4_vec_dropper's recorded gap is attributed to post-RA spill reloads, which is the shape this tier addresses";
    X86_VEC_UNROLL_K = "x86-vec-unroll-k", "TCG_X86_VEC_UNROLL_K", Shape::Uint,
        "unroll factor K for the SSE2 vectorizer's reg-arg PADDQ reduction: the number of INDEPENDENT packed accumulators the hot body emits per iteration, over K*2 i64 elements. DEFAULT 2, clamped DOWN to {1,2,4,8} (never widened -- the packed-body gate `len & -(K*2)` is only correct for a power of two). Multiple accumulators break the serial PADDQ dependency chain. Until 2026-09-30 the only channels were the `TCG_*` variables trustc refuses, so the unroll factor of the backend's LARGEST optimization (the vectorizer, measured at 3x-54x here) had never been swept through the bridge, and its \"Default K=2 ... LLVM-parity structure\" claim had never been checked against LLVM on this host";
    X86_LOOP_ALIGN_MAX_BODY = "x86-loop-align-max-body", "TCG_X86_LOOP_ALIGN_MAX_BODY", Shape::Uint,
        "largest loop body in bytes the aligner will try to contain (DEFAULT 64; `=0` disables all padding while LEAVING the 64-byte function alignment, which is the arm that separates the pass from the placement re-roll)";
    X86_LOOP_ALIGN_MAX_SKIP = "x86-loop-align-max-skip", "TCG_X86_LOOP_ALIGN_MAX_SKIP", Shape::Uint,
        "largest pad in bytes the aligner will insert (DEFAULT 63)";
    TRACE_X86_LOOP_ALIGN = "trace-x86-loop-align", "TCG_X86_LOOP_ALIGN_LOG", Shape::Boolean,
        "print the loop-head aligner's per-function decision census (heads, pads, and each decline reason) to stderr";
    NO_X86_RELOAD_ELIDE = "no-x86-reload-elide", "TCG_NO_X86_RELOAD_ELIDE", Shape::Boolean,
        "disable post-RA redundant spill-reload elision (DEFAULT ON: the spiller emits each instruction's reloads with no memory of the previous instruction's, so consecutive uses of one spilled vreg each reload the same slot into the same scratch)";
    X86_SR_FLAG_SAFE_SEED = "x86-sr-flag-safe-seed", "TCG_X86_SR_FLAG_SAFE_SEED", Shape::Boolean,
        "let x86 strength reduction place its seed multiply EARLIER in the preheader, behind a full flag overwriter, instead of only immediately before the terminator. Without it the pass declines every loop whose preheader ends `cmp; jcc` -- which `trace-x86-strength-reduce` showed was keeping it off BOTH hot loops of p4_matmul, the program its own doc names as the canonical win. DEFAULT OFF because it is a MEASURED REGRESSION: enabling it takes p4 from 1.0800 to 1.0926 vs LLVM -O3 (pass off is 1.0864), since the recurrence carrier is live across the whole k loop and adds register pressure to a tight SIMD body -- the same wall LICM's pointer-base hoisting hit. Kept opt-in because the reduction may pay on a loop that is not register-starved";
    NO_X86_STRENGTH_REDUCE = "no-x86-strength-reduce", "TCG_NO_STRENGTH_REDUCE", Shape::Boolean,
        "disable x86 induction-variable strength reduction (OPT-3a), which rewrites a loop-body `imul iv, const-stride` into an add recurrence. DEFAULT ON, and its contribution had never been measured through the bridge: the only channel was the `TCG_NO_STRENGTH_REDUCE` env var, which trustc refuses. Its own doc names p4_matmul's `a[i*N + k]` (stride 24, not SIB-encodable) as the canonical win, yet p4's k-loop body still carries 5 `imul`, so it is declining somewhere -- use `trace-x86-strength-reduce` to see which condition";
    TRACE_X86_STRENGTH_REDUCE = "trace-x86-strength-reduce", "TCG_TRACE_X86_STRENGTH_REDUCE", Shape::Boolean,
        "print, per loop, whether x86 strength reduction found a candidate and -- for each candidate multiply it rejected -- WHICH side condition declined it (preheader flags live, no induction variable, flags live after the multiply, iv not defined at the preheader, SIB-legal scale, immediate out of i32, or the algebraic obligation undischarged). The pass has 52 decline points and no diagnostics; this is the sibling of `trace-vectorize-bail` (diagnostics only, no codegen effect)";
    NO_X86_SLOT_FORWARD = "no-x86-slot-forward", "TCG_NO_X86_SLOT_FORWARD", Shape::Boolean,
        "disable x86 frame-slot value forwarding (DEFAULT ON: store-to-load and load-to-load reuse through directly-addressed fixed slots, the shape SROA cannot see because it has no materialized address root)";
    TRACE_X86_SLOT_FORWARD = "trace-x86-slot-forward", "TCG_TRACE_X86_SLOT_FORWARD", Shape::Boolean,
        "trace x86 frame-slot value forwarding decisions (per-load forward, delete and record)";
    SROA_TRACE = "sroa-trace", "TCG_X86_SROA_TRACE", Shape::Boolean,
        "trace the x86 SROA pass's per-slot decline reasons and escape details";
    REFINE_TRACE = "refine-trace", "TCG_REFINE_TRACE", Shape::Boolean,
        "trace refinement obligation construction and discharge";
    VC_TRACE = "vc-trace", "TCG_VC_TRACE", Shape::Boolean,
        "trace verification-condition construction";
    BIV_TRACE = "biv-trace", "TCG_BIV_TRACE", Shape::Boolean,
        "trace basic-induction-variable recognition";
    MUTRELOAD_TRACE = "mutreload-trace", "TCG_MUTRELOAD_TRACE", Shape::Boolean,
        "trace the mutable-reload analysis";
    BATCH_TRACE = "batch-trace", "TCG_BATCH_TRACE", Shape::Boolean,
        "trace CGU batching decisions";
    TRACE_TY = "trace-ty", "TCG_TRACE_TY", Shape::Boolean,
        "trace type lowering";
    TYCYCLE_TRACE = "tycycle-trace", "TCG_TYCYCLE_TRACE", Shape::Boolean,
        "trace recursive-type cycle breaking";
    TRACE_MERGE_ERRORS = "trace-merge-errors", "TRUST_CG_TRACE_MERGE_ERRORS", Shape::Boolean,
        "print the reason a CGU merge was declined";
    NO_WASM_LOCAL_OPT = "no-wasm-local-opt", "TCG_NO_WASM_LOCAL_OPT", Shape::Boolean,
        "kill switch for both of the wasm32 lane's optimizations: compiles at O0, so neither the trust-ir mid-end nor the translation-validated local emission pass runs, and every function keeps its baseline body, the bytes the lane emits at O0 (use no-wasm-irmid to switch off the mid-end alone)";
    TRACE_WASM_LOCAL_OPT = "trace-wasm-local-opt", "TCG_TRACE_WASM_LOCAL_OPT", Shape::Boolean,
        "print, per wasm32 codegen unit, the local emission pass's summary as one JSON line: functions emitted with a rewritten body its translation validator accepted, and functions that kept their baseline body, by reason (diagnostics; the emitted bytes are the same)";
    NO_WASM_IRMID = "no-wasm-irmid", "TCG_NO_WASM_IRMID", Shape::Boolean,
        "kill switch for the wasm32 lane's trust-ir mid-end (copy propagation, pointer chain to byte-offset GEP, constant-branch folding, pure dead-code elimination, single-dominating-store forwarding, dead-slot removal, constant-table promotion, each rewrite kept only when its witness checker and interpreter differential accept it): the lane lowers the module as the bridge produced it; the local emission pass still runs at O1 and above (the mid-end already does not run at O0)";
    NO_WASM32_PLACE_GEP = "no-wasm32-place-gep", "TCG_NO_WASM32_PLACE_GEP", Shape::Boolean,
        "kill switch for the wasm32 MIR lowering's in-bounds address GEPs: at backend level O1 and above (`-C opt-level`, or the `opt-level` knob when set) a constant-offset field, constant-index, accessed-place or vtable-slot address is otherwise spelled `gep inbounds u8 base, [k]` (Rust guarantees it in bounds, so the lane may fold `k` into a memarg offset under the GEP's no-wrap premise); with this knob every such address stays the integer chain `inttoptr(ptrtoint(base) + k)` the lowering emits on every other target and at backend level O0";
    TRACE_WASM_IRMID = "trace-wasm-irmid", "TCG_TRACE_WASM_IRMID", Shape::Boolean,
        "print, per wasm32 codegen unit, the trust-ir mid-end's report as one JSON line: passes run, functions changed, rollbacks with their reasons, skipped functions, proof-table transport and interpreter-differential coverage, and whether its output was lowered (diagnostics; the emitted bytes are the same)";

    // ---- test-only shaping
    TEST_SKIP_LANG_START = "test-skip-lang-start", "TRUST_CG_TEST_SKIP_LANG_START", Shape::Boolean,
        "skip lowering `lang_start` (test fixtures only)";
}

impl Shape {
    /// The value grammar in one column, for the accepted-knobs listing.
    fn spelling(self) -> &'static str {
        match self {
            Shape::Boolean => "[=BOOL]",
            Shape::OneOf(_) => "=ONE-OF",
            Shape::Uint => "=N",
            Shape::Count { .. } => "[=N]",
            Shape::Free => "=TEXT",
            Shape::CheckedAtUse => "=N",
        }
    }
}

/// The knobs this compilation was given, keyed by knob key.
///
/// A knob written bare (`no-proof-certs`) stores the value `"1"`, so every call
/// site can keep the exact predicate it used against the environment variable —
/// `TCG_X=1` was the universal spelling in this workspace — and the
/// value-carrying knobs (`refine-solver=0`, `opt-level=2`) keep reading their
/// value the same way.
#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq)]
pub(crate) struct BackendKnobs {
    entries: BTreeMap<&'static str, String>,
}

impl BackendKnobs {
    /// The empty knob set: every knob absent, i.e. the fully checked default
    /// lane. This is what a reader sees before `install` and on a compiler that
    /// does not carry `-Ztrust-ir-cg-args`.
    const fn empty() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    /// Parse one `-Ztrust-ir-cg-args` list.
    ///
    /// Each item is `key` (meaning `key=1`) or `key=value`. An unknown key is
    /// refused, and so is a key repeated with a DIFFERENT value: two spellings
    /// of one knob have no defined precedence, and guessing one would be a wrong
    /// answer where a refusal is available.
    ///
    /// A key repeated with the SAME value is accepted, because it is not
    /// ambiguous — there is exactly one thing it can mean. `-Ztrust-ir-cg-args`
    /// flags concatenate, so a caller that composes a base list with an overlay
    /// legitimately produces one; refusing that would buy no safety and would
    /// make knob lists brittle to build.
    fn parse(args: &[String]) -> Result<Self, String> {
        let mut entries: BTreeMap<&'static str, String> = BTreeMap::new();
        for arg in args {
            // `None` here is the BARE spelling (`no-proof-certs`), which is not
            // the same thing as an empty value (`artifact-cache-dir=`): the
            // first means "the knob's on-value", the second is a value of its
            // own. Canonicalization below is told which it saw.
            let (key, value) = match arg.split_once('=') {
                Some((key, value)) => (key, Some(value)),
                None => (arg.as_str(), None),
            };
            let Some(knob) = ACCEPTED.iter().find(|knob| knob.key == key) else {
                return Err(unknown_key_message(key));
            };
            // The VALUE GRAMMAR is checked here, once, and the stored value is
            // canonical from this point on. This is the whole of the
            // `no-proof-certs=0` fix: a spelling the knob does not accept is a
            // refusal, and an accepted one is normalized so no call site has to
            // re-decide what it meant.
            let value = canonical_value(knob, value)?;
            let previous = entries.insert(knob.key, value.clone());
            if previous
                .as_deref()
                .is_some_and(|previous| previous != value)
            {
                let previous = previous.unwrap_or_default();
                return Err(format!(
                    "-Ztrust-ir-cg-args knob `{key}` was given twice with different values \
                     (`{previous}` and `{value}`)\n\
                     note: two values for one knob have no defined precedence, so the backend \
                     refuses rather than pick one\n\
                     help: pass `{key}` once with the value you want; repeated \
                     `-Ztrust-ir-cg-args` flags are concatenated, so check every one of them"
                ));
            }
        }
        Ok(Self { entries })
    }

    /// The knob's CANONICAL value, or `None` when the knob was not given.
    ///
    /// For a [`Shape::Boolean`] knob this is `"1"` or `"0"` and nothing else, so
    /// a boolean must be read through [`is_enabled`] / [`is_disabled`] rather
    /// than through presence. `raw` stays for the value-carrying knobs.
    fn raw(&self, key: &str) -> Option<&str> {
        self.entries.get(key).map(String::as_str)
    }
}

/// The canonical stored value for one knob occurrence, or the refusal.
///
/// `given` is `None` for the BARE spelling. Every refusal names the accepted
/// spellings for that knob's shape, because "invalid value" with no next step is
/// a defect (design principle 10).
fn canonical_value(knob: &Knob, given: Option<&str>) -> Result<String, String> {
    match knob.shape {
        Shape::Boolean => match given {
            None => Ok("1".to_owned()),
            Some(value) => match value.trim() {
                "1" | "true" | "on" | "yes" => Ok("1".to_owned()),
                "0" | "false" | "off" | "no" => Ok("0".to_owned()),
                other => Err(bad_value_message(
                    knob,
                    other,
                    "a boolean: `1`, `true`, `on` or `yes` to turn it ON; `0`, `false`, \
                     `off` or `no` to turn it OFF; or the bare key `{key}`, which means ON",
                )),
            },
        },
        Shape::OneOf(accepted) => match given {
            // A fixed-set knob has no meaningful ON value, so the bare spelling
            // is a refusal rather than a guess at which member was meant.
            None => Err(bad_value_message(
                knob,
                "",
                "one of `{alternatives}` — this knob has no bare spelling",
            )),
            Some(value) if accepted.contains(&value.trim()) => Ok(value.trim().to_owned()),
            Some(other) => Err(bad_value_message(knob, other, "one of `{alternatives}`")),
        },
        Shape::Uint => match given.map(str::trim) {
            Some(value) if value.parse::<usize>().is_ok() => Ok(value.to_owned()),
            other => Err(bad_value_message(
                knob,
                other.unwrap_or(""),
                "a base-10 non-negative integer, as `{key}=N`",
            )),
        },
        Shape::Count { default } => match given.map(str::trim) {
            None | Some("1") | Some("on") | Some("true") => Ok(default.to_string()),
            Some("") | Some("0") | Some("off") | Some("false") => Ok("0".to_owned()),
            Some(value) if value.parse::<usize>().is_ok() => Ok(value.to_owned()),
            Some(other) => Err(bad_value_message(
                knob,
                other,
                "a base-10 count `{key}=N`; `0`, `off` or `false` to disable; or the bare \
                 key / `on` / `true` for the default count",
            )),
        },
        // Every value is meaningful and there is nothing to normalize. A BARE
        // spelling is the empty value, which is what the call site's own
        // emptiness filter already handles.
        Shape::Free => Ok(given.unwrap_or("").to_owned()),
        // Stored verbatim; the read site owns the grammar and its refusal.
        Shape::CheckedAtUse => Ok(given.unwrap_or("1").to_owned()),
    }
}

/// The refusal for a value the knob's shape does not accept. `expected` may use
/// `{key}` for the knob key and `{alternatives}` for a `OneOf` list.
fn bad_value_message(knob: &Knob, given: &str, expected: &str) -> String {
    let alternatives = match knob.shape {
        Shape::OneOf(accepted) => accepted.join("`, `"),
        _ => String::new(),
    };
    let expected = expected
        .replace("{key}", knob.key)
        .replace("{alternatives}", &alternatives);
    format!(
        "`-Ztrust-ir-cg-args` knob `{key}` was given the value `{given}`, which it does not \
         accept\n\
         note: {key} — {help}\n\
         help: it takes {expected}\n\
         help: or drop the knob entirely — every knob is optional and the backend's default \
         is the fully checked lane",
        key = knob.key,
        help = knob.help,
    )
}

/// The knob list this compilation was given. `None` until `install` runs.
static KNOBS: OnceLock<BackendKnobs> = OnceLock::new();

/// The fully checked default lane, handed out before `install` and on a
/// compiler without the option. Never mutated.
static DEFAULTS: BackendKnobs = BackendKnobs::empty();

/// The knob set in force. See the fail-closed argument in the module doc: the
/// pre-`install` answer is the DEFAULT lane, never a guess.
fn knobs() -> &'static BackendKnobs {
    KNOBS.get().unwrap_or(&DEFAULTS)
}

/// The knob's value, or `None` when it was not given. Replaces `env::var_os`.
pub(crate) fn raw(key: &str) -> Option<&'static str> {
    knobs().raw(key)
}

/// Is this [`Shape::Boolean`] knob ON?
///
/// `true` only for a knob given as bare / `=1` / `=true` / `=on` / `=yes`; false
/// when absent AND when explicitly turned off. This is the reader for a
/// DEFAULT-OFF knob.
///
/// It replaces `raw(key).is_some()`, which was the `no-proof-certs=0` fail-open:
/// presence is not truth once a knob can carry a value, and the parse table
/// above now guarantees a boolean's stored value is exactly `"1"` or `"0"`.
pub(crate) fn is_enabled(key: &str) -> bool {
    raw(key) == Some("1")
}

/// Is this [`Shape::Boolean`] knob EXPLICITLY OFF?
///
/// The reader for a DEFAULT-ON knob, whose `=0` is the kill switch
/// (`batch-cgu`, `batch-parallel`, `refine-fast`, `refine-solver`). Absent is
/// `false` — the knob keeps its default — so "not disabled" is the right way to
/// spell "still on".
pub(crate) fn is_disabled(key: &str) -> bool {
    raw(key) == Some("0")
}

/// The refusal for a key the table does not carry: it names every accepted key
/// with what it does, and the legacy variable it replaces, so a reader who
/// knows the old name can find the new one (design principle 10).
fn unknown_key_message(key: &str) -> String {
    let mut message = format!("unknown `-Ztrust-ir-cg-args` knob `{key}`\n");
    // A near-miss is by far the likeliest cause, and naming it first saves the
    // reader scanning forty rows. Offered, never applied.
    if let Some(close) = closest_key(key) {
        message.push_str(&format!(
            "help: a knob named `{close}` exists; did you mean it?\n"
        ));
    }
    if let Some(stripped) = strip_legacy_env_spelling(key) {
        message.push_str(&format!(
            "help: `{key}` is an environment-variable spelling; this option takes the knob key \
             `{stripped}`\n"
        ));
    }
    message.push_str("note: the accepted knobs are\n");
    for knob in ACCEPTED {
        message.push_str(&format!(
            "        {:<26} {:<9} {}  (was `{}`)\n",
            knob.key,
            knob.shape.spelling(),
            knob.help,
            knob.legacy_env
        ));
    }
    message.push_str(
        "help: pass `key` or `key=value`, space-separated; or drop the knob — every knob is \
         optional and the backend's default is the fully checked lane",
    );
    message
}

/// `TCG_NO_PROOF_CERTS` -> `no-proof-certs`, when that IS an accepted key.
///
/// Someone migrating a script reaches for the old name first; this turns the
/// generic refusal into the exact edit. `None` when the input is not a legacy
/// spelling of a knob we accept, so the hint never fires on a guess.
fn strip_legacy_env_spelling(key: &str) -> Option<&'static str> {
    let upper = key.to_ascii_uppercase();
    ACCEPTED
        .iter()
        .find(|knob| knob.legacy_env == upper)
        .map(|knob| knob.key)
}

/// The accepted key within edit distance 2 of `key`, if exactly one is closest.
///
/// Pure suggestion: it is printed, never applied, so a bad suggestion costs a
/// line of output and cannot change a compile.
fn closest_key(key: &str) -> Option<&'static str> {
    let mut best: Option<(usize, &'static str)> = None;
    let mut tied = false;
    for knob in ACCEPTED {
        let distance = edit_distance(key, knob.key);
        match best {
            Some((best_distance, _)) if distance > best_distance => {}
            Some((best_distance, _)) if distance == best_distance => tied = true,
            _ => {
                best = Some((distance, knob.key));
                tied = false;
            }
        }
    }
    match best {
        Some((distance, candidate)) if distance <= 2 && !tied => Some(candidate),
        _ => None,
    }
}

/// Levenshtein distance over `char`s. Small table, small inputs (knob keys).
fn edit_distance(left: &str, right: &str) -> usize {
    let right: Vec<char> = right.chars().collect();
    let mut previous: Vec<usize> = (0..=right.len()).collect();
    let mut current = vec![0usize; right.len() + 1];
    for (row, left_char) in left.chars().enumerate() {
        current[0] = row + 1;
        for (column, right_char) in right.iter().enumerate() {
            let substitution = previous[column] + usize::from(left_char != *right_char);
            let deletion = previous[column + 1] + 1;
            let insertion = current[column] + 1;
            current[column + 1] = substitution.min(deletion).min(insertion);
        }
        std::mem::swap(&mut previous, &mut current);
    }
    previous[right.len()]
}

/// Parse and install `-Ztrust-ir-cg-args`, refusing incompatible reinstallation.
///
/// Called from `CodegenBackend::init`, before anything else in the backend can
/// read a knob. The caller makes an error fatal before lowering. Equal parsed
/// maps are idempotent; a different map must not reuse the earlier session's
/// policy under this session's tracked arguments. Explicit/default spellings
/// are not generally equivalent and are not silently normalized together.
pub(crate) fn install(args: &[String]) -> Result<(), String> {
    install_into(&KNOBS, args)
}

fn install_into(cell: &OnceLock<BackendKnobs>, args: &[String]) -> Result<(), String> {
    let requested = BackendKnobs::parse(args)?;
    match cell.set(requested) {
        Ok(()) => Ok(()),
        Err(requested) if cell.get() == Some(&requested) => Ok(()),
        Err(_) => Err("conflicting Trust Codegen knob reinstallation: this process already has a different tracked backend policy; use a new compiler process".to_owned()),
    }
}

/// Convert a library setter's first-or-equal result into the startup contract.
/// Both the compiler entry point and compiler-independent tests use this check.
pub(crate) fn require_compatible_policy(key: &str, compatible: bool) -> Result<(), String> {
    if compatible {
        Ok(())
    } else {
        Err(format!(
            "incompatible or unavailable Trust Codegen process policy for {key}; use a new compiler process"
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> Result<BackendKnobs, String> {
        BackendKnobs::parse(&args.iter().map(|a| (*a).to_owned()).collect::<Vec<_>>())
    }

    fn install_test(cell: &OnceLock<BackendKnobs>, args: &[&str]) -> Result<(), String> {
        install_into(
            cell,
            &args.iter().map(|arg| (*arg).to_owned()).collect::<Vec<_>>(),
        )
    }

    #[test]
    fn installation_is_idempotent_for_equal_parsed_maps() {
        let cell = OnceLock::new();
        install_test(&cell, &["no-proof-certs", "bridge-coverage-strict=1"]).unwrap();
        install_test(&cell, &["bridge-coverage-strict=1", "no-proof-certs=1"]).unwrap();
    }

    #[test]
    fn installation_refuses_conflicting_proof_and_library_policies() {
        for (first, second) in [
            ("no-proof-certs=1", "no-proof-certs=0"),
            ("no-proof-certs=0", "no-proof-certs=1"),
            ("bridge-coverage-strict=0", "bridge-coverage-strict=1"),
            ("bridge-coverage-strict=1", "bridge-coverage-strict=0"),
            ("diag-json=0", "diag-json=1"),
            ("max-parallelism=2", "max-parallelism=8"),
            ("proof-walk-workers=1", "proof-walk-workers=2"),
        ] {
            let cell = OnceLock::new();
            install_test(&cell, &[first]).unwrap();
            let error = install_test(&cell, &[second]).unwrap_err();
            assert!(error.contains("conflicting Trust Codegen knob reinstallation"));
            assert_eq!(cell.get(), Some(&parse(&[first]).unwrap()));
            install_test(&cell, &[first]).unwrap();
        }
    }

    #[test]
    fn installation_does_not_equate_explicit_and_absent_policy() {
        for explicit in ["no-proof-certs=0", "max-parallelism=2"] {
            for explicit_first in [false, true] {
                let cell = OnceLock::new();
                let value = [explicit];
                let (first, second): (&[&str], &[&str]) = if explicit_first {
                    (&value, &[])
                } else {
                    (&[], &value)
                };
                install_test(&cell, first).unwrap();
                assert!(install_test(&cell, second).is_err());
                assert_eq!(cell.get(), Some(&parse(first).unwrap()));
            }
        }
    }

    #[test]
    fn malformed_installation_never_publishes_or_replaces_policy() {
        let cell = OnceLock::new();
        assert!(install_test(&cell, &["no-proof-certs=nonsense"]).is_err());
        assert!(cell.get().is_none());
        install_test(&cell, &[]).unwrap();
        assert!(install_test(&cell, &["unknown-policy=1"]).is_err());
        assert_eq!(cell.get(), Some(&BackendKnobs::empty()));
    }

    #[test]
    fn concurrent_installations_only_accept_one_policy() {
        let cell = OnceLock::new();
        let barrier = std::sync::Barrier::new(8);
        let accepted = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..8)
                .map(|index| {
                    let cell = &cell;
                    let barrier = &barrier;
                    scope.spawn(move || {
                        let arg = if index % 2 == 0 {
                            "no-proof-certs=0"
                        } else {
                            "no-proof-certs=1"
                        };
                        barrier.wait();
                        (arg, install_test(cell, &[arg]).is_ok())
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().unwrap())
                .collect::<Vec<_>>()
        });
        assert_eq!(accepted.iter().filter(|(_, success)| *success).count(), 4);
        for (arg, success) in accepted {
            assert_eq!(success, cell.get() == Some(&parse(&[arg]).unwrap()));
        }
    }

    #[test]
    fn library_incompatibility_is_a_named_startup_error() {
        for key in [
            DIAG_JSON,
            BRIDGE_COVERAGE_STRICT,
            MAX_PARALLELISM,
            PROOF_WALK_WORKERS,
        ] {
            assert!(require_compatible_policy(key, true).is_ok());
            assert!(
                require_compatible_policy(key, false)
                    .unwrap_err()
                    .contains(key)
            );
        }
    }

    #[test]
    fn bare_knob_reads_as_one() {
        let knobs = parse(&["no-proof-certs"]).expect("accepted");
        assert_eq!(
            knobs.entries.get(NO_PROOF_CERTS).map(String::as_str),
            Some("1")
        );
    }

    #[test]
    fn valued_knob_keeps_its_value() {
        let knobs = parse(&["refine-solver=0", "opt-level=2"]).expect("accepted");
        assert_eq!(
            knobs.entries.get(REFINE_SOLVER).map(String::as_str),
            Some("0")
        );
        assert_eq!(knobs.entries.get(OPT_LEVEL).map(String::as_str), Some("2"));
    }

    #[test]
    fn empty_value_is_preserved_not_dropped() {
        // `key=` is an explicit empty value, distinct from an absent knob:
        // `artifact-cache-dir=` must reach the call site that filters empties.
        let knobs = parse(&["artifact-cache-dir="]).expect("accepted");
        assert_eq!(
            knobs.entries.get(ARTIFACT_CACHE_DIR).map(String::as_str),
            Some("")
        );
    }

    #[test]
    fn unknown_knob_refuses_and_names_every_accepted_key() {
        let error = parse(&["no-such-knob"]).expect_err("must refuse");
        assert!(
            error.contains("unknown `-Ztrust-ir-cg-args` knob `no-such-knob`"),
            "{error}"
        );
        for knob in ACCEPTED {
            assert!(
                error.contains(knob.key),
                "refusal omitted `{}`: {error}",
                knob.key
            );
        }
    }

    #[test]
    fn legacy_environment_spelling_is_translated_in_the_refusal() {
        let error = parse(&["TCG_NO_PROOF_CERTS=1"]).expect_err("must refuse");
        assert!(
            error.contains("this option takes the knob key `no-proof-certs`"),
            "{error}"
        );
    }

    #[test]
    fn near_miss_is_suggested() {
        let error = parse(&["no-proof-cert"]).expect_err("must refuse");
        assert!(error.contains("did you mean"), "{error}");
        assert!(error.contains("`no-proof-certs`"), "{error}");
    }

    #[test]
    fn conflicting_repeat_refuses() {
        let error = parse(&["refine-solver=0", "refine-solver=1"]).expect_err("must refuse");
        assert!(error.contains("different values"), "{error}");
    }

    #[test]
    fn identical_repeat_is_accepted() {
        // Composing a base list with an overlay legitimately produces one, and
        // it is unambiguous: there is exactly one value it can mean.
        let knobs = parse(&["no-proof-certs", "no-proof-certs=1"]).expect("accepted");
        assert_eq!(
            knobs.entries.get(NO_PROOF_CERTS).map(String::as_str),
            Some("1")
        );
        let knobs = parse(&["refine-solver=0", "refine-solver=0"]).expect("accepted");
        assert_eq!(
            knobs.entries.get(REFINE_SOLVER).map(String::as_str),
            Some("0")
        );
    }

    #[test]
    fn every_accepted_key_is_lowercase_kebab_and_unique() {
        let mut seen = std::collections::BTreeSet::new();
        for knob in ACCEPTED {
            assert!(
                knob.key
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-'),
                "knob key `{}` is not lowercase kebab-case",
                knob.key
            );
            assert!(seen.insert(knob.key), "duplicate knob key `{}`", knob.key);
            assert!(
                knob.legacy_env.starts_with("TCG_") || knob.legacy_env.starts_with("TRUST_CG_"),
                "knob `{}` names a legacy variable outside the refused prefixes",
                knob.key
            );
        }
    }

    /// THE DEFECT, in one test. `no-proof-certs=0` is what an operator writes to
    /// mean "keep the certificates". Before the value grammar existed, `parse`
    /// stored `"0"` verbatim and the call site asked `raw(..).is_none()`, so the
    /// knob counted as SET and the proof-certificate gate went OFF — under an
    /// argument spelled to keep it on. Measured end-to-end on the real backend
    /// before the fix: `certs=0` for `no-proof-certs=0`, `=false`, and even
    /// `=nope`.
    #[test]
    fn a_false_boolean_value_turns_the_knob_off_not_on() {
        for spelling in ["0", "false", "off", "no"] {
            let knobs = parse(&[&format!("no-proof-certs={spelling}")]).expect("accepted");
            assert_eq!(
                knobs.entries.get(NO_PROOF_CERTS).map(String::as_str),
                Some("0"),
                "`no-proof-certs={spelling}` must canonicalize to OFF"
            );
        }
    }

    /// ...and the ON half of the same table, bare spelling included.
    #[test]
    fn a_true_boolean_value_and_the_bare_key_turn_the_knob_on() {
        for arg in [
            "no-proof-certs",
            "no-proof-certs=1",
            "no-proof-certs=true",
            "no-proof-certs=on",
            "no-proof-certs=yes",
        ] {
            let knobs = parse(&[arg]).expect("accepted");
            assert_eq!(
                knobs.entries.get(NO_PROOF_CERTS).map(String::as_str),
                Some("1"),
                "`{arg}` must canonicalize to ON"
            );
        }
    }

    /// The whole table, for EVERY boolean knob — so a knob added later cannot
    /// quietly acquire a different grammar from the one the refusal advertises.
    #[test]
    fn every_boolean_knob_takes_the_same_value_table() {
        for knob in ACCEPTED.iter().filter(|knob| knob.shape == Shape::Boolean) {
            for (spelling, canonical) in [
                ("", "1"),
                ("=1", "1"),
                ("=true", "1"),
                ("=on", "1"),
                ("=yes", "1"),
                ("=0", "0"),
                ("=false", "0"),
                ("=off", "0"),
                ("=no", "0"),
            ] {
                let arg = format!("{}{spelling}", knob.key);
                let parsed = parse(&[&arg]).unwrap_or_else(|e| panic!("`{arg}` refused: {e}"));
                assert_eq!(
                    parsed.entries.get(knob.key).map(String::as_str),
                    Some(canonical),
                    "`{arg}`"
                );
            }
            let arg = format!("{}=maybe", knob.key);
            let error = parse(&[&arg]).expect_err("a value outside the table must refuse");
            assert!(error.contains("does not accept"), "{error}");
            assert!(error.contains("`1`, `true`, `on` or `yes`"), "{error}");
            assert!(error.contains("`0`, `false`, `off` or `no`"), "{error}");
        }
    }

    /// A refusal has to carry the fix (design principle 10): the knob's own help
    /// line, the accepted spellings, and the option of dropping it.
    #[test]
    fn a_bad_boolean_value_refusal_names_the_knob_its_help_and_the_way_out() {
        let error = parse(&["no-proof-certs=nope"]).expect_err("must refuse");
        assert!(
            error.contains("knob `no-proof-certs` was given the value `nope`"),
            "{error}"
        );
        assert!(error.contains(ACCEPTED[0].help), "{error}");
        assert!(error.contains("or drop the knob entirely"), "{error}");
    }

    /// `opt-level` is a fixed set. An unrecognized value used to fall through to
    /// `-C opt-level`, so `opt-level=O2` changed nothing while reading as if it
    /// had; and there is no member a BARE `opt-level` could mean.
    #[test]
    fn opt_level_takes_only_its_four_members() {
        for level in ["0", "1", "2", "3"] {
            let knobs = parse(&[&format!("opt-level={level}")]).expect("accepted");
            assert_eq!(
                knobs.entries.get(OPT_LEVEL).map(String::as_str),
                Some(level)
            );
        }
        for bad in ["opt-level=O2", "opt-level=4", "opt-level=", "opt-level"] {
            let error = parse(&[bad]).expect_err("must refuse");
            assert!(error.contains("`0`, `1`, `2`, `3`"), "{bad}: {error}");
        }
    }

    /// `slot-array-min-lanes` reached a `parse().ok().unwrap_or(1)`, so a typo
    /// silently meant the default.
    #[test]
    fn a_uint_knob_refuses_a_non_number() {
        assert_eq!(
            parse(&["slot-array-min-lanes=4"])
                .expect("accepted")
                .entries
                .get(SLOT_ARRAY_MIN_LANES)
                .map(String::as_str),
            Some("4")
        );
        for bad in [
            "slot-array-min-lanes=two",
            "slot-array-min-lanes=-1",
            "slot-array-min-lanes",
        ] {
            let error = parse(&[bad]).expect_err("must refuse");
            assert!(
                error.contains("base-10 non-negative integer"),
                "{bad}: {error}"
            );
        }
    }

    /// `time-codegen` keeps its documented spellings and gains a refusal for the
    /// rest, which used to be `parse().unwrap_or(10)`.
    #[test]
    fn a_count_knob_canonicalizes_its_off_and_default_spellings() {
        for (arg, canonical) in [
            ("time-codegen", "10"),
            ("time-codegen=on", "10"),
            ("time-codegen=true", "10"),
            ("time-codegen=1", "10"),
            ("time-codegen=0", "0"),
            ("time-codegen=off", "0"),
            ("time-codegen=false", "0"),
            ("time-codegen=", "0"),
            ("time-codegen=25", "25"),
        ] {
            let knobs = parse(&[arg]).unwrap_or_else(|e| panic!("`{arg}` refused: {e}"));
            assert_eq!(
                knobs.entries.get(TIME_CODEGEN).map(String::as_str),
                Some(canonical),
                "{arg}"
            );
        }
        let error = parse(&["time-codegen=ten"]).expect_err("must refuse");
        assert!(error.contains("base-10 count"), "{error}");
    }

    /// A path knob takes any text, including the empty value, because every one
    /// of them is meaningful.
    #[test]
    fn a_free_knob_takes_any_text() {
        let knobs = parse(&["artifact-cache-dir=/tmp/x=y"]).expect("accepted");
        assert_eq!(
            knobs.entries.get(ARTIFACT_CACHE_DIR).map(String::as_str),
            Some("/tmp/x=y")
        );
    }

    /// The boolean READERS, which are what the call sites use. `is_enabled` is
    /// the default-OFF question and `is_disabled` the default-ON one; ABSENT
    /// must answer `false` to BOTH, so neither reader can invent a setting the
    /// operator did not write.
    #[test]
    fn the_boolean_readers_separate_absent_from_off() {
        let absent = BackendKnobs::empty();
        assert!(!absent.raw(NO_PROOF_CERTS).is_some_and(|v| v == "1"));
        assert!(!absent.raw(NO_PROOF_CERTS).is_some_and(|v| v == "0"));

        let off = parse(&["refine-solver=0"]).expect("accepted");
        assert_eq!(off.raw(REFINE_SOLVER), Some("0"));
        let on = parse(&["refine-solver"]).expect("accepted");
        assert_eq!(on.raw(REFINE_SOLVER), Some("1"));
    }

    /// The accepted-knobs listing must show the value grammar, not only the key:
    /// a reader who mis-spelled a value needs to see what the knob takes.
    #[test]
    fn the_accepted_listing_shows_each_knobs_value_grammar() {
        let error = parse(&["no-such-knob"]).expect_err("must refuse");
        assert!(
            error.contains("no-proof-certs             [=BOOL]"),
            "{error}"
        );
        assert!(error.contains("=ONE-OF"), "{error}");
    }

    #[test]
    fn defaults_are_the_empty_knob_set() {
        // The pre-`install` reader must see EVERY knob absent — that is the
        // fail-closed property the module doc claims.
        for knob in ACCEPTED {
            assert!(DEFAULTS.raw(knob.key).is_none(), "{}", knob.key);
        }
    }
}
