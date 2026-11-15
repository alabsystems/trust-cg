# Per-program parity on x86-64 Linux (2026-09-29): a measured table, not a geomean

The completion objective asks for performance "at least matching LLVM and clang". A
geomean answers a different question, so this is a per-program measurement, and it
replaces an earlier looser statement ("~6 programs between 1.03x and 1.15x") that came
from single harness runs inside the noise band.

Method: one bridge dylib, `-Copt-level=3`, `no-proof-certs`, against `rustc 1.97.1
-Copt-level=3` on the SAME source. Exit codes compared first (all agree). 11
INTERLEAVED samples per program per arm on one pinned core, `min` reported, plus
`P(a random trust-cg sample < a random LLVM sample)` — the harness's own single-run
numbers swing ~6% on `b1_mispredict` and ~1.6 geomean points between byte-identical
binaries, so nothing here rests on a single run.

## The table

| program | LLVM min | trust-cg min | ratio | P(tcg<llvm) | verdict |
| --- | ---: | ---: | ---: | ---: | --- |
| m2_call_heavy | 60.22ms | 45.58ms | **0.757x** | 1.000 | beats |
| p3_gcd | 292.35ms | 260.18ms | **0.890x** | 1.000 | beats |
| p6_branch_match | 1581.08ms | 1550.46ms | **0.981x** | 1.000 | beats |
| p8_closure_nest | 149.93ms | 149.84ms | 0.999x | 0.430 | matches |
| p1_xorshift | 448.46ms | 448.41ms | 1.000x | 0.752 | matches |
| p5_struct_acc | 448.65ms | 448.71ms | 1.000x | 0.223 | matches |
| m1_call_chain | 67.69ms | 67.73ms | 1.000x | 0.289 | matches |
| **p2_collatz** | 164.28ms | 166.39ms | **1.013x** | 0.000 | slower |
| **p4_matmul** | 58.33ms | 63.77ms | **1.093x** | 0.000 | slower |
| **b1_mispredict** | 188.10ms | 221.40ms | **1.177x** | 0.000 | slower |

Plus, from the corpus: the four `vectorizable` programs all beat LLVM (v3 0.103x, v1
0.645x, p7 0.704x, v2 0.999x); `h1_vec_push_sum` is 2.557x; `h3_box_leak` (38ms) and
`h4_vec_dropper` (8ms) sit below the harness's 50ms resolvability floor and are not
claimed either way.

**So 7 of the 10 resolvable scalar/multifn programs match or beat LLVM, and three are
genuinely slower** — with `P(tcg<llvm) = 0.000`, so those three are real and not noise.

## Two gaps closed or narrowed in this round

**p6_branch_match: 1.032x -> 0.981x, crossing to faster than LLVM.** Its 7-way
`match s % 7` was lowered as a balanced binary-search tree (~2.6 dependent
compare-and-branches per iteration on a uniformly random selector) because the
already-implemented jump-table lowering was reachable only through an environment
variable `trustc` refuses. See `../2026-09-29-x86-jump-table/README.md`.

**p2_collatz: 1.022x -> 1.013x.** Its inner loop is
`bt $0,c ; mov ; shr $1 ; lea ; add $1 ; bt $0,c ; cmovb ; ...`: the `c & 1` test is
emitted, the arithmetic of both arms destroys the flags, and the test is
RE-MATERIALISED for the `cmov`. The first `bt` is dead, and two things kept it:

1. `BtRI` was missing from the dead-code pass's flag-only opcode set, although it
   produces no register or memory result and `effects.rs` already documents that it
   "writes only CF".
2. The dead-flag scan returned `false` on a PARTIAL flag overwrite, and `shr $1` is
   partial (shifts leave AF undefined). That was stricter than the argument requires:
   the scan already returns `false` on ANY flag reader, so reaching a full overwrite
   means nothing ever observed the flags in question, whichever bits a partial writer
   left intact.

Inner loop 12 -> 11 instructions (LLVM: 9), after/before 0.9909x with
P(after<before) = 1.000. Corpus 18/18 MATCH.

## What remains, named

* **h1_vec_push_sum 2.557x** — 1.979x is LLVM's vectorization, 1.334x residual scalar.
  The vectorization needs a dominating rematerialization of the trip bound that upstream
  has explicitly flagged as the required step; four hypotheses for the scalar part are
  refuted in `../2026-09-29-x86-scalar-gap-refutations/README.md`.
* **b1_mispredict ~1.168x** — misprediction-bound, and that now rests on two
  measurements rather than one. Removing two instructions from its hot loop moved it 0%
  (though that reading was noise-limited, taken before the harness was calibrated). The
  branch-layout FALLTHROUGH rule, which targets exactly b1's hot-loop shape
  (`jcc T; jmp F` where `T` is the layout successor, twice per iteration), is also
  neutral: 219.03ms -> 218.48ms, ON/off 0.9975x with P(ON<off) = 0.734 — not decisive at
  13 interleaved samples. trust-cg emits 137 instructions in `main` against LLVM's 91 and
  neither change moves it, which is what misprediction-bound looks like.
* **p4_matmul 1.093x** — LLVM vectorizes the kernel (its matmul loop is a 143-instruction
  `xmm` body). But an earlier diagnosis of mine, "needs i64 multiply vectorization", was
  reached from whole-function opcode counts and is too coarse. Reading the actual
  innermost loop, trust-cg spends **8 of 26 instructions on work LLVM does not do at all**:
  three un-eliminated bounds checks (`cmp $0x240,%rcx; jae trap` — 0x240 is `N*N` = 576,
  one per array access) and two loop-invariant recomputations (`imul $0x18,%r13,%rdx`,
  i.e. `k*N`, and a stack-slot reload of `i*N`). Removing those is a smaller job than
  vectorizing an i64 product, and the bounds checks need affine range reasoning
  (`i<N & j<N => i*N+j < N*N`) rather than the identical-compare matching
  `X86BoundsCheckElimination` does today.
* **p2_collatz ~1.015x** — one of the two two-address copies is now folded (see below);
  the remaining one is a plain register-to-register copy that needs coalescing, and
  `post_ra_coalesce` handles only `PSEUDO_COPY`.

## The two-address increment collapse, and why it is shipped WITHOUT a speedup claim

`x += k` on a value the allocator keeps in `base` reaches the machine level
non-destructively — `add tmp, base, k` (or, after two-address expansion,
`lea tmp,[base+k]`) plus a write-back `mov base, tmp`. Two instructions and a live
vreg for what `add $k, base` does in one. It is present once or twice per hot loop in
11 of the 14 ported programs. `latch_advance_collapse` already handled it, but only
inside a 4-instruction window ending `Cmp; Jcc`, which `p2_collatz` misses because an
unrelated copy sits in the window.

The fold is now general (use-count and flag-deadness instead of a fixed window), and the
flag reasoning is the whole of it: the `AddRI` spelling needs NO flag condition, because
the rewrite keeps the same flag write at the same position with the identical result;
the `Lea` spelling is flag-NEUTRAL, so folding it INTRODUCES a flag write and is allowed
only where the flags are provably dead from the `lea` onward. Eight tests, including the
pair that distinguishes exactly that: the `AddRI` form must fold with a live flag reader
downstream, and the `Lea` form must refuse the same shape.

**Measured effect: none.** Corpus A/B on one bridge — geomean 0.887x (on) against 0.896x
(off), resolvable-rows 0.786x against 0.788x, every per-program row inside the
calibrated noise band, 18/18 MATCH in both arms. On `p2_collatz` in isolation the fold
even reads 0.4% SLOWER than without it (1.011x vs 1.015x), and the visible reason is an
`xchg %ax,%ax` alignment pad that appears inside the loop once the instruction is
removed — the same fetch-line interaction recorded for `h1` in
`../2026-09-29-x86-scalar-gap-refutations/README.md`.

So it ships default-on for one fewer instruction and one fewer live vreg per hot loop,
NOT for a speedup, and `-Ztrust-ir-cg-args=no-x86-lea-writeback` is the lever. The
instruction-count argument is the honest one and the runtime claim is explicitly not
made.

## A stale refutation retired: the branch-layout fallthrough rule

`X86BranchLayoutConfig::fallthrough_rule` inverts `jcc T; jmp F` when `T` is the layout
successor, so the trailing `jmp` targets the layout successor and the encoder elides it
to zero bytes. It has been DEFAULT OFF because it assumes layout-successor == hot, and
that measured **`p6_branch_match` +4.3% — a real regression** on match-heavy code. The
rule was reachable only through `TCG_BRANCH_LAYOUT_FALLTHROUGH`, which `trustc` refuses,
so it had never been A/B'd through the bridge.

**That refutation no longer holds, and this round is why.** The p6 regression was about a
match DISPATCH, which used to lower to a binary-search tree full of `jcc T; jmp F` pairs.
Since the dense-switch jump table became the default, p6's dispatch is a range check and
one indirect jump — and with the rule on, p6's instruction count is now IDENTICAL in both
arms (156), i.e. the shape that regressed is simply not there any more.

Re-measured on one bridge with the new `-Ztrust-ir-cg-args=branch-layout-fallthrough`:

| program | rule off | rule ON | ON/off | P(ON<off) |
| --- | ---: | ---: | ---: | ---: |
| p6_branch_match | 0.980x | 0.979x | 0.9984x | **1.000** |
| b1_mispredict | 1.168x | 1.165x | 0.9975x | 0.734 |
| p2_collatz | 1.017x | 1.021x | **1.0038x** | 0.000 |

So p6 now slightly IMPROVES with the rule instead of regressing 4.3%. But the rule is
still not a win: it is neutral on `b1_mispredict`, the program whose hot-loop shape it
targets twice per iteration, and 0.4% WORSE on `p2_collatz` with P = 0.000.

**It stays default off — for a better reason than before.** The old reason (a 4.3% p6
regression) is obsolete; the current reason is that its measured effect on its own target
is nothing, and it costs 0.4% elsewhere. The knob is there, and this table is what a
future profile-guided version has to beat.

## A LICM limitation removed, and the second gate behind it

`is_vreg_loop_invariant` refused any vreg with more than ONE definition in the whole
function. An enclosing loop's induction variable has at least two (init and increment),
so under that rule **nothing derived from an outer loop's counter could ever be hoisted
out of an inner loop** — the commonest invariant there is in nested code, and exactly why
`p4_matmul`'s innermost loop recomputes `k * N` on every `j` iteration.

The multi-def count was never the property that mattered. A vreg with NO definition inside
the loop body holds one value for the whole execution of the loop however many
definitions it has elsewhere, and the value at the preheader is that value, because
`find_preheader` only yields a block that is the header's UNIQUE out-of-body predecessor.
`loop_defs` already answers "no def inside the body" exactly.

Relaxed behind `-Ztrust-ir-cg-args=licm-outer-iv`, DEFAULT OFF, with both answers
unit-tested (a `_with` inner form exists precisely so the enabled path is testable in one
process, which a `OnceLock` gate is not). Four tests, including the one the relaxation must
NOT touch: a def inside the body stays non-invariant either way.

**Measured effect: none, and the reason is named.** p4_matmul, p7_sieve, v1_saxpy,
p5_struct_acc, h1_vec_push_sum and p1_xorshift all compile BYTE-IDENTICALLY with the knob
on. Operand invariance was one of two gates; the other is `preheader_flag_hoist_safe`,
whose condition (1) refuses the whole Lever-B tier for a loop whose preheader terminator
READS flags — which is the case for a guarded inner loop, because the guard's `Jcc` is that
terminator. p4's invariant `imul` writes flags, so it needs Lever-B, so it is still
refused.

The next step for p4's invariant `imul` is therefore the INSERTION POINT: splice a hoisted
flag-writer ahead of the preheader's flag-producing tail (its compare) instead of
immediately before the terminator, which is sound when the operands are available there.
Not attempted here. Kept opt-in regardless, because more hoisting raises register
pressure, and that has already cost this pass once — the pointer-base invariant-load arm
measured 1.46x SLOWER on h1 from pressure alone.

## All four goal clauses re-verified on the current backend

The objective names four program classes. This round changed the x86 backend about twenty
times while looking only at Rust performance, so all four were re-run against the final
backend rather than assumed:

| clause | target | result |
| --- | --- | --- |
| Rust | `benchmarks/beat-llvm`, 18 programs | **18/18 MATCH, 0 MISMATCH** |
| Trust | `rustc-codegen-trust-cg --test trust_verified_corpus_x86` | **1/1 pass** — 23 strict-verified functions, verification ON, byte-identical checksum against LLVM |
| Lean-through-Clean | `trust-cg-codegen --test clean_fixture_host_lowering` | **5/5 pass** |
| TY | `--test ty_bfs_minimal` | **9/9 pass** |

So no clause regressed under a day of optimization changes, which is the thing worth
checking and was not obvious in advance.

ONE PRE-EXISTING RED, named so it is not mistaken for fallout:
`ty_bfs_minimal_o1_o3_summary` has 2 failures, both `[TCG-PROOF-465]` — proof promotion
rejected because the FIRST uncovered opcode is `x86_64::MovRR` with "statistical sampling
is not proof credit". That is the register-copy obligation which is 98.1% of the `core`
census and waits on the XD-01 route (ruled 2026-10-02), unconditional since upstream withdrew statistical credit in
September. The target compiles with `jit_fast` and no `no-proof-certs`, so it requires a
promotion the evidence gap denies; it was enabled 2026-09-27 and nothing in its opcode
inventory is new. Separately, `trust-cg-codegen --lib` carries 2 pre-existing failures
(`compile_service_refuses_variadic_definition_with_shared_diagnostic` and upstream's
`object_and_executable_payloads_disclose_the_spliced_bodies`), both verified pre-existing
by stashing earlier in the round.

