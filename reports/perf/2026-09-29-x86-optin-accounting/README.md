# Every default-off x86 optimization, accounted for (2026-09-29)

Two of this round's wins came from the same pattern: an optimization **already written**,
gated behind an environment variable `trustc` refuses, and therefore never measured through
the real compiler. That raised an obvious question — how many more are there? This is the
complete answer for the x86 lane, so nobody has to re-derive it.

Method: enumerate every `TCG_*` env read in the x86 lane that is OPT-IN (`.is_some()`, i.e.
default OFF), discard the `*_LOG`/`*_TRACE`/`*_DEBUG`/`*_DUMP`/`*_STATS` diagnostics, and
account for each remaining performance switch.

| switch | status |
| --- | --- |
| `TCG_X86_JUMP_TABLE` | **WIN.** Was unreachable; now default-on. `p6_branch_match` 1.032x -> 0.980x vs LLVM, `P(JT<BST) = 1.000`. |
| `TCG_BRANCH_LAYOUT_FALLTHROUGH` | Measured this round. Its p6 refutation is obsolete (the jump table removed the shape), but it is neutral on `b1_mispredict` — the program whose shape it targets — and 0.4% worse on `p2_collatz`. **Stays off, for a better reason.** |
| `TCG_X86_TEST_ELIDE` | **Measured this round: fires on nothing.** Its comment called it opt-in "for the staged rollout"; with a tracked knob, `b1`, `p2`, `p4`, `p6` and `p3` all compile BYTE-IDENTICALLY. Nothing to roll out on this corpus. |
| `TCG_X86_BCE_CARRIER` | Already A/B'd and REJECTED by the author, with numbers in the source: never-taken checks are ~free and removing them perturbs regalloc — b12 crc32 +15%, b01 +8%, b04 +7%. |
| `TCG_X86_COMMUTE_DST` | Already "REFUTED as a default" in the source comment. |
| `TCG_X86_RA_FULL_POOL` | Already measured "firing on almost nothing": only a function whose 14-wide allocation spills NOTHING can keep the retry, and in the loss cluster only b01 reaches zero. |
| `TCG_X86_COLD_ARM_SINK` | Justified ONLY by call evidence (a call-bearing arm inside a hot loop). `b1_mispredict`'s diamond arms contain no calls, so it cannot fire there by construction. |
| `TCG_X86_TWOADDR_EXPAND_ALL` | Documented as "kept for suite A/Bs" — a counterfactual lever, not a candidate default. |
| `TCG_X86_LICM_GUARDED_HOIST` | **The one still unmeasured.** Not pursued: every other LICM lever measured this round (`licm-outer-iv`, `licm-pointer-loads`) either fires on nothing or is 1.49x SLOWER. |

And the levers added this round, all of which fire on nothing: `vectorize-late`,
`vectorize-post-sroa`, `licm-outer-iv`, `x86-cse-load-transparent`, `no-x86-bce-reload`,
`no-x86-bce-earlycopy`. Plus `no-x86-vectorize`, which is not a candidate default but
produced the round's strongest positive measurement — the vectorizer is worth **3.2x to
54x** (`../2026-09-29-x86-vectorizer-worth/README.md`).

## What this means for the remaining parity gaps

**The "unmeasured existing optimization" seam is exhausted.** Of nine default-off x86
performance switches: one was a win and is now the default, three were measured this round
(one neutral, two firing on nothing), four had already been measured and rejected by the
author with recorded evidence, and one remains, in a pass whose every other lever measured
as neutral or harmful.

So `b1_mispredict` (1.189x clang), `p4_matmul` (1.029x clang / 1.243x gcc), `p2_collatz`
(1.017x clang) and `h1_vec_push_sum` (2.488x LLVM) cannot be closed by flipping anything
that already exists. Each needs new work, and each is scoped elsewhere:

* `h1` — a dominating rematerialization of the vectorizer's trip bound, which upstream
  named as the required step (`../2026-09-29-x86-sib-scale1-fold/README.md`).
* `p4` — scheduling/blocking quality against gcc, on a loop already unrolled 24-wide,
  check-free and packing its accumulation, AFTER a 3.2x vectorization win.
* `b1` — misprediction, on a program written to defeat if-conversion; two independent
  levers aimed at its exact shape measured neutral.
* `p2` — one loop-carried phi copy; `post_ra_coalesce` handles only `PSEUDO_COPY`.
