# The x86 dense-switch jump table (2026-09-29): implemented, unreachable, and worth 1.032x -> 0.981x

`emit_x86_jump_table` has been in `x86_64_isel.rs` all along: a full indexed
jump-table lowering for a dense switch, fail-safe (it declines any shape it cannot
lower soundly and falls through to the always-correct binary-search tree or linear
chain) and covered by the #62 switch-preservation gate. It was reachable ONLY through
the `TCG_X86_JUMP_TABLE` environment variable, and `trustc` refuses every `TCG_*`
variable before the backend loads.

So through the bridge — the only place a real program's switch exists — **every dense
x86 switch has taken the binary-search path, and the jump table had never been
measured.** This is that measurement, and the pass is now default-on.

## What it changes in the code

`p6_branch_match`'s inner dispatch is `match s % 7` over 7 arms. Both backends lower
the modulo identically (the same `0x2492492492492493` magic multiply), so the modulo is
not the difference. The dispatch is:

* **LLVM**: `lea 0x0(,%rax,8)`, a `cmp $5 / ja` range check, and an indirect jump
  through a table.
* **trust-cg, before**: a balanced BST — `cmp $3 / je`, `cmp $1 / je`, `cmp $4 / je`,
  `cmp $5 / je` — i.e. ~2.6 dependent compare-and-branches per iteration on a
  uniformly random selector.
* **trust-cg, now**: `cmp` count 7 -> 4, indirect jumps 0 -> 2.

## Measurement

`p6_branch_match` is the most resolvable program in the corpus at ~1.58s, so a 3%
effect is unambiguous. One bridge dylib, both arms, the pass's own lever, 9 interleaved
samples on one pinned core:

| build | min | vs LLVM -O3 |
| --- | ---: | ---: |
| LLVM -O3 | 1.5808s | 1.000x |
| trust-cg, BST (the old default) | 1.6340s | **1.034x** |
| trust-cg, jump table | **1.5495s** | **0.980x** |

jumptable/BST = **0.9483x** (min), 0.9485x (median), and
`P(a random JT sample < a random BST sample) = 1.000` over all 81 pairs.

**p6 crosses from slower than LLVM to faster than LLVM.** That is a per-program parity
gap closed, not a geomean improvement.

Whole corpus, both arms, one bridge:

| | BST | jump table |
| --- | ---: | ---: |
| coverage | 18/18 MATCH, 0 MISMATCH | 18/18 MATCH, 0 MISMATCH |
| p6_branch_match | 1.032x | **0.981x** |
| p2_collatz | 1.037x | **1.014x** |
| runtime geomean vs LLVM -O3 | 0.892x | 0.888x |
| scalar category | 0.992x | 0.981x |

Two programs improve and both were above 1.0x. Everything else moves inside the
harness's measured noise band (6% on `b1_mispredict`, ~1.6 geomean points — see
`../2026-09-29-x86-sib-scale1-fold/README.md`), so only the p6 and p2 rows are claimed.

## The evidence question, asked and answered as far as it can be here

A dense switch compiled with certificates ON fails closed in BOTH arms, on the SAME
pre-existing reason — the `MovRR` register-copy obligation that is 98.1% of the `core`
census and waits on the XD-01 route (ruled 2026-10-02). So **the jump table does not change the proof
verdict.** The opcode inventory trades two extra distinct opcodes (`LeaRip`,
`MovRMSib`, the table base and the indexed target load) for five fewer uncovered
instances (26 across 15 distinct, against 31 across 13).

⚑ ONE THING THAT IS NOT SETTLED BY ANY NUMBER HERE (ruled 2026-10-02 as OD-51 in the
decision record: the table stays default-on, and its computed branch is
its own obligation, never credited as a direct branch). `select_switch` describes the BST
as "the verifiable — **all-direct-branch** — approximation" of a jump table. A computed
branch target is a different verification obligation from a direct branch even where
today's gate does not distinguish them. If that property is load-bearing for the
evidence posture, this default is the thing to revert: `-Ztrust-ir-cg-args=no-x86-jump-table`
is the lever and the table above is exactly what reverting costs.
