# 203 `core` roots promote by rewriting one SMT assertion (2026-09-28)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`library/core` on x86-64 Linux, proofs REQUIRED, goes from **3363 failed roots to
3160**, and emitted objects from **67 to 270**, because of a workaround for one
solver defect. No newer AY, no owner decision, no change to any query that
already worked, and no committed certificate invalidated.

## The defect

AY reaches UNSAT on the register-copy obligation and then refuses to publish its
own proof:

```
invalid surface proof step t1: and_pos indexed conjunct is absent from its
effective source
```

`and_pos` is the Alethe rule that indexes into an n-ary conjunction. The backend
renders every obligation as ONE assertion whose term is a conjunction, and for
some of those AY cannot index it correctly. It is right to refuse — an
unverifiable proof is worse than none — so the backend sees `replay=none (no
independently checked proof)` and fails the root closed with `[TCG-PROOF-465]`.

## The fix, and why it is not a semantic change

`(assert (and A (and B C)))` and `(assert A) (assert B) (assert C)` are the same
SMT-LIB2 script: the assertion stack is itself conjunctive, so no solver's
satisfiability verdict can differ. Only AY's ability to PUBLISH a proof differs.

Measured over all 65 conjunctive queries in
`crates/trust-cg-verify/tests/fixtures/x86_source_bound_body/snapshots.smt2`,
each run both ways through `ay 0.26.0+build.9624`:

| single `assert` | one per conjunct | queries |
| --- | --- | ---: |
| proof | proof | 48 |
| **`and_pos` FAILURE** | **proof** | **9** |
| incomplete (other cause) | incomplete | 8 |

**9 newly publish a proof; none regresses.** The 9 include `Ident`, the
register-to-register copy. The same obligation that failed returns
`unproved_steps=0 foreign_assumes=no trust_free=yes ay_self_checkable=yes`.

Two hypotheses were tested and REJECTED first, which is why the shape above is
stated narrowly: flattening the right-nested `and` into a flat n-ary `and` does
NOT help (fails identically), and the trigger is not simply "more than two
conjuncts" (a 4-conjunct flat `and` over fresh variables proves fine). The
property that matters is empirical per query, so the workaround is applied per
query rather than by a rule about size.

## It is a RETRY, not a rewrite

The change lands in `split_assert_conjuncts` and
`is_and_pos_publication_failure` (`crates/trust-cg-verify/src/ay_bridge.rs`) and
fires ONLY after AY reports that exact publication failure. That matters:

* Rewriting every query invalidates the committed certificate corpus, which is
  keyed to query TEXT — measured, by doing it: 8 tests fail, including
  `canary_cert::tests::committed_queries_match_all_current_obligations`. That
  would be a proof-authority change. As a retry, no working query changes by a
  byte and those 8 tests pass untouched.
* The retry transforms the exact bytes the solver was just given, so the retried
  script is provably the same problem. Regenerating from the obligation could not
  guarantee that: several renderers feed this path and they differ.
* It fails closed everywhere. An unparseable or unfamiliar query declines. More
  than one conjunctive assert declines. If the retry also fails, or returns any
  Error/Unknown, the ORIGINAL result is kept — a retry can never turn a failure
  into a weaker answer.
* The trigger is narrow by test: a timeout, an incomplete certificate, a plain
  verdict and an unrelated error all do NOT retry.

Nothing here weakens the gate. The retried script admits exactly the models the
original did, and whatever proof AY returns is replayed by the independent
checker exactly as before.

## Result

| Measurement | Before | After |
| --- | ---: | ---: |
| Failed roots, proofs required | 3363 | **3160** |
| Objects emitted | 67 | **270** |
| Refusals on the SOURCE-BOUND route | 494 | **291** |
| Refusals on the SAMPLING route | 2849 | 2849 |
| First-uncovered `MovRR` | 2879 | 2676 |

The sampling route is untouched, as expected — this fix only concerns the replay.
The 291 source-bound roots that remain fail for AY's OTHER reason, an incomplete
certificate (`unproved_steps=1 … trust_free=no`), which separate asserts does not
address; that is an AY capacity limit on bool/shift-shaped obligations.

The smallest witness now compiles in the proof-required lane:
`pub fn c(a: u64) -> u64 { a }` reports `bound rows=3 replay=Valid` where it
previously reported `replay=none` and refused.

## The `and_pos` class is now EMPTY, and what remains is one AY limitation

Re-running the census with `-Ztrust-ir-cg-args=x86-body-trace` gives the replay
outcome for every obligation:

| outcome | count |
| --- | ---: |
| `replay=Valid` | **414** |
| `replay=none` (all `outcome=Unknown`) | 582 |
| — of those, `unproved_steps=1` | 478 |
| **`and_pos`** | **0** |

So the defect this report is about is GONE, not merely reduced: no obligation in
`core` still fails on `and_pos`. Every remaining replay failure is AY's OTHER
mode, and its message names it exactly:

```
strict UNSAT proof validation failed: step t1 uses unverified trust rule
```

AY's proof leans on a rule it cannot self-check, and `--strict-proofs` rejects
that. This is NOT reshapeable, and the reason is worth recording so nobody tries:

`ShlImm` is `(= s1 (bvshl p0 3))` against `(= m2 (bvshl m0 3))` with `p0 = m0 =
e_rdi` — the two sides are syntactically identical, yet AY still needs a trust
rule to get through the auxiliary equalities. Inlining those definitions DOES make
it prove cleanly (`unsat`, `unproved_steps=0`), measured. But the inlined query is
`(not (= X X))` — a constant `false`, which is precisely the shape
`simplifier_alone_proved_unsat` exists to keep from minting `Verified`: "when the
local simplifier alone collapses the negated equivalence to a constant `false`,
the solver would only ever see `(assert false)` and never the real formula". Taking
that route would defeat a deliberate TCB guard to gain credit. Separate asserts
(the fix above) do not help this class either — measured, 8 of 8 stay incomplete.

**So this class needs a better AY, and nothing in trust-cg can substitute for it.**

## What this does NOT achieve

A trivial Rust BINARY still does not compile in the default lane, so X14 still
has no eligible row — but the distance is now **7 roots**, and their split is the
useful part: **5 are the SAMPLING route** (`MovRR` via `RECONSTRUCTED x86_64
Copy_64 -> MovRR (real-operand)`), which needs either more source-bound theorem
coverage or the owner's decision about whether a total bit-routing-table equality
is complete evidence; only 2 are the AY replay class (`Movzx`, `MovRR32`).

So after this change the binary-completeness blocker is almost entirely the
OWNER-DECISION class, not a solver defect.

## Provenance

Bridge rebuilt from the tree carrying this change
(`RUSTC=<stage2>/bin/trustc targo --unverified build --release`), census driven by
the tree-built stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)`, Trust repo
`ceb94fe99`, `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs required
(the default), `PATH=/usr/bin:$PATH CC=/usr/bin/gcc`. Wall 88s. Retained:
`gap_table.md`, `provenance.json`, `stderr.log.gz`. Gates: trust-cg-verify 4598
pass / 4 fail (the 4 are the pre-existing root-workspace
`[TCG-AY-IDENTITY-UNRECORDED]` failures, unchanged); trust-cg-codegen `--lib` at
its unchanged 4355 / 19 baseline; trust-cg-opt 3705 / 0; check_fmt OK; clippy
clean on `ay_bridge.rs`.
