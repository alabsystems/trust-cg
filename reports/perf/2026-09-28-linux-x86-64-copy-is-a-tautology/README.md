# The register-copy obligation is a SYNTACTIC TAUTOLOGY, so no solver route can ever credit it (2026-09-28)

`RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)` is the first uncovered
opcode in **2578** of the 2881 failed roots in the x86-64 `library/core` census,
and `-> MovRR32` in a further 436. Every attempt to give it solver-backed evidence
has failed today, and this report explains why they must: there is nothing for a
solver to prove.

## The obligation, in full

Extracted verbatim from the committed tier-0 DB (`entry 201`):

```smt2
(set-logic QF_BV)
(set-option :timeout 30000)
(set-option :produce-models true)
(declare-const recon_src (_ BitVec 64))
(assert (not (= recon_src recon_src)))
(check-sat)
```

That is `¬(x = x)`. The reconstructed expression for a register move is LITERALLY
the source expression, so the negated equivalence is closed by syntactic identity
before any theory reasoning. The obligation is real — it says the emitted `MovRR`
denotes the source operand — but its SMT form carries no content.

## Which is why every solver route refuses it, each for its own correct reason

**Portable DRAT certificate** — attempted by extending
`is_certifiable_reconstruction` (the filter that today admits only
`ShlRR`/`ShrRR`/`SarRR`) to the two copy obligations and running
`regen_canary_certs`. It refuses, by name:

```
no DRAT certificate available for "RECONSTRUCTED x86_64 Copy_64 -> MovRR
(real-operand)": ay's SMT rewriter closed the query before the bit-blaster ran
(canonical-false export at .../obligation.cnf) — a DRAT over that canonical
formula would carry no information about the obligation
```

The tool is right. A DRAT refutation of the canonical `false` says nothing about
register copies. Minting it would be a vacuous certificate with a real
certificate's authority — precisely the failure `simplifier_alone_proved_unsat`
exists to prevent on the live path.

**Tier-0 verdict DB** — holds the row (`entry 201`) but cannot serve it on this
host at all: rows are keyed `H(solver_identity, query)` using the DB's OWN header
identity (`ay 0.11.0`), so every lookup misses. That is a separate defect,
reported in `2026-09-28-linux-x86-64-tier0-dead`. Even repaired, the row would be
a recorded verdict on the canonical-false formula — the same vacuity, cached.

**Live solver** — AY proves `¬(x=x)` instantly and, since the 0.27.0 bump, emits a
complete checkable proof for it. It still cannot be CREDIT: the route requires a
committed artifact, and `discharge_registry_obligation` "spends no solve on a
miss" by design, because an ad-hoc live solve of a tautology is not evidence that
the LOWERING is right.

**Statistical sampling** — what actually happens today
(`found no counterexample in 100000 sampled inputs`), and
`STATISTICAL_EVIDENCE_IS_NOT_CREDIT` has made it non-credit since upstream
`8d4e83b54`. Sampling `x == x` is the emptiest possible sweep.

## What this means for XD-01

XD-01 has been carried as an evidence-TAXONOMY question: "does a total,
exactly-transcribed result-bit-to-source-bit table equality count as complete
evidence for a register move?" This report supplies the missing half of that
question — a mechanical reason the alternatives cannot substitute:

**A register copy has no solver-expressible content.** Its correctness is not a
theorem about bitvectors; it is the claim that the emitted instruction's
result-bit-to-source-bit routing equals the source's. So the evidence must be
either

1. **structural** — the bit-routing-table equality XD-01 proposes, decided rather
   than solved (the same shape `x86_sse_lane_proofs` already credits for ten SSE
   rows, on the stated ground that "a routing instruction's meaning is a total
   function from result-bit index to which bit of which operand, and two such
   functions denote the same instruction iff their tables are equal … the
   comparison is a decision"), or
2. **the source-bound body theorem**, which is the only existing route that
   reasons about the BODY — the source-to-machine binding — rather than about a
   formula. It is why that route, once AY and Clean were bumped, took the
   source-bound refusals from 494 to 12 while the sampling route did not move a
   single root.

There is no third option, and no amount of solver work produces one. That is the
useful content of a day spent trying all of them.

## What was NOT changed

The canary filter extension was reverted; the 34 committed certificate files and
their manifest are untouched (`git diff` over `verdict_db/` is empty). No vacuous
certificate was minted, and `EXPECTED_CERT_COUNT` is back at 33.

## Provenance

`ay 0.27.0+build.11385` installed at the stage2 sysroot; Clean `e75141b7b` with
`carcara-verify`; `regen_canary_certs` built with
`RUSTC=<stage2>/bin/trustc ... targo --unverified` so AY is admitted; census
figures from `2026-09-28-linux-x86-64-clean-bump`. The obligation text is quoted
from the committed `verdict_db/tier0.vdb`.
