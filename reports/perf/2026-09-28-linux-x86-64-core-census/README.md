# `library/core` census on x86-64 Linux, 2026-09-28: the lowering is COMPLETE, and the 3363 refusals are entirely the evidence gate

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`scripts/trust_ir_cg_census.py --crate core --opt-level 0 --panic abort` from the
Trust checkout, driven by the tree-built stage2 `trustc`
(`rustc 1.99.0-dev (3a3e781fe 2026-09-14)`) against the bridge dylib built from
`trust-cg` `9da5e2376` in its own worktree. Trust repo rev `ceb94fe99`. Backend
SHA-256 in `backend.sha256`. Wall 90s. Retained: `provenance.json`,
`gap_table.md`, `failed_roots.jsonl.gz`, `stderr.log.gz`,
`first-uncovered-opcodes.txt`.

Run with `PATH=/usr/bin:$PATH CC=/usr/bin/gcc`, which this host requires — see the
round-5 report's host-inputs section. This is a refusal measurement in the
explicit unverified frontend lane (`-Ztrust-verify=off`). It is not a proof claim.

## The headline: the LOWERING is complete; the 3363 is entirely the evidence gate

The same corpus was compiled twice, differing only in whether proof certificates
are requested. That difference is the whole story.

| Lane | Failed roots | Reasons | Exit | Objects | Defined text symbols |
| --- | ---: | ---: | ---: | ---: | ---: |
| certificates ON (default) | **3363** | 1 | 1 | 67 | — |
| `-Ztrust-ir-cg-args=no-proof-certs` | **0** | 0 | **0** | 45 | **3432** |

With the evidence gate off, `library/core` compiles **completely**: exit code 0,
zero failed roots, zero typed refusals, zero trapping stubs, zero skipped internal
functions, 45 real `ELF 64-bit LSB relocatable, x86-64` objects totalling 2.8 MB
and carrying **3432 defined text symbols**. Retained as
`provenance-no-proof-certs.json`, `gap_table-no-proof-certs.md`,
`stderr-no-proof-certs.log.gz`, `no-proof-certs-text-symbols.txt`.

So not one of the 3363 is a lowering, ABI, layout, construct or codegen gap. Every
one is the proof-promotion gate declining evidence it considers insufficient. The
two numbers answer two different questions, and it is worth being exact about
which:

* **"Does trust-cg compile `core` correctly on x86-64 Linux?"** — for the lowering,
  measured yes, 3432 functions emitted with no refusal.
* **"Does it compile `core` with proof credit?"** — no, 3363 roots short, on one
  reason.

WHAT THE CERTS-OFF LANE IS NOT. It carries no proof evidence, and a non-default
backend knob makes it a DIAGNOSTIC lane that
`benchmarks/beat-llvm/contract/metrics-contract.md` does not accept as release
evidence. It does not show the emitted code is correct — that is what the
cross-backend differentials and the execution oracles are for — only that the
backend produced code for every root instead of refusing. Nothing here weakens the
proof-required default, and the default lane's 3363 stands unchanged.

## The result, certificates on

| Measurement | Value |
| --- | ---: |
| Failed roots (externally required, fail-closed) | **3363** |
| Distinct reasons | **1** |
| Typed JSON refusals | 0 |
| Objects emitted | 67 |
| Skipped internal functions | 0 |
| Trapping stubs | 0 |

Every one of the 3363 is `[TCG-PROOF-465]` — proof promotion rejected. Not one
root fails for a lowering, ABI, layout or construct reason.

## Two opcodes are 98.1% of it

`first-uncovered-opcodes.txt`, the FIRST uncovered non-pseudo opcode named in each
root's refusal:

| Count | Opcode | Share |
| ---: | --- | ---: |
| 2862 | `x86_64::MovRR` | 85.1% |
| 437 | `x86_64::MovRR32` | 13.0% |
| 41 | `x86_64::Lea` | 1.2% |
| 8 | `x86_64::MovssRR` | |
| 8 | `x86_64::MovsdRR` | |
| 3 | `x86_64::Movzx` | |
| 1 each | `MovRipRel`, `AndRI`, `MovssRipRel`, `MovsdRipRel` | |

`MovRR` + `MovRR32` = **3299 of 3363**. Ten opcodes cover the whole census, and
the two that dominate are register-to-register copies — the simplest semantics in
the instruction set, `dst := src`.

That is the actionable content of this measurement. The blocker is not spread
across the ISA surface; it is concentrated in a handful of moves.

## This is NOT a regression against the old 87, and the two numbers do not compare

Earlier x86-64 censuses on this host read 726 as found, then 335, 183, 140/150 and
about 87 failed roots. Those were taken under an evidence standard that CREDITED
statistical sampling. Upstream `8d4e83b54` (2026-09-17, "withdraw: a registry name
lookup and a sampled discharge are not proof credit") withdrew that credit on every
ISA, and `STATISTICAL_EVIDENCE_IS_NOT_CREDIT` /
`REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT` are now unconditional constants with no policy
switch.

So 3363 is not 87 having got worse. It is the first count of `core` under the
CURRENT standard, and the old 87 is the count under a standard the project has
deliberately retired. Reporting 87 as the present state would be quoting a
withdrawn credit. The honest statement is that `core` at O0 has 3363 roots whose
evidence is insufficient, and that the earlier numbers measured a different
question.

## What it says about the shape of the remaining work

`MovRR`'s refusal text is the same every time:

```
x86_64::MovRR (no complete evidence: statistical sampling is not proof credit:
`RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)` found no counterexample in
100000 sampled inputs)
```

The obligation is real, it is real-operand, and it is answered by sampling. The
operand-exact route that would carry it already exists and is already wired
(`x86_source_operand_binding.rs`,
`discharge_reconstructed_obligation_with_exact_source_binding`), but it reaches
`Formal` only by replaying a COMMITTED artifact — a portable DRAT certificate or a
tier-0 candidate revalidated by a live checked solver — and it "spends no solve on
a miss". `verdict_db/tier0.vdb`'s seeds are five program-independent canaries, so
none of these ten opcodes has an artifact.

Two consequences worth stating plainly:

* Giving operand-exact, committed evidence to just `MovRR` and `MovRR32` would
  address 98.1% of this census. That is a far smaller target than "the x86 opcode
  inventory", and it is the same evidence the 12 XD-01 floor targets and the first
  x86-64 performance row need. See XD-01 in
  the completion plan for the three
  measured constraints on minting it, including that the stock-built root
  workspace cannot admit AY at all.
* Because a complete binary needs every function, this is also exactly why
  `benchmarks/beat-llvm` cannot produce an x86-64 Linux ledger row IN THE DEFAULT
  LANE: a trivial program fails closed on `std::rt::lang_start`. The certs-off lane
  compiles, so a runtime comparison is measurable there — as a diagnostic row the
  contract does not accept as evidence, which is exactly the distinction this
  report draws.

## What this does not measure

No `alloc` or `std` census, no O1/O2/O3 census, no runtime or size number, no
Trust-verified compilation of trust-cg itself, and no re-measurement of the
per-construct classes (X05) — under one blanket reason those classes are not
observable here, so this census says nothing about whether they improved or
regressed.
