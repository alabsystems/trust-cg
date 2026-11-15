# XD-01 on x86-64 Linux is blocked by AY's PROOF EMISSION, not by policy, a checker, or an owner decision (2026-09-28)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The `core` census on this host has read **3363 failed roots, one reason**
(`[TCG-PROOF-465]`) since it was first taken under the current evidence
standard. That single reason hid two different blockers with two different
owners. This report separates them, names the one that is actually in the way,
and shows it is a TOOLCHAIN VERSION rather than a decision anyone has to make.

Re-measured on the merged tree after upstream landed slices 2 and 3 of the
x86-64 source-bound body theorem. Bridge rebuilt from `7b9ee7663`
(`RUSTC=<stage2>/bin/trustc targo --unverified build --release`), census driven
by the tree-built stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)`, Trust repo
`ceb94fe99`, `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs
REQUIRED (the default). `PATH=/usr/bin:$PATH CC=/usr/bin/gcc`, which this host
requires. Retained: `gap_table.md`, `provenance.json`, `stderr.log.gz`.

## The total did not move, but its COMPOSITION did

| Census | Failed roots | Reasons |
| --- | ---: | ---: |
| 2026-09-28, pre-merge | 3363 | 1 |
| 2026-09-28, merged (slices 2+3) | **3363** | 1 |

Identical totals. The composition is not identical: the FIRST uncovered opcode
moved for 17 roots, `Lea` 41 -> **24** and `MovRR` 2862 -> **2879**, and
`MovRipRel`/`AndRI`-first roots disappeared. Upstream's theorem NOW covers
`Lea` in those roots; they still fail because `MovRR` in the same function does
not. A root needs EVERY opcode covered, so a headline count is insensitive to
real progress underneath it — which is exactly why this report splits by route
instead.

## The split that matters: two routes, 494 vs 2849

| Route named in the refusal | Roots | Blocked on |
| --- | ---: | --- |
| `source-bound x86 body needs independently replayed proof` | **494** | THE REPLAY (below) |
| `statistical sampling is not proof credit` | **2849** | more theorem coverage |

By first uncovered opcode: source-bound is `MovRR` 396, `MovRR32` 95, `Movzx`
3; sampling is `MovRR` 2483, `MovRR32` 341, `Lea` 24, `AndRI` 1. The remaining
~18 are the scalar-FP moves.

So **494 roots (14.7%) have a bound body and lack only an independently
replayed proof**, and 2849 (84.7%) are not yet reached by the theorem at all.
The second group is upstream's ongoing slice work — Darwin's slice 3 promoted
191 roots against its slice-2 baseline, 0 newly failing. The first group is the
subject of the rest of this report.

## The replay fails INSIDE AY, and the checker is fine

Traced with `-Ztrust-ir-cg-args=x86-body-trace` on the smallest possible
witness, `pub fn c(a: u64) -> u64 { a }`, which lowers to a single `MovRR` and
refuses with exactly the 396-root message.

Checker discovery WORKS and is not the problem:

```
[trust-cg] proof checker …/stage2/bin/clean skipped (it was built WITHOUT the
`carcara-verify` cargo feature, so it rejects every Alethe proof regardless of
validity …); using $HOME/trust/first-party/clean/target/release/clean
```

It correctly declines the stage2 `clean` and falls back to the dev-built
carcara-capable one. AY is also admitted and RUNS. What fails is AY's ability to
emit a proof of the obligation, and it fails DIFFERENTLY at the two widths:

| Width | Opcode | `replay outcome` | Gate class |
| --- | --- | --- | --- |
| `u64` | `MovRR` | `Error(… invalid surface proof step t1: and_pos indexed conjunct is absent from its effective source)` | **SOUNDNESS** |
| `u32` | `MovRR32` | `Unknown(incomplete AY proof certificate: unproved_steps=1 foreign_assumes=no trust_free=no ay_self_checkable=yes)` | **PENDING(solver-capacity)** |
| `u16`, `u8` | | `Unknown`, as `u32` | PENDING |

At 64 bits AY reaches a verdict but its own surface proof is INVALID, and it
refuses to publish an unverifiable proof — the right call, and the reason the
gate class is SOUNDNESS. At 32 bits AY publishes a certificate with one
UNPROVED step and `trust_free=no`, which is incomplete rather than wrong. In
both cases the backend reports `replay=none (no independently checked proof)`
and the root fails closed. In both cases the body itself is bound:
`bound rows=3`.

This is the narrowest true statement of the blocker:

> On x86-64 Linux the 494 source-bound roots are blocked by the proof-EMISSION
> capability of `ay 0.26.0+build.9624` on the register-copy obligation. Not by
> the proof-required policy, not by an owner decision, not by a missing or
> mis-featured checker, and not by AY admission.

## Why this is a version, and what this host can and cannot do

Every `ay` on this host is the same build — stage1, stage2, stage3,
stage2-tools and bootstrap-tools all report
`ay 0.26.0+build.9624.075a482ae…@2026-09-14`. `aterm pkg which ay` reports
`unavailable on x86_64-unknown-linux-gnu: no build is published for this
target`, so the package manager cannot supply another. `~/trust` at
`ceb94fe99` (2026-09-21) carries AY source `version = "0.26.0"`, so rebuilding
from this checkout reproduces the same version.

Upstream's Darwin slice-3 census — the one where 191 roots newly promote —
records `ay 0.27.0+build.10530`. A NEWER AY than anything this host can
currently build. That is consistent with the defect being fixed upstream, and
it is the obvious first thing to test, but this report does NOT claim a newer AY
promotes these roots: that has not been measured here, because the AY it needs
cannot be built from this checkout. Getting it requires updating `~/trust`,
which is a different repository and a stage rebuild.

## What this changes about XD-01

XD-01 has been carried as needing an owner decision — whether a total,
exactly-transcribed result-bit-to-source-bit table counts as complete evidence
for a register move — with a note that the stock-built root workspace cannot
admit AY at all. Both statements need qualifying:

* The root-workspace claim is about the ROOT WORKSPACE, whose build compiler is
  stock 1.97.1 and whose sysroot ships no `bin/ay`; four `trust-cg-verify`
  tests fail on this host for exactly that reason
  (`[TCG-AY-IDENTITY-UNRECORDED]`). It does NOT describe the BRIDGE, which is
  built with `RUSTC=<stage2>/bin/trustc`, records a toolchain AY, and runs it.
* For 494 of the 3363 roots no owner decision is needed at all. The evidence
  route the project already accepts — a bound source body plus an
  independently replayed proof — is wired, reached, and attempted. It fails on
  an AY defect.

The owner decision still governs the other 2849, where the obligation is
answered by sampling and the theorem has not yet reached the body. Nothing here
weakens the proof-required default, and the default lane's 3363 stands.

## What this does not measure

No `alloc`/`std` census, no O1/O2/O3 census, no runtime or size number, no
Trust-verified compilation of trust-cg itself, and no demonstration that a
newer AY fixes either failure mode. The two AY failure modes were characterised
on minimal single-`MovRR`/`MovRR32` witnesses, not across all 494 roots; the
route SPLIT is measured across all 3363, the per-width diagnosis is not.
