# Bumping Clean takes the SOURCE-BOUND route from 193 refusals to 12 (2026-09-28)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Continuing "bump and fix forward". After AY 0.26.0 -> 0.27.0 moved the bottleneck
from the solver to the CHECKER, `first-party/clean` was bumped too. It was **1561
commits behind** its remote main.

## The day, in one table

| step | failed roots | objects | source-bound refusals | sampling refusals |
| --- | ---: | ---: | ---: | ---: |
| baseline | 3363 | 67 | 494 | 2849 |
| in-repo `and_pos` retry | 3160 | 270 | 291 | 2849 |
| AY 0.26.0 -> 0.27.0 | 3062 | 368 | 193 | 2849 |
| **Clean `ec4b05723` -> `e75141b7b`** | **2881** | **549** | **12** | 2849 |

**Failed roots 3363 -> 2881. Emitted objects 67 -> 549, an 8.2x increase. The
source-bound proof route went 494 -> 12, a 97.6% reduction.** The sampling route
does not move at any step, which is the expected signature: none of this work
touches it.

## Why Clean was the bottleneck

Immediately after the AY bump, the remaining source-bound failures stopped being
AY refusing to publish and became the checker refusing to verify:

```
replay outcome=Unknown("AY reported UNSAT but .../clean — which verified a
known-good control proof, so it is a working checker — rejected or could not
fully verify THIS Alethe proof ...")
```

That message is worth reading precisely: Clean was WORKING (it verified a
known-good control), it simply could not check the proofs the newer solver emits.
A checker 1561 commits behind the solver it certifies is stale in the way that
matters. After the bump, on the trivial-binary witness: **`replay=Valid` x10 and
ZERO `replay=none`** — every replay failure on that program is gone.

## The trivial binary is now 5 roots away, and all 5 wait on the XD-01 route

Before today it was "many". After the `and_pos` retry, 7 — 5 sampling, 2 replay.
After both bumps, **5 — all of them sampling**:

```
5  x86_64::MovRR (no complete evidence: statistical sampling is not proof
   credit: `RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)` ...)
```

So every solver- and checker-side blocker for that program is closed, and what
remains is exactly the XD-01 question: whether a total, exactly-transcribed
result-bit-to-source-bit table equality counts as complete evidence for a register
move — or, equivalently, more source-bound theorem DOMAIN coverage so the
reconstructed route is not consulted at all. Ruled 2026-10-02 (XD-01 in the
decision record): the table equality is not admitted yet, so the route
is source-bound body coverage. Ruled 2026-10-02 (XD-01 in the
decision record): the table equality is not admitted yet, so the route
is source-bound body coverage. Ruled 2026-10-02 (XD-01 in the
decision record): the table equality is not admitted yet, so the route
is source-bound body coverage.

## Build recipe (both bumps)

    CARGO_TARGET_DIR=<dir> RUSTC=<stage2>/bin/trustc \
    RUSTFLAGS="-Ztrust-verify=off" RUSTDOCFLAGS="" \
    <stage2>/bin/targo --unverified build --release [--bin ay --features cli
                                                    | --features carcara-verify]

AY ~10m, Clean ~17m. `targo --unverified` ALONE is not enough — it does not
override the explicit rustflags in each project's `.cargo/config.toml`, so
`RUSTFLAGS` must be set or the `libc`/`unicode-ident`/`proc-macro2`/`quote` build
scripts fail under `channel = "trust"`. Clean's build emits a pre-existing,
NON-fatal `compiler_timeuot_secs` diagnostic from an intentionally malformed
control fixture in the `ty` checkout; its own
`reports/2026-09-25-literal-builtin-name-byte-observer.md` records that the exit
status is 0, and it is 0 here.

Clean is discovered by PATH at compile time, so no bridge rebuild was needed for
it — unlike AY, whose digest is recorded into the bridge at build time.

## What remains, with its owner

* **2849 sampling-route roots** — the XD-01 evidence decision, or source-bound
  domain widening. The largest single domain exclusion is 4632 occurrences of the
  frame gate, and 100% of those are the STACK SLOT condition (measured
  separately); that boundary is deliberate and pinned by
  `out_of_domain_sources_and_abis_are_unsupported`.
* **12 source-bound stragglers** plus ~20 scalar-FP moves.
* `MulU32` / `MulI16` remain unprovable even on AY 0.27.0 — both `bvmul`, with
  proofs that are ABSENT rather than partial (AY exports `rule=Trust
  clause=[false]` and `rule=Hole` whose clause is the negation of the whole
  asserted formula). That is solver work: a checkable derivation for bit-blasted
  multiplication.

## Provenance and scope

Census: stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)`, Trust repo
`ceb94fe99`, bridge from this tree, `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one
CGU, proofs REQUIRED, `PATH=/usr/bin:$PATH CC=/usr/bin/gcc`, wall 257s. Retained:
`gap_table.md`, `provenance.json`, `stderr.log.gz`.

The AY and Clean submodule moves live in `~/trust`, whose only remote is the
`alabsystems` RELEASE tier, and are NOT pushed: pushing there needs the owner's
release credential. Both
previous binaries are retained so either bump is reversible.
