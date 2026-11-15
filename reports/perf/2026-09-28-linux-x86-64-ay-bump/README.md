# Bumping AY 0.26.0 -> 0.27.0 promotes 98 more `core` roots, and moves the bottleneck to Clean (2026-09-28)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The owner directed "bump and fix forward for ay". Done, measured, and the
result relocates the remaining blocker.

| | roots | objects | source-bound refusals | sampling refusals |
| --- | ---: | ---: | ---: | ---: |
| baseline (this morning) | 3363 | 67 | 494 | 2849 |
| after the `and_pos` retry | 3160 | 270 | 291 | 2849 |
| **after the AY bump** | **3062** | **368** | **193** | 2849 |

Cumulative for the day: **3363 -> 3062 failed roots**, emitted objects
**67 -> 368**, and the source-bound route **494 -> 193**. The sampling route does
not move, as expected — nothing here touches it.

## What the bump was

`first-party/ay` is a pinned submodule and it was **1761 commits behind** its
remote main. The installed solver was `ay 0.26.0+build.9624.075a482ae`
(2026-09-14); upstream main is `c75076a20`, `ay 0.27.0+build.11385` — the same
0.27.0 line the Darwin slice-3 census used. Built and installed into the stage2
sysroot, then the bridge was rebuilt so AY admission records the new digest.

FIX-FORWARD NOTES, because none of the three obvious build routes works:

* `cargo build --bin ay` fails: the `ay` target needs `--features cli`.
* With the feature, the build dies on `libc`, `unicode-ident`, `proc-macro2` and
  `quote` BUILD SCRIPTS, because `rust-toolchain.toml` pins `channel = "trust"`
  and `.cargo/config.toml` forces `-Ztrust-verify=on -Ztrust-policy=certify` on
  every unit including build scripts and proc-macros.
* `RUSTUP_TOOLCHAIN=1.97.1` does not rescue it either — stock rustc rejects the
  `-Z` options the config injects.
* What works: the Trust compiler with verification explicitly off —
  `CARGO_TARGET_DIR=target-unv RUSTC=<stage2>/bin/trustc RUSTFLAGS="-Ztrust-verify=off"
  RUSTDOCFLAGS="" targo --unverified build --release --bin ay --features cli`
  (10m17s). `targo --unverified` ALONE is not enough: it does not override the
  config's explicit rustflags.

## What it fixed, measured per obligation

All 65 conjunctive queries in
`crates/trust-cg-verify/tests/fixtures/x86_source_bound_body/snapshots.smt2`, run
under both solvers:

| ay 0.26.0 | ay 0.27.0 | queries | examples |
| --- | --- | ---: | --- |
| proof | proof | 48 | Add, Sub, U8Ident, I16Ident |
| `and_pos` | **proof** | 9 | Ident, Const, BlackBox, PtrCast |
| `unverified trust rule` | **proof** | 4 | BoolIdent, ShlImm, LshrImm, AddShl2 |
| incomplete | **proof** | 2 | BoolAnd, BoolXor |
| `unverified trust rule` | unchanged | 1 | MulU32 |
| incomplete / hole | unchanged | 1 | MulI16 |

**15 newly provable, 0 regressed** — 48/65 becomes 63/65. The bump fixes BOTH
classes this repo had characterised separately: the `and_pos` publication refusal
AND the `trust rule` class that was shown to be unfixable inside trust-cg without
defeating `simplifier_alone_proved_unsat`.

It also makes the in-repo `and_pos` retry redundant on this solver. The retry is
kept: it is narrow, fail-closed, keeps the original result when it does not help,
and the repo must still behave correctly against an older admitted AY.

## IS THERE AN EVEN NEWER AY? No.

Re-fetched after building: origin/main is `1dd268205`, exactly **4 commits**
ahead of what was built, and all four are docs, a deps pin move and a merge —
nothing touching proof emission. So 0.27.0+build.11385 is current for this
purpose.

## The two that remain are a real AY capability gap

Both are `bvmul` obligations, and their proofs are not partial — they are absent.
With `--debug-cert`, AY discloses the step it could not justify:

* `MulU32`: `rule=Trust clause=[(not false)]` then `clause=[false]` — the formula
  was reduced internally and the conclusion exported as a trust step.
* `MulI16`: `rule=Hole clause=[(not (and (= p0 ((_ extract 15 0) e_rdi)) ...)))]`
  — the hole's clause is the NEGATION OF THE WHOLE ASSERTED FORMULA. One step,
  asserting the entire goal.

So AY decides these by bit-blasting and has no Alethe-expressible derivation for a
multiplier. AY does carry a DEFERRED-TRUST lane built for exactly this — collect
the unjustified clause and discharge it independently
(`checker/step_validation.rs`: a `Trust`/`Hole` step is deferred when a collector
is present and hard-rejected when it is `None`) — but it does not help here, for
two independent reasons:

1. Its own documentation states the strict screen withholds such a refutation
   deliberately: "a nested refutation accepted only under the deferred-trust
   discharge screen is not grant authority", and the CLI sets that under
   `--rigor strict|certified`.
2. Even if AY accepted it, trust-cg's evidence is an Alethe proof REPLAYED BY
   CLEAN. A published proof containing a `Trust`/`Hole` step is exactly what an
   independent checker cannot verify, so accepting it upstream would not produce
   replayable evidence.

Closing this needs AY to emit a checkable derivation for bit-blasted
multiplication. That is solver work, not backend work.

## The tier-0 verdict DB cannot be regenerated on this host, and it is NOT the bump's fault

`verdict_db/tier0.vdb` records `solver-version: build.version=0.11.0` and
`provenance: ... regen, ay 0.11.0`, so the committed DB is 16 minor versions stale
against the installed solver, and the certificate store declines a solver-identity
mismatch (`consume_declines_solver_identity_mismatch`). Regenerating it is
therefore the obvious move, and it turns out to be possible to ATTEMPT here for
the first time: the stock-built root workspace records no toolchain AY identity
(`[TCG-AY-IDENTITY-UNRECORDED]`), but the same workspace builds under
`RUSTC=<stage2>/bin/trustc` and then records one. `regen_verdict_db` built that way
admits the solver and re-proves 1865 registry obligations.

It still FAILS, at a seed:

```
pass[x86-popcnt-expand]: popcount SWAR expansion matches spec on x86_64 (i32):
fail-closed: solver unknown ((:reason-unknown (incomplete self-check-rejected)))
```

and the tool writes nothing unless every seed discharges `Verified`, so nothing
was written. NOTE the rebuild must follow the install: a regen binary built before
the new solver was installed refuses with `[TCG-AY-IDENTITY-MISMATCH]`, naming
both digests.

**This is not a regression from the bump.** Extracting that seed's query straight
out of the committed DB and running it under both solvers gives the same answer:

| solver | popcnt SWAR (i32) seed |
| --- | --- |
| ay 0.26.0+build.9624 | `unknown`, `unsupported hole rule` |
| ay 0.27.0+build.11385 | `unknown`, `unsupported hole rule` |

So tier-0 regeneration was already impossible on this host before today, and the
committed DB's ay-0.11.0 provenance records a solver that could still discharge it.

## The one remaining AY item, characterised

Every solver-side blocker left is the SAME shape: a bit-heavy arithmetic
obligation AY decides by bit-blasting and then cannot express as an Alethe
derivation, so it exports `Trust`/`Hole` and strict certification refuses. It
covers `MulU32` and `MulI16` (the two snapshot queries) and the popcnt SWAR seed
that blocks tier-0 regeneration. Improving AY for this project means exactly one
thing: **emit a checkable Alethe derivation for bit-blasted arithmetic** — a
CNF/DRAT-to-Alethe path for multipliers and SWAR popcount. Nothing in trust-cg
substitutes for it, because the evidence trust-cg accepts is a proof an
independent checker replays, and a `Trust`/`Hole` step is precisely what cannot be
replayed.

## AND THE BOTTLENECK MOVED: Clean now rejects proofs AY publishes

On the trivial-binary witness the distance is unchanged at 7 roots (5 sampling,
2 source-bound), but the 2 source-bound ones fail somewhere NEW. Their replay
outcome is no longer AY refusing to publish:

```
replay outcome=Unknown("AY reported UNSAT but .../clean — which verified a
known-good control proof, so it is a working checker — rejected or could not
fully verify THIS Alethe proof ...")
```

6 obligations replay Valid on that binary and 4 fail here. So the newer AY emits
proofs the pinned Clean cannot check. `first-party/clean` is **1561 commits
behind** its remote main (`0.9.0`, `ec4b05723` -> `e75141b7b`), so it is stale
against the solver it is meant to check. Bumping it is the next fix-forward step
and is in progress.

Fix-forward note for that build too: it emits `error: unknown field
`compiler_timeuot_secs`` from an intentionally MALFORMED negative-control fixture
in the `ty` dependency checkout. That diagnostic is pre-existing and NOT fatal —
Clean's own `reports/2026-09-25-literal-builtin-name-byte-observer.md` records it
and states "the actual build exit status is 0".

## Provenance and scope

Census: bridge rebuilt from this tree, stage2 `trustc 1.99.0-dev (3a3e781fe
2026-09-14)`, Trust repo `ceb94fe99`, `-Ztrust-verify=off`, O0, `-Cpanic=abort`,
one CGU, proofs REQUIRED, `PATH=/usr/bin:$PATH CC=/usr/bin/gcc`, wall 254s.
Retained: `gap_table.md`, `provenance.json`, `stderr.log.gz`.

The AY and Clean submodule moves live in the `~/trust` checkout, whose only
remote is the `alabsystems` RELEASE tier. They are NOT pushed: pushing there
needs the owner's release credential. The previous solver is retained beside this report's scratch
as `ay-0.26.0.backup` so the bump is reversible.
