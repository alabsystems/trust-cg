# Darwin AArch64 qualification of the x86-64 body lane on AY build 12713, 2026-10-16

This record gives `aarch64-apple-darwin` its own qualified replayer pair for
the x86-64 source-bound body lane (`crates/trust-cg-verify`, every
`*_qualification` test), from real runs on this host, the way `4c6ce87e8` gave
`x86_64-unknown-linux-gnu` one. Before it, every lane that checks the pair
panicked here with "no qualified replayer pair is recorded for host
aarch64-apple-darwin". The ruling is the "Applied: Darwin AArch64" addendum to
DR-PER-HOST-QUALIFIED-PAIR-20261015 in
docs/decision-record.md; LIMITATIONS.md
states what it implies.

These lanes replay the x86-64 body theorems' SMT queries with AY and check
AY's Alethe proofs with Clean. Nothing here executes x86-64 code, and nothing
here is a completion claim.

**Measured tree.** trust-cg `origin/main` `190b3e53d` plus this branch
(`qual/aarch64-darwin-20261016`). **Host.** Apple M5 Max (`Mac17,6`, 18
CPUs: 6 Super and 12 Performance cores, 128 GiB), macOS 26.6.2 (`25G83`),
Darwin 25.6.0 arm64, on AC power, shared with other
agents' builds: the 1-minute load ran from 4 to 113 during this work, and each
run's load, sampled every 30 s, is in `load/`. **Toolchain.** Trust package 9192
(`trustc` `321aaeda7`), `targo --unverified` through `scripts/trust_cargo.sh`
(no proof claim about any build); heavy jobs through `build-slot`.

## The pair

| | AY | Clean |
| --- | --- | --- |
| binary | `bin/ay` of the overlay below (built at `ay-target/release/ay`) | `bin/clean` of the overlay below (built at `clean-target/release/clean`) |
| identity | `ay 0.27.0+build.12713.b1b0b9de07af146c1244633189f92971a3347db9` (`QUALIFIED_AY`) | `clean 0.9.0+g92bcc897908b248154ace880a6c518a3d9c09634`; the commit is embedded in the binary |
| sha256 | `dd6d36615a46f753d8ea6f98a73341648409805bf1b4392d6a0accadc37de671` | `80090967fcad609d43f42af52d22198702d186e3be8d88656e7658e4cf307116` (the new `QUALIFIED_CLEAN_SHA256_BY_HOST` row) |
| source | an `~/ay` worktree at `b1b0b9de0`, clean tree; build number = `git rev-list --count` | an `~/clean` worktree at `92bcc8979`, the revision trust-cg's `Cargo.lock` pinned when the pair was measured (it pins `e05c6fdd6` since LD-PIN6382-2, which re-qualifies nothing) |
| build | `targo --unverified build --release --locked -p ay --features cli`, from a sibling directory whose `.cargo/config.toml` is AY's minus its Trust-lane block (`strip_trust_lane_config`): 288 s wall | `scripts/trust_cargo.sh build --locked --release -p clean --bin clean --features clean/carcara-verify`: 659 s wall |

[`commands/build_and_assemble.sh`](commands/build_and_assemble.sh) holds every
command. Both binaries are unverified local builds, unsigned, and not release
inputs.

**How the test build admits AY 12713.** `trust-cg-verify`'s `build.rs`
records the AY of the toolchain that builds it, and a Trust build always
records one: package 9192's AY 0.26.0 build 9624. `TCG_X86_BODY_QUALIFY_AY`
is read only when the build records none, which only a stock build does, so
it cannot select build 12713 here. The documented route is OD-85's local
overlay (`scripts/assemble_trust_overlay.py`): an APFS clone of package 9192
with `bin/ay` and `bin/clean` replaced and an `overlay.json` naming both
digests. `TRUST_TARGO=<overlay>/bin/targo` makes `build.rs` record the
overlay's AY through the unchanged digest rule, and pins the overlay's Clean
as the only checker that build accepts. The overlay lives in scratch;
nothing was installed into a toolchain or package store. Its manifest is
`4c7a49f3c5565d06b2fd7adf94f2615e885b28fa5c6e2d108b69c554f6520f86`. Every
lane prints the pair it ran:

```text
X86_BODY_REPLAY_IDENTITY test=... ay=[route=toolchain-pinned-ay toolchain=<R>/overlay-ay12713-clean92bc (build-compiler) ay=<R>/overlay-ay12713-clean92bc/bin/ay identity=[ay 0.27.0 build 12713 commit b1b0b9de07af146c1244633189f92971a3347db9 sha256 dd6d36615a46f753d8ea6f98a73341648409805bf1b4392d6a0accadc37de671 overlay-toolchain manifest-sha256 4c7a49f3c5565d06b2fd7adf94f2615e885b28fa5c6e2d108b69c554f6520f86 clean-sha256 80090967fcad609d43f42af52d22198702d186e3be8d88656e7658e4cf307116 clean-commit 92bcc897908b248154ace880a6c518a3d9c09634]] ay_banner=[ay 0.27.0+build.12713.b1b0b9de07af146c1244633189f92971a3347db9@2026-10-16T20:56:19Z] clean=<R>/overlay-ay12713-clean92bc/bin/clean clean_sha256=80090967fcad609d43f42af52d22198702d186e3be8d88656e7658e4cf307116
```

(`<R>` is `~/scratch.noindex/round3-20261016`.)

## Why the checker is not the package's Clean 8606

In an ordinary build on this host, default discovery skips the toolchain's own
`bin/clean` (built without `carcara-verify`) and selects the package's Clean
8606 (`9c594e838ff7e73815977c2d675238828f82417e77986abfe38d75b8ab060e16`,
`clean 0.9.0`; its binary embeds commit `8da2da391`, whose `rev-list --count`
is 8606). That was measured first, as this pair's checker, through an overlay
with the same AY and Clean 8606 (`b88f1445…`): measure 0 below.

* 0 of 34 lanes passed. They reached 512 replays: 10 were the expected
  refutations of wrong lowerings (`CounterExample`), and of the other 502,
  151 certified, 285 were proofs Clean rejected as a working checker ("AY
  reported UNSAT but ... rejected or could not fully verify THIS Alethe
  proof", `SOUNDNESS`), and 66 were AY's own answers: 51 timeouts, 14
  self-check rejections and one unrenderable proof
  (`outcomes/measure0-clean8606.tsv`). Measure 1, the same AY with Clean
  `92bcc8979`, rejects none.
* Offline ([`commands/offline_replay.py`](commands/offline_replay.py) over
  every dumped query, `offline/measure0-clean8606-30s.tsv`):
  of the 396 queries AY answers `unsat`, Clean 8606 rejects 246, and Clean
  `a5d3fe0df` (a newer local build, diagnostic only) fully verifies all 396.
* What Clean 8606 lacks: the `zero_extend` spelling this AY's proofs use
  (`refl` 131 times, `cong` 40), its `poly_simp` normalization (65), and the
  rules `bitblast_shl`, `bitblast_lshr` and `bitblast_urem` (10, "unknown
  rule"). AY build 12713 announces the first itself:
  `carcara_surface=clean-dialect — a zero_extend word is checked as the concat
  Clean's parser normalizes it to`.

A checker that cannot read the AY's proofs measures the checker, not the body
theorems. The pair therefore takes a named, capable Clean, and the revision
is the one this tree pinned when it was measured, not whichever certifies
most.

## Runs

Each run is the first step of
[`commands/qualify.sh`](commands/qualify.sh): `--lib _qualification`, 47
tests of which 13 are `#[ignore]`d printers, one process,
`--test-threads=1` (measure 0 left `TCG_EXTERNAL_CLEAN_CHECKER` unset, and
discovery selected its overlay's Clean 8606). On `main`'s tables every lane
that checks the pair (18 of the 34) refuses here, "no qualified replayer pair
is recorded for host aarch64-apple-darwin". (Those counts are the 2026-10-16
tree's. Since "Harness round 2" below, the filter selects 48 tests, 14 of
them `#[ignore]`d (the printers and the explicit 300 s lane), and every one
of the 34 others checks the pair, as do the two credit lanes the filter does
not select. Since "Fail closed" below, it selects those two as well, 50
tests of which 14 are `#[ignore]`d, and `qualify.sh` runs the explicit lane
after it: the script is now the whole qualification.)

| Run | Pair | Tables | UTC | Wall | 1-minute load (min-max, mean) | Result |
| --- | --- | --- | --- | ---: | --- | --- |
| measure 0 (`logs/measure0-clean8606.log`) | AY 12713 + Clean 8606 | `main` | 21:03:53-21:36:44 | 1971 s | 4.3-26.8, 11.1 | 0 passed, 34 failed |
| measure 1 (`logs/measure1-clean92bc.log`) | AY 12713 + Clean 92bcc8979 | `main` | 21:52:16-22:30:20 | 2284 s | 4.7-23.8, 9.7 | 12 passed, 22 failed |
| confirm 1 (`logs/confirm1.log`) | same | first aarch64 rows | 22:36:14-23:17:19 | 2466 s | 27.6-56.2, 38.3 | 32 passed, 2 failed |
| confirm 2 (`logs/confirm2.log`) | same | slice 14 deadline-bound | 23:25:02-00:04:55 | 2394 s | 6.9-47.2, 17.3 | 32 passed, 2 failed |
| confirm 3 (`logs/confirm3.log`) | same | slices 12 and 14 deadline-bound | 00:16:20-00:56:53 | 2433 s | 12.1-108.4, 22.7 | 34 passed, 0 failed |
| negative control (`logs/negative-control.log`) | same | confirm 3's, aarch64 digest `8009…` changed to `9009…` | 01:02:52-01:42:24 | 2372 s | 5.9-70.6, 26.0 | 15 passed, 19 failed |
| **confirm 4** (`logs/confirm4.log`) | same | **this commit** | 01:53:13-02:32:07 | 2334 s | 8.7-22.6, 13.5 | **34 passed, 0 failed** (13 ignored) |

* Measure 1 fails exactly where a missing host row must fail: 18 lanes at
  the identity check after printing every outcome, slice 1 at `MulI16`'s
  outcome, and the credit lanes of slices 11, 12 and 14 on the shapes that
  certify here (`SubU128: left 0, right 8`, `EarlyExit: left 0, right 25`)
  or time out (`GuardedUdiv`).
* Confirm 1 and 2 each failed one slice on an obligation whose answer
  flipped between runs (slice 14's pair, then `EarlyExit`); confirm 3 passed
  with `GuardThenCall` timing out.
* The negative control is confirm 3's tree with the recorded aarch64 digest
  changed by one hex digit (reverted afterwards). All 18 lanes that check the
  pair refuse: "the pinned qualification outcomes for host
  aarch64-apple-darwin were measured with [ay 0.27.0 build 12713 commit
  b1b0b9de...] and Clean sha256 90090967...; this host admits [...] and Clean
  sha256 80090967...". The 15 credit lanes pass; they did not check the pair
  (they do since 2026-10-17, "Harness round 2" below).
  The nineteenth failure is slice 1's canonical lane, which did not check the
  pair either (pre-existing, on `main` too; it does since 2026-10-17, "Harness
  round 2" below): it failed on `MulI16`, which ran
  past the deadline at load 54-71. That answer is why `MulI16` joined the
  deadline-bound record in this commit; confirm 4 is the run of the result.

## Every difference from the recorded tables

The recorded tables are the Darwin x86-64 pair's (AY 12713, Clean 5f09e36c).
On this pair, every other outcome is identical, including every encoding
record: slice 1's preserved tail, UF + world and concatenated forms, the
memory encodings, slice 6's `(=> C X)` and merged spellings, slice 9's
spellings, slice 16's parts and its unrefuted part, slice 17's mis-models,
and every refutation.

| Lane | Label | Recorded | Here | Record |
| --- | --- | --- | --- | --- |
| slice 11 | `SubU128` | gap, `Timeout` | certifies, 8.4-27.2 s on every run | `CERTIFIED_HERE_BY_HOST` |
| slice 11 | `SlotU128` | gap, `Timeout` | certifies, 9.1-25.8 s on every run | `CERTIFIED_HERE_BY_HOST` |
| slice 1 | `MulI16` | gap, `Timeout` | gap: AY's self-check rejection (`SOUNDNESS`) in 17.6-29.9 s, or `Timeout` at load 54-71 | `DEADLINE_BOUND_HERE_BY_HOST` |
| slice 12 | `EarlyExit` | gap, `Timeout` | certifies, except once past the deadline | `DEADLINE_BOUND_HERE_BY_HOST` |
| slice 14 | `GuardedUdiv` | certifies | certifies on 16 of 19 attempts, 5 of the 7 lane runs | `DEADLINE_BOUND_HERE_BY_HOST` |
| slice 14 | `GuardThenCall` | certifies | certifies on 9 of 19 attempts, 2 of the 7 lane runs | `DEADLINE_BOUND_HERE_BY_HOST` |

`SubU128`, `SlotU128` and `MulI16` match the Linux pair's rows, which stay
keyed to that host; `EarlyExit` is a third Linux row, deadline-bound here.

### Deadline-bound obligations

An obligation that needs most of the lane's 30 s deadline answers one way on
one run and another way on the next on a host this shared. A fixed record of
one answer makes its lane fail on a coin toss, so these get a fourth per-host
record, `DEADLINE_BOUND_HERE_BY_HOST`, which names every measured answer with
its `proof_gate` class, and whose gap lanes accept no other: a label some runs
certify is dropped by its gap lane only when it carries a measured answer,
outcome and class, and its credit lane takes every bound row credited or every
bound row awaiting replay, never a mix (an awaiting row does not say why, so
the credit lane cannot tell a timeout from another answer); `MulI16`, which no
run certifies, stays a recorded gap whose lane accepts either of its two
reasons. The 30 s deadline is not raised. The 30 s lanes cannot notice a
label that some runs certify ceasing to certify here altogether, since they
accept `Timeout` for it on every run; the explicit lane of "Harness round 2"
below replays each deadline-bound label with the 300 s budget and does.

| Attempt | Kind | UTC | Load | `EarlyExit` | `GuardedUdiv` | `GuardThenCall` | `MulI16` | `SubU128` | `SlotU128` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| measure 0 | lane (Clean 8606) | ~21:10 | ~10 | AY 20.3 s, checker rejected | Timeout | Timeout | rejected 22.0 s | AY 11.2 s, checker rejected | AY 9.1 s, checker rejected |
| measure 1 | lane | ~22:00 | 9-16 | 23.0 s | Timeout | Timeout | rejected 21.0 s | 13.5 s | 10.3 s |
| 300 s offline | one process | 22:31-22:35 | 8-37 | | `unsat` 75.0 s | `unsat` 164.4 s | | | |
| confirm 1 | lane | ~22:40 | 27-40 | 35.6 s | 2.6 s | 5.1 s | rejected 18.9 s | 17.0 s | 14.6 s |
| 30 s offline x3 | one process | ~23:00 | ~31 | | 2.2-2.4 s | 3.6-4.1 s | | | |
| 30 s offline x8 | one process | 23:17-23:20 | 30-58 | | 1.6-5.3 s (8 of 8) | 4 Timeout, then 4 at 3.8-6.8 s | | | |
| confirm 2 | lane | ~23:30 | 24-47 | **Timeout** | 2.2 s | 3.3 s | rejected 29.9 s | 22.1 s | 20.9 s |
| 30 s offline x6 | one process | 00:05-00:11 | 8-10 | 17.1-18.6 s | | | rejected 17.6-19.0 s | 8.4-10.9 s | 9.1-9.7 s |
| 30 s offline, 12 at once | 12 processes | 00:11 | 8-10 | 20.5 s | | | rejected 20.8 s | 11.0 s | 11.5 s |
| confirm 3 | lane | ~00:20 | 13-32 | 32.2 s | 1.7 s | **Timeout** | rejected 23.0 s | 20.0 s | 17.1 s |
| negative control | lane | ~01:04-01:10 | 54-71 | 38.1 s | 1.6 s | **Timeout** | **Timeout** | 27.2 s | 25.8 s |
| confirm 4 | lane | ~01:55-02:05 | 9-20 | 26.5 s | 1.7 s | **Timeout** | rejected 22.5 s | 15.6 s | 12.3 s |
| negative control, round 2 (10-17) | lane | 09:35-10:09 | 42-98 | 38.4 s | 2.0 s | 3.3 s | **Timeout** | 40.7 s | 16.3 s |
| gate, round 2 | lane | 10:26-11:04 | 12-67 | 28.2 s | 2.8 s | 3.7 s | **Timeout** | 12.6 s | 13.6 s |
| deadline-bound lane, round 2 | lane route, 300 s budget | 11:16-11:19 | 22-29 | 22.7 s | 75.7 s | 92.8 s | rejected 17.9 s | | |
| gate, landing (10-17) | lane | 13:42-14:22 | 8-43 | 30.8 s | **Timeout** | **Timeout** | rejected 18.8 s | 16.2 s | 12.3 s |
| deadline-bound lane, landing | lane route, 300 s budget | 14:26-14:31 | 18-73 | 27.4 s | 99.6 s | 94.0 s | rejected 30.5 s | | |
| gate, landing merged tip | lane | 14:40-15:20 | 12-47 | 36.6 s | 2.3 s | 3.8 s | rejected 23.8 s | 16.4 s | 11.9 s |
| deadline-bound lane, merged tip | lane route, 300 s budget | 15:20-15:23 | 11-14 | 31.4 s | 1.7 s | 102.1 s | rejected 24.4 s | | |

Lane times include Clean's check (`SubU128`'s 40.7 s in round 2's
negative control is a certification: AY answered inside its 30 s); offline
times are AY plus Clean
(`offline/near-deadline-repeats.tsv`,
[`commands/burst.sh`](commands/burst.sh) for the twelve at once). Clean
`92bcc8979` fully verifies every offline `unsat` above (all 47 such rows of
the TSV). Every row of both recorded TSVs predates the 2026-10-17 fix to
`offline_replay.py` ("Harness round 2" below): its `ay_tail` holds AY's last
two output lines alone. On the 29 `unsat` rows of `GuardedUdiv`,
`GuardThenCall` and `SubU128` they show `unproved_steps=0 trust_free=yes`;
on the 18 of `EarlyExit` and `SlotU128` the last line is AY's
`carcara_surface=clean-dialect` warning instead, so the TSV does not show the
field for them (nor for 236 of the 396 `unsat` rows of
`offline/measure0-clean8606-30s.tsv`). Rows written since the fix carry the
fields first, extracted from AY's whole output. `EarlyExit`'s and `MulI16`'s times grow with the load
other builds put on the host's 18 CPUs: load, not capability.
`GuardedUdiv`'s and `GuardThenCall`'s do not: they are fast or minutes long,
clustered in time, at loads that overlap. Both kinds certify given the time:
budget, not capability. `SubU128` and `SlotU128` gave one answer on every run
(up to 27.2 s and 25.8 s, at load 54-71), so they keep exact records; a
heavier load than measured can still make them answer `Timeout`, which their
records refuse.

## Outcome table

`outcomes/confirm4.tsv` holds every replay of the
final run (test, label, class, milliseconds, outcome), and `outcomes/` the
same for every other run; [`commands/outcomes.py`](commands/outcomes.py)
extracts them from the logs. Per lane, in confirm 4:

| Test | Result | Replays | Certified | Not certified at the deadline (label: outcome) |
| --- | --- | ---: | ---: | --- |
| `arraygep_qualification::host_qualification_replays_the_arraygep_body_theorems` | ok | 18 | 18 | - |
| `arraygep_qualification::verifier_credits_every_bound_arraygep_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `memory::host_qualification_replays_the_memory_body_theorems` | ok | 35 | 35 | - |
| `sext_bool_qualification::host_qualification_replays_the_bool_sign_extension_theorems` | ok | 7 | 7 | - |
| `sext_bool_qualification::verifier_credits_every_bound_bool_sign_extension_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `host_qualification_replays_the_canonical_body_theorems` | ok | 79 | 77 | `MulI16`: self-check rejected, `Mul/commuted`: Timeout |
| `slice10_qualification::host_qualification_replays_the_slice_ten_body_theorems` | ok | 25 | 23 | `MulU64`: Timeout, `MulPanics`: Timeout |
| `slice10_qualification::verifier_credits_every_bound_slice_ten_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice11_qualification::host_qualification_replays_the_slice_eleven_body_theorems` | ok | 36 | 35 | `MulU128`: Timeout |
| `slice11_qualification::verifier_credits_every_bound_slice_eleven_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice12_qualification::host_qualification_replays_the_slice_twelve_body_theorems` | ok | 20 | 20 | - |
| `slice12_qualification::verifier_credits_every_bound_slice_twelve_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice13_qualification::host_qualification_replays_the_slice_thirteen_body_theorems` | ok | 20 | 20 | - |
| `slice13_qualification::verifier_credits_every_bound_slice_thirteen_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice14_qualification::host_qualification_replays_the_slice_fourteen_body_theorems` | ok | 28 | 25 | `UdivConst`: Timeout, `UremConst32`: Timeout, `GuardThenCall`: Timeout |
| `slice14_qualification::verifier_credits_every_bound_slice_fourteen_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice15_qualification::host_qualification_replays_the_slice_fifteen_body_theorems` | ok | 22 | 22 | - |
| `slice15_qualification::verifier_credits_every_bound_slice_fifteen_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice16_qualification::host_qualification_replays_the_slice_sixteen_parts` | ok | 26 | 22 | `LongChain part 1`: Timeout, `LongChain part 2`: Timeout, `LongChain part 3`: Timeout, `refutation a branch inverted mid-chain part 2`: Timeout (and 10 parts of refuted wrong lowerings) |
| `slice16_qualification::verifier_credits_every_bound_row_of_a_function_in_parts` | ok | - | - | - |
| `slice17_qualification::host_qualification_refutes_every_slice_seventeen_mis_model` | ok | - | - | - |
| `slice17_qualification::host_qualification_replays_the_slice_seventeen_body_theorems` | ok | 22 | 22 | - |
| `slice17_qualification::verifier_credits_every_bound_slice_seventeen_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice5_qualification::host_qualification_replays_the_slice_five_body_theorems` | ok | 43 | 43 | - |
| `slice5_qualification::verifier_credits_every_bound_slice_five_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice6_qualification::host_qualification_replays_the_slice_six_body_theorems` | ok | 28 | 28 | - |
| `slice6_qualification::verifier_credits_every_bound_slice_six_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice7_qualification::host_qualification_replays_the_slice_seven_body_theorems` | ok | 15 | 15 | - |
| `slice7_qualification::verifier_credits_every_bound_slice_seven_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice8_qualification::host_qualification_replays_the_slice_eight_body_theorems` | ok | 22 | 22 | - |
| `slice8_qualification::verifier_credits_every_bound_slice_eight_row_with_the_replayed_body_theorem` | ok | - | - | - |
| `slice9_qualification::host_qualification_records_the_slice_nine_spellings` | ok | 75 | 29 | encoding evidence: Timeout 33, self-check rejected 12, Unknown("(:reason-unknown (incomplete proof-unrenderable))") 1 |
| `slice9_qualification::host_qualification_replays_the_slice_nine_body_theorems` | ok | 15 | 7 | `Diamonds5`: Timeout, `Diamonds6`: Timeout, `GuardChain9`: Timeout, `SwitchChain`: Timeout, `LongArm`: Timeout, `LongChain`: self-check rejected, `CallJoin`: Timeout, `LoadDag`: Timeout |
| `slice9_qualification::verifier_credits_every_bound_slice_nine_row_with_the_replayed_body_theorem` | ok | - | - | - |

The slice-16 row's `refutation ... part 2` is the recorded unrefuted part of a
wrong lowering (`KNOWN_UNREFUTED_SLICE_SIXTEEN`), not a correct one. Slice 1's
encoding records and the memory encodings print as their own lines and match.

## Gates on the final tree

All on this host, on the recording commit `3b31c460a` unless a row says
otherwise; the landing's gates are under "Landing" below.

| Gate | Command | Result |
| --- | --- | --- |
| format | `scripts/check_fmt.sh` | OK, every workspace file matches trustfmt |
| documentation | `python3 scripts/check_documentation.py --check` | OK |
| lint, `trust-cg-verify` | the `check_tippy.sh` invocation for the package: `targo tippy --locked -p trust-cg-verify --lib --tests --no-deps --keep-going --message-format short` (`logs/tippy-trust-cg-verify.log`) | exit 0, no finding, on the final tree (2 min of linting after a wait for a build slot; an earlier pass found one `iter().any()` that is now `contains()`) |
| qualification | `--lib _qualification`, confirm 4 above | **34 passed, 0 failed**, 13 ignored; 2330 s at load 8.7-22.6 |
| negative control | the same with the aarch64 digest changed by one hex digit, then reverted | every lane that checks the pair (18) refuses on the digest |
| `trust-cg-verify --lib`, once | `scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib` on the overlay, default test threads (`logs/full-lib-summary.log`) | 5915 passed, 20 failed, 72 ignored of 6007, 2648 s at load 8.4-35.1; all 34 qualification lanes pass inside it |
| the 20, on `main` | the same 20 tests by exact name on `origin/main` `190b3e53d` with the same overlay (`logs/base-same-pair-20-failures.log`) | the same 20 fail: nothing else moved |

The 20 are the pair's solver capability outside this lane, none in a file this
change touches: 13 `ay_bridge` tests (floating-point round trips and
identities, a constant array, an expanded buffer, the arithmetic subset of
the proof database), `checked_overflow_proofs` (`CheckedSadd_I128`: AY's
self-check rejection), two `function_request` and one `read_only_replay`
diagnostic, one `verdict_db` memo test and two `wasm_value_domain` formal
discharges. They are what this AY and Clean prove on this host, measured on
`main`, and are not this record's to triage.

Confirm 4 ran this commit's code except two comments' figures, edited
afterwards: `SubU128`/`SlotU128`'s range, widened to 27.2 s by the
negative-control run, and the load range in a `DEADLINE_BOUND_HERE_BY_HOST`
comment. The full `--lib` run and the lint pass are of the code with the
first edit; the second is a `//` comment, which neither compiles nor lints.

## Landing

Two reviews shipped this record and refuted six of its statements; they are
corrected above, in the code's comments, in LIMITATIONS.md and in the
decision record ("Corrected at landing"). One was about the code:
`settle_here`, which the slice-12 and slice-14 gap lanes call, let an answer
an entry does not name through when its outcome equalled the recorded one,
and never compared the `proof_gate` class. The gap lanes now pass the class,
and an answer whose outcome and class are not both measured is marked "not
an answer measured for it at the deadline on this host", which no recorded
outcome equals.

The controls add two temporary `DEADLINE_BOUND_HERE_BY_HOST` entries to the
slice-14 table, reverted afterwards, and run that table's gap lane alone
(`host_qualification_replays_the_slice_fourteen_body_theorems`, the same
overlay and pair). `UdivConst` and `UremConst32` are recorded `Timeout` gaps
there and timed out on every run below.

| Run | Code | Temporary entries | Load (1-minute, test window) | Result |
| --- | --- | --- | --- | --- |
| negative control, before (`landing/nc-before.log`) | `3b31c460a` | `UremConst32` [self-check rejection]; `UdivConst` [`("Timeout", "SOUNDNESS")`] | 11.4-17.3 | **passed**: both `Timeout`s accepted, one with an unmeasured answer and one under the wrong class |
| negative control, after (`landing/nc-after.log`) | the fix | the same | 31.0-38.5 | **failed**: left `[("UdivConst", "Timeout / PENDING(solver-capacity): not an answer measured for it at the deadline on this host"), ("UremConst32", ...)]`, right `[("UdivConst", "Timeout"), ("UremConst32", "Timeout")]` |
| positive control (`landing/pc-after.log`) | the fix | `UdivConst` [`Verified`, `Timeout`]; `UremConst32` [self-check rejection, `Timeout`] | 17.4-22.1 | **passed**: both measured `Timeout`s accepted, and the recorded `GuardThenCall` entry's `Timeout` too |

At the merged tip `23f87ff3c` (this lane merged with `origin/main`
`c72ecf73f`, whose three commits change `docs/decision-record.md` only):

| Gate | Result |
| --- | --- |
| `scripts/check_fmt.sh` | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `targo tippy --locked -p trust-cg-verify --lib --tests --no-deps --keep-going --message-format short` (package 9192, `landing/tippy-merged.log`) | exit 0, no finding |
| `scripts/check_tippy.sh`, the pre-push hook's lint pre-flight, every package (`landing/check-tippy-all.log`) | OK, 19 packages clean |
| `--lib _qualification`, `commands/qualify.sh`'s invocation (`landing/qualification-merged.log`, `landing/qualification-merged.tsv`) | **34 passed, 0 failed**, 13 ignored; 2328 s at load 14.4-104.1 (mean 28.5); every lane names AY build 12713 (`dd6d3661…`) and Clean `80090967…` |

In that run `MulI16` was AY's self-check rejection (27.9 s), `EarlyExit`
certified in 30.7 s, `GuardedUdiv` in 1.9 s and `GuardThenCall` in 3.6 s,
and `SubU128` and `SlotU128` in 17.2 s and 13.1 s; slice 14's other two gaps
timed out as recorded. The payloads are under `landing/` in the payload
directory below, with the three helpers that made the controls
(`run_lane.sh`, `mutate-negative.py`, `mutate-positive.py`) and the anchor
verifier's verdict on the merged tip (`anchored-verify.log`: no record yet,
as for every landing while the interim exception is in force).

## Harness round 2 (2026-10-17)

The landing's reviews left three things open. Each is fixed at its cause,
in `crates/trust-cg-verify/src/x86_source_bound_body_tests.rs` (and the
lanes that call it) and in this record's `offline_replay.py`; the ruling is
the "Every lane checks the pair" addendum to DR-PER-HOST-QUALIFIED-PAIR-20261015.
The pair, the overlay, the host and the commands are the ones above; the
tree is trust-cg `origin/main` `bd0837748` plus `a7f4697de`, `9b52b5b52`
and `92c518f7d` (branch `qual/harness-r2-20261017`), whose code every run
below ran. A later commit edits one doc comment; the format and lint gates
ran again on it.

### Every lane checks the pair

`assert_qualification_replayer` was a call each lane had to remember. Slice
1's canonical lane and every credit lane did not make it: the 15 credit
lanes of `--lib _qualification`, and slice 1's
(`verifier_credits_every_bound_row_with_the_replayed_body_theorem`) and
slice 4's (`memory::verifier_credits_every_bound_memory_row_with_the_replayed_body_theorem`),
which that filter does not select. It now returns a `QualifiedPair`
witness that only it can construct, and every reader of the host's record
that a lane can call requires one. As first committed, the record's own
constants and four of its helpers stayed readable by every lane, so the
compiler did not hold a lane to the check; since the landing review they
are private to the witness's module, and it does ("Landing review" below).
A gap lane still replays and prints every outcome
first and checks before it compares; slice 1's canonical lane now does the
same; a credit lane, which compares as it replays, checks before its first
replay. `canonical_migration_pairs_original_mul_i16_under_one_captured_authority`
reads no record, and its comment says why it needs no check.

| Run | Code | Command | Load (1-minute, min-max, mean) | Result |
| --- | --- | --- | --- | --- |
| negative control (`logs/negative-control.log`) | this round's, with the aarch64 digest `8009…` changed to `9009…`, then reverted | `--lib -- _qualification` plus the two credit lanes outside that filter, `--test-threads=1` | 42.0-98.2, 55.3 | **0 passed, 36 failed**, 14 ignored, 2010.6 s: every failure is the pair check, "the pinned qualification outcomes for host aarch64-apple-darwin were measured with [ay 0.27.0 build 12713 ...] and Clean sha256 90090967...; this host admits [...] and Clean sha256 80090967..." |
| the explicit lane under the same digest (`logs/negative-control-explicit.log`) | the same | the command below | - | **refused** at the same check, 0.4 s |

The landing's control had the 15 credit lanes passing and slice 1's
canonical lane failing on an outcome, not on the pair; now all 36 refuse,
each at the line where it checks.

### Deadline-bound labels at the record's budget

The 30 s lanes accept `Timeout` for a label that some runs certify, so they
cannot notice one ceasing to certify altogether. The explicitly run lane
replays every deadline-bound label of the host through the lanes' route
(AY, then Clean's check of its proof) with the 300 s budget of this
record's offline replays, and fails if `EarlyExit`, `GuardedUdiv` or
`GuardThenCall` does not certify, or if `MulI16` does (a strengthening the
record must take). Its command, after a qualification run on the pair:

```sh
env TRUST_TARGO="$OV/bin/targo" TCG_EXTERNAL_CLEAN_CHECKER="$OV/bin/clean" \
  scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib \
  x86_source_bound_body::tests::host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget \
  -- --ignored --exact --nocapture
```

Run once (`logs/deadline-bound-budget.log`, load 22.3-28.9): **1 passed**,
209.3 s.

| Label (table) | Record at the 30 s deadline | 300 s budget, this run |
| --- | --- | --- |
| `MulI16` (`KNOWN_UNCERTIFIED`) | no run certifies | AY's self-check rejection, `SOUNDNESS`, 17.9 s |
| `EarlyExit` (`KNOWN_UNCERTIFIED_SLICE_TWELVE`) | some runs certify | certified, 22.7 s |
| `GuardedUdiv` (`KNOWN_UNCERTIFIED_SLICE_FOURTEEN`) | some runs certify | certified, 75.7 s |
| `GuardThenCall` (`KNOWN_UNCERTIFIED_SLICE_FOURTEEN`) | some runs certify | certified, 92.8 s |

Slice 14's pair took over a minute each here and a few seconds in the gate
run that preceded it (2.8 s and 3.7 s), the clustering the record
describes.

### `offline_replay.py` reads the whole output

The script kept AY's last two output lines, so a row lost `unproved_steps=`
and `trust_free=` whenever AY's `carcara_surface=clean-dialect` warning came
after its certificate line. `ay_tail` now starts with both fields, taken
from AY's whole output (`-` when it printed none), then ` | ` and the same
two lines; the columns are unchanged. Every row of
`offline/measure0-clean8606-30s.tsv` and `offline/near-deadline-repeats.tsv`
(and of the burst's TSVs) was written on 2026-10-16, before the fix: the
field is missing from 18 of the 47 `unsat` rows of the second (every
`EarlyExit` and `SlotU128` row) and from 236 of the 396 of the first. After
the fix, at 30 s on the gate run's dumped queries
(`offline/fields-after-fix.tsv`), `EarlyExit` (26.3 s) and `SlotU128`
(13.7 s), whose last line is still that warning, and `SubU128` (10.5 s) all
read `unproved_steps=0 trust_free=yes`, and Clean `92bcc8979` fully verifies
each.

### Gates on the final tree

| Gate | Command | Result |
| --- | --- | --- |
| qualification | `commands/qualify.sh`'s invocation, `--lib _qualification -- --nocapture --test-threads=1` (`logs/qualification.log`) | **34 passed, 0 failed**, 14 ignored (the 13 printers and the explicit lane), 2335.0 s at load 12.4-67.4 (mean 26.3); every lane prints one `X86_BODY_REPLAY_IDENTITY` line naming AY build 12713 (`dd6d3661…`, overlay manifest `4c7a49f3…`) and Clean `80090967…` |
| the two credit lanes outside that filter | `--lib -- --exact` with both names (`logs/credit-outside-filter.log`) | **2 passed**, 56.0 s |
| explicit deadline-bound lane | its command above | **1 passed**, 209.3 s |
| format | `scripts/check_fmt.sh` | OK |
| lint, `trust-cg-verify` | `targo tippy --locked -p trust-cg-verify --lib --tests --no-deps --keep-going --message-format short`, `check_tippy.sh`'s invocation, package 9192 (`logs/tippy-trust-cg-verify.log`, and `-final.log` after the comment edit) | exit 0, no finding, both times |
| documentation | `python3 scripts/check_documentation.py --check` | OK |
| ignored-test inventory | `python3 scripts/full_test_matrix_hosts.py --check`; `scripts/tests/test_full_test_matrix_hosts.py` | OK; 33 passed |

In the gate run every recorded outcome held. `MulI16` ran past the
deadline (30.1 s), as it did in the negative control, both at 1-minute
loads of 55 to 64 when it ran: the record's `Timeout` answer, now on three
of the nine 30 s lane runs that replayed it, each at a load above 50. `EarlyExit`
certified in 28.2 s, `GuardedUdiv` in 2.8 s, `GuardThenCall` in 3.7 s, and
`SubU128` and `SlotU128` in 12.6 s and 13.6 s. (A run's tests start when
its `libtest` time says, after the build slot is granted; the load at a
replay is read from the samples at that time.)

The payloads are in
`~/scratch.noindex/qual-aarch64-20261017-harness-r2-payloads/` on the
measuring host, with a `SHA256SUMS`; `helpers/` holds the scripts that made
the runs (they name the directory `payloads/`, its name while they ran, and
it was later moved out of the round's scratch directory, unchanged).

| Payload | sha256 |
| --- | --- |
| `helpers/gates.sh` | `653852a77f6a96c80afd1a6da21080650504e0cf0d916173c640d9cbec354c26` |
| `helpers/run_lane.sh` | `51b40ae6525082cb43a7873d5b26ae42fdaa721ceb94c6415232cae3564b7172` |
| `helpers/verdicts.py` | `3f80fd6055633625ab1b6463d4a89a4ab57f4bb945ffd891b7e7045d0b5888f6` |
| `logs/credit-outside-filter.log` | `d38add41b49156b6dee1cdb471b168b58baf7ec8db9661e4adb2ac3c1cf7d469` |
| `logs/credit-outside-filter.log.build` | `111918376290dff081ee386bd27d9ff5b9a17d57ddd880cac1183c482e17e6db` |
| `logs/credit-outside-filter.log.load` | `635a7444ff6e74809f733be879340a14637f9308ed5e57fcae40c3c3b8b5cb80` |
| `logs/deadline-bound-budget.log` | `872bc621c2b9b0c0514ea328164c291376e6417dc2bae779aeb9af9378a39cab` |
| `logs/deadline-bound-budget.log.build` | `73e2f6770874a70220ec2daa0d4c27ae0cbae3d87418ecb164972284b462deef` |
| `logs/deadline-bound-budget.log.load` | `f9b2c6cc4a0490f601434d522a70240813e6eb909e1f1d1b7166a216b4ed3032` |
| `logs/gates-head.txt` | `5535d3be6ed8a12f7c26168057a75f0d147276986dc9a18d3f98e9887a88db9c` |
| `logs/negative-control-explicit.log` | `c4f139f2f4ff2bac75b2b36d7368c636b89782dcfa3301202b3cbd99d584d367` |
| `logs/negative-control-explicit.log.build` | `f9c0662d8136f34a1e96c5a1cc8c6c19908d63dd8e9f09c2d86f8567c9e1f5c3` |
| `logs/negative-control-explicit.log.load` | `4255445a680bc7052372e27e9885e6a3e11ce5e7c59abc3637b174535968ce9c` |
| `logs/negative-control.log` | `d5bdfb8fabe1c3af2f603cfdc0cfcddb682a2c61f1355b3778f154380267cf45` |
| `logs/negative-control.log.build` | `8824269f7f8363535a9ef6dc125bb6c5e553a23877a1b23a938f6ae39600e369` |
| `logs/negative-control.log.load` | `40a76c38cf2005eea253db0c0803c1dfab3e7dc658e40786207e9ac4d17d2181` |
| `logs/offline-fields-after-fix.log` | `856c065563b34cd182f1365355c631941d487024576611447823aea9e4a54f28` |
| `logs/qualification.log` | `4c4bb08279851842e3f2e3c25b1998237a6e1d1d7a061ff713800ca41ae22ddd` |
| `logs/qualification.log.build` | `20a373d0b0951cface19a42ce48a28c3581131b5ea027a22995b46cf85fe4198` |
| `logs/qualification.log.load` | `6b9f8fdaf08fbc500d6f37fb309737d4b41733a28ada24d1d6843a30556deed0` |
| `logs/tippy-trust-cg-verify-final.log` | `ec90bf8dd172c40789c1801881d45728e2737a6612be51df7a7213745cc3bc31` |
| `logs/tippy-trust-cg-verify.log` | `04d24c19b23f5a284ee652c945bd8a10a44c685dcb631ace1cf7933bb8893120` |
| `offline/fields-after-fix.tsv` | `454a658e84aeccf04279fa04280c20ae227589ea4c3b81e1d2258aab62655b94` |
| `outcomes/negative-control.tsv` | `36724eb52133fa9a6c6abb3ae358d729c1a2dab60a0405681064b9788f3c168c` |
| `outcomes/qualification-summary.txt` | `1774844cba745e9a02916a5a31883b7dd791c6721fb67b5d13a73a3bca09624e` |
| `outcomes/qualification.tsv` | `af76b15d5a505ae4c7a950b46caa32a15778a3f0be755395983cb957355d2c8d` |

### Landing review (2026-10-17)

Two reviews of round 2 ran every tool-gated lane, ignored ones included,
under two unqualified pairs. Every lane that reads the record refused both
at its own check line: with `QUALIFIED_AY` changed to build 12719 on the
overlay (`review/A-ay-perturbed.log`: 3 passed, 37 failed, 2003.7 s), and
with the host's ordinary package pair, AY 9624 with Clean 8606
(`review/B-ordinary-pair.log`: 3 passed, 37 failed, 259.1 s). The three
that passed read no record of the qualified pair:
`canonical_migration_pairs_original_mul_i16_under_one_captured_authority`
and the two envelope lanes.

They refuted round 2's main claim. The witness gated only the readers a
lane calls by name. The record's constants (`CERTIFIED_HERE_BY_HOST`,
`OUTCOME_HERE_BY_HOST`, `ALSO_UNCERTIFIED_HERE_BY_HOST`,
`DEADLINE_BOUND_HERE_BY_HOST`) and four helpers that read them
(`certified_here`, `also_uncertified_here`, `deadline_bound_here`,
`certifies_sometimes_here`) were private items of
`x86_source_bound_body::tests`, which every lane module, as its child, can
name. A probe lane in `slice5_qualification` read them all with no witness,
and compiled and passed (`review/C-probe-before.log`).

The fix, `9fd8ed6ac`, moves the record, every function that reads it and
the witness into one module,
`crates/trust-cg-verify/src/x86_source_bound_body_qualified_pair_tests.rs`
(`tests::qualified_pair`); only the readers that take a witness leave it.
The same probe, extended with the `qualified_pair::` spellings and a forged
`QualifiedPair(())` (`helpers/privacy-probe.rs`), now fails to compile with
11 errors: E0425 for each old spelling, E0603 for each private item and
E0423 for the forged witness (`logs/privacy-probe-after.log`).

The explicit lane changed too:

- a label no run certifies is held to the answers measured for it, not
  only to "does not certify";
- a `Timeout` of a label some runs certify still fails it, but the message
  says to re-run on a quieter host before re-qualifying. In a review run
  `GuardThenCall` took 224.9 s of the 300 s budget
  (`review/B-flip-300s.log`, which ended at a 1-minute load of 25);
- its comment says that a refuted label fails it at once, and gives the
  command with the overlay's `TRUST_TARGO` and `TCG_EXTERNAL_CLEAN_CHECKER`.

A negative control of the new branches cut the budget to 1 s and reduced
`MulI16`'s measured answers to the self-check rejection
(`helpers/negative-control.diff`, reverted; `logs/negative-control-explicit.log`):
**1 failed** in 4.4 s, naming `MulI16` ("none of the answers measured for
it") and `EarlyExit`, `GuardedUdiv` and `GuardThenCall` (past the budget,
"re-run this lane on a quieter host first").

Gates on `9fd8ed6ac`, each run once, with the pair, overlay and commands
above (the working tree held only this section's documentation edits):

| Gate | Command | Result |
| --- | --- | --- |
| qualification | `commands/qualify.sh`'s invocation, `--lib _qualification -- --nocapture --test-threads=1` (`logs/qualification.log`) | **34 passed, 0 failed**, 14 ignored, 2357.0 s at load 8.4-43.5 (mean 15.7); 34 `X86_BODY_REPLAY_IDENTITY` lines, each naming AY build 12713 (`dd6d3661…`) and Clean `80090967…` |
| the two credit lanes outside that filter | `--lib -- --exact` with both names (`logs/credit-outside-filter.log`) | **2 passed**, 60.3 s |
| explicit deadline-bound lane | its command above (`logs/deadline-bound-budget.log`) | **1 passed**, 252.0 s at load 18.2-73.4: `MulI16` AY's self-check rejection (`SOUNDNESS`) in 30.5 s; `EarlyExit`, `GuardedUdiv` and `GuardThenCall` certified in 27.4 s, 99.6 s and 94.0 s |
| format | `scripts/check_fmt.sh` | OK |
| lint, `trust-cg-verify` | `check_tippy.sh`'s invocation, package 9192 (`logs/tippy-trust-cg-verify.log`) | exit 0, no finding |
| documentation | `python3 scripts/check_documentation.py --check` | OK |
| ignored-test inventory | `python3 scripts/full_test_matrix_hosts.py --check`; `scripts/tests/test_full_test_matrix_hosts.py` | OK; 33 passed |

In the gate run every recorded outcome held: `MulI16` was AY's self-check
rejection (18.8 s), `EarlyExit` certified in 30.8 s and `SubU128` and
`SlotU128` in 16.2 s and 12.3 s, and `GuardedUdiv` and `GuardThenCall` both
ran past the deadline, an answer measured for each.

`main` moved during the landing: `e5560e8db` moved the trust-ir and Clean
pins (LD-PIN6382-1..2), which changes the dependency graph of
`trust-cg-verify`. The same gates ran again on the merged tip `9b5f793c8`,
with a clean tree (`merged-tip/`): qualification **34 passed, 0 failed**, 14
ignored, 2356.2 s at load 11.6-46.8 (mean 26.1), with 34 identity lines
naming the same pair; the two credit lanes outside the filter, **2 passed**,
58.5 s; the explicit lane, **1 passed**, 159.9 s at load 10.6-14.1 (`MulI16`
rejected in 24.4 s; `EarlyExit`, `GuardedUdiv` and `GuardThenCall`
certified in 31.4 s, 1.7 s and 102.1 s); lint for `trust-cg-verify`, exit 0
with no finding; format, documentation and inventory checks, OK. Every
recorded outcome held: `MulI16` was the self-check rejection (23.8 s), and
the other five certified (`EarlyExit` 36.6 s, `GuardedUdiv` 2.3 s,
`GuardThenCall` 3.8 s, `SubU128` 16.4 s, `SlotU128` 11.9 s).

The payloads are in
`~/scratch.noindex/qual-aarch64-20261017-harness-r2-landing-payloads/` on
the measuring host, with a `SHA256SUMS`. `review/` holds copies of the
reviews' logs cited above; `helpers/` holds the scripts, the probe and the
negative control's diff (the scripts name the directory under
`~/scratch.noindex/round5-20261017/`, where it was while they ran; it was
moved from there unchanged).

| Payload | sha256 |
| --- | --- |
| `helpers/gates-merged.sh` | `2d12d546f124d1792a818af5326831179a3181646a3972c7798d7cc38188a807` |
| `helpers/gates.sh` | `24de1742c7ad813ea021e2e3febbae2735d4dfd46e9a6c144547cab476bac310` |
| `helpers/negative-control.diff` | `4adad318bab736218568ed937b10378fabfef44b3662e49a703baa6917abe5c8` |
| `helpers/privacy-probe.rs` | `20e25f66fe303fda8a147a21dd2dd85592ffc73de9a943f557d4f4cdc2b1a763` |
| `helpers/run_lane.sh` | `6cfa8d4660097e14d40f4b2a6ed969c3af3cd5ea00fb53e9a39cb14ffc7c18e6` |
| `logs/credit-outside-filter.log` | `b5a9498e94bae0deca0612c8287e2d1848514fa2d489708db5c92181e19ace2f` |
| `logs/credit-outside-filter.log.build` | `931e17b36706e5dbb07c805826d44202ce566d5491f9c6169d0fd0b562762c0a` |
| `logs/credit-outside-filter.log.head` | `73dc82b51360b5734fc20b799f81ae2db909d8c5a036cba0cd868cdeb9a28db9` |
| `logs/credit-outside-filter.log.load` | `533291d8b8bcce2c2463fd5ff86e5cf26dd2a7ee43fd6f537747c137db9b1906` |
| `logs/deadline-bound-budget.log` | `70e5ecaa9d42abd94c1da39831afb965d4185c72a5abc3e60921cbca9f14f47b` |
| `logs/deadline-bound-budget.log.build` | `812bb1438b45743b9baa0b3280d2a7e5e08bd6533524974f5ab09cc8a81d0f45` |
| `logs/deadline-bound-budget.log.head` | `73dc82b51360b5734fc20b799f81ae2db909d8c5a036cba0cd868cdeb9a28db9` |
| `logs/deadline-bound-budget.log.load` | `c30abc7fe5723231522990dc28d8c3ea7d1399145eaf17196a3617b42356ad32` |
| `logs/gates.out` | `7241880bc3b8e1a4881ec88b39f2904fc046c2e0a1125e8beff73069a28c4a24` |
| `logs/negative-control-explicit.log` | `dfc8f145c27473136922d616b9dc52994cfb7945a31cf5ed16d37ea881ad319f` |
| `logs/negative-control-explicit.log.build` | `bcd019a6c38916fd8e6bf723d55924337166de2b74c41a86bb90971c9d957913` |
| `logs/negative-control-explicit.log.head` | `533f8a934e83806cf72d26e30dea55d93efcd35691b9ed173cb7e8556d690e77` |
| `logs/negative-control-explicit.log.load` | `b6fed09c9bb092f37a38cf8d5dca1878f8e34129539ff764d1194d29b2500730` |
| `logs/privacy-probe-after.log` | `feb56649d6f59a8c02e4606f8eaf892fa985c39dc4486c91f7858d3d9468677d` |
| `logs/qualification.log` | `0d13d347762545db8982cf5af127e8987846eb9fb687c35e17db9019ebab647e` |
| `logs/qualification.log.build` | `c5229ddeef40bb91e1dfc831210da0c7e041e3bbe2f25bb42cc77337d5747b95` |
| `logs/qualification.log.head` | `18c3d9fe9ad376c71b11d0397552ad650071ba2dc71b7d9f4ff9c26cc26c7e48` |
| `logs/qualification.log.load` | `506cc55a2fbda39132504548d7637901d0881c9f5c21942eea853c85f84f9e58` |
| `logs/tippy-trust-cg-verify.log` | `9d969e5b338cbeec6cc3a5a0956d13a1add482fdd08a9debe7c0b68a1b7aa03d` |
| `merged-tip/credit-outside-filter.log` | `a2c00c9decd73a68de2268bf84b8f4a78edcf4edc2bdcb998893ee86addbce9c` |
| `merged-tip/credit-outside-filter.log.build` | `7478eaa2f844819f92852a931a47934ea8cd287c461e9a5f8adc7a17162ec603` |
| `merged-tip/credit-outside-filter.log.head` | `d372c3aac883c002c7dc283436b3b638ac953cc6b89199cacaf98037db4ea442` |
| `merged-tip/credit-outside-filter.log.load` | `32a3c1a882434b7144f43576cd24ed1ce922db429f172e39bedfa51c557e9600` |
| `merged-tip/deadline-bound-budget.log` | `95e80b37ba87b5bd66583960836b976303f9b0df7a62ecd09f17f13baa56b5f1` |
| `merged-tip/deadline-bound-budget.log.build` | `95d3526530c4d3aaa3f7a5472e2efc938c4b8d96c1c513b9856dc3aa989eb3dd` |
| `merged-tip/deadline-bound-budget.log.head` | `d372c3aac883c002c7dc283436b3b638ac953cc6b89199cacaf98037db4ea442` |
| `merged-tip/deadline-bound-budget.log.load` | `108b1e50a274e4ffe746bac6dfb02d0abecbf3fd00cadd08c0b8567ad28ae42c` |
| `merged-tip/gates.out` | `7241880bc3b8e1a4881ec88b39f2904fc046c2e0a1125e8beff73069a28c4a24` |
| `merged-tip/qualification.log` | `031901f70d406e98bfde318ef8dfd81ac1114a876ae5e3116ec51db09bed9d3d` |
| `merged-tip/qualification.log.build` | `2f52b4d00cf547ebf6dd45cc602ee2e18f32e66a86aeada1a7478d7ebc2fb110` |
| `merged-tip/qualification.log.head` | `d372c3aac883c002c7dc283436b3b638ac953cc6b89199cacaf98037db4ea442` |
| `merged-tip/qualification.log.load` | `4f27a03339d0ad788f2b7f9bd7a1158c84b4028d543abec111d63ceb9a24ea89` |
| `merged-tip/tippy-trust-cg-verify.log` | `f73fb002f28923c488cd5dae6dbb7a5da54f66c814051d53022687bc27f68fd6` |
| `review/A-ay-perturbed.log` | `6e730fd1b29b990d8b9a5ef439840380177000ca7c2bdd376fec9cf9e6d592a0` |
| `review/B-flip-300s.log` | `fad776c629baf4a08320b2fe2dfaa0bc023d9ed3cb1743fe3251365506f75abd` |
| `review/B-ordinary-pair.log` | `97add251e83dae26ea274513745d96f36bdacc31f419cbec65bec9ee932f5023` |
| `review/C-probe-before.log` | `7a1650c35ae32c9eac0953df6576aa26cbbd6605b08bb87c830c2b925b83a783` |

## Fail closed (2026-10-17)

Two faults the harness rounds left, each fixed at its cause in
`crates/trust-cg-verify/src/x86_source_bound_body_tests.rs` (and the lanes
that call it), `x86_source_bound_body_qualified_pair_tests.rs` and this
record's `commands/qualify.sh`; the ruling is the "Every lane fails closed"
addendum to DR-PER-HOST-QUALIFIED-PAIR-20261015. The pair, the overlay and
the host are the ones above. The tree is trust-cg `origin/main` `e276015bf`
plus `b15aa5e17`, `74b2375e4` and `59a9bd8cf` (branch
`fix/fail-closed-lanes-20261017`), whose code every run below ran. The later
commits merge `main` (up to `ff44162f3`) and add documentation; they change
nothing the root workspace builds (in code, only the bridge,
`crates/rustc-codegen-trust-cg`, which is its own workspace), so the runs
below are the lane tip's too ("Gates on the final tree").

### A lane that cannot judge fails

`replay_environment` printed `SKIP <test>: <reason>` and returned when it
found no checker (or, in a build that records no AY, no AY to admit), and
each of the 40 lanes that call it returned, which libtest counts as a pass.
It now fails the lane at its own call site, naming what is missing and how
to provide it. The 39 lanes below are every caller that runs by default;
the fortieth is the explicit lane. A capable checker that the build's proof
authority refuses still passed two of them until the repair below ("The
checker the build accepts").

| Run | Tree | What is missing | Result |
| --- | --- | --- | --- |
| before (`logs/nc-before.log`, `logs/nc-before-explicit.log`) | `e276015bf` | no checker: `TCG_CLEAN_CHECKER=/nonexistent/clean`, so discovery selects none | **39 passed, 0 failed**, each printing `SKIP <test>: no capable independent Clean/Carcara checker ...`; the explicit lane **1 passed**, printing the same |
| after (`logs/nc-after-nodiscovery.log`, `logs/nc-after-explicit-lane.log`) | `59a9bd8cf` | the same | **0 passed, 39 failed**, no `SKIP` line: "`<test>` cannot judge: no Clean/Carcara checker: TCG_EXTERNAL_CLEAN_CHECKER is unset and default discovery found no capable one (...). Provide the checker: ..."; the explicit lane **1 failed**, the same |
| after (`logs/nc-after-explicitnofile.log`) | `59a9bd8cf` | `TCG_EXTERNAL_CLEAN_CHECKER=/nonexistent/clean` | **0 passed, 39 failed**: "... TCG_EXTERNAL_CLEAN_CHECKER=/nonexistent/clean names no file. Provide the checker: ..." |
| after (`logs/nc-after-noay.log`) | `59a9bd8cf` | the qualified Clean named, `AY_SOLVER_PATH` naming a file that is not the recorded AY | **0 passed, 39 failed**: "... no AY is admitted under this environment ([TCG-AY-IDENTITY-OVERRIDE-MISSING] ...). Provide the AY: ..." |

Each failure is reported at the lane's own line. The arm a build that
records no AY takes (`TCG_X86_BODY_QUALIFY_AY` unset, or not an absolute
file) is held by `replay_environment_names_what_is_missing`, which injects
its inputs and needs no tool; with the witness's negative control below it
reads **2 passed** (`logs/unit-new.log`). The explicit lane, on a host whose
record holds no deadline-bound label, now passes saying so instead of
printing `SKIP`: it has checked the pair, and nothing there can stop
certifying unnoticed.

### One command runs every lane the record depends on

`--lib _qualification` did not select slice 1's and slice 4's credit lanes,
and nothing ran the explicit lane. The two credit lanes are renamed into the
filter, and `assert_qualification_replayer`, which every lane that reads the
record calls before it reads it, refuses a lane whose libtest name (its
thread's name) lacks `_qualification`
(`the_pair_witness_refuses_a_lane_the_command_does_not_select` is the
negative control). A lane named outside the filter therefore fails wherever
it runs (the default library suite), not in this command, and only when it
runs: the `host_qualification_replays_*` lanes take the witness after all
their replays. The filter now selects 50 tests: 36 that run and 14
`#[ignore]`d (the 13 printers and the explicit lane). Three tool-gated lanes
stay outside it because they read no host qualification record (the
certifying envelope lane reads its own `KNOWN_UNCERTIFIED` table, keyed by
the AY's sha256):
`canonical_migration_pairs_original_mul_i16_under_one_captured_authority`
and the two envelope lanes.

A qualification is [`commands/qualify.sh`](commands/qualify.sh), from the
trust-cg checkout under test (`OV` is the overlay):

```sh
CARGO_TARGET_DIR=<target dir> \
  reports/perf/2026-10-16-darwin-aarch64-ay12713-qualification/commands/qualify.sh "$OV" <dump dir>
```

It runs these two commands, each through `build-slot`, and fails if either
fails or (since the repair below) runs another number of lanes than the
record names, 36 and 1:

```sh
env TRUST_TARGO="$OV/bin/targo" TCG_EXTERNAL_CLEAN_CHECKER="$OV/bin/clean" \
  TCG_X86_BODY_QUALIFY_DUMP=<dump dir> \
  scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib _qualification \
  -- --nocapture --test-threads=1
env TRUST_TARGO="$OV/bin/targo" TCG_EXTERNAL_CLEAN_CHECKER="$OV/bin/clean" \
  scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib \
  x86_source_bound_body::tests::host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget \
  -- --ignored --exact --nocapture
```

### Runs with the pair

| Run | Command | Load (1-minute, min-max, mean) | Result |
| --- | --- | --- | --- |
| qualification (`logs/qualify.log`, `logs/qualify-outcomes.tsv`) | `commands/qualify.sh` above, 22:40:27-23:25:18 UTC | 3.8-28.0, 9.5 | `--lib _qualification`: **36 passed, 0 failed**, 14 ignored, 2376.4 s; the explicit lane: **1 passed**, 261.5 s; exit 0. Each of the 37 lanes printed one `X86_BODY_REPLAY_IDENTITY` line, all naming AY build 12713 (`dd6d3661…`, overlay manifest `4c7a49f3…`) and Clean `92bcc8979` (`80090967…`) |
| the three lanes outside the record (`logs/outside-record.log`) | `--lib -- --exact` with the three names, `--test-threads=1` | 8.0-10.4, 9.2 | **3 passed**, 139.6 s |

Every recorded outcome held. In the 30 s lanes `SubU128` and `SlotU128`
certified (12.4 s, 9.3 s), `EarlyExit` certified in 22.1 s and
`GuardedUdiv` in 1.5 s, `GuardThenCall` ran past the deadline (an answer the
record accepts for it), and `MulI16` was AY's self-check rejection. At the
300 s budget `MulI16` was the self-check rejection again (18.2 s) and
`EarlyExit`, `GuardedUdiv` and `GuardThenCall` certified in 22.9 s, 71.3 s
and 148.7 s.

### Gates on the final tree

Superseded: the lane went on past `dbdb5a4fc` ("The checker the build
accepts" below), and its merged tip's gates are in "Gates on the merged
tree (2026-10-19)". This section records the tree it names.

The lane's tip was `dbdb5a4fc`, `main` merged up to `ff44162f3` onto the
commits above. Nothing the root workspace builds differs from `59a9bd8cf`:
`git diff --stat 59a9bd8cf dbdb5a4fc -- crates Cargo.toml Cargo.lock .cargo
rust-toolchain.toml` lists only `crates/rustc-codegen-trust-cg`, the bridge,
which is its own workspace. The runs with the pair above, at `59a9bd8cf`,
stand for the tip by those identical sources (checked `59a9bd8cf`, composed
onto `ff44162f3`); they were not repeated there. The tip's build of the
library tests recompiled the workspace members and produced another binary
from the same sources (`trust_cg_verify-dde1ca55e4b22fb8`, sha256
`29ce0162…`; the qualification ran `611a9fa9…`). Every other gate ran on the
tip:

| Gate | Command | Result |
| --- | --- | --- |
| format | `scripts/check_fmt.sh` (`final/fmt.log`) | OK |
| documentation | `python3 scripts/check_documentation.py --check` (`final/doc.log`) | OK |
| ignored-test inventory | `python3 scripts/full_test_matrix_hosts.py --check`; `scripts/tests/test_full_test_matrix_hosts.py` (`final/matrix.log`, `final/matrix-tests.log`) | OK; 33 passed |
| lint | `scripts/check_tippy.sh`, package 9192 (`final/tippy.log`) | **19 packages clean**, exit 0 |
| the kernel-TV CLI row | `scripts/trust_cargo.sh test --locked -p trust-cg-cli --test codegen_license_flags`, the overlay's `targo` (`final/cli-license.log`) | **7 passed**, 39.0 s |
| the tool-free unit tests | `--lib -- --exact` with both names (`final/unit.log`) | **2 passed** |
| the three absences | as in the first table (`final/nc-nodiscovery.log`, `final/nc-explicitnofile.log`, `final/nc-noay.log`) | **0 passed, 39 failed** each, every failure at the lane's own line and naming what is missing; no `SKIP` line |
| the explicit lane, no checker | as in the first table (`final/nc-explicit-lane.log`) | **1 failed**, the same |

The payloads are in
`~/scratch.noindex/round9-20261017/tcg-fail-closed-payloads/` on the
measuring host, with a `SHA256SUMS` over all 689 files: `logs/` holds the
runs at `e276015bf` and `59a9bd8cf`, `final/` the tip's, `dump/` the 615
queries the qualification dumped, and `helpers/` the scripts that made the
runs, the 39 lane names, and the crate's skip-site scan the decision
record's count of other loud skips comes from.

| Payload | sha256 |
| --- | --- |
| `final/build-verify.log` | `1fefe8fecdc5d3cc865a243fe110b6365e3d2770c9a1b9381abe6c2c22b1e1e7` |
| `final/cli-license.log` | `ca4ec0b83087c168b5e8da962aa09c3e601858eb723a3ef9a806c4cb2af2cce3` |
| `final/doc.log` | `9219ff0f5cdf87ae3ab0208e599279acd52c1e41937d9e1b3ae218784541ab03` |
| `final/fmt.log` | `66508778f65b94be7158bea47b7af680e13198ed31337f1e956d0d2da2af1649` |
| `final/heavy.head` | `cac73b1ce1229b55e8e4bf891d0a9a2f62d55aa7840198e1d238c55cf0db3197` |
| `final/matrix-tests.log` | `c36f2690fc054fdd03bed9cdc82d0e9bb666bc1f9629d79d8d266684a02291a1` |
| `final/matrix.log` | `19eaf43821a7660ec323a87c8457bf74823beb296c39f5e01aa8a683aa50f061` |
| `final/nc-explicit-lane.log` | `5d9348ef8359fe4df86a831d176a41c7f07afbaf284a92dfff961ec867816762` |
| `final/nc-explicitnofile.log` | `8386ed54303b42b8fd59eb5a2451cd48a8da719516809e0fbe91e302f9663a1f` |
| `final/nc-noay.log` | `22f303eb470a44143b6abdcdb59b7fc346f5e79488398aba4473c7c38f5baef4` |
| `final/nc-nodiscovery.log` | `c869852aba0609a62b204d5ce550943c816f78acd6bdd897c8b735e350740852` |
| `final/tippy.log` | `e601f9c9f116d3cc424d6b13490f59e7d88b1441a3e9c6635cd12f06f4e637f2` |
| `final/unit.log` | `1e79c46247719d0748ae4c3213d300816e5648b59414728b9d479dcb2db8110f` |
| `final/verify-binary.sha256` | `dda632217e83064795e77aecdb92a9bbcbdb1c253e878c62c8884997ff4b7460` |
| `helpers/lanes-after.txt` | `d13efd702e5df939623897ba29a687a9ba9a30a1da8ebdf338f6d8884de2540e` |
| `helpers/run-final-gates.sh` | `87f03841a9d48fadcb2b2c312c8290e9af37ff4f0213b9e7caa73e858723098c` |
| `helpers/run-qualify.sh` | `9dc7ba91d0e2ecc30f73ff7c413e9944e371331bca86cf19aa3a734f03cb4c50` |
| `helpers/skipscan.py` | `14f91ba9410df9b08216ad1be21961b4b25051f97f2815fc6bde77cef2e5b01c` |
| `helpers/skipscan.tsv` | `11a55e91479f225118ea302e10172a7c6e0e122abcb8ae1493f526c44597f7f9` |
| `logs/cli-license-after.log` | `b94efea8e13115fee768862cfa61eb4718088e32a288e7e02445ba82b1fa636e` |
| `logs/cli-license-before.log` | `2286adbd32bbadcc557ed646353d0d2c12e7629ca6c172a35297cc8a2267e773` |
| `logs/nc-after-explicit-lane.log` | `ed52e9c0379cd764d500105de9ee551cc860f6739e15bc34aa25357d81234940` |
| `logs/nc-after-explicitnofile.log` | `cd0943441d838a016e56ec5d26490e429cb67cbd920744aa606631d3ce8fff62` |
| `logs/nc-after-noay.log` | `e4f4e471478a4a1c4f0aff16b740e827b00615cf4a217df6ebe8bc8faef45443` |
| `logs/nc-after-nodiscovery.log` | `1941dc272880c70496ff2478d526404c1b1d92aafadd388f669956ebeeb2f0af` |
| `logs/nc-before-explicit.log` | `84f59ec01cdc7da8e9503310347ef29e563f7dab24f5fb90af8fa8df7f1f1a55` |
| `logs/nc-before.log` | `614b7168b19e619c7f90284a4af3a6aef2064d066249a9cc62783236415e017e` |
| `logs/outside-record.load` | `8539c6240413494dfd04624925563abca515e563e124151e29ca14b0a05f78c7` |
| `logs/outside-record.log` | `ab15c16cd805fa571529617702e7564e93e14a1cecd59bfb7d87bc16948fb25a` |
| `logs/qualify-outcomes.tsv` | `573ed709026cc57d3ae5a3b684126d4130cb85285a3226f0ad600b29c4586a43` |
| `logs/qualify.load` | `bb23b64e9d6813f2f8b01df1a2fc5b4c45d3e603b12279a7b2c957961eec80aa` |
| `logs/qualify.log` | `f4f10475a7f5f711a22354b1983fcd7ad5c851f513c04574961291eb334b6a28` |
| `logs/unit-new.log` | `9a15b4c2c6b6631bafecf00555d7a34787f78e8c2c544f31aae915ea03766d7b` |

### The checker the build accepts (2026-10-18)

A review of the round above named, with `TCG_EXTERNAL_CLEAN_CHECKER`, a
capable Clean of another revision (`trust-current/bin/clean`, sha256
`09bebde2…`) to the overlay build, which accepts only its overlay's Clean
(`80090967…`). The build's proof authority refused it and printed that it
treats it as ABSENT, but `replay_environment` had checked only that the file
exists and the AY admission only that it is capable, so the lanes replayed
with no checker to accept a proof. The `MulI16` migration lane compared two
absent checker digests (`"checker_sha256":null` in both forms) and passed,
the mutant-envelope lane, whose refutations need no checker, passed, and each
record lane replayed in full before its witness refused the pair.

`replay_environment` now resolves the named checker through the authority
path (`obligation_cert_store::resolve_proof_checker`) under the lane's edits,
before it admits the AY, and fails the lane naming the checker and the bytes
the build accepts. A checker that is no Clean is named as the checker too,
where the message used to say "no AY is admitted". The tool-free negative
control `replay_environment_refuses_a_checker_the_proof_authority_refuses`
runs the real discovery under an overlay pin over a stub that passes the
control-proof probe: refused under a pin of other bytes, admitted under its
own. The same round fixed three smaller faults the reviews found. The
`MulI16` lane requires the captured authority to bind a checker before it
compares the two forms' digests. The witness compares the AY's build
identity with `QUALIFIED_AY` by equality, no longer as a substring of a
description that also holds the AY's path
(`the_pair_witness_compares_the_ay_build_not_its_description`). And
`qualify.sh` requires its two steps to run 36 lanes and 1, since libtest
passes a filter or an exact name that selects nothing (the review
reproduced that with a misnamed explicit lane).

Runs on the lane worktree at `5fcb1c0c3` with this repair applied, through
`scripts/trust_cargo.sh` with the overlay's `targo` (the "before" rows run
the lane tip's own test binary, `trust_cg_verify-dde1ca55e4b22fb8`, sha256
`29ce0162…`, directly, as the review did; the "after" rows run the rebuilt
`4853c204…`). "Other Clean" is `trust-current/bin/clean`, "no Clean" a
shell script that prints a line and exits 0:

| Run | Checker | Lanes | Result |
| --- | --- | --- | --- |
| before (`logs/before-otherclean-outside.log`) | other Clean | the three outside the record | **2 passed, 1 failed**, 37.6 s: `MulI16` and the mutant-envelope lane pass, `envelope_theorems_certify_on_the_admitted_pair` fails at its UNSAT ("CANNOT BE CHECKED") |
| before (`logs/before-fake-mul.log`) | no Clean | `MulI16` | **1 failed**: "... no AY is admitted under this environment ($TCG_EXTERNAL_CLEAN_CHECKER explicitly selects ... unusable ...). Provide the AY: ..." |
| after (`logs/after-otherclean-outside.log`) | other Clean | the three outside the record | **0 passed, 3 failed**, 0.10 s: "`<test>` cannot judge: no Clean/Carcara checker this build accepts as its proof authority: ... names the Clean with sha256 80090967…, but this file's sha256 is 09bebde2…" |
| after (`logs/after-otherclean-qual.log`, `logs/after-otherclean-explicit.log`) | other Clean | `--lib _qualification`; the explicit lane | **0 passed, 36 failed**, 14 ignored, 0.07 s, each at its own line; the explicit lane **1 failed** |
| after (`logs/after-fake-mul.log`, `logs/after-fake-qual.log`) | no Clean | `MulI16`; `--lib _qualification` | **1 failed** and **0 passed, 36 failed**, the checker named: "... it did not verify a known-good control proof ..." |
| after (`logs/nc-nodiscovery.log`, `logs/nc-explicitnofile.log`, `logs/nc-noay.log`, `logs/nc-explicit-lane.log`) | the three absences of the first table | the 39 default lanes; the explicit lane | **0 passed, 39 failed** under each, the same messages as before the repair (the AY one now after the checker is accepted); the explicit lane **1 failed** |
| after (`logs/pair-outside.log`) | the overlay's Clean | the three outside the record | **3 passed**, 146.2 s; every identity line names Clean `80090967…`, and `MulI16`'s two forms bind `"checker_sha256":"80090967…"` |
| after (`logs/stripped-mul.log`) | none named: discovery selects the overlay's `bin/clean` | `MulI16` | **1 passed**, 38.4 s, binding `80090967…` |
| after (`logs/unit.log`) | none | the four tool-free tests | **4 passed** |

No run printed `SKIP`. The qualification itself, `commands/qualify.sh` as
now committed, from the lane worktree with the pair (`logs/qualify.log`,
`logs/qualify.load`, 10:17:25-11:03:41 UTC, 1-minute load 8.2-25.6, mean
15.0): `--lib _qualification` **36 passed, 0 failed**, 14 ignored, 2450.2
s; the explicit lane **1 passed**, 139.0 s; exit 0. Each of the 37 lanes
printed one `X86_BODY_REPLAY_IDENTITY` line naming AY build 12713
(`dd6d3661…`) and Clean `80090967…`. The step-count check refuses a step
that ran 0 or 37 lanes, or exited nonzero, on simulated libtest summaries
(`logs/counted-test.log`).

The rest of the lane's gates on this tree: the kernel-TV row's compiler-lane
half (`logs/codegen-evidence-before.log`: with the lane tip's test file, 10
passed, 2 failed, `UnevidencedGate` on `addmul`;
`logs/codegen-evidence-after.log`: 12 passed) and its CLI half
(`logs/cli-license.log`: 7 passed), recorded in
DR-KERNEL-TV-CLI-ARMS-20261017; trust-cg-cli `link_imports`, 5 passed, 4
failed, unchanged by this lane and recorded as open under OD-155
(`logs/cli-link-imports.log`); `scripts/check_tippy.sh`, 19 packages clean
(`logs/tippy.log`); format, documentation and the ignored-test inventory
OK.

The payloads are in
`~/scratch.noindex/round9-20261017/tcg-fc-repair/` on the measuring host,
with a `SHA256SUMS`: `logs/` holds every run above, `helpers/` the scripts
that made them.

| Payload | sha256 |
| --- | --- |
| `helpers/before.sh` | `261e1d82bb38168fedd32db4f2783bf2f0a00619d4317a0bead9ca197d246b6c` |
| `helpers/counted-test.sh` | `805e4c9488d10a513a280abb8d047f306ae44fdb2f42036cdb820974c6a67153` |
| `helpers/counted.sh` | `8030541e128e32ecfd6a8ce8c68c405a8261cfaf6d3a1661eaf9c39f8597e704` |
| `helpers/fake-clean` | `47006b45d6a6c3af72b5c8c3b11bb54a5ae3910f4c91204ff4e5d5c8f16f4275` |
| `helpers/group1.sh` | `fdbde080283c1603ef6782c50b0706be6d28967263cf7316ddb656ca7a83eb9e` |
| `helpers/run-lanes.sh` | `46285d992e9c189159ffb8c3136cfff078056bd3ba18df53a6e9073b3d7fe0a7` |
| `helpers/verify.sh` | `859037c460e3b6e5cd194d29de8c00b9da487fec02326390aa73b18e6d17977b` |
| `helpers/watch.sh` | `09b1f32adc38604aeeaef196ff9a10c327965e06622cd1f4556c7d56fdd59a8a` |
| `logs/after-fake-mul.log` | `d3231498724f36e3901b344494e543e9bb33b68c7adee048088e9690a1fcf452` |
| `logs/after-fake-qual.log` | `e11080b90139404f6acbf2bcb05c2a6598501c78718fc1513978081f03d3ab57` |
| `logs/after-otherclean-explicit.log` | `86d587596f45389bec7e198a5fc6816a8bb9fde1f0bb92b780078f50afbc8881` |
| `logs/after-otherclean-outside.log` | `1e5c7812d6a12dc2c328561c9becd1173938de9853c716a1f4258719bf45647a` |
| `logs/after-otherclean-qual.log` | `60519cd085964ef43c3a831c5f3427deadd286d90ed8a73ce2c1fb16c0fd1d11` |
| `logs/before-fake-mul.log` | `bd1c7c2076918bfccecfa93ffeb09b3457a44409cc3e10662d0ea658d745752c` |
| `logs/before-otherclean-outside.log` | `98851c9488c98d0e1cb2df7424247e286ff5ef39fd57b943d181af9087a17e06` |
| `logs/build-verify.log` | `83bbafc1139398768d29f6590da80d54397883cdf1776113bd8739d39ce443a4` |
| `logs/cli-license.log` | `64c6d83572f8198b0950d92b2a9b28b96b41148f1f538f1a91a3f7331528b23e` |
| `logs/cli-link-imports.log` | `40586a94b49568ca15315cb65649370ac82f331fe446becd6a6da60e675cced3` |
| `logs/codegen-evidence-after.log` | `eb2e08ea499a001cca867f68f4a98d55c8d9544dc89938210e85a00774fce47f` |
| `logs/codegen-evidence-before.log` | `954c764dd1ad16161b359401ee1f1392ac649f4ef34196949926acce9bd35a44` |
| `logs/counted-test.log` | `052452b98670cd42c816aaf5ceee7ad6c75c91d0032703890e105ef89185795f` |
| `logs/group1.slot.log` | `bba57907c612189ade2f54dd7d1879044457d869c0073da27d6ce1ba191f25ca` |
| `logs/nc-explicit-lane.log` | `1f7f07db07c038a768a0a33f64adde8c0d4bb25d4f07dec79f54a0150ab29638` |
| `logs/nc-explicitnofile.log` | `0ff6d1381e8d8d03a84610110f8f657fe6c6f6543d6db2a849afd79d4be0835c` |
| `logs/nc-noay.log` | `667210da90e80737b3f764ca6ef4257d0384f20c39aeac3013201f9d3b5e85da` |
| `logs/nc-nodiscovery.log` | `eea665a82c34a6164602d2153e6ed696da550b391b3a0a8dc8268f0d6ca73e52` |
| `logs/pair-outside.log` | `ff72ac5e2ec7a4befd73004d88fe2f4460b229e266bfbc0e8b4027ece88e68e9` |
| `logs/qualify.log` | `c45cf531114508b5dea6eb644ba1a8c7df7004d4628cc679d5e1d1f3a47447a8` |
| `logs/stripped-mul.log` | `ee2fdf936f490d75992700d29a6ce5193693cde017eacea577bdbdbda38ccc95` |
| `logs/tippy.log` | `1d3f50c926cd82c0939bc0f8cfd54eb47f658eb7f043fe8cef4e28a7446e661e` |
| `logs/unit.log` | `b70743a7602b0cd0c1929af5abc8b2f34ff7a262fb665b3873160bb7c0d554b8` |

### Gates on the merged tree (2026-10-19)

Superseded for the landed tip: `main` moved to `787d8e25c` (slice 18) after
these runs, and the gates on that merge are in "Gates on the merged tree
onto 787d8e25c" below. This section records the tree it names.

A review of the round above (2026-10-19, at `0035d2945` with that round's
uncommitted documentation) asked for two corrections, both made in
`af8a9c6e3`: the `mutation-knobs` controls of the kernel-TV license row are
recorded as open (DR-KERNEL-TV-CLI-ARMS-20261017, "The mutation-knobs
controls"), and the note at the head of "Gates on the final tree" no longer
points to a section that did not exist. `74063aed1` adds the tool-free test
the 2026-10-18 reviews found missing:
`replay_environment` runs its checker discovery, the proof authority and
the AY admission through `admit_replay`, which takes them as arguments, and
`replay_environment_admits_the_ay_only_under_a_checker_the_authority_accepts`
holds that order: under a checker the authority refuses, the AY step never
runs.

Every gate below ran on `1cf0880aa`, the lane's commits merged with
`origin/main` `b80b65c8f`. Since the lane's previous merge (`ff44162f3`)
`main` changed, in the root workspace, the refusal message of
`crates/trust-cg-lower/src/x86_64_isel.rs` and two trust-cg-codegen
integration tests (`e2e_aarch64_sext_bool_linux`,
`lean_encode_golden_binding`) that no gate below runs; outside the Rust
code it changed `scripts/soundness_check.sh` and two of its tests
(`scripts/tests/soundness_fixture.py`,
`scripts/tests/test_soundness_leg_inventory.py`), which no gate below runs
either; the rest is the bridge (its own workspace), the Lean model and
documentation. The gates ran with the overlay's `targo` through
`scripts/trust_cargo.sh` unless the row says otherwise. The first two rows
ran before the commits, on `0035d2945` plus an uncommitted working tree.
`logs/phase1.diff.sha256` hashes that tree's whole `git diff`,
documentation included, so it does not by itself show that the verify
sources were `74063aed1`'s; the unit row on the merged tree, and the
re-runs on the later merge below, stand without it:

| Gate | Command | Result |
| --- | --- | --- |
| the tool-free unit tests, before the commits (`logs/p1-unit.log`) | the five by exact name | **5 passed** |
| the new test under its mutant (`logs/p1-mutant.log`) | `admit_replay` takes the named checker without asking the authority | **1 failed**, at its first arm: the AY admitted under the refused checker |
| format (`logs/fmt.log`) | `scripts/check_fmt.sh`, package 9192 | OK |
| documentation (`logs/doc.log`) | `python3 scripts/check_documentation.py --check` | OK |
| ignored-test inventory (`logs/matrix.log`, `logs/matrix-tests.log`) | `python3 scripts/full_test_matrix_hosts.py --check`; `scripts/tests/test_full_test_matrix_hosts.py` | OK; **33 passed** |
| lint (`logs/tippy.log`) | `scripts/check_tippy.sh`, package 9192 | **19 packages clean**, exit 0 |
| the tool-free unit tests (`logs/unit.log`) | the five by exact name | **5 passed** |
| the three absences (`logs/nc-nodiscovery.log`, `logs/nc-explicitnofile.log`, `logs/nc-noay.log`) | as in "A lane that cannot judge fails" | **0 passed, 39 failed** each, 39 distinct panic sites, every one "cannot judge", no `SKIP` line |
| other Clean, no Clean (`logs/nc-otherclean.log`, `logs/nc-fake.log`) | as in "The checker the build accepts" | **0 passed, 39 failed** each, the checker named |
| the explicit lane, no checker (`logs/nc-explicit-lane.log`) | as in the first table | **1 failed** |
| the kernel-TV row, compiler lanes (`logs/codegen-evidence.log`, `logs/lower-evidence.log`) | trust-cg-codegen and trust-cg-lower `--test codegen_license_evidence` | **12 passed**; **24 passed** |
| its `mutation-knobs` controls, open (`logs/knob-codegen.log`, `logs/knob-lower.log`) | the same with `--features mutation-knobs` | **12 passed, 1 failed** and **24 passed, 1 failed**, the controls, red as recorded: `InvalidTrustIrModule` at the AOT `expect`, `UnevidencedGate` on `with_tls` |
| the corpus row the license row cites (`logs/codegen-corpus.log`) | trust-cg-codegen `--test must_refuse_corpus` | **5 passed** |
| the kernel-TV row, CLI (`logs/cli-license.log`) | trust-cg-cli `--test codegen_license_flags` | **7 passed**, 36.4 s |
| the CLI suite (`logs/cli-all.log`) | `-p trust-cg-cli --no-fail-fast` | 23 libtest summaries, **187 passed, 4 failed**: `link_imports` 5 passed, 4 failed, each `UnauthenticatedImport` (OD-155, open) |
| `link_imports` on `main` (`logs/main-link-imports.log`) | `origin/main` `15d262831` in a detached worktree | **5 passed, 4 failed**, the same four, the same refusal |
| the three lanes outside the record (`logs/pair-outside.log`) | `--lib -- --exact` with the three names, the overlay's Clean | **3 passed**, 123.7 s; every identity line names Clean `80090967…`, and `MulI16`'s two forms bind it |
| the qualification (`logs/qualify.log`, `logs/qualify.load`, `logs/qualify-outcomes.tsv`) | `commands/qualify.sh`, 23:16:09-23:59:38 UTC, 1-minute load 2.5-22.3, mean 7.6 | `--lib _qualification` **36 passed, 0 failed**, 14 ignored, 2393.5 s; the explicit lane **1 passed**, 123.0 s; exit 0. All 37 lanes print one identity line naming AY build 12713 (`dd6d3661…`) and Clean `80090967…` |

Every recorded outcome held. In the 30 s lanes `SubU128` and `SlotU128`
certified (13.3 s, 11.4 s), `EarlyExit` certified in 22.5 s, `GuardedUdiv`
and `GuardThenCall` ran past the deadline (answers the record accepts for
them), and `MulI16` was AY's self-check rejection (19.5 s). At the 300 s
budget `MulI16` was the self-check rejection again (17.5 s), and
`EarlyExit`, `GuardedUdiv` and `GuardThenCall` certified in 24.0 s, 1.5 s
and 79.7 s. The qualification ran the test binary with sha256 `19030c70…`
(`logs/verify-binary.sha256`).

`main` moved to `15d262831` after these runs; its new commits change, in
the root workspace, only a test assertion in
`crates/trust-cg-lower/src/x86_64_isel.rs`'s own unit tests, which none of
these gates runs, so the runs stand for the lane merged with it (checked
`1cf0880aa`, composed onto `15d262831`). That merge's one conflict was two
entries appended to the end of `docs/decision-record.md`, resolved by
keeping both in order; the documentation, format and ignored-test
inventory checks ran again on the result.

The payloads are in `~/scratch.noindex/round10-20261019/tcg-fc-repair2/` on
the measuring host, with a `SHA256SUMS`: `logs/` holds every run above,
`helpers/` the scripts that made them, `dump/` the 615 queries the
qualification dumped.

| Payload | sha256 |
| --- | --- |
| `logs/fmt.log` | `e0029a00b54609258f5389b1a8a920f5c94342a83c2edf47a64cabf99792afbc` |
| `logs/doc.log` | `a6a60ba870f3c4c0803140250982f702d3af80518ab7fe6072417b0651ee7404` |
| `logs/matrix.log` | `e40ae973e3aaaa3e5108653215a1107f946b7f66e163d0230a2d8e2e7216472f` |
| `logs/matrix-tests.log` | `fedc68b0a3e67ad5f45d30e62d847d5ab67b59f3c7b36fc18076acd5579766d3` |
| `logs/tippy.log` | `de914d199deb3fe43df079f3719830a46920347a50788eeccbec016cfbb793ec` |
| `logs/unit.log` | `0942b3604308dd5211969fc75a5b3b8ce2661333486742d3b1eec94fa68f23ca` |
| `logs/p1-unit.log` | `b24f90492ad017de766e10b1787bbe694c5a04c82d7955909debfd4f52bf1483` |
| `logs/p1-mutant.log` | `8a58bd05d59f0bb53453a2fd6cac45462a7538714d5e6279171d964037acdc1b` |
| `logs/phase1.diff.sha256` | `1b0c2b95a9b899a0d6714674b52123abb4e5ace401bcb48c50677307085ba22e` |
| `logs/nc-nodiscovery.log` | `a717781fdd1a0e951f7468e01ab8c0a6010f32d56a49c5284a481faa0fd06b05` |
| `logs/nc-explicitnofile.log` | `b3e7d782f2d4d8d3699393408add567b827a91ee47a4a942d2c10e619c0e13eb` |
| `logs/nc-noay.log` | `36f0920f5ec5f0b4c509ce6b3ef2d5a0c671ab6871e6c79e68b2b94b491efaf2` |
| `logs/nc-otherclean.log` | `68b7651640c0afaa565ce0f34e919aebd05c1003e198e23a20b5609de802e0ba` |
| `logs/nc-fake.log` | `414c76b7c9166ef76c6221a9d620dd7be223e65868e39eafebd4f43faa47df46` |
| `logs/nc-explicit-lane.log` | `bb64cf2bbbceb138f9381d2e11884dad9fda155cd5e625548cbf9ea03d7662e4` |
| `logs/codegen-evidence.log` | `21d1e4d47388183ab7a4b3fd239abf82e2aa8124046f966b8b707458f577199c` |
| `logs/lower-evidence.log` | `35d70c667593522343e4511131841fe22b2200b1cd29c501370c4252f6d6355d` |
| `logs/knob-codegen.log` | `ad30315663d4e7055f7d5d27c667dd3ae63773f1c04eec2fcb5294c078fa4f11` |
| `logs/knob-lower.log` | `e0496dbb73a5cccd3af49c98500db25766d04d56c369fa2fd77543b61ea78a72` |
| `logs/codegen-corpus.log` | `a89888d4876afe0e608aa2548e9e52edf35f62564216d49ba457143d9f8670ce` |
| `logs/cli-license.log` | `de6d39aa710d6aa2714f76447468b48f9cc1d86007381f60251b6b8162bccb21` |
| `logs/cli-all.log` | `3b958762469656284c9bd11be276c6b0724d5488b2084a54eb83fbb93bc3b556` |
| `logs/pair-outside.log` | `47ec0b70d31496ff02138a48e27285bb324118cde72a6094285f62fe4a1fecc0` |
| `logs/qualify.log` | `3c9c53d4add8c85817c5b369eb3fc16eb83ca9847de7d9d797447f3a665c4c10` |
| `logs/qualify.load` | `a21c4def1682dfe7b082d576eda32ac7054d06f831cb21edbb85af7ad4da6888` |
| `logs/qualify-outcomes.tsv` | `a3b81b20b49ffbb0ab864c4c88a6d3447bf733ff8d770d65eb0b57889e167ff7` |
| `logs/main-link-imports.log` | `393d9c11ef93af87133b4112f3539a3c481f1d5b8e8f9754c49bbb37444c67f9` |
| `logs/verify-binary.sha256` | `f5ea497810e569e820c296ab60747785feb6324ea0cecfaa0af57945ef32a46d` |
| `helpers/phase1.sh` | `6e68bc72c59fba4c38f26577a7dd91a32e061d22688fd91adcb876ed64ef561c` |
| `helpers/gates.sh` | `09a5bd55d8fcfe25c12da601c87ce0ad7848f125591398f19830b9b7fa0f30e1` |
| `helpers/main-link-imports.sh` | `940d29a4a2ba5ebe9c284d0fe9ffb88bba611bcd9c4a1bbc374f49c92470aef5` |

### Gates on the merged tree onto 787d8e25c (2026-10-19)

`main` moved to `787d8e25c` (x86-64 body slice 18, the canonical theorem
spelling, OD-187 to OD-189) after the section above. Its commits touch
twelve of the lane's files (`LIMITATIONS.md`, the decision record,
`x86_source_bound_body_tests.rs` and nine qualification and test files of
trust-cg-verify) and re-spell every fixture theorem the record lanes
replay, so the runs above do not stand for the merge. The merge
(`57e1484d9`) was clean, and every gate ran again on it and on the commits
after it. The fail-closed structure is unchanged by it: the 41
`replay_environment(` sites and the 39 lanes are the same, `main` adds no
`SKIP` or `skip_test` site, and slice 18's new tests are tool-free.

The merged tree's gates found two problems, both from `main`, and both are
fixed on the branch:

- **Lint.** `scripts/check_tippy.sh` (package 9192) was red in
  trust-cg-verify (`logs/tippy.log`): "manual checked division" in
  `fold_constant` (`x86_source_bound_body/split.rs`, slice 18 stage 2).
  With that fixed it reached the test code and named three more in
  `x86_source_bound_body_slice18_tests.rs`: the same lint in the sweep's
  exact `udiv`, and two "very complex type used". `042fef195` and
  `21459fd16` spell both divisions through `checked_div` (the same value:
  `None` exactly on a zero divisor) and name the two types. The pre-push
  hook runs this lint as a pre-flight.
- **This host's record.** The qualification read `--lib _qualification`
  **34 passed, 2 failed**, 14 ignored, 1353.1 s, at 1-minute loads of 3.8
  to 9.6, then the explicit lane **1 passed** (`logs/qualify.log`). Both
  failures were slice 10's lanes on one row. Slice 18's report leaves this
  host's record to be re-qualified by a run on this host, and in this run
  `MulU64`, still a gap of `KNOWN_UNCERTIFIED_SLICE_TEN` on the Darwin
  x86-64 pair (a timeout at 30 s there, certified offline in 68.4 s),
  certified here in 16.95 s and was credited in its credit lane. Every
  other entry of this host held: `SubU128` certified, `MulI16` was AY's
  self-check rejection, and the explicit lane passed. `2a04db7f9` makes
  `MulU64` this host's `CERTIFIED_HERE_BY_HOST` entry, beside `SubU128`.
  The gap lane alone, three times, each its own process, then certified
  it in 16.99 s, 16.71 s and 17.39 s at 1-minute loads of 7.6 to 7.9, and
  the credit lane passed (`logs/b-gap10-*.log`, `logs/b-credit10.log`, on
  `2a04db7f9`).

`6c377b6c6` also makes the record fixes the reviews of `47808425f` asked
for. The knob controls' doc comments and the knob's own docs now open with
OPEN. The decision record records as open the wiring the admission-order
test cannot see. The section above no longer rests on
`logs/phase1.diff.sha256`.

The gates on the landed tree ran on `21459fd16` (`logs/c-*.log`, one
build-slot admission, `c-gates.status` and `c-gates.status.end` empty),
with the overlay's `targo` through `scripts/trust_cargo.sh` unless the row
says otherwise:

| Gate | Command | Result |
| --- | --- | --- |
| format, documentation, ignored-test inventory (`logs/c-fmt.log`, `logs/c-doc.log`, `logs/c-matrix.log`) | as above | OK |
| lint (`logs/c-tippy.log`) | `scripts/check_tippy.sh`, package 9192 | **19 packages clean**, exit 0 |
| the tool-free unit tests (`logs/c-unit.log`) | the five by exact name | **5 passed** |
| the solver-free body gate (`logs/c-body-gate.log`) | `--lib x86_source_bound_body`, skipping the 39 lanes | **333 passed**, 0 failed, 16 ignored |
| the five absences (`logs/c-nc-*.log`) | as in the section above | **0 passed, 39 failed** each, 39 distinct panic sites, every one "cannot judge", no `SKIP` line, no identity line |
| the explicit lane, no checker (`logs/c-nc-explicit-lane.log`) | as above | **1 failed** |
| slice 10's two lanes (`logs/c-gap10-1.log`, `logs/c-credit10.log`) | each by exact name, its own process, with the pair | **1 passed** each; `MulU64` certified in 16.8 s |
| the CLI suite (`logs/c-cli-all.log`) | `-p trust-cg-cli --no-fail-fast` | 23 libtest summaries, **187 passed, 4 failed**: the four `link_imports` tests of OD-155, as on `main` |
| the qualification (`logs/c-qualify.log`, `logs/c-qualify.load`) | `commands/qualify.sh`, 02:25-02:48 UTC, 1-minute load 8.8-22.6, mean 11.4 | `--lib _qualification` **36 passed, 0 failed**, 14 ignored, 1408.4 s; the explicit lane **1 passed**, 23.5 s; exit 0. All 37 identity lines name AY build 12713 and Clean `80090967…` |

In that qualification `MulU64` certified in 24.3 s and `SubU128` in
14.1 s, and `MulI16` was the self-check rejection (25.3 s). Since slice 18,
the three labels whose record says that some runs certify certify in
0.1-1.4 s, at the 30 s deadline and in the explicit lane's 300 s budget
alike: `EarlyExit` (1.4 s) and slice 14's `GuardedUdiv` and
`GuardThenCall` (0.15-0.25 s). Their `DEADLINE_BOUND_HERE_BY_HOST` entries
still accept a `Timeout` at 30 s; retiring them needs their own repeated
measurement on this host and is left open (LIMITATIONS.md). The
qualification ran the test binary with sha256 `1f2bcec4…`
(`logs/c-verify-binaries.sha256`).

The kernel-TV row ran in the first admission, on `6c377b6c6` (the merge
plus the documentation commit; `gates.status` empty). The commits after it
change only trust-cg-verify:
fold_constant's division, slice 18's tests and this host's table. The rows
were trust-cg-codegen `codegen_license_evidence` **12 passed** and
trust-cg-lower's **24 passed**. Their `mutation-knobs` controls were
**12 passed, 1 failed** and **24 passed, 1 failed**, red as recorded:
`InvalidTrustIrModule` on the AOT lane and `UnevidencedGate` on `with_tls`.
The rest of that admission: `must_refuse_corpus` **5 passed**, the CLI's
`codegen_license_flags` **7 passed**, the three lanes outside the record
**3 passed** with the pair, and the hook's case-collision check found
none.

The payloads are in `~/scratch.noindex/round10-20261019/tcg-fc-land3/` on
the measuring host, with a `SHA256SUMS`: `logs/` holds every run (the
first admission unprefixed, then `b-` and `c-`), `helpers/` the scripts
(`gates.sh`, `gates2.sh` stopped at its lint step when the lint named the
test findings, `gates3.sh`), and `dump/` and `dump3/` the queries the two
qualifications dumped.

| Payload | sha256 |
| --- | --- |
| `logs/tippy.log` | `d8e721085f0c6224734a6e9a092798a68aa431a5425a0b4a55ea4130a20d34f4` |
| `logs/qualify.log` | `0b921023dd37890765bcd7df07acccd9b68e55072b2cc6daa7709105e52e3733` |
| `logs/qualify.load` | `afbaea2a962e5e45d2bf83dab03db2778b89c4d9ecea9955a98bef0d7371a060` |
| `logs/b-gap10-1.log` | `5840bb3067d8ddb604cafb34adaf8be7181ea5eb7f9523913e3fe880ae1793af` |
| `logs/b-gap10-2.log` | `e8b75ef32699c94ffb4b3aed4eeddafbb153d0d1baadb31c20578b064458032a` |
| `logs/b-gap10-3.log` | `a8bfec801bd382347708a9c0f74831918f70f40417a2cf7acfd608f167759210` |
| `logs/b-credit10.log` | `6b675fc92b478306b6ef050ce6370b5829ac1e00295d8e710d71e13dd591d956` |
| `logs/c-fmt.log` | `b5417ba7fc199d5d57ab2bf5218659ebcb9b649a32d20064f9388438917f1253` |
| `logs/c-doc.log` | `2fe8943580f042ca7828afaac26c75ada976da1290275d47ccb8ba401e87bfd9` |
| `logs/c-matrix.log` | `85e373fea250f24b0bfa7fc1899ff65d91bc074aeecdec1a61dfe7ddb27c3bbd` |
| `logs/c-tippy.log` | `1415897cfc84c08c9d33d577425a644be261b28a66f878fcb74e7445c362fc4e` |
| `logs/c-unit.log` | `1a5489d790ea5a289b3a4b005f116eca24fbfc79d11e9d327ca69ab9d54158a2` |
| `logs/c-body-gate.log` | `a74bcf9385a9589249677fc16184f0499ebca992dcf077fb4af7751f9ca54623` |
| `logs/c-nc-nodiscovery.log` | `059fd9bf933568fd986613785cbc61bed8e7a4cfcca6866562985dd2d03dbc4e` |
| `logs/c-nc-explicitnofile.log` | `7fbe2d0f22b4a990c138d0e00e6a4a7deb1c60674d0810526fe34d67a153c136` |
| `logs/c-nc-noay.log` | `793ba3290cb43ce906dc669385d2dbd8e9db77990ad4d260375a1706903c4556` |
| `logs/c-nc-otherclean.log` | `f97aebe7db9535a0a7bd801a24d208d516ce3a4209a322b49176d6aa8544fafe` |
| `logs/c-nc-fake.log` | `ff343b7b97403d741269663297664a7ba8069d287f4cf56e9ca78a1fd05bcc20` |
| `logs/c-nc-explicit-lane.log` | `99e077184f42f8e72bce4821912057e15f97f654987a3f8dca859af91f31fbd8` |
| `logs/c-gap10-1.log` | `676fc7e99d77d3883b3e0ad2e41349e56c9014636c03a41c8dcf70012d41bbb8` |
| `logs/c-credit10.log` | `6bfdeb008db158a1ed50446ceec99ba2425bec0d416372158b574a68247ab62c` |
| `logs/c-cli-all.log` | `eecd8ea27b74387cd81a09a5af11fdd7ad73f33b5ca90c14f75c9985c8e2c2dd` |
| `logs/c-qualify.log` | `bae270c22e17670c27a80570ce46270281735a5d8873c79d14ca51c9f56d150f` |
| `logs/c-qualify.load` | `048ee36d66aedcb0b28d8f2ee63aeba8d32e6ffae1ed7ff5000fbdc616f01aca` |
| `logs/c-verify-binaries.sha256` | `4c0239962285d10269458eecd634a326cb0e6a570eff8668e4d8f7d629990b35` |
| `logs/codegen-evidence.log` | `97e9ff2cd1e58b60a7ff1a8c6f9d690961fbd99342001ec9eb906e2e05104d37` |
| `logs/lower-evidence.log` | `d2e01746402ec9d82cf31b27902815defed8ba0f761aafa0cd3d0bf14089a8be` |
| `logs/knob-codegen.log` | `f6adeb5904f9e07f6763f78e12dca8d612c555d85d06bc8f3417a89db34169cd` |
| `logs/knob-lower.log` | `2b70c640f3ac8b3aea377e765c18aa9e350fbbce5397bb702cb11b2236d17e14` |
| `logs/codegen-corpus.log` | `4fc5a0ea741f31e104a0fab3a93682097b498a3c47b16fafd5868bed299b18f2` |
| `logs/cli-license.log` | `9c3dca924100912e7f4c112c389f6a71a0d898bd239763655d1da3ee60599de6` |
| `logs/pair-outside.log` | `60ba83724274215518ca086a0fcc710908dab4dc881372a7a0325e261fa23400` |
| `logs/case.log` | `fbd94472d622d6b51cb5037d0b57ef19b874e95bc14f65fad753417272bb5a7c` |
| `helpers/gates.sh` | `1a7164d9bc4ceebb57cb91bb26faedf75c42314dccfb544d1702e1992ab95380` |
| `helpers/gates2.sh` | `efc5b399d85b7e84c566a2bf6a60c0f0930e0f51d0f619e9d8eb43f5e11ed798` |
| `helpers/gates3.sh` | `cf35738e3f0ea7a66af894536417c68b8ad4e3ab4561fa0c87eed4cbffd28307` |

#### Then onto 89e8d8f77 and later (2026-10-20)

`main` moved again before the push. `89e8d8f77` brings `b79533c9c`
(AArch64 arithmetic admission, byte-address GEPs), whose trust-cg-lower
change moves the memory fixtures' lowering, and `395a25626`, which cleared
the same three slice-18 lint findings as `21459fd16`. The merge
`f6aa61c6b` took `main`'s slice-18 test file as is: both sides' fixes were
equivalent, and `split.rs` merged cleanly because the two changes were
identical. Every gate then ran again (`logs/d-*.log`, `helpers/gates4.sh`)
on `b55fe20d0`, which also holds `main` up to `e6d95a84d`. Those later
commits change the bridge, its build-probe script test, and
documentation; nothing the root workspace builds. `d-gates.status` and
`d-gates.status.end` are empty.

| Gate | Result |
| --- | --- |
| format, documentation, ignored-test inventory (and its 33 tests), case collisions | OK |
| lint, `scripts/check_tippy.sh`, package 9192 | **19 packages clean** |
| the tool-free unit tests | **5 passed** |
| the solver-free body gate | **333 passed**, 0 failed, 16 ignored |
| the five absences | **0 passed, 39 failed** each, 39 distinct panic sites, every one "cannot judge", no `SKIP` line |
| the explicit lane, no checker | **1 failed** |
| slice 10's two lanes, the pair | **1 passed** each; `MulU64` certified in 18.6 s at a 1-minute load near 9 |
| the kernel-TV row, compiler lanes | codegen **12 passed**, lower **24 passed**, `must_refuse_corpus` **5 passed** |
| its `mutation-knobs` controls, open | **12 passed, 1 failed** and **24 passed, 1 failed**, red as recorded (`InvalidTrustIrModule`, `UnevidencedGate` on `with_tls`) |
| the three lanes outside the record, the pair | **3 passed**, 174.0 s, each identity line naming Clean `80090967…` |
| the CLI suite | 23 summaries, **185 passed, 6 failed**: the four `link_imports` tests of OD-155, and `emit_proofs_flag`'s `cli_emit_proofs_rejects_unmapped_frame_spill_object` and `cli_emit_proofs_rejects_unmapped_and_unbound_frame_spill_object` (below) |
| the qualification, `commands/qualify.sh`, 09:19-09:44 UTC, 1-minute load 9.2-36.6, mean 24.3 | `--lib _qualification` **36 passed, 0 failed**, 14 ignored, 1459.9 s; the explicit lane **1 passed**, 28.7 s; exit 0; all 37 identity lines name AY build 12713 and Clean `80090967…` |

In that qualification `MulU64` certified in 20.7 s and `SubU128` in
16.7 s. `MulI16` was the self-check rejection in 28.0 s, near the
deadline at that load. `EarlyExit`, `GuardedUdiv` and `GuardThenCall`
certified in 0.1-1.9 s at both budgets. The test binary's sha256 was
`d39a9182…` (`logs/d-verify-binaries.sha256`).

The two new CLI failures are `emit_proofs_flag.rs:758`. The test pins
the exact uncovered opcode set of its frame-spill object,
`["AddRI", "SubRI", "Movz", "Madd", "Movn", "AddRR"]`, and the compile now
names seven opcodes, `MulRR` among them. They passed at `a4df638f9` (in
`logs/c-cli-all.log`, 187 passed, 4 failed) and fail since the merge of
`89e8d8f77`. `b79533c9c` removed the aggregate MADD/MSUB admission. The
lane changes no instruction selection, and its only non-test code is
documentation in trust-cg-lower and checker discovery in trust-cg-verify.
So the failures come from `main`, and they are recorded open here.
Measured on `main` itself (`376641c44`, a detached worktree with its own
target dir, `logs/e-main-emit-proofs.log`): `emit_proofs_flag` reads
**11 passed, 2 failed**, the same two tests with the same message.

| Payload | sha256 |
| --- | --- |
| `logs/d-fmt.log` | `97fac149afe2804b5c8707964a33f17658875f96d0ac3f938b392061204a3c67` |
| `logs/d-doc.log` | `e1e08769924e347bffaef7c19dec406df334ade8e1cbf1f9dffa8914943babf3` |
| `logs/d-matrix.log` | `4b2e59e5f6dc4b6c64cd52e63a0edc2cffae602a45100f62b3333b0591763d71` |
| `logs/d-matrix-tests.log` | `f5bfaac390352850bf5424b4e276de127b7c370159ed19cc0d0341c1b03a94ca` |
| `logs/d-case.log` | `d52bdcd327252f6fb02a6208b89f8f0d0821d151b349821affc92dc620aa3de5` |
| `logs/d-tippy.log` | `b4ea8421c1cdbd5fbc43e24aa64755f90cd7c6baa65d6c89fbfef049e455df46` |
| `logs/d-unit.log` | `203919f3275badb068aacff25afbcbbdc906685d6af5da0b97bfde0d460c33fb` |
| `logs/d-body-gate.log` | `f355916924284e9292dd238ad0f1e4243052c8a5e6e4335c783b7021304883a9` |
| `logs/d-nc-nodiscovery.log` | `a9fa07a683a57dfba6e3176653d6477ca9fa8db079152382a70818267f34f003` |
| `logs/d-nc-explicitnofile.log` | `025ef210a5b95d5b75964ee457825ee97066ca021229780b282456d1eb53804e` |
| `logs/d-nc-noay.log` | `00fe6425a3c496c8d645d900de0b47671e6d54c4db527b7a170fab87f7ff9434` |
| `logs/d-nc-otherclean.log` | `20561121f7d74a88b44439ac1653ec43e754bf3bc78fe58aafbfb64f4a9a0d7a` |
| `logs/d-nc-fake.log` | `ed78247f72b1832b274534e31ebd560aaa3c70ccb3a5e02146020126f95594d5` |
| `logs/d-nc-explicit-lane.log` | `7c9d49032ee2c8a0f3367f07750186999f66c1b4b5a379f677d0957a5ecdd196` |
| `logs/d-gap10-1.log` | `0353e84ff2c2cd957ee4c5e64dd83d90a33f8b65b4e6ab00a7b7e27213ec68eb` |
| `logs/d-credit10.log` | `ebd61a46366a027fcf72f0890820e27d69e8c4ec05bb6b08ece4b4f27aad26ab` |
| `logs/d-codegen-evidence.log` | `c270ec6e19e23d4576b2b15228212ff74ee6b4fbf053a9ac61591398ed5ac808` |
| `logs/d-lower-evidence.log` | `f0e72b83e497aab24cd4347060aa533490c3ddfe865b0e8bb3eab092458aa99b` |
| `logs/d-knob-codegen.log` | `88df7d3b9129484e629822f107971b4f9338df8dd9f5323225db7bae4213b60f` |
| `logs/d-knob-lower.log` | `f2a0c8deb1f4baac68cbbc1d8822e3bf8bc5f96c1ca8e3cd8d3fa6f38deb1173` |
| `logs/d-codegen-corpus.log` | `e9882669b43dac6704cb74ecead01b9030856a0e71b61daeaaa75ba6f68a04a0` |
| `logs/d-pair-outside.log` | `77dc838cccf9f49855188506a873d75fdfe9b4a437af10bc49a640db29698def` |
| `logs/d-cli-all.log` | `74ffa8349a789efe772885748fd921990c652f07b563bdcafc88289c228ee9dc` |
| `logs/d-qualify.log` | `df96a601fdd5a99b2fa96fc045e0c5067093b00ffb832ee5c73684c27c842f0a` |
| `logs/d-qualify.load` | `6555ccac81985900b1ceb507bfdcf71175b4c10d0878ac79645ae929c6bcb9c1` |
| `logs/d-verify-binaries.sha256` | `7d07c69f39acea878ac9199052e4f404af7686ce4f77f6efd5855bf1be1b8140` |
| `helpers/gates4.sh` | `3319ce7686121970d0638b3d25555aaff2d4e1f4681126de90213b8a9773a7ff` |
| `helpers/main-emit-proofs.sh` | `068ab1b5cd8bce463e1bb3e2b2666626f00a8ff96bcdb5a44a250a3fd1b18379` |

`helpers/main-emit-proofs.sh` never ran: its build-slot waiter was
cancelled, and the run on `main` is `gates5.sh`'s last step.

#### Then onto 376641c44: QUALIFIED_AY is AY build 13556 (2026-10-20)

`main` then moved `QUALIFIED_AY` to AY build 13556 (OD-190, `3e67351d2`)
and requalified the Darwin x86-64 pair on it. `QUALIFIED_AY` is one AY for
every host, so this host's record, AY build 12713's, is refused by the pair
check until this host re-measures its outcomes with build 13556 (its
LIMITATIONS.md section says so). The merge `568200020` kept both
paragraphs of `CERTIFIED_HERE_BY_HOST`'s doc comment: `MulU64` is now one
of this host's build-12713 entries that `main` keeps. With the 12713
overlay, this record's lanes therefore fail closed at the witness, and
the qualification was not run. The gates ran on `568200020`, with
`LIMITATIONS.md`'s documentation edit uncommitted (`e-gates.status`; it
was committed after):

| Gate | Result |
| --- | --- |
| format, documentation, ignored-test inventory, case collisions | OK |
| lint, `scripts/check_tippy.sh`, package 9192 | **19 packages clean** |
| the tool-free unit tests | **5 passed** |
| the solver-free body gate | **332 passed, 1 failed**, 16 ignored (see below) |
| `negative_memo`, twice more, at a 1-minute load near 12 | **12 passed** each |
| the five absences | **0 passed, 39 failed** each, 39 distinct panic sites, every one "cannot judge", no `SKIP` line |
| the explicit lane, no checker | **1 failed** |
| slice 10's gap and credit lanes, the 12713 pair | **1 failed** each, refused by the pair witness, the gap lane after replaying (`MulU64` certified in 18.5 s) and the credit lane before its first replay |
| the three lanes outside the record, the 12713 pair | **3 passed** |
| the CLI suite | **185 passed, 6 failed**, the same six as on `b55fe20d0` |
| `emit_proofs_flag` on `main` `376641c44` | **11 passed, 2 failed**, the two frame-spill tests above |

The body gate's one failure was
`negative_memo::any_key_component_change_misses` (`replays` 2, expected
1). The negative memo records a certification failure only from a solve
that held the processor (CPU at least 90% of wall), and the test's
fixture AY was starved under the load of the moment. The same module
passed 12 of 12 in the three earlier admissions, and passed twice more
right after this one. The lane does not touch the memo.

The witness's refusal reads "the pinned qualification outcomes for host
aarch64-apple-darwin were measured with [ay 0.27.0 build 13556 …]". That
is not true of this host's record, which build 12713 measured. The text
is `main`'s (it prints `QUALIFIED_AY`, which is one string for every
host) and is left open here.

| Payload | sha256 |
| --- | --- |
| `logs/e-tippy.log` | `51603af6c545ee79aea5b7d4786431ca0c3bc73b29672891bd3378e5112e8916` |
| `logs/e-unit.log` | `fe6dd08033a4fa353f525face5924ede955e9c599c3417dc41a87f4e9eb501df` |
| `logs/e-body-gate.log` | `d6d804f6d7d0bb08a3677efbf6c00509a82a2219454c7eaefd1363b640bdd116` |
| `logs/e-negmemo-1.log` | `14ca9d6c0228c0e129854ff7136db4097c82bb95acaf108ca408488d104970a9` |
| `logs/e-negmemo-2.log` | `b953d129a33e534f15decc0c3d110962914e2fb13226b8884ede306debef8018` |
| `logs/e-nc-nodiscovery.log` | `ae41a930ca608c93bfb4a8523c397a8196e0815f9c4cebd5323e0def71acf17c` |
| `logs/e-nc-explicitnofile.log` | `240b9e7601529701ab48afbab30c824c6b71a81a9c2008125cf991fcb011ade2` |
| `logs/e-nc-noay.log` | `484cdc2c368c8ea45dd998491476aa6b821847695770bc0327300b9f5988e53f` |
| `logs/e-nc-otherclean.log` | `f1b8458c7acfc9e3fb4ae772f0a551b17bd3dc8fc913007122b907ace1b2e592` |
| `logs/e-nc-fake.log` | `facf6a4d2f0b87f950532be1fcf0b9af5055343e7778cbc869028d1fa53e51db` |
| `logs/e-nc-explicit-lane.log` | `b3d1aa6f13a87d89241b29a269e736b8eadf5925f5b8b9075ef492f2abad3835` |
| `logs/e-gap10-1.log` | `a96402fcf3dd10057f019b0b77a0c21b8fff5e0fe3fbbfc68e3d1a4b7e3c67f9` |
| `logs/e-credit10.log` | `1cbf7ffef0733abea26d2904348dfe698e7375a037563dc59e5509fc5d202efc` |
| `logs/e-pair-outside.log` | `a7a13f5efe972ea534feb224da34514c8872749a3d4f8db874f9cfcce157ee1c` |
| `logs/e-cli-all.log` | `c4426c93744002a98eb1e203e7656dde0a37edd3e4ada5b0e5bc5f817ef72d8a` |
| `logs/e-main-emit-proofs.log` | `e724b2faa1b605dd7f8ce9337f0f127a0d70993d3ec117e3e8804164a89e0f41` |
| `helpers/gates5.sh` | `d289a37adc8af88c0b3687ad27559a06987bedc674fa0596903a5aadc399e5dc` |

## Files

Committed beside this README, the reproducer sources:
[`commands/build_and_assemble.sh`](commands/build_and_assemble.sh) (the
worktrees, both builds, both overlays), [`commands/qualify.sh`](commands/qualify.sh)
(a qualification: every lane, then the explicit lane),
[`commands/offline_replay.py`](commands/offline_replay.py) (a dumped
query through AY and Clean), [`commands/burst.sh`](commands/burst.sh) (twelve
replays at once) and [`commands/outcomes.py`](commands/outcomes.py) (a run's
replays from its log).

The payloads stay out of tree (docs/linux-aarch64-completion.md, "Durable
evidence policy"). The 2026-10-17 rounds' are in
`~/scratch.noindex/qual-aarch64-20261017-harness-r2-payloads/` ("Harness
round 2") and
`~/scratch.noindex/qual-aarch64-20261017-harness-r2-landing-payloads/`
("Landing review"), and
`~/scratch.noindex/round9-20261017/tcg-fail-closed-payloads/` ("Fail
closed"), `~/scratch.noindex/round9-20261017/tcg-fc-repair/` ("The checker
the build accepts") and `~/scratch.noindex/round10-20261019/tcg-fc-repair2/`
("Gates on the merged tree"), each listed with its sha256s in that
section.
The
2026-10-16 payloads are kept at
`~/scratch.noindex/qual-aarch64-20261016-payloads/` on the measuring host,
under the names this README uses, with a `SHA256SUMS`:

| Payload | sha256 |
| --- | --- |
| `host.txt` | `320777afcf11fb276844f30caa34450d2e30310ef9f0910098fc2588720e8a4b` |
| `load/confirm1.tsv` | `486abf0a30dc4ced2a1daae8a1e2ff1130d1cf1f1b593eb9c064f1146a4a21e7` |
| `load/confirm2.tsv` | `53a2c50c8366e3136b788b703dfa54767209d244ba901cb7730deea7d431860d` |
| `load/confirm3.tsv` | `30fa5ca50d2015ad7f59a0dd1d996123ceb49676dba3544205be74d091d57ee8` |
| `load/confirm4.tsv` | `27b0a505f3025fcfa46262ecc570212500a5049fbfbaf88d2a4c3363be09c335` |
| `load/measure0.tsv` | `234e9e43eb0878b8a5ef2552de9fbbc2568cb799158df2b73b0d574a05935b27` |
| `load/measure1.tsv` | `55a76a6a46701f889172c0feb7d34d1cc046604f30c4550df7ae561c9e1f75dc` |
| `load/negative-control.tsv` | `55dbcf89ded12130f256305839ec0535bae489f509c88f401e7e37b2055d5f15` |
| `logs/ay-build.log` | `6de661bcec97d4b6d6dff9783e1c5d277d11f4e6f00fd537fc9e9bcbc60848cd` |
| `logs/base-same-pair-20-failures.log` | `26553eed0d27ad31ccdf7d924948d0ea262ee596562447097d1c37b7970ba9bb` |
| `logs/burst.log` | `3e2b886c6e496a27b9d2fca3a34b0c1d1df4098941173dc99c774988ecad44e6` |
| `logs/clean-92bc-build.log` | `d3b92d1c6d4a67bb0fcefb903334827022c7b82cc8cfa5c9ca42fab928f022ed` |
| `logs/confirm1.log` | `13ec74956b85fc8be06e507fc7cd959234066b193fdfe69ced86ed11b98b24e2` |
| `logs/confirm2.log` | `3fe6870bbd95efeca3a357a321b0b5b945144412fbd6799a1f3c6c621729bf6e` |
| `logs/confirm3.log` | `236ec8f85a2ce38d657c8eefcf2a2edf7d5d55227d5135ca81498aa4293ce553` |
| `logs/confirm4.log` | `50fb199e75b2039053d365eb74e140baefafc013eb87b30457840e454a6cc2de` |
| `logs/full-lib-summary.log` | `3a0d50a142b5af6b393bce5170b8f5a7d0c3f27fc6ffa63b92afb50f23c241e7` |
| `logs/full-lib.log` | `595a6c4bf3a54aa1c4d7a6d12b1a4994aec81f7487fc7729cdfc6315f527da28` |
| `logs/measure0-clean8606.log` | `7be6e1c933d708ae9217f05c951935104eaa6609cedb9a5dcc491fb0f6cb0989` |
| `logs/measure1-clean92bc.log` | `2877cab4e015bdc332c600ef702235934b01d94f226906ff3c4324183d595b27` |
| `logs/neardeadline-repeat6.log` | `cffc917134d83b90b69a9e2865c78bba9f81872bf87904461b72a22eb7163f99` |
| `logs/negative-control.log` | `4b6d7108edae37514bfe7831b8efbd1162cf88c41fbc4eada87437fdbe1b2760` |
| `logs/overlay-clean8606-assemble.log` | `207760b4db1d70ed2afd398a36103ed81e1179fd799f2fe6a5dc793dcacd1e15` |
| `logs/overlay-clean92bc-assemble.log` | `93ee0773a24cae2b23e6f3306e38e9eef8706f3055c804caebc37190dab1ca21` |
| `logs/slice14-budget-300s.log` | `a66abcc2b99122a6acb41e5fa8f555015ea69b522bfb98a64cb8ce8968210f59` |
| `logs/slice14-repeat8.log` | `928079a09ff9bb5fead752368ec16c134a2992f2740326e1c1ec75a6e24f83ed` |
| `logs/tippy-trust-cg-verify.log` | `bcc611bdd99972c16696c5ee6358e76c752f816811d178c958d9b070bbab3f63` |
| `logs/trust-cg-verify-build-clean8606-overlay.log` | `21ad990a359f4ff21b4d4f2cc0f0fe46142d5b55f9419d89e74c798aed76a50d` |
| `offline/measure0-clean8606-30s.tsv` | `33439d7218d0e82b99410a2f9dc642c7180193c4937cc69382ba1f0e5526cb62` |
| `offline/near-deadline-repeats.tsv` | `9eae704fb058f2dae0ca1a52b0e9b344deebd55c39f9ba6560a3522c02c824a4` |
| `outcomes/confirm1.tsv` | `bc054aa79c81ff39eea806d03d5016f10b2d68810270d1b9c9cb9430eaae8b8d` |
| `outcomes/confirm2.tsv` | `ff28c11fab31a17a2c94baf382e2475c4b9f559db41cf3eba5d3dd16f8039bea` |
| `outcomes/confirm3.tsv` | `e2d651ea6862fc21ca6ac1a702b705e1497f0b6210b08439bda410c4a72e5045` |
| `outcomes/confirm4.tsv` | `203c5af00ffdd6efcbe74780dfdd1b7444804c0feaf68f1e35854c50093c7c1b` |
| `outcomes/measure0-clean8606.tsv` | `141c6d37b45c53eaa9ccf23ae3aae4264638467cf4179dc1c8e697a7c41be992` |
| `outcomes/measure1-clean92bc.tsv` | `97a362d806b41804a277bbe9d7aaee2d7c3e93a037b741a8d3439695068a0b15` |
| `outcomes/negative-control.tsv` | `bf3358b8f138fd8eeeef5b020aad7117e8ab7b4b8d720236e70e0629e12d410b` |
| `overlay-ay12713-clean8606.json` | `b88f144514a07fe3bdf9580e16ff4d2970ba30f3b750cd7b67279935c8324d9e` |
| `overlay-ay12713-clean92bc.json` | `4c7a49f3c5565d06b2fd7adf94f2615e885b28fa5c6e2d108b69c554f6520f86` |
| `landing/anchored-verify.log` | `76ea3eb57044bcf1e3e504127ac5ceccf2cc40dec333bbe2134d22a371a21537` |
| `landing/check-tippy-all.log` | `4b0d02bb1da15f8715ed419034896b9f5f92bdf7171bda08f74d0166a17e63f7` |
| `landing/mutate-negative.py` | `9bf05ead9ff5503e9d9d404d6c4fc5916b332929758c613311dc5e890b14160e` |
| `landing/mutate-positive.py` | `3ecd636f15e4168325ae16aac60c21a059a9553d5c882bc02c6c72d6cddc965d` |
| `landing/nc-after.log` | `552ac97ecb9ae53424a6c25ebb8d25e67c06558b2ba68b297480fc60faaa045d` |
| `landing/nc-after.log.load` | `b18ca8fc20ed1111d34f019b49db0cca4c1fa5e2db8b13dc9dd395938cf76c8d` |
| `landing/nc-before.log` | `473cf87219c3d4e96b268d80a7ba0838ff297cc9512c7814d6ee328e61fa83b8` |
| `landing/nc-before.log.load` | `73ce8c620d21a2eba6a669957d9ae3f42c52bf90ab049dde9edbd1d92c391313` |
| `landing/pc-after.log` | `0e348ab592249131410cd943825e21612cbb3f9a7be99c40218db0b72bc75285` |
| `landing/pc-after.log.load` | `876ae498ddb3cdac4ec689bb800fd54a380222b6027664e0d90876bd89f1d303` |
| `landing/qualification-merged.log` | `ff81000a23c05e0103a145d4bf2491b43d19aa2ec05ce986eb41a6b77288b57b` |
| `landing/qualification-merged.log.load` | `f0b16ee06c5fd1de3ec4e03702937db31f4f3d0b9243a527a0cee6376695b240` |
| `landing/qualification-merged.tsv` | `fd1be476f0e87c605a56fa660362d1dcec9fd03d3c3b7bf6e718d7ed0997f98d` |
| `landing/run_lane.sh` | `ad9532233de5968a73f752becbacb88c44c4e23072ac6e0e0795abcda03714b9` |
| `landing/tippy-merged.log` | `97fdaf17c0277c57caea3c60d5dc073d21600417aa93276313728b3ee9189307` |
