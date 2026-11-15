# Source-bound negative memo: probe crate and Darwin x86-64 `core` census, 2026-09-30

What the negative memo (`crates/trust-cg-verify/src/source_bound_negative_memo.rs`,
LIMITATIONS.md) changes in compile time, and that it changes no verdict,
measured through the rustc bridge on the slice-5 host: native stage-1
`trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this host
against the stage-1 `stage0-sysroot` (`targo --unverified build --release
--locked`), toolchain AY 0.27.0 build 10530 and the stage-1 `bin/clean` as
the default discovery selects them. Single runs on a shared four-core host;
other sessions' builds and censuses ran during every row, so wall times are a
trend, not a measurement. Nothing here is a completion claim.

| Bridge | Tree | `backend.sha256` |
| --- | --- | --- |
| before | `main` `73e5a69f5` (this branch's base) | `0c7ee18d808156806bd216111d5b63893315547fc6e8d69f0a6b42825b55fd27` |
| after | this branch (`frontier/x86-body-negative-memo`), first version (`ee9454af0`) | `acd238300351897ebde7cf4b352576c7de243508b64d3f0090d7839b579c1428` |
| after, review fixes | this branch merged with `main` `f2ba63226`, with the review fixes (`d4ceb2482`) | `fe294f80a4b7b6f4c39654ad10280c096fe06d83069c9b9a1c8cd15f8d357eaa` |

The probe and census sections below were measured with the first version;
[the last section](#after-the-review-fixes) re-measures the probe after an
adversarial review's fixes.

## Probe crate

`probe/probe.rs` is the slice-5 review's three-function crate
(`u32::overflowing_mul` through `s5_mul`, a pair swap and a compare;
`no_std`, O0, `-Cpanic=abort`, one CGU, proofs required), compiled with
`probe/run.sh` and `-Ztrust-ir-cg-args=solve-trace
-Ztrust-ir-cg-args=x86-body-trace`, interleaved (`probe/probe_ab.sh`). The
body query of `overflowing_mul` (3180 bytes; the crate's function and
`core`'s local copy share it) does not certify: the resident AY answers an
`unsat` candidate after 22.0 s and the fresh proof-bearing replay ends
`(:reason-unknown (incomplete self-check-rejected))`, 34.3-34.6 s per
occurrence in all. The batched compile fails and the per-function fallback
replays every body again, so the query occurs four times.

| Run | Bridge | Negative namespace | Wall | Body solves | Memo hits |
| --- | --- | --- | ---: | ---: | ---: |
| before 1 | before | (none) | 146.5 s | 5 | 0 |
| cold 1 | after | removed first | 45.0 s | 2 | 3 |
| warm 1 | after | as cold 1 left it | 8.7 s | 1 | 4 |
| before 2 | before | (none) | 148.0 s | 5 | 0 |
| cold 2 | after | removed first | 44.7 s | 2 | 3 |
| warm 2 | after | as cold 2 left it | 9.6 s | 1 | 4 |
| bypass | after + `source-bound-no-negative-memo` | (not read or written) | 147.5 s | 5 | 0 |

Every run ends with the same refusal (`s5_mul: [TCG-PROOF-465] ...`, rc 1)
and the same body trace (`overflowing_mul` and `s5_mul` `replay=none`,
`s5_lt` and `s5_pair` `replay=Valid`); only the source of the non-credit
outcome differs. The remaining body solve in every run is `s5_lt` (836
bytes, Valid in 1.1 s). A cold run solves the failing query once (the
process tier answers `s5_mul` and both fallback occurrences); a warm run
reads the per-box entry recorded by the cold run (`reuses=1/2`) and solves
nothing that fails. The bypass knob restores the old behaviour exactly.
Per-run stderr is in `probe/`, `summary.txt` has the lines above.

## Census

`~/tcg-scratch/postpush_census.sh <worktree> <tag>` for each row: the Darwin
x86-64 `core` census (`trust/scripts/trust_ir_cg_census.py`, O0,
`-Cpanic=abort`, one CGU, proofs required, `-Ztrust-verify=off`,
`-Ztrust-ir-cg-args=x86-body-trace`, `--timeout 14400`). The base row is the
post-push census of `main` `73e5a69f5` another session ran (its first 15
minutes shared the host with a one-core AY replay sweep). The two memo rows
ran back to back from one working directory (the memo key binds the
verifier child's working directory): `cold` after removing
`~/.cache/trust-cg/alethe-certs/source-bound-negative-v1/`, `warm` with
what `cold` recorded. Other sessions' builds, lint runs and censuses shared
the host during all three rows (load averages 4-8).

| Row | Wall | Failed roots | Bound bodies Valid / not certified | Failing-body solves | Memo hits (process / store) |
| --- | ---: | ---: | --- | ---: | --- |
| base `73e5a69f5` | 3994 s | 2114 | 1271 / 165 | 330 | 0 |
| negative memo, cold | 2824 s | 2114 | 1271 / 165 | 95 | 235 / 0 |
| negative memo, warm | 1031 s | 2114 | 1271 / 165 | 0 | 235 / 95 |

- **Verdicts.** No root differs: 0 promoted and 0 newly failing in both
  A/Bs (`ab/`), the same 2113 `[TCG-PROOF-465]` roots and one
  `[TCG-MIR-UNSUPPORTED]` root in all three rows, the same 165 functions
  `replay=none` (each judged twice, by the batched compile and its
  per-function fallback) and the same 1271 `replay=Valid`, and the same
  count in every body-trace class (`body_trace.txt.gz` per row). No
  `[TCG-COMPILE-DRIVER]` resource-budget refusal in any row.
- **Cold.** The 165 bodies are 95 distinct query texts. Each was solved
  once and recorded (all 95 as `(:reason-unknown (incomplete
  self-check-rejected))`; recorded solve time median 14.5 s, max 37.5 s,
  1503 s in all); the other 235 occurrences (the fallback's second replays
  and byte-identical bodies) were answered by the in-process tier.
- **Outcome kind, not verdict, differed once.** The three
  `core::fmt::num::imp::*::_fmt` bodies (two texts) ended as an incomplete
  certificate (`unproved_steps=1`) on all six base-row occurrences and as a
  strict self-check rejection on the cold row's live solves (the first
  occurrence of each text, no memo hit before it), so the base row has 324
  rejections and 6 incomplete certificates and the memo rows 330
  rejections. Both kinds withhold credit and the three roots fail on every
  row. The same bytes give both kinds when replayed directly, depending on
  load (`reports/2026-09-30-ay-strict-selfcheck-nondeterminism/`, text
  `d8bb35f5a58572dd`); the warm row replays the kind the cold row recorded.
- **Warm.** Each text's first occurrence read its per-box entry (one reuse
  of a budget of two) and every later occurrence was answered in process;
  AY ran for no body it does not certify. What remains is the rest of the
  compile, including the 1271 Valid bodies, which the per-box Alethe store
  and the process's `Verified` memo answer exactly as on the base row.
- **Wall.** 3994 s -> 2824 s -> 1031 s. For reference, `main` before slice
  5 took 2597 s and slice 5 4726 s in the slice-5 A/B
  (`reports/perf/2026-09-29-darwin-x86-64-census-slice5/`). All rows are
  single runs on a shared host.

## After the review fixes

The review found no path by which the memo grants credit and asked for
eight fixes (LIMITATIONS.md lists them): a build identity in the key and a
protocol rendered from the real commands; only the measured-stable classes
recorded; an in-process hit and time budget; no entry after a SAT verdict;
a namespace lock around every read-modify-write and delete; regular files
only (a FIFO hung the compile); a stored reason that must classify as its
label; and a fresh-process ordering test. Same probe, same script
(`probe-after-review/probe_ab2.sh`), interleaved:

| Run | Bridge | Negative namespace | Wall | Body solves | Memo hits |
| --- | --- | --- | ---: | ---: | ---: |
| before 1 | before (`73e5a69f5`) | (none) | 145.0 s | 5 | 0 |
| cold 1 | after, review fixes | removed first | 43.8 s | 2 | 3 |
| warm 1 | after, review fixes | as cold 1 left it | 7.8 s | 1 | 4 |
| before 2 | before (`73e5a69f5`) | (none) | 145.0 s | 5 | 0 |
| cold 2 | after, review fixes | removed first | 43.0 s | 2 | 3 |
| warm 2 | after, review fixes | as cold 2 left it | 8.1 s | 1 | 4 |
| bypass | after, review fixes + `source-bound-no-negative-memo` | (not read or written) | 145.0 s | 5 | 0 |

Every run ends with the same refusal and body trace as before. The entry is
now `outcome:self-check-rejected` under `source-bound-negative-v2/`; the warm
runs' first hit reads it (`tier=store reuses=1/2 process_hit=1`) and the
other three are answered in process (`process_hit=2..4` of 64).

The census was not re-run. For its keys the fixes change only the key's
build component: every uncertified census body ends in a recorded class (a
strict self-check rejection, or an incomplete certificate), the most frequent
key occurs 26 times in one compile (within the 64-hit budget) and the cold
compile took 47 minutes (within the 60-minute window), so the census would
behave as the rows above, except that the first version's entries (namespace
`v1`, other keys) are not read.

