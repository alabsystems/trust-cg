# Darwin x86-64 body lane requalified on AY build 13556, 2026-10-19

The x86-64 source-bound body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) is credited only by an
AY proof that Clean checks. Its host qualification pins every outcome it
measures to one replayer pair (`QUALIFIED_AY` and the per-host Clean digest).
This record moves the AY half of that pair on the x86_64 Darwin qualification
host from AY main build 12713 (`b1b0b9de0`, ruling OD-85,
[its record](../2026-10-05-darwin-x86-64-ay12713-requalification/README.md))
to AY main build 13556 (`ebde49de3`), which carries the two fixes OD-85 asked
AY for: the resident `ay --incremental` route takes the word-level path (AY
DR-49), and the circuit lane compares a printed literal with its own spelling
up to literal spelling (AY DR-50). Clean 5f09e36c is unchanged. It follows
the 12713 move's procedure and evidence standard: overlay toolchains, every
lane re-run, every changed outcome reviewed, each remaining gap's tool output
re-measured, every counterexample checked by z3. Ruling OD-190 in
docs/decision-record.md records the
decision. Nothing here is a completion claim. Payloads are out of tree:
[PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256, and this README
states the numbers they carry.

Host: the shared x86_64 Mac (4 cores, 16 GB), an AY agent's offline
measurements beside this lane (1-minute load 2.5-5.7 during the
measurements). Toolchain: the overlay `x86-stage1-ay13556` (native stage-1
`trustc 1.99.0-dev (d7f143f3b 2026-09-21)`), `targo --unverified` (no proof
claim about any build), `nice -n 19`, `-j2`. Branch `feat/x86-requal-ay13556`
from origin/main `787d8e25c` (slices 1-18 landed); origin/main `f75a45cc1`
merged before the final ledger and gates (`measure3`, below).

## Findings first

1. **No soundness question.** Every wrong lowering is refuted with a
   counterexample: 282 refutations, the same set as on build 12713. Pinned
   variable by variable into its own wrong-lowering query, each of the 281
   wrong-lowering models is satisfiable for z3 5.1.0
   (`replay/check_all_cex.py`; the 282nd is slice 1's UF + world swap, an
   encoding's evidence). Twelve models differ from build 12713's, and all
   twelve check. No correct lowering is refuted.
2. **The one-shot route certifies one more fixture and loses none.**
   `SubU128` (`u128::wrapping_sub`), build 12713's regression, certifies in
   3.6 s in the lane (offline 1.9-2.6 s, a 12.5 MB proof that Clean checks
   in 1.0-1.2 s; build 12713: past the 30 s deadline in every lane run,
   and its recorded offline replay in slice 18's spelling certified after
   138.6 s). It leaves `KNOWN_UNCERTIFIED_SLICE_ELEVEN`.
   No gap joins and no fixture newly fails. The other ten gaps keep their
   outcome at the deadline.
3. **The queries did not move.** All 618 queries the qualification replayed
   (every lane's `TCG_X86_BODY_QUALIFY_DUMP`) are byte for byte the queries
   of slice 18's ledger on build 12713 (`s18/qual/stage3`). Every changed
   outcome below is the AY's.
4. **The resident route's loss is closed where measured.** In the codegen
   end-to-end test, which compiles through the production replay (resident
   `ay --incremental` first, then the fresh proof-producing solve),
   `mul_u32` promotes Formal on both triples (`replay=Valid`): build 12713's
   resident route ran past 30 s on it. `dag_stores` replays in 0.6 s. On the
   `StoreJoin` spellings before slice 18 (the AY agent's export; about
   28.7 s on build 12713 in the coordinator's offline evidence), build 12713
   takes 6.8 s of AY and 22.0-22.6 s of Clean on an 18.6 MB proof; build
   13556 takes 1.4 s and 0.2-0.3 s on a 3.8-3.9 MB proof.
5. **Four gaps now end in a self-rejection rather than a timeout, offline.**
   At a 300 s budget, `Mul/commuted` and slice 16's three `LongChain` parts
   end with AY rejecting its own proof (`step t1 uses unverified trust
   rule`, 150-292 s) where build 12713 ran out the budget. At the lane's
   30 s deadline all four are still `Timeout`, as recorded. `MulI16`
   reaches the same `unsupported hole rule` rejection in 44 s against 84 s,
   and `MulU64` certifies offline in 52 s against 68 s.
6. **The other hosts refuse until re-measured.** `QUALIFIED_AY` is one
   string for every host. The Linux x86-64 and Darwin AArch64 records were
   measured with build 12713 and are kept as they are; the pair check now
   refuses both hosts until each runs build 13556 and re-measures its own
   outcomes (OD-190).
7. **A tooling gap, not addressed here.** `scripts/export_x86_qualification_matrix.py`
   refuses main's own matrix capture at its first slice-15 record ("invalid
   matrix record 532"): the exporter does not know slice 15's family, as it
   did not know slice 9's in the 12713 record. The z3 check reads the
   capture's `X86_BODY_MATRIX` lines directly instead.

## The AY and the overlays

No published x86_64 Darwin pack carries build 13556 (the managed pack 6808
bundles AY 0.13.0, the stage-1 tree build bundles build 10530), so the AY runs
from two local overlays assembled by `scripts/assemble_trust_overlay.py`, as
for build 12713. Each is a copy-on-write APFS clone with `bin/ay` and
`bin/clean` replaced and an `overlay.json` that names both digests and source
commits. Neither is a published pack, a release input or signed.

| Overlay | Assembled from | `overlay.json` sha256 | Used by |
| --- | --- | --- | --- |
| `~/.local/share/trust-overlays/x86-stage1-ay13556` | `trust/build/x86_64-apple-darwin/stage1` (installed kind; `trustc` d7f143f3b) | `cb33f79408ec4c0bd368d0578749c0e9a57df6f225e967a509af7176411bf46e` | `TRUST_TARGO=<overlay>/bin/targo` for the root workspace; the census's hosting `trustc` |
| `~/.local/share/trust-overlays/x86-stage0-bridge-ay13556` | `trust/build/x86_64-apple-darwin/stage0-sysroot` (`--pack-kind wrapper-sysroot`; wrapper sha256 `416d4429…` before, `0c61994e…` after, running pack 6808's `trustc` 3d7768caf) | `acccbbb924352edf2cc32ac46472b2fb104e9c59d98d5ca3cc27e2a69459a90e` | `RUSTC=<overlay>/bin/trustc` for the rustc bridge |

In both overlays `bin/ay` is
`55d348f454d5e939f32657222fd773b938ed444328400ba58efaa24f01103de8`, the same
bytes as `~/tcg-scratch/ay-cert/bin/ay-main-ebde49de3`, banner
`ay 0.27.0+build.13556.ebde49de3c2c3b03f3b1a4e5dc60a5b37aa870a0@2026-10-19T09:53:16Z`:
an unverified release build (`targo --unverified build --release -p ay
--features cli`, by the AY agent) of `~/tcg-scratch/ay-cert/ay-src-ebde`. The
assembler checked the banner's `build.commit` and `build.increment` against
that checkout: HEAD `ebde49de3`, `git rev-list --count` 13556, tracked tree
clean. `b1b0b9de0` (build 12713) is its ancestor, 843 commits back. `bin/clean`
is `949365b61779ed281fc65677517fa333ab17e91dffa33396746e6a493bf00ac9`, Clean
5f09e36c from `~/clean-5f09`, the binary of the 12713 overlays and of every
earlier Darwin x86-64 record.

trust-cg-verify's `build.rs` validated the root overlay and records it
(`TOOLCHAIN_AY_RECORD_OVERLAY=valid`, `OVERLAY_SHA256=cb33f794…`,
`SHA256=55d348f4…`, `INCREMENT=13556`, `OVERLAY_CLEAN_SHA256=949365b6…`), and
every lane printed the admitted identity before replaying:
`ay 0.27.0 build 13556 commit ebde49de3c2c3b03f3b1a4e5dc60a5b37aa870a0 sha256
55d348f4… overlay-toolchain manifest-sha256 cb33f794… clean-sha256 949365b6…
clean-commit 5f09e36c…`. The bridge overlay is validated by the bridge build
the coordinator's census runs (`census/census13556.sh`); this lane did not
build the bridge.

## Every changed qualification outcome

The qualification lanes run on the one-shot route (`TCG_NO_SOLVER_SERVER=1`),
then Clean, one test per process (`replay/qualify.sh`, the 40 tests of
`replay/tool_gated_tests.sh`: every slice's qualification and credit lane,
slice 9's spellings, slice 17's mis-models, the canonical-migration pair, the
deadline-bound lane and the envelope's two lanes). Two runs were made, as for
build 12713, and a third after merging origin/main. `measure1` ran with
`QUALIFIED_AY` moved and the old tables: 38 of 40 passed, and the two slice-11 lanes failed on `SubU128` alone
(`left: [MulU128]`, `right: [SubU128, MulU128]`; the credit lane `SubU128:
left 0, right 8`). `measure2` ran with the new tables (below): 40 of 40
passed, with the same outcome on every one of the 941 outcome lines as
`measure1` (`SubU128` 3.8 s), and z3 again finds all 281 wrong-lowering
models satisfiable. After origin/main `f75a45cc1` was merged (its adapter
now spells byte-address arithmetic as `ArrayGep` of `i8`; no golden moved),
`measure3` re-ran all 40 on the merged tree: 40 of 40 passed, every one of
the 618 replayed queries byte for byte `measure2`'s, every outcome the same,
and z3 again confirms all 281 models. The baseline is
slice 18's final ledger on build 12713 (`s18/qual/stage3`, the same code);
`replay/compare_ledgers.py` compares the 944 outcome lines of the two ledgers.
Each remaining gap was replayed offline from the lane's own dump at a 300 s
budget (`replay/gaps300.sh`, `replay/replay_one.py`).

| Module | Fixture or evidence | AY build 12713 | AY build 13556 | Review |
| --- | --- | --- | --- | --- |
| slice 11 | `SubU128` | `Timeout`; offline, Verified after 138.6 s (8.4 MB, Clean 5.6 s) | Verified (3.6 s); offline 1.9-2.6 s, 12.5 MB, Clean 1.0-1.2 s | **gap removed** |
| slice 1 | `MulI16` | `Timeout`; offline, self-check rejected after 83.7 s | `Timeout`; offline, self-check rejected after 44.4 s (`unsupported hole rule`) | gap kept, tool output updated |
| slice 1 | `Mul/commuted` | `Timeout`; offline, `unknown` / timeout after 296.8 s | `Timeout`; offline, self-check rejected after 150.1 s (`step t1 uses unverified trust rule`) | gap kept, tool output updated |
| slice 9 | `LongChain` | self-check rejected (0.45 s; `step t0`) | self-check rejected (0.48 s; `step t1`) | gap kept, tool output updated |
| slice 10 | `MulU64` | `Timeout`; offline, Verified after 68.4 s | `Timeout`; offline, Verified after 52.2 s (4.1 MB, Clean 0.4 s) | gap kept, tool output updated |
| slice 11 | `MulU128` | `Timeout`; offline, no answer at 300 s | the same (300.1 s) | gap kept |
| slice 14 | `UdivConst`, `UremConst32` | `Timeout`; offline, no answer at 300 s | the same (300.1 s each) | gaps kept |
| slice 16 | `LongChain` parts 1-3 | `Timeout`; offline, no answer at 300.1-305.9 s | `Timeout`; offline, self-check rejected after 187.8, 180.0 and 291.6 s | gaps kept, tool output updated |
| slice 9 spellings (evidence, no record) | `SlotJoin` without inlining / with the untrimmed chain | `Timeout` / `Timeout` | Verified (31.6 s with Clean) / Verified (3 ms) | none: the lane holds each spelling only to being refuted or not |
| slice 1 | UF + world (19), concatenated (19) and preserved-tail (2) forms | as recorded | identical | none |
| slice 4 (memory) | six rejected encodings | 5 Verified, `store_then_load` byte-UF self-check rejected | identical | none |
| slice 6 | `(=> C X)`, every-definition, case-split and merged spellings | as recorded (`PairJoin` merged: Verified or a Clean timeout) | identical; `PairJoin` merged Verified in all three runs | none; the merged record keeps its tolerance until a run measures its Clean time here |
| envelope | 3 theorems, 10 mutants | (not in the slice-18 ledger; OD-85: Verified, all refuted) | Verified, all refuted | none |
| every other outcome line of the 40 lanes | certified fixtures, credit rows, refutations | as recorded | identical | none |

The only other differences between the ledgers are the canonical-migration
diagnostic's identity fields (the AY path and digest; both forms still
`Timeout`, `proof_credit=false`) and lines the slice-18 ledger did not run
(the envelope). Certified cases also got faster: slice 5's `CmpUleU16`
22.3 s to 3.8 s, slice 9's plain `StoreJoin` spelling 26.7 s to 1.6 s, slice
16's `DiamondChain` parts 16 s to 13 s.

`verifier_credits_*` passes in every module under the new tables: every
covered row of a certified fixture is Formal, and every gap's rows are
Unverified and never Failed. No check changed shape and none was weakened:
the only table edit that changes what a lane accepts is `SubU128`'s removal,
a strengthening (its rows must now be credited).

## Codegen end to end

`replay/gate_e2e.sh` runs the codegen `x86_source_bound_body` and
`must_refuse_corpus` tests serially with `x86-body-trace` on and every line
time-stamped (`replay/stamp.py`), on the production replay route. Both pass
(5 and 5). The identity line names the overlay's AY (`X86_BODY_E2E_REPLAY_IDENTITY
... build 13556 ...`). `a_body_the_replayer_may_not_certify_is_judged_only_by_its_theorem`
takes its second branch: `mul_u32` replays Valid and promotes Formal on both
triples. In `slice_one_to_ten_functions_promote_with_replayed_body_theorems`
the slice-9 functions replay in 0.36 s (`dag_calls`), 0.37 s (`dag_xors`) and
0.59 s (`dag_stores`) on the first triple, and from the run's memo on the
second; the whole test takes 42 s.

| Query (`StoreJoin`, `replay/replay_one.py`, `replay/resident_one.py`) | AY 12713 fresh: AY / Clean / proof | AY 13556 fresh: AY / Clean / proof | resident, 12713 / 13556 |
| --- | --- | --- | --- |
| balanced spelling before slice 18 (`fe2c9ab5`, the AY agent's export) | 6.8 s / 22.6 s / 18.6 MB | 1.4 s / 0.3 s / 3.8 MB | 1.4 s / 0.2 s |
| right-nested spelling before slice 18 (`707d79fa`) | 6.8 s / 22.0 s / 18.6 MB | 1.4 s / 0.2 s / 3.9 MB | 1.3 s / 0.2 s |
| slice 18's fixture query (the lane's dump) | 0.7 s / 0.1 s / 1.5 MB | 0.3 s / 0.1 s / 1.0 MB | 0.3 s / 0.1 s |

Slice 18's spelling had already taken most of `StoreJoin`'s cost away on
build 12713; build 13556 removes the Clean cost the earlier spellings paid.

## Census

The Darwin x86-64 `core` proof census on this branch (O0, `-Cpanic=abort`,
one CGU, proofs required, `-Ztrust-verify=off`, `x86-body-trace` and
`x86-body-dump`) is the coordinator's, run with `census/census13556.sh` (a
copy of `~/tcg-scratch/census13556.sh`): a release bridge built against
`x86-stage0-bridge-ay13556`, hosted by the root overlay's `trustc`, compared
with the landing baseline.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-d0ecc859f-ay12713` (baseline) | `main` `d0ecc859f` | 12713 | `9b754868…` | 114 | 2588 s |
| `core-x86_64-darwin-O0-proof-ay13556` | this branch, `f0113c522` | 13556 | `de9f4943…` | **106** | 4493 s |

**8 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
8 bodies bound on both sides that build 12713 did not certify now replay
Valid. The baseline ran on the 12713 lane (`census12713.sh`), this branch on
the 13556 lane, each bridge in its own tree, with no resource-budget refusal.

## Gates

On this branch after the merge of origin/main `f75a45cc1`, on the root
overlay (`targo --unverified`, AY build 13556 and Clean 5f09e36c admitted),
`--no-fail-fast` (`replay/gates.sh`, payload `gates-merged/`; the same gates
before the merge, payload `gates/`, all passed too, with 2093 lowering tests
where main's merge adds two):

| Gate | Result |
| --- | --- |
| verify library: `x86_source_bound_body`, `x86_source_bound_envelope`, `diag::` (every slice's qualification and credit test included) | 389 passed, 0 failed, 16 ignored (1964 s) |
| codegen `--test x86_source_bound_body --test must_refuse_corpus` | 5 and 5 passed; the serial, traced run of the same two targets before the merge (`e2e/e2e_serial.log`) passed too |
| `trust-cg-lower --lib` | 2095 passed, 0 failed |
| `scripts/check_fmt.sh` (pack 6808's `targo`) | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK (exit 0) |
| the 40 tool-gated tests, one per process (`measure3`, merged tree; `measure2` before the merge) | 40 passed, 0 failed (`measure3` 21:07-21:47, `measure2` 19:28-20:05, 1-minute load 2.7-4.2) |

No test in the tree pins the bridge's recorded AY: the bridge records the AY
of the sysroot it is built against (`crates/trust-cg-verify/build.rs`), and
the census checks it by running.

## Reproducers (in tree)

- `replay/qualify.sh` runs tool-gated tests one per process under the
  overlay; `replay/tool_gated_tests.sh` lists the 40.
- `replay/compare_ledgers.py` compares two ledgers outcome by outcome.
- `replay/gaps300.sh` replays every remaining gap (and `SubU128`) offline at
  300 s with `replay/replay_one.py` (one-shot strict Alethe, then Clean, with
  the proof size and Clean's own time); `replay/resident_one.py` times the
  resident route (copied from the 12713 record).
- `replay/check_all_cex.py` checks every counterexample with z3.
- `replay/gate_e2e.sh` and `replay/stamp.py` time the codegen end-to-end
  test's replays; `replay/gates.sh` runs the gates above.
- `census/census13556.sh` is the census command.
