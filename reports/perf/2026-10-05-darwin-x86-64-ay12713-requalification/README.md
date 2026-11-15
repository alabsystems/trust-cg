# Darwin x86-64 body lane requalified on AY build 12713, with its `core` census, 2026-10-05

The x86-64 source-bound body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) is credited only by an
AY proof that Clean checks. Its host qualification pins every outcome it
measures to one replayer pair (`QUALIFIED_AY`, `QUALIFIED_CLEAN_SHA256`). This
record moves that pair on the x86_64 Darwin qualification host from the native
stage-1 toolchain's AY 0.27.0 build 10530 (`d14080122`) to AY main build 12713
(`b1b0b9de0`, "the raw ground closure certifies trust-cg's x86-64 body theorems
word by word"). Clean 5f09e36c is unchanged. It holds the overlay toolchains
that run the new AY, the review of every changed outcome, the regressions found,
the census row and the gates. Ruling OD-85 in
docs/decision-record.md records the
decision. Nothing here is a completion claim. Payloads are out of tree:
[PAYLOADS.md](PAYLOADS.md) lists each one with its SHA-256, and this README
states the numbers they carry.

Host: x86_64 Mac, 4 cores, 16 GB, shared with two other agents' builds and a
census (load 5-15 during these measurements). Toolchain: native stage-1
`trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, `targo --unverified` (no proof
claim about any build).

## Findings first

On the Darwin `core` census, the same trust-cg tree's bridge fails **573
roots on build 12713 against 1095 on build 10530**. 525 roots are promoted and
3 newly fail. Each of the three is an AY regression, explained below. No
mismatch is named and no bound body is refuted. The bodies AY does not
certify drop from 620 to 98. The library qualification gains five certified
fixtures and loses one. The regressions found are these:

1. **AY regression, `SubU128` (`u128::wrapping_sub`).** Build 10530 certifies
   this fixture in 6-12 s. Build 12713 performs the same search: the same 4811
   conflicts and 19261 decisions, on a CNF of 1343 variables against 1346. It then
   spends 30-44 s of CPU producing and self-checking a proof of 83.5 MB,
   against 18.9 MB, and passes the replay's 30 s deadline. Offline, without
   the deadline, the proof certifies and Clean accepts it. AY main build
   12515 (`57ea58ca3`, 2026-10-02, before the word-level merge) takes 49.2 s,
   and branch build 12519 (`9ad05eb80`) takes 53.2 s. So the slowdown landed
   on AY main between builds 10530 and 12515. It is not the word-level work,
   which recovers part of it. The fixture is recorded as a gap and named a
   regression (`KNOWN_UNCERTIFIED_SLICE_ELEVEN`).
2. **The live lanes' resident route does not get the word-level path.** A
   compile's replay asks the resident `ay --incremental` first, with
   verdict only, and runs the fresh proof-producing solve only after an
   `unsat` (`replay_protocol_description`). The library qualification
   disables the resident route (`TCG_NO_SOLVER_SERVER=1`). Measured on
   the bridge's own query of `u32::wrapping_mul`, the one-shot
   `ay -smt2 --strict-proofs` of build 12713 certifies in 0.1 s. Its resident
   route answers `unknown` / `timeout` at 30 s, where build 10530 answered
   `unsat` in 12.3 s. So `mul32` certifies in the library qualification and
   times out in a compile (`replay/smoke.sh`, `replay/resident_one.py`). Two
   of the census's three newly failing roots, `u64::wrapping_mul` and
   `usize::wrapping_mul`, fail on this route: build 10530's resident route
   answered in 3.1 s. The census measures the production route, so its
   promotions already count this loss. On a sample of 40 of the slice-11
   census's 381 uncertified texts, a simulation of that protocol on build
   12713 (`replay/production_replay.py`) certifies 33. Three run out the
   resident deadline, and in four the fresh solve does.
3. **Proofs cost Clean more.** Certified proofs are larger, and Clean takes up
   to 60 times longer to check them. `PairJoin`'s merged slice-6 spelling is a
   4.6 MB proof that Clean checks in 0.5 s on build 10530, and a 10.4 MB
   proof that takes 30.6 s on build 12713, at the checker's own 30 s budget.
   Certified fixtures slow down too: `NegI128` takes 17.5-20.4 s against
   5.1-6.6 s, `SlotJoin` takes 20.5-23.3 s, and `StoreJoin`'s canonical
   theorem takes 34.2 s of AY plus Clean. Credit near the budget therefore
   depends on load.
4. **AY build 12713 does not honour its own `:timeout` on every query.** On
   a 300 s budget, `Diamonds5` was still running at 900 s and `SwitchChain`
   at 310 s, when the process groups were killed. The lane is unaffected,
   because its own deadline kills the process group. Several gaps that build
   10530 rejected in 1-13 s now run for minutes and end in `memout`:
   `MulU64` after 233.6 s, `MulPanics` after 210.3 s and `LongArm` after
   188.5 s.
5. **No soundness question.** Every wrong lowering is still refuted. The
   new AY reports 147 counterexamples. Each one, pinned variable by variable
   into its wrong-lowering query, is satisfiable for z3 5.1.0
   (`replay/check_all_cex.py`). The model values differ from build 10530's
   in two refutations, `AddU128/adc-as-sbb` and `SubU128/high-swapped`, and
   both models check. No correct lowering is refuted.

## Overlay toolchains

No published x86_64 Darwin pack carries build 12713. The managed pack 6808
bundles AY 0.13.0, and the stage-1 tree build bundles build 10530. So the AY
runs from local overlays assembled by `scripts/assemble_trust_overlay.py`.
Each overlay is a copy-on-write APFS clone with `bin/ay` and `bin/clean`
replaced and an `overlay.json` that names both digests and source commits.
None is a published pack, a release input or signed.

| Overlay | Assembled from | `overlay.json` sha256 | Used by |
| --- | --- | --- | --- |
| `~/.local/share/trust-overlays/x86-stage1-ay12713` | `trust/build/x86_64-apple-darwin/stage1` (installed kind; `trustc` d7f143f3b, its `bin/trustc` sha256 `8d4201dd…`) | `c31d083b30613a136d0c416bac63a16bdcf3ef9d2b257d0ed95576306a6ef460` | `TRUST_TARGO=<overlay>/bin/targo` for the root workspace; the census's hosting `trustc` |
| `~/.local/share/trust-overlays/x86-stage0-bridge-ay12713` | `trust/build/x86_64-apple-darwin/stage0-sysroot` (`--pack-kind wrapper-sysroot`; wrapper sha256 `416d4429…` before, `b7e45c03…` after, running pack 6808's `trustc` 3d7768caf) | `bc48d68b9a5f24df14cc06049592ce37bda5b06205c4a1a178a5772c5f1d9423` | `RUSTC=<overlay>/bin/trustc` for the rustc bridge |

In both overlays `bin/ay` is
`ae2773da7c4d3f8fb01cbbdf8fc21c04faa13d4645940b934d8366780f2876b9`, the
banner `ay 0.27.0+build.12713.b1b0b9de07af146c1244633189f92971a3347db9@2026-10-05T11:55:07Z`,
an unverified release build of `~/tcg-scratch/ay-cert/ay-src-b1b0`. Its
banner commit and build number match that checkout's HEAD and
`git rev-list --count`. `bin/clean` is
`949365b61779ed281fc65677517fa333ab17e91dffa33396746e6a493bf00ac9`, Clean
5f09e36c from `~/clean-5f09`; that commit string is embedded in the binary,
and the binary fully verifies trust-cg's control proof. Both overlays were
assembled from the original trees, which are unchanged.

The stage-0 sysroot's `trustc` is a shell wrapper with `--sysroot`
hard-coded. The assembler's new `--pack-kind wrapper-sysroot` rewrites that
one `sysroot=` assignment to name the overlay. It refuses a symlinked or
binary wrapper, a wrapper with no or several assignments, an assignment that
names another directory, and a wrapper that names the sysroot anywhere else
(ten new tests in `scripts/tests/test_assemble_trust_overlay.py`, 23 in
all).
trust-cg-verify's `build.rs` validates both overlays and records them:

| Build | `TOOLCHAIN_AY_RECORD_SYSROOT` | Overlay | AY recorded | Clean pinned |
| --- | --- | --- | --- | --- |
| root workspace (`trust-cg-verify` lib tests) | `x86-stage1-ay12713` | `valid`, `c31d083b…` | build 12713, `ae2773da…` | `949365b6…` |
| rustc bridge (release) | `x86-stage0-bridge-ay12713` | `valid`, `bc48d68b…` | build 12713, `ae2773da…` | `949365b6…` |

A bridge loaded into a compiler admits that compiler's sysroot `bin/ay`. The
census therefore runs on the root overlay's `trustc`, which is a clone of
stage 1's, so its bytes and its `librustc_driver` are the same. Hosted by
stage 1's own `trustc`, the bridge would find build 10530 and refuse it.

## Every changed qualification outcome

The qualification modules run with `TCG_NO_SOLVER_SERVER=1`, the one-shot
route, then Clean. Two runs were made. The first, `measure1`, ran with the
old `QUALIFIED_AY`, so every module printed all of its outcomes before
failing on the identity. The second, `measure2`, ran with the new tables. Its
only failure was `PairJoin`'s merged spelling, which a third table revision
records (finding 3). An offline replay of the changed queries
(`replay/investigate*.sh`, `replay/replay_one.py`) supplies each new gap's
tool output.

| Module | Fixture or evidence | AY build 10530 | AY build 12713 | Review |
| --- | --- | --- | --- | --- |
| slice 1 | `MulU32` | self-check rejected (9-12 s) | Verified (0.1 s) | gap removed |
| slice 1 | `AddShl2/LeaSib` | incomplete certificate (`hole`) | Verified (2.4 s) | gap removed |
| slice 1 | `MulI16` | self-check rejected (11.8-12.3 s) | `Timeout`; offline, self-check rejected after 83.7 s | gap kept, outcome updated |
| slice 1 | `Mul/commuted` | self-check rejected | `Timeout`; offline, no answer within 300 s | gap kept, outcome updated |
| slice 1 | preserved tail, `U8Ident` / `Add/commuted` | self-check rejected / self-check rejected | Verified / `proof-trusted` | evidence table (new: `PRESERVED_TAIL_OUTCOMES`) |
| slice 1 | UF + world form, 19 call shapes | 18 self-check rejected, 1 incomplete | 18 Verified, `CallBoolArg` self-check rejected | evidence; Ackermann-reduced encoding kept |
| slice 1 | concatenated form, `CallSix` (7 items) | self-check rejected | Verified (all 19 now Verified) | evidence |
| slice 4 (memory) | 35 fixtures | all Verified | all Verified | none |
| slice 4 (memory) | rejected encodings, 6 forms | 5 self-check rejected, 1 refused at publication (#8821) | 5 Verified, `store_then_load` byte-UF self-check rejected | evidence; access-trace encoding kept |
| slices 5, 7, 8 | 40 + 3, 15, 22 fixtures | all Verified | all Verified | none |
| slice 6 | 25 + 3 fixtures | all Verified | all Verified | none |
| slice 6 | `(=> C X)` spelling, 26 cases | incomplete certificate (`hole`) | `proof-trusted` | evidence |
| slice 6 | `PairJoin` merged spelling | Verified | Verified, or `Timeout` at Clean's budget under load | record accepts either (finding 3) |
| slice 9 | `SlotJoin`, `BoolDag` | self-check rejected / incomplete certificate | Verified (20.5-23.3 s / 4.7-5.0 s) | gaps removed |
| slice 9 | `Diamonds5`, `Diamonds6`, `GuardChain9`, `SwitchChain`, `LongArm`, `CallJoin`, `LoadDag` | self-check rejected (0.2-13 s) | `Timeout`; offline: no answer, timeout, `memout`, or (`CallJoin`) certified after 277 s | gaps kept, outcomes updated |
| slice 9 | `LongChain` | self-check rejected | self-check rejected | none |
| slice 9 | `NestedTree` | self-check rejected | `proof-unrenderable` ("authored assume canonical term exceeds the structural rendering bound") | gap kept, outcome updated |
| slice 10 | `MulI64` | self-check rejected | Verified (1.3 s) | gap removed |
| slice 10 | `MulU64`, `MulPanics` | self-check rejected (about 1 s) | `Timeout`; offline `memout` after 210-234 s | gaps kept, outcomes updated |
| slice 11 | `SubU128` | Verified (6-12 s) | `Timeout`; offline Verified after 30-44 s | **REGRESSION**, recorded as a gap and reported |
| slice 11 | `MulU128` | `Timeout` | `Timeout`; offline, no answer within 300 s | none |
| envelope | 3 theorems, 10 mutants | Verified, all refuted | Verified, all refuted | none |
| all | 147 wrong lowerings and the UF + world swap | counterexamples | counterexamples, z3-confirmed | none |

Net, on the one-shot route: five fixtures now certify and one regresses.
`verifier_credits_*` passes in every module under the new tables: every
covered row of a certified fixture is Formal, and every gap's rows are
Unverified and never Failed. Two checks changed shape, and no check was
weakened:

- The slice-9 check compares each gap's recorded outcome. It keeps the
  existing tolerance between AY's two self-rejections and accepts nothing
  else.
- The slice-1 preserved-tail evidence is a pinned table, like the other
  encodings, where it was one assertion that both forms are self-check
  rejections.

## Census

**The first run was discarded.** It started at 10:02, and the host's disk
was full (0 bytes free) from about 10:45 to 11:05, filled by other work on
the host. The compile and AY's proof files both write to that disk, so a
failed write could have shown up as an uncertified body or a compile error,
which is exactly what a census measures. The coordinator stopped that run
at 11:14. Its out-dir and dumps were deleted. The 36 source-bound negative-memo
entries written during it (30 `timeout`, 6 `self-check-rejected`) were moved
out of the per-box store, so that the rerun would not be answered from them.
They are kept as a payload, and `census_discarded_diskfull.log` is the
discarded run's log. The rerun started at 11:16:52 with 204 GiB free, under
the coordinator's hold on other censuses. `census_host.log` samples the free
disk and the load every minute through the rerun. The disk never fell below
188 GiB free, the load stayed between 2.7 and 11.4, and no row recorded a
resource-budget refusal.

The census is the Darwin x86-64 `core` proof census at O0 with
`-Cpanic=abort`, one CGU, proofs required (the bridge default),
`-Ztrust-verify=off`, `x86-body-trace` and `x86-body-dump`. It is the
command of every earlier row (`census/census_ay12713.sh`). Both bridges carry
the same trust-cg code: the branch changes only tests, comments and scripts
beyond `6b108b81d`. They differ in the AY each records and in the compiler
that hosts them, a byte-identical clone whose `bin/ay` differs.

| Row | Bridge built from | Bridge sha256 | Hosting `trustc` / AY | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-6b10` (baseline, run by the slice-13 lane) | `main` `6b108b81d`, `stage0-sysroot` | `abf52e17…` | stage-1 / build 10530 | 1095 | 15029 s |
| `core-x86_64-darwin-O0-proof-ay12713` | this branch, `486982bfd`, `x86-stage0-bridge-ay12713` | `dc0f68b9…` | `x86-stage1-ay12713` / build 12713 | 573 | 8342 s |

**525 roots are promoted and 3 newly fail. No mismatch is named and no bound
body is refuted** (`census/census_compare.py`, payload `compare/`). Every
failed root of both runs is `[TCG-PROOF-465]`, plus one
`[TCG-MIR-UNSUPPORTED]` typed refusal in each. Both runs bind the same 2921
bodies. Those that replay Valid go from 2301 to 2823, and those with no
independently checked proof from 620 to 98. The two wall times are a trend
only: the baseline overlapped this branch's builds and qualification runs.

| Bound bodies on both runs | Bodies |
| --- | ---: |
| not certified -> Valid, from a strict self-check rejection | 450 |
| not certified -> Valid, from an incomplete certificate | 70 |
| not certified -> Valid, from a timeout | 5 |
| Valid -> not certified, a timeout | 3 |
| not certified on both | 95 |

**The three newly failing roots** are AY regressions on the live route,
replayed from the census's own dump (payload `newly/`):

- `u64::wrapping_mul` and `usize::wrapping_mul` have byte-identical
  queries, the 64-bit `bvmul` against `imul`. Build 10530's resident route
  answers `unsat` in 3.1 s, and its fresh solve certifies in 6.1 s. Build
  12713's resident route answers `unknown` / `timeout` at 30 s, although its
  one-shot solve certifies the same query in 0.1 s. This is finding 2.
- `core::str::traits::check_range`: both resident routes answer `unsat` in
  5-7 s. The fresh, proof-producing solve certifies in 29.5 s on build
  10530, which is at the deadline already, and in 49.0 s on build 12713,
  past it (finding 1's class of slowdown).

Of the 98 bodies left uncertified (76 distinct query texts), 83 time out, 14
are strict self-check rejections and 1 keeps a trusted step. Replayed
offline through the same protocol at load 6-8 (`replay/production_replay.py`,
payload `prod_census98_new.tsv`), the 76 texts split as follows:

- 34 run out the resident deadline. The one-shot route certifies 7 of
  them in 0.1-8.1 s, and those 7 are finding 2's loss (payload
  `oneshot_resident_deadline.tsv`).
- 22 run out the fresh deadline.
- 12 are AY rejecting its own proof.
- 8 certify, near the deadline. The root classes
(`reports/perf/2026-09-27-darwin-x86-64-census/root_classes.py`, payloads
`classes_*.txt`) are unchanged except the AY class:

| Class of the failed root's named function | Baseline | Build 12713 |
| --- | ---: | ---: |
| bound, not certified (AY) | 620 | 98 |
| a loop | 165 | 165 |
| a private slot's address escapes | 49 | 49 |
| a join of paths with different escapes | 35 | 35 |
| more machine rows than the bound | 30 | 30 |
| non-scalar parameters | 22 | 22 |
| division or remainder | 21 | 21 |
| call shapes | 20 | 20 |
| control flow outside the acyclic domain (three kinds) | 26 | 26 |
| no observable | 14 | 14 |
| atomics | 14 | 14 |
| guards | 12 | 12 |
| narrow and `bool` loads and stores outside the lane | 15 | 15 |
| floating-point operations, constants and conversions | 19 | 19 |
| other refusals (nine kinds, each 6 or fewer) | 33 | 33 |
| **total** | **1095** | **573** |

## Gates

The gates ran on this branch with the root overlay (`targo --unverified`,
`TRUST_TARGO=<x86-stage1-ay12713>/bin/targo`, AY build 12713 and Clean
5f09e36c admitted). They used `~/tcg-scratch/gates_full_stage1.sh`, which now
selects the overlay lane from the worktree's pin.

| Gate | Result |
| --- | --- |
| verify library, `x86_source_bound_body`, `x86_source_bound_envelope` and `diag::`, every slice's qualification and credit test included | First run: 11 of the 12 negative-memo controls failed (overlay build; see below). After the fix: 239 passed, 0 failed, 9 ignored (payload `gate_verify1.log`, 2419 s) |
| codegen `x86_source_bound_body` end to end and `must_refuse_corpus` | 5 and 5 passed. The end-to-end test replays on build 12713 (`X86_BODY_E2E_REPLAY_IDENTITY`, payload `e2e.log`) |
| IR, lowering and optimizer libraries | 538, 1993 and 4226 passed (2 ignored) |
| codegen library | 4612 passed, 0 failed, 1 ignored |
| CLI `must_refuse_corpus` | 1 passed |
| `--lib --tests` build of every root-workspace test target, `--keep-going` | every target compiles except the three kernel-JIT fixtures (`e2e_defeq_cache`, `e2e_lazy_delta`, `e2e_phase_completion`: "kernel JIT fixtures require exact Rust 1.95.0, Rust 1.97.1, or the certified Trust compiler"), the known refusal (payload `gates_alltargets.log`) |
| `scripts/tests/test_assemble_trust_overlay.py`, `test_export_x86_qualification_matrix.py` | 23 and 10 passed |
| `bash scripts/check_fmt.sh` | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `scripts/check_tippy.sh` | cannot run here. The only `tippy` on this host is the managed package 6808's, and it stops before linting any package: 320 `unknown field compiler_timeout_secs` and 5 `no matching package named ay-pb` (payload `tippy.log`). The stage-1 build and the overlay ship no `tippy` |

**The negative-memo controls on an overlay build.** An overlay build's record
pins the overlay's own Clean, and it refuses the fixture checker that
`x86_source_bound_body::tests::negative_memo::` drives. With that checker
refused, no replay outcome reached the memo, and 11 of the 12 controls
failed ("the non-certified replay is recorded: left 0"; payload
`negmemo_overlay.log`). This is the same incompatibility that ruling OD-60
removed from the transport controls. The memo controls now run under the
fixture pair's own record (`fixture_pair_record`, shared with
`with_fixture_replay`) and pass 12 of 12 there. Production discovery and the
memo itself are unchanged.

None of the known flakes recurred in the final run: the `SlotFoldedOffset`
memory qualification, the AArch64 parallel/serial byte identity, and the
x86 verifying JIT's envelope replay.

## Reproducers (in tree)

- `census/census_ay12713.sh` runs the census. `census/census_compare.py`
  reports the promoted, newly failing and mismatched roots, the refuted
  bodies, the verdict changes with their replay-outcome classes, and the
  outcome counts.
- `replay/qualify.sh` runs the qualification modules under the overlay.
  `replay/replay_one.py` replays one query strictly, with a wall cap that
  kills the process group, then Clean. `replay/replay_matrix.py` replays
  part of the exported qualification matrix.
- `replay/resident_one.py` and `replay/production_replay.py` time the
  resident route and simulate the live replay protocol.
  `replay/oneshot_dir.py` replays a directory on the one-shot route.
  `replay/smoke.sh` compiles three functions through a bridge.
- `replay/gate_verify.sh` and `replay/gate_e2e_alltargets.sh` are the gate
  steps whose complete output is kept.
- `replay/clean_time.py` times AY and Clean separately.
  `replay/check_cex.py` and `replay/check_all_cex.py` confirm
  counterexamples with z3. `replay/investigate*.sh` replays the changed
  fixtures offline.
- The qualification matrix comes from
  `scripts/export_x86_qualification_matrix.py`. On this tree it refused
  main's own capture at the first slice-9 record until the exporter learnt
  slice 9's family (this branch).
