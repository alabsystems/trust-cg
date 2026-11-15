# The Clean proof check's own deadline (OD-223), 2026-11-02

Ruling OD-223 (`docs/decision-record.md`) separates the Clean check of an AY
Alethe proof from the AY solve. The two had shared one deadline. This report
records the measured case, the controls and their fails-before runs, and the
offline replay of the case. Host: the Darwin x86-64 qualification host (8
logical CPUs), with the qualification pair of the
`x86-stage1-ay13556-t011` overlay: AY 0.27.0 build 13556 (`55d348f4…`) and
Clean 5f09e36c (`949365b6…`). Lane: `fix/x86-body-checker-deadline` on main
`9d9e1a372`. Every build and test ran through `build-slot`, with one test
per process where the gate says so. The payloads live out of tree, under `~/tcg-scratch/`;
[PAYLOADS.md](PAYLOADS.md) binds them by size and SHA-256.

## The measured case

`core::num::<u64>::leading_zeros`, census s23final, query SHA-256
`9eb494ad18054a7eb50a942f45efcd20212f0eaf00b96ae2c63abab016841a68` (10,049
bytes, byte-identical since slice 16):

```
bound rows=26 replay=none (no independently checked proof); reason=AY TIMEOUT
bound rows=26 replay=none (no independently checked proof); reason=negative memo (AY not run): AY TIMEOUT
```

The first line is the batch pass and the second its per-function fallback.
AY answers the query `unsat` in 7.6-8.0 s, or 2.3 s resident. Clean needs
41-53 s of CPU time to check the ~11 MB proof. Main ran both the fresh
replay's check and the certificate store's re-check under the query's 30 s
solve budget, reported the expired check as `AYResult::Timeout`, and the
negative memo recorded it as a solver `timeout` (entry `b6d4d878…`).

## The census case, replayed offline

The measurement ran in the lane's own `build-slot` hold, at load 3.5-6.1.

Through the verifier's own funnel, the probe
`x86_source_bound_body::tests::negative_memo::checker_deadline::od223_probe_replays_a_dumped_body_query_through_the_funnel`
replays the dumped bytes with `TCG_SOLVE_TRACE=1` and `TCG_OD223_PROBE_QUERY`
naming the query. Its defaults are the 30 s solve budget and the checker's
own 180 s:

| route | AY | Clean check | wall | children CPU | outcome |
| --- | ---: | ---: | ---: | ---: | --- |
| one-shot, into a fresh store | 4.487 s | 31.738 s | 36.256 s | 35.458 s | `Verified`, `LiveSolve` |
| census route (resident, then the one-shot replay of its candidate) | 1.644 s resident | 32.298 s | 38.526 s | 36.087 s | `Verified`, `LiveSolve` |
| fresh process, the store's re-check of the stored proof | not run | (all of it) | 32.365 s | 31.557 s | `Verified`, `AletheCertStore` |

The children's CPU excludes the resident server, which is never reaped.

The tools alone, through `measure_lz.py` (the replay's commands and JSON, the
verifier's sanitized environment):

| run | step | deadline | outcome | wall | CPU |
| --- | --- | ---: | --- | ---: | ---: |
| 0 | AY one-shot | 30 s | `unsat`, clean certificate, 11,185,753-byte proof | 4.788 s | 4.562 s |
| 0 | Clean, old deadline | 30 s | killed at the deadline | 30.009 s | 29.736 s |
| 0 | Clean, new deadline | 180 s | accepted | 31.877 s | 31.753 s |
| 1 | AY one-shot | 30 s | `unsat`, the same proof | 4.452 s | 4.426 s |
| 1 | Clean, new deadline | 180 s | accepted | 31.162 s | 31.065 s |

Under the old deadline the check used 99 % of it in CPU time, which is why
main's memo recorded a `timeout`. At this load the check needs 31-32 s; the
earlier measurement of the same proof was 41-53 s of CPU (51 s at load
8.8). Either way it exceeds the 30 s solve budget, and 180 s is 3.4 times
the worst.

## Controls and fails-before

The fixture pair is a counting AY that answers `unsat` at once, and a
Clean whose check of the fixture proof is slow, never ends or refuses. The
controls are in `x86_source_bound_body_checker_deadline_tests.rs`, plus one
each in `proof_certificate.rs` and `source_bound_negative_memo_tests.rs`;
the decision record lists them. Each ran in a process of its own. The
mutants are applied by `ckdl/mutate.py`, which restores the sources after
each run, with one build per mutant. P is pass, F is fail.

| control | lane | main-route | deadline ignored | timeout as AY's | memo files as `timeout` | memo judges on solver | key without deadline | memo reads v5 |
| --- | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| one-shot, check outlasts the solve budget | P | F (`AY TIMEOUT`) | F | P | P | P | P | P |
| census route (resident deadline, then the slow check) | P | F (`AY TIMEOUT`) | F | P | P | P | P | P |
| check that never ends: label, `checker-timeout`, key | P | F | F | F (`AY TIMEOUT`) | F (no entry) | F | F (`(1, 1)`) | P |
| refusal never credited, labelled as Clean's | P | F (`AY TIMEOUT`) | F | P | P | P | P | P |
| store re-check outlasts the solve budget | P | F (AY ran) | F | P | P | P | P | P |
| claims each outlast the solve budget (65 checks) | P | F | F | P | P | P | P | P |
| labels and `proof_gate` classes (unit) | P | P | P | P | P | P | P | P |
| the deadline (unit) | P | F | F | P | P | P | P | P |
| export sidecar publishes, refused one does not | P | F (`TIMEOUT`) | F | P | P | P | P | P |
| memo judges the two kinds apart (unit) | P | P | P | P | F | F | P | P |
| every key component changes the key (unit) | P | P | P | P | P | P | F | P |
| the store format, v5 foreign (unit) | P | P | P | P | F | P | P | F |
| promotion's replay timeout is the checker's (adapted) | P | F (`Timeout`) | P | F (`Timeout`) | P | P | P | P |

In the "lane" column, the run on the lane also passes the controls outside
the mutant set: the adapted probe-timeout, consume and mint controls, and
the memo units `only_measured_stable_outcomes_are_classified`,
`a_reason_that_does_not_classify_as_its_label_is_a_miss` and
`a_hit_can_only_withhold_credit`. Main's route reproduces the census
symptom on the fixture pair. The memo-only mutants leave the labels right
and are caught by the memo. The first `main-route` build did not compile:
the mutant left `clean_check_timeout_reason` unused, which the workspace's
`warnings = "deny"` refuses. It was rebuilt with the function referenced
(`ckdl/jobD.log`).

## Gates

All of these ran on `66b972623`, the lane merged with main `451c75834`:

- **The x86 body suite** (`x86_source_bound_body::tests::` with
  `--skip negative_memo --skip host_qualification --skip verifier_credits
  --skip canonical_migration`, one process): 397 passed, 0 failed, 18
  ignored.
- **The negative-memo controls** (OD-197's 17 real-path controls, one per
  process): 17 passed.
- **The qualification lanes** (one per process, the qualification pair):
  - slice 6: `host_qualification_replays_the_slice_six_body_theorems` and
    `verifier_credits_every_bound_slice_six_row_with_the_replayed_body_theorem`;
  - slice 13: `host_qualification_replays_the_slice_thirteen_body_theorems`,
    `verifier_credits_every_bound_slice_thirteen_row_with_the_replayed_body_theorem`
    and `verifier_credits_no_row_whose_routine_the_crate_defines`;
  - slice 16: `host_qualification_replays_the_slice_sixteen_parts` and
    `verifier_credits_every_bound_row_of_a_function_in_parts`;
  - slice 20: `host_qualification_replays_the_slice_twenty_body_theorems`
    and `verifier_credits_every_bound_slice_twenty_row_with_the_replayed_body_theorem`;
  - slice 22: `host_qualification_replays_the_slice_twenty_two_body_theorems`,
    `host_qualification_refutes_every_slice_twenty_two_wrong_lowering`,
    `verifier_credits_every_bound_slice_twenty_two_row_with_the_replayed_body_theorem`
    and `verifier_credits_no_row_whose_routine_the_module_defines`.

  All 13 passed. Slice 19 has no host-qualification lane of its own: its
  real-path controls are the negative-memo controls above, and its
  solver-free tests are in the suite.
- **The lib groups the change touches:**
  - pass: `source_bound_negative_memo::` 25, `obligation_cert_store::` 66,
    `proof_certificate::` 24, `ay_bridge::subprocess_tests::` 18,
    `subprocess::` 30, `gap_classify::` 5 and `formal_gap::` 4;
  - `verdict_db::`: 26 of 27, and `function_request::`: 8 of 10. The 3
    failures fail identically on main's own sources in the same overlay
    build (`ckdl/main-sources/`): their fixture checkers are refused
    because they are not the overlay's Clean.
- **trust-cg-codegen** `--no-fail-fast --test x86_source_bound_body --test
  must_refuse_corpus`: 11 and 5 passed.
- **The scripts:** `python3 scripts/check_documentation.py --check` and
  `python3 scripts/full_test_matrix_hosts.py --check` pass, and so does
  `scripts/check_fmt.sh`, run with the 6808 targo.
- **Re-run on the lane merged with main `e5b5dcd01`** (`d33c37a30`,
  TrustIR pin 2a43946e), one `build-slot` hold (`ckdl/jobE.log`): the
  lane's 19 controls and OD-197's 17 memo controls pass, one per process.
  The x86 body suite passes (397, 0 failed, 18 ignored), and so do the
  trust-cg-codegen targets (`must_refuse_corpus` 5, `x86_source_bound_body`
  11).
- **Not run:** `targo tippy`. The t011 overlay's targo has no `tippy`
  subcommand (`error: no such command: tippy`), and the older targos cannot
  read the current manifest (`backstop`).
