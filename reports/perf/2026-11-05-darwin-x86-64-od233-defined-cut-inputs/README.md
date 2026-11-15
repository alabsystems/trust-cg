# Darwin x86-64 body theorem in parts — OD-233 (cut inputs the source fixes for the run), 2026-11-05

OD-233 changes the parts route (OD-182) of the x86-64 source-bound
whole-body theorem (`crates/trust-cg-verify/src/x86_source_bound_body.rs`,
`x86_source_bound_body/split.rs`). A cut input that the source brings, on
every edge into its cut, as one term over the run's fixed inputs is DEFINED
as that term in the cut's region, instead of being a free input both sides
share. On every edge into the cut, in that edge's part, under its guard and
where the source runs, the theorem CLAIMS the input's source term equal to
the defined name. The design is `~/tcg-scratch/od233-design/README.md`
(§2 the rule, §3 what stays free, §5 the tests, §8 the plan); this lane
followed §8 steps 2 to 12. Step 13, the O0 and O2 censuses, ran on
`c76048fa3` (*Census*). The landing is left to the orchestrator.

| Ruling | Rule | Design |
| --- | --- | --- |
| OD-233 | a value item (not `I128`) or byte item of a cut, not tainted, whose source term on every edge into the cut, forward and back, resolves to one `T` over the run's fixed inputs (entry registers and incoming stack eightbytes, parameter bindings, symbol addresses, frame bytes' initial values, `bool` caller views; no slot address; at most 64 nodes; with the statement's definitions and the other defined inputs inlined, after OD-182's bit identities and OD-188's exact fold) is defined as `T`, and claimed on every edge, each claim stating the source term OD-182's relation states there; checks K1 (a defined term names only run-fixed inputs) and K2 (every stated edge `(region, from, cut)` into the cut claims each defined input) refuse by name; the claims are no observable | §2.1-§2.7 |

Host: the shared x86_64 Mac (8 logical CPUs, Darwin 22.6, i7-7920HQ), other
lanes building and replaying throughout; every build through
`scripts/trust_cargo.sh` with the local overlay `x86-stage1-ay13556-t011`
(`targo --unverified`, `-j2`, through `build-slot` at
`BUILD_SLOT_MEM_GB=6`; no proof claim about any build). Replayer pair: AY
0.27.0 build 13556 with Clean 5f09e36c (the overlay's `bin/ay` and
`bin/clean`). Branch `feat/x86-body-od233` (worktree
`~/tcg-scratch/wt-od233`) from `b30110fcd` (slice 25 with its census,
OD-227): `c5ef7cccc` OD-233 (code, tests, LIMITATIONS, the OD-182
amendment, CHANGELOG), `a8d1d38c6` the `x86_slot_forward` module doc (it
forwards across a single-predecessor edge too, not only within a block),
then this record with OD-233's entry (`e1163b5bc`). The review round
(*Review round*) added `5896ae541` (K2 per region, the claims' terms from
the relation, the new fixtures, mutants and tests), `3ef06d6dd` (the re-cut
timing lane's fixture lookup), `454963b4c` (that lane listed among the
matrix's ignored tests) and this record's update. The census record
(*Census*) is the commit after `c76048fa3`. The fails-before records
ran in two helper worktrees, each in its own target directory:
`~/tcg-scratch/wt-od233-base` at `b30110fcd` and
`~/tcg-scratch/wt-od233-pre` at `12ebba653` (`origin/main` before slice
25). Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md) binds each by
size and SHA-256.

## Census

Run on 2026-11-07 by `scripts/census.sh` (`census.log`, ending
`CENSUS-OD233-DONE 13:02` and `DRIVER-EXIT=0`). One release bridge was
built from `c76048fa3` with `CARGO_TARGET_DIR` unset
(`build_bridge.t011.sh`, 09:22-10:40, `Finished release … in 77m 35s`).
Its build inputs are `3ef06d6dd`'s, since the later commits change no Cargo
input. `o2-od233.dylib` and `o0-od233.dylib` are that one build, SHA-256
`1bf4e628…`. From it ran the O2 and O0 `core` proof censuses
(`census_t011_dylib.sh`: the overlay's `trustc`, `-Ccodegen-units=1
-Cpanic=abort -Ztrust-verify=off`, `-Copt-level=2` or `0`, the knobs
`diag-json`, `x86-body-trace`, `x86-body-dump` and `solve-trace`; AY
0.27.0 build 13556 with Clean 5f09e36c).

The named baselines are slice 25's censuses `census-o2-s25` and
`census-o0-s25` (2026-11-04; `o2-s25.dylib` and `o0-s25.dylib`, one build
at `d92b944fe`, SHA-256 `2e47fae1…`, bound in [slice 25's
PAYLOADS.md](../2026-11-04-darwin-x86-64-slice25-sib-rows/PAYLOADS.md) and
in this record's). They ran without `solve-trace`, a diagnostic knob
that prints one line per solve, proof check and promoted result and changes
no decision, so they carry no per-part time. Right after each OD-233
census, a copy of the baseline dylib (`o2-s25-st.dylib`, `o0-s25-st.dylib`,
the same SHA-256) ran again with the same knobs, back to back on the same
host under comparable load (`census-o2-s25-st`, `census-o0-s25-st`: the
paired control; the 1-minute load at each run's start and end is in
`census.log`, below). Each re-run's `failed_roots.jsonl` and
`refusals.jsonl` are byte-identical to its baseline's, so the knob changes
no record.

The comparisons are slice 15's `census_compare.py`, `root_classes.py`,
`scripts/parts_census.py`, `scripts/census233.py` (the stop rule's items,
wtf8's trace, the `cut_pairing` texts), an object comparison, slice 25's
`trace_diff.py` at O0, and `scripts/part_times.py`, which pairs each
OD-233 census with its re-run part by part. No census had an
execution-budget refusal (`budget refusals: 0`). Every census's
`trust-cg rev` field reads `de1f19099` and is stale (design §1); the
dylib's SHA-256 names the build.

| | `census-o2-s25` | O2 OD-233 | O2 re-run | `census-o0-s25` | O0 OD-233 | O0 re-run |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| failed roots (distinct reasons) | 254 (2) | **253** (2) | 254 (2) | 20 (1) | 20 (1) | 20 (1) |
| typed refusals | 255 | 254 | 255 | 22 | 22 | 22 |
| promoted / newly failing, against the baseline | | 1 / 0 | 0 / 0 | | 0 / 0 | 0 / 0 |
| named mismatches | 0 | 0 | 0 | 0 | 0 | 0 |
| refuted bodies (lines) | 2 (one function) | 0 | 2 (the same) | 0 | 0 | 0 |
| emitted objects | 1034 | 1035 | 1034 | 3426 | 3426 | 3426 |
| wall | 909 s | 976 s | 1010 s | 2465 s | 3329 s | 3215 s |

The wall times are not a compile-time measurement. Other lanes ran
throughout, and the 1-minute load at each census's start and end was
between 6.1 and 14.0 (`census.log`: O2 OD-233 7.92 → 13.98, its re-run
13.98 → 6.12; O0 OD-233 6.19 → 6.51, its re-run 6.51 → 8.26), on a host
with 8 logical CPUs and 4 cores (`od233-run/fact-checks/host.txt`,
`sysctl`).

**O2: 254 → 253.** One root is promoted, `core::wtf8::slice_error_fail`.
None is newly failing, and there is no named mismatch and no refuted body.
On `census-o2-s25` its two codegen attempts were the two refuted lines;
both now print `defined cut inputs bytes=16 items=0`, `stated in
parts=3`, then `bound rows=555 replay=Valid` and `bound rows=571
replay=Valid`. The certificates of its parts (`od233-run/census/wtf8/`,
copied from the shared certified-part store;
`od233-run/fact-checks/fact_checks.txt` G) show what changed:

- Part 1 (399 B) and part 3 (1872 B) are the queries `census-o2-s25`
  dumped for those parts: each certificate's `smt2-sha256` is the SHA-256
  of `dump-o2-s25`'s `part1.smt2` and `part3.smt2`. Part 1 was answered
  from a store entry an earlier run wrote (its certificate's mtime is
  2026-11-07 06:57, before this census began at 10:40; the census prints
  no solve for it). The store's key is derived from the solver's identity
  and the query's bytes, and a hit re-checks the query's SHA-256 against
  the certificate's (`obligation_cert_store.rs`), so the hit is that same
  query. Part 3 was solved and certified during this census (AY 0.29 s,
  Clean 0.11 s): it is certified for the first time, not after a change,
  because every earlier replay of wtf8 stopped at part 2's counterexample
  (`census-o2-s25-st` prints no line for part 3).
- Part 2 is 856 B where `census-o2-s25`'s was 1273 B (`CounterExample`
  there, `Verified` now: AY 0.06 s, Clean 0.06 s; solved and certified
  during this census). Slot 37's eight bytes at cut `Block(2)`
  (`x2b37o0` … `x2b37o7`) are no longer declared, and
  the source's compare reads `e_rsi`, the `len` the machine compares
  (`(bvult e_rsi e_rcx)`).

The root class `bound, not certified (AY)` goes 5 → 4 (the refuted body
was one of the five), and every other root class is unchanged
(`root_classes.py`). 1034 of the 1035 common entries of `obj/` are
byte-identical; the other is the `trust-witness` directory (*O0*, below).
The one new object is
`core._RNvNtCs7e1ihmkzmZ8_4core4wtf816slice_error_fail.rcgu.o`.

**Deviation: `bytes=16`, not the design's `bytes=8`.** The replayed parts
show the effect of 8 of the 16 defined bytes: part 2 loses slot 37's eight
bytes at `Block(2)`, and parts 1 and 3 are byte-identical to
`census-o2-s25`'s. The other 8 defined bytes change no replayed part's
text. Which cut and which bytes they are is not measured: the census
prints only the counts, and nothing of wtf8 was dumped because it replays
Valid. (The fixture P1L, the same reduction stated by the production
planner, also prints `bytes=16` (*The solver-free gate*), which is
consistent with this, and does not locate the bytes either.)

All 35 in-parts functions are Valid on their last attempt
(`census-o2-s25`: 34 and the refuted one). The parts histogram is
unchanged: {1: 8, 2: 8, 3: 7, 4: 4, 5: 1, 6: 2, 7: 2, 10: 1, 29: 2}.
No attempt's part count or row count changed. 12 of the 35 define inputs
on their last attempt (610 bytes, 55 items; `(bytes, items)` → functions:
(1, 0) 1, (7, 0) 2, (16, 0) 1, (24, 1) 1, (32, 11) 2, (48, 5) 2,
(55, 0) 1, (112, 21) 1, (228, 1) 1). A 13th defines inputs on one attempt
only: `<Ipv4Addr as Display>::fmt` defines 32 bytes on its first codegen
attempt (`bound rows=638`) and none on its second (654), both stated in 2
parts and Valid. `census233.py`'s stop rule holds at O2. It finds no named
mismatch, no refuted body, and no K1, K2 or `(OD-233)` text in
`stderr.log` or the records. There is no new NoObservable (54 → 54), no
function with more timeouts (attributed `outcome=Timeout` 2 → 2,
negative-memo timeout hits 1 → 1), and no bound attempt that lost Valid;
two gained it (wtf8's).

**O0: 20 → 20.** `failed_roots.jsonl` and `refusals.jsonl` are
byte-identical to `census-o0-s25`'s, and so are 3426 of the 3427 entries
of `obj/`: every emitted object (the two `obj/` directories' file
manifests are equal, [PAYLOADS.md](PAYLOADS.md)). The other entry is the
`trust-witness` directory, which the comparison reports as differing
because it is a directory. Its one `.twit` file differs between any two of
these runs, `census-o0-s25` and `census-o0-s25-st` (one dylib) included,
so it records the run, not the code. There is no named mismatch, no
refuted body and no K1, K2 or `(OD-233)` text, and NoObservable stays
81 → 81. The root classes are the same (20 no observable).

The traces are not byte-identical (7160 → 7278 keyed trace lines, those
naming a function with `fn=`, over the same 3457 functions). 59 functions
print `defined cut inputs` once per attempt (2 × 59 = 118 lines), and no
other keyed line changes except in
`core::num::flt2dec::digits_to_exp_str`, whose `stated in parts=` goes
11 → 10 (it defines 24 bytes and 11 items; `bound rows=2108 replay=Valid`
on both sides). The unkeyed replay lines also change in count (73 → 83:
the `Timeout`, `Unknown` and memo-hit lines of *The O0 stop*).
`trace_diff.py` counts those 59 functions and five unkeyed-line counts as
its 64 anomalies, and exits 1. So the design's "O0
byte-identical" holds for the records and the objects,
not for the trace. The attributed timeouts moved (*The O0 stop*).

At O0, 150 functions are stated in parts, all Valid on both sides. Their
histogram is {1: 15, 2: 17, 3: 28, 4: 26, 5: 6, 6: 8, 7: 14, 8: 11, 9: 11,
10: 3, 11: 1, 12: 4, 13: 2, 15: 3, 24: 1}; `census-o0-s25` has 10: 2 and
11: 2, the difference being `digits_to_exp_str`. 59 of the 150 define
inputs (778 bytes, 173 items; `(bytes, items)` → functions: (0, 1) 8,
(0, 2) 15, (0, 3) 5, (0, 4) 2, (0, 5) 1, (0, 7) 1, (0, 20) 1, (0, 23) 1,
(0, 33) 1, (3, 0) 1, (7, 0) 2, (8, 0) 3, (8, 2) 1, (9, 0) 1, (16, 0) 4,
(24, 0) 2, (24, 11) 1, (32, 0) 4, (40, 0) 1, (56, 9) 1, (88, 0) 1,
(112, 0) 1, (160, 2) 1). wtf8 at O0 defines nothing and is stated in 3
parts, `bound rows=585 replay=Valid` on both sides.

### The O0 stop

`census233.py`'s stop rule, run against the named baseline
`census-o0-s25`, fired on one item: 6 functions have more attributed
timeouts (`replay outcome=Timeout` 22 → 31, negative-memo timeout hits
15 → 18). Nothing else in the stop rule fired. The six add 11 `Timeout`
lines and 6 memo hits; the totals rise less because three functions have
fewer (`fact-checks/fact_checks.txt` A, which lists every function whose
counts differ in either direction): `grisu::format_shortest_opt` timed out
on `census-o0-s25` (2, 1) and `census-o0-s24c` (1, 0) but on neither the
OD-233 census nor the re-run (0, 0), and `align_offset::mod_inv` and the
`i64` `from_ascii_radix` have one memo hit fewer each. Timeouts vary
between runs in both directions. The six, with their
`(outcome=Timeout, memo timeout)` counts over both codegen attempts
(`followup/`, `stop-diagnosis/`):

| function (O0, `cgu.0.N`) | defines inputs | timed-out query (re-run and OD-233) | `census-o0-s25` | re-run | OD-233 |
| --- | --- | --- | --- | --- | --- |
| `core::fmt::num::<impl u128>::_fmt_inner` (1243) | no | parts 4 and 7 of 10 (3201 B, 2884 B) | (2, 1) | (4, 2) | (4, 2) |
| `core::fmt::num::imp::<impl u64>::_fmt_inner` (1958) | 1 item, 8 parts | part 2 of 8 (3139 B) | (0, 0) | (2, 1) | (2, 1) |
| `core::fmt::num::imp::<impl usize>::_fmt_inner` (1975) | no | part 2 of 8 (3139 B, a memo hit on 1958's query) | (0, 0) | (2, 2) | (2, 2) |
| `core::intrinsics::fallback::wide_mul_u128` (2044) | no | part 2 of 2 (8159 B) | (0, 0) | (2, 0) | (2, 1) |
| `core::fmt::num::imp::exp_u64` (2117) | 32 bytes, 15 parts | part 8 of 15 (6269 B) | (0, 0) | (2, 0) | (2, 1) |
| `wide_mul_u128::scalar_mul` (2271) | whole body, not in parts | the whole query (6249 B) | (0, 0) | (0, 0) | (1, 0) |

The column of timed-out queries is read from the solve-trace lines of the
re-run and the OD-233 census, where 1243 times out in both parts 4 and 7
on each attempt. `census-o0-s25` ran without `solve-trace`: there 1243
timed out in one part per attempt (one `Timeout` on attempt 0, one memo
hit and one `Timeout` on attempt 1; `six-parts.txt`), and which part is
not recorded.

On each timed-out part the resident server's solve returns (`server_solve`
0.34-1.59 s; 20.3-24.3 s for `wide_mul_u128`'s part) and the part's
result is `Timeout`. The negative memo later records that replay's solve
time as 30.4-31.6 s (51.3 s for `wide_mul_u128`). The knob prints no line
for the step between (`six-parts.txt`). The two timed-out queries in
functions that define inputs (1958's part 2 and 2117's part 8) have the
same smt2 byte length on both sides (3139 B and 6269 B), so OD-233 did not
grow them; their content was not compared.

**Ruling** (the orchestrator, 2026-11-07, recorded in OD-233): this is
host solver capacity, not an effect of OD-233, and it does not block
landing. Its grounds, each checked against the payloads:

1. **The paired control reproduces 5 of the 6.** `census233.py` of
   `census-o0-s25` against the re-run (`stop-diagnosis/base-vs-rerun/`)
   reports 5 functions with more timeouts (1243, 1958, 1975, 2044, 2117;
   `outcome=Timeout` 22 → 30, memo 15 → 16), on the same parts with the
   same smt2 byte lengths as the OD-233 census (`six-parts.txt`). The
   sixth, `scalar_mul`, is the race in (2). Slice 24c's O0 census
   (`census-o0-s24c`, another dylib, 2026-11-07, without `solve-trace`)
   shows the same five timing out.
2. **Against the control, no part of an in-parts statement newly times
   out; one whole-body query's result changed, non-Valid on both sides.**
   `part_times.py` pairs 7987 (function, attempt, part) keys of the re-run
   and the OD-233 census (`o0/times/parts.tsv`). 7986 have the same
   promotion results, among them all 28 paired parts of in-parts
   statements that carry a `Timeout` result on either side
   (`fact-checks/fact_checks.txt` I). The one that differs is
   `scalar_mul`'s first attempt, a whole-body query (6249 B on both sides)
   that OD-233 does not state in parts and that defines nothing. It newly
   reads `Timeout` where the re-run read `Unknown(self-check-rejected)`,
   after the same 30 s server deadline on both sides (`server_timeout
   30.006s`), followed by a live solve of 30.0 s on OD-233's side and
   24.6 s on the re-run's. That is the one more `outcome=Timeout` line
   (30 → 31). OD-233's second attempt returned
   `Unknown(self-check-rejected)` (30.0 s and 26.2 s), where the re-run's
   was a memo hit with the same result. Both outcomes are non-Valid on a
   query of the same length: a race against the 30 s deadline.
   `part_times.py` also lists two "parts newly over 30 s"
   (`o0/times/times.txt`), `scalar_mul`'s second attempt and the `i64`
   `from_ascii_radix`'s part 8; each has the same results on both sides,
   and on the re-run's side a memo hit answered it without a solve
   (*Time*).

   `census233.py` of the re-run against OD-233
   (`stop-diagnosis/rerun-vs-od233/`, `outcome=Timeout` 30 → 31, memo
   16 → 18) still ends `STOP RULE: BROKEN: 4 functions with more
   timeouts`. One is `scalar_mul`, the race above. In the other three
   (`from_ascii_radix` for `usize`, `wide_mul_u128`, `exp_u64`) the
   `Timeout` count is the same and the memo-hit count rose by one: on
   OD-233's side a process negative-memo hit answered a part that the
   re-run solved again, with the same `Timeout` result (`usize`
   `from_ascii_radix` attempt 0 part 8, `wide_mul_u128` attempt 1 part 2,
   `exp_u64` attempt 1 part 8; `fact_checks.txt` B, `six-parts.txt`).
   `align_offset::mod_inv` has one memo hit fewer on OD-233's side
   (`fact_checks.txt` A); `census233.py` reports only increases. So the
   per-function count does not clear the stop against the control; the
   per-part comparison above does.
3. **Nothing else moved.** `failed_roots.jsonl` and `refusals.jsonl` are
   byte-identical (20 → 20), 3426 of 3427 `obj/` entries are
   byte-identical (the other is `trust-witness`), and there is no named
   mismatch, no refuted body, no K1, K2 or `(OD-233)` text, and
   NoObservable stays 81 → 81.
4. **No coverage was lost.** All six end `bound rows=N replay=Valid` with
   unchanged row counts (1771, 1694, 1690, 480, 2762 and 321 on
   `census-o0-s25`, the re-run and OD-233). Five (1243, 1958, 1975, 2044,
   2117) reach it through OD-197's claim fallback, which verifies every
   claim of a timed-out part (`… | part 4 of 10 | claim 1 of 10` …
   `claim 10 of 10`, `result=Verified`). `scalar_mul`, stated as one
   whole-body query, reaches it through OD-206's generalized replay
   (`… | generalized`, `result=Verified`, after the whole query's
   `Timeout` or `Unknown`). Both routes are read from the re-run's and the
   OD-233 census's solve-trace lines, the same on both
   (`fact_checks.txt` C); `census-o0-s25` prints none.

A timeout is fail-closed and never earns credit, so the ruling relabels no
evidence. It is reversible: re-running both censuses on a quiet host would
settle it. Method decision: a timeout-count stop compares against a paired
control (the baseline dylib re-run back to back with the new census on the
same host), not against an earlier census alone. In this ruling the
comparison that clears the stop is per part: each (function, attempt,
part)'s promotion results against the control's (`part_times.py`, ground
2). `census233.py`'s per-function count, which also counts negative-memo
hits, still reports four functions against the control and was read by
hand (ground 2). Query identity here rests on smt2 byte lengths and on
the reproducing baseline-dylib run, not on content hashes. The negative-memo keys include
`VERIFIER_BUILD` (`source_bound_negative_memo.rs`), so they differ across
dylibs, and the census dumps (`dump-o0-od233`, `dump-o0-s25-st`) are empty
because every body ended Valid.

### Time

`part_times.py`, each OD-233 census against its re-run. AY time is the
resident server's solves and timeouts plus the live solves on the body
theorem's obligations (whole-body queries and parts); Clean time is the
proof checks of the same obligations. "Parts" include whole-body queries.
The censuses' other AY solves (the memcopy and precondition-probe
obligations, 145 lines in each) are not in the table: 101.3 s, 96.7 s,
102.7 s and 97.3 s in the four columns' order (`fact-checks/fact_checks.txt`
E).

| | O2 OD-233 | O2 re-run | O0 OD-233 | O0 re-run |
| --- | ---: | ---: | ---: | ---: |
| AY s (of it in in-parts statements) | 69.4 (4.7) | 131.2 (0.0) | 462.4 (299.4) | 384.4 (300.5) |
| Clean s (of it in in-parts statements) | 4.6 (4.5) | 0.1 (0.0) | 27.3 (27.3) | 0.0 |
| parts checked by Clean | 21 | 1 | 64 | 0 |
| parts over 30 s (AY or Clean) | 1 | 2 | 5 | 4 |

- **O2.** Every part over 30 s is the whole-body query of `wide_mul_u128`
  (64.6 s; 66.2 s and 64.9 s on the re-run). No part of an in-parts
  statement takes more than 0.95 s of AY on the OD-233 side
  (`digits_to_dec_str` part 9 of 10). The re-run solved only wtf8's
  refuted part 2 (0.015 s and 0.006 s), never reached wtf8's part 3 (the
  replay stops at part 2's counterexample), and answered every other such
  part without a solve (no AY line). Of the 21 parts checked by Clean on
  the OD-233 side, 20 are parts of in-parts statements, all accepted. The
  21st is `as_chunks`'s whole-body theorem (`cgu.0.12`, attempt 0): Clean
  refused the check of the whole query and of its first claim, on both
  sides (it is the re-run's one part checked by Clean; its results are
  `Unknown` on both sides, no credit; `fact_checks.txt` F). It carries the
  0.1 s of Clean outside in-parts statements.
- **O0.** The OD-233 census's five are `from_ascii_radix` for `isize`
  parts 8 and 9 of 9 and for `i64` part 8 (60.0 s each, `Timeout`), and
  `scalar_mul`'s two attempts. The re-run's four are the same `isize`
  parts, the `i64` part 9, and `scalar_mul`'s first attempt. The `i64`
  function's parts 8 (3693 B) and 9 (3691 B) time out on both sides; which
  of the two is solved and which the process memo answers differs between
  the runs. That and `scalar_mul`'s second attempt (solved on OD-233's
  side, a memo hit on the re-run's) are the two parts `part_times.py`
  lists as newly over 30 s, each with the same results on both sides. In
  paired parts of the 59 defining functions AY goes 228.3 s →
  251.1 s and Clean 0.0 s → 26.1 s; in the others AY goes 156.2 s →
  208.7 s, all of it in queries whose result is `Timeout` or `Unknown`
  on one side or both, and no non-defining part solved on both sides (26)
  has a different smt2 byte length.
- **The design's "no part crosses 30 s" (§7) is false on both sides,**
  before and after OD-233: `from_ascii_radix`'s parts take 60 s and time
  out with the same smt2 byte length in the re-run and in the OD-233
  census.

### Statement growth on the census

Measured:

- **Re-cuts.** One function is cut into a different number of parts at
  O0 (`digits_to_exp_str`, 11 → 10). None is at O2.
- **Parts certified during the census.** The certified-part store's key
  is derived from the solver's identity and the query's bytes, so a
  statement OD-233 changes is solved and certified again on its first run
  (design §7). The shared store's entry count rose by 20 during the O2
  census and by 64 during the O0 census, and by none during either re-run (`census.log`). At O0, 64
  parts of 30 of the 59 defining functions were solved by AY and checked
  by Clean, all `Verified`. The re-run solved none of them: 59 it answered
  without a solve (no AY or Clean line), and 5, `digits_to_exp_str`'s, it
  does not have (its cut differs). They took 42.4 s of AY (at most 3.39 s
  a part) and 27.3 s of Clean (at most 4.64 s). The largest query is
  16809 B (`Big8x3::mul_pow2`'s part 7 of 7). At O2, 20 parts of 4
  functions (`digits_to_dec_str` 9, the f64 `to_shortest_exp_str` 5 and
  `to_shortest_str` 4, wtf8 2) were checked by Clean, all `Verified`, at
  most 0.95 s of AY, 1.32 s of Clean and 3028 B. One of the 20, wtf8's
  part 3 (1872 B), is not a changed query: it is the query
  `census-o2-s25` dumped, byte for byte (*Census*, above), certified for
  the first time because every earlier replay stopped at the refuted
  part 2.
- **Statements that define nothing.** No part of a function that defines
  nothing has a different smt2 byte length where both sides solved it (O0
  26 parts, O2 8); their content was not compared.
- **Distinct claims, where the census prints them.** A part is replayed
  claim by claim (OD-197) only after its whole query fails, and only then
  does the census print its distinct claims (`| claim i of m`;
  `fact-checks/fact_checks.txt` D). At O0 these are the five functions'
  timed-out parts of *The O0 stop*, m = 8 to 12, two of them in defining
  functions (1958's part 2, 10 claims; `exp_u64`'s part 8, 12); at O2 two
  whole-body queries (`as_chunks` 3, `wide_mul_u128` 4). Every one is
  under the claim split's 64, with the same m on the re-run.

Not measured: the size before OD-233 of a part certified during the
census (only a solve prints a query's size, and the re-run solved none of
them; the exceptions are wtf8's part 2, 1273 B → 856 B, and part 3,
1872 B → 1872 B, both from `dump-o2-s25`), the statements' depth, and the
distinct claims of every part that verified whole (the census prints
neither). No census aborted (`harness errors: 0` on each).

**OD-233b's trigger.** `cut_pairing`'s `no machine row writes a register
as the definition of …` texts in the trace: O2 2 lines in 1 function
(`digits_to_exp_str`, both codegen attempts), as on `census-o2-s25`; O0 0
on both sides.

## Soundness notes first

- **Only a choice is untrusted.** `split::cut_definitions` reads only the
  theorem's own source terms on the stated edges and the statement's own
  definitions; it never reads the machine. Seed: cut points in region order,
  an input whose term resolves to one `T` on every forward edge. Shrink:
  until nothing changes, an input whose term on some edge into its cut (a
  back edge included) does not resolve to its `T` under the current choice
  is dropped. A wrong choice is refuted by its edge's claim (mutants
  `od233-forge-byte` and `od233-forge-item`, which forge the choice itself)
  or refused by K1 or K2.
- **The claims state the relation's own source terms.** Each claim on an
  edge is `t = x`, where `t` is the source term OD-182's relation states for
  the input on that edge (`split_relation`: an item's value; a byte's
  source byte, whose concatenation over its run is the run's term), not the
  choice's copy (`edge_sources`), which only chooses. (Review round: the
  claims used `edge_sources`, a second computation of the same term.)
- **K1** (`build_theorem`): a defined term naming anything but a run-fixed
  input, or a slot address, refuses with `cut point …'s input … is defined
  by a term that is not fixed for the run (OD-233)` (mutant
  `od233-any-name`).
- **K2** (`build_theorem`): every stated edge `(region, from, cut)` must
  claim each of the cut's defined inputs, else `cut point …'s defined input
  … is not claimed on the edge from … in region … (OD-233)` (mutants
  `od233-no-claim`, and `od233-drop-repeat-claim`, which drops the claims
  on the second region's copy of an edge only). A block two regions hold
  (reached from two cut points without crossing a cut, P8's join) states
  its edge into a later cut once in each region, each with its own source
  term, and K2 checks each (review round: it was keyed by block and cut
  alone; `od233-k2-by-pair` restores that keying, under which the dropped
  claim passes). Without K2 and without the claims, a forged byte or item
  holds (`od233-no-claim-no-k2`): the claim is what carries the
  soundness.
- **The definitions precede every source definition** (after the caller
  views), so the definitional check orders them (mutant `od233-late`: `s1
  uses x2b0o0 before its definition`), and a defined name is never a free
  input (mutant `od233-free`: `premise constrains the free input x1b0o0`).
- **The claims are no observable.** A statement whose only claims are
  OD-233's still refuses `NoObservable` (N1; mutant `od233-observable`
  states it).
- **A statement that defines nothing is byte-identical to before.** Every
  free-input control (V1-V9, V2b) keeps its digest at `b30110fcd` and
  `12ebba653` (*Fails-before*); slice 16's five in-parts goldens (its size
  shapes, by the production planner) keep theirs; every single-query
  golden is unchanged (gate 1's `*_smt2_is_canonical_per_shape` tests, the
  golden files and their digests as at `b30110fcd`); and every swept
  statement that defines nothing has the digest slice 25's base gives it
  (*The cross-tree digests*).
- **Trusted in addition:** OD-182's meta-argument with defined cut inputs
  (each supplied at a crossing by that crossing's own claims), the
  run-fixed check K1, the per-edge claim check K2, and that each claim's
  term is the relation's on that edge (a run's whole store read as its
  bytes' concatenation, slice 7's reading). No assumption is added. Not
  trusted: the choice, including its taint exclusion, which no swept
  statement reaches (`od233-taint` changes none of the 1102).
- `run_fixed_term` (renamed from `closed_machine_term`) now resolves names
  deepest first on an explicit stack; its result is unchanged (a source
  definition chain may be thousands of definitions deep).

## Fixtures

`crates/trust-cg-verify/src/x86_source_bound_body_od233_tests.rs`. Each
fixture's LIR comes from the trust-ir adapter and its machine stream from
the real instruction selector and then the real x86 pass pipeline at O2
(`X86Pipeline::run_x86_optimization_passes`, with `x86_slot_forward`), or at
O1 for the three loop fixtures (*Deviations*). The only hand edits are the
labelled wrong lowerings. `every_fixture_has_its_shape` asserts each
fixture's shape (the forwarded compare, the single store, the reload at a
join, no SIB row) so a pass change that removes it fails by name.

| | fixture | what it is |
| --- | --- | --- |
| P1 | `Wtf8LenLocal` | the `core::wtf8::slice_error_fail` reduction: `len` copied through a slot, stored once into the address-taken local L in Block 0; Block 2 (one predecessor) compares `end > L` against the forwarded register |
| P1b | `Wtf8LenDirect` | P1 storing `len` directly (a leaf: L's bytes are closed already, nothing is defined) |
| P2 | `ComputedLenLocal` | P1 storing `len + 1` |
| P3 | `SymbolLocal` | a symbol's address stored into L, reloaded past a branch and passed to a call |
| P4 | `CommonCutParam` | `m = x * 3` passed by both arms to Block 3's parameter |
| P5 | `InvariantLocalAcrossHeader` | L stored `x + 1`, reloaded every iteration of a loop that never writes it (O1) |
| P6 | slice 25's `SlotConstU64`, `SlotConstAcrossBlocks`, `SlotStoreReloadU32` | the `imul` of two constants that `every_point` cuts out as a free item |
| P7 | `NarrowReadBack` | L stored the u64 `x + 1`, the low u32 reloaded past a branch |
| P8 | `SharedJoinLocal` (review round) | L stored `x + 1`; each arm of a branch on `y` calls out and jumps to the join J, which branches to C (`&L` to a call) or returns; cut at the first arm and at C, so J is in Block 0's region and the arm's, and its edge into C is stated in both |
| Q1 | `MergedLenLocal` (review round) | P1 with a jump-only block before Block 2, which O2 merges: stated over the merged-chain quotient (slice 24a) |
| P1L | `LongLenLocal` (review round) | P1 with 300 calls before its return: past the single-query machine bounds, stated in parts by the production planner over the quotient (the trace test's subject) |
| V1-V8, V2b | `PathsDiffer`, `CallAfterStore`, `MayAliasStore`, `LoopCarried`, `EarlierFreeItem`, `TaintedStore`, `OverSixtyFour`, `WideItem`, `CallInLoop` | inputs that must stay free (different terms per edge, a call or a may-alias store after the store, a loop-carried value, a value over an earlier cut's free item, a tainted store, more than 64 nodes, an `I128`, a call result) |
| V9 | `SharedJoinDiffers` (review round) | P8 whose first arm re-stores L with `y` and whose C reloads L: J's two stated edges into C bring different terms, and L's bytes stay free at C |
| N1 | `SymbolNoObservable` | every claim an identity though L's bytes are definable: still `NoObservable` |
| W1-W4 | `ComparesLenPlusOne`, `StoresBegin`, `ForwardsAcrossJoin`, `IncrementsInLoop` | hand-edited wrong lowerings of P1, P1, `TwoPredecessors` and P5 |
| W5 | `SlotConstU64` with its `imul` by 16 | a wrong lowering of P6 |
| W6 | `StoresInArm` (review round) | P8 with the first arm's machine block storing `y` into L before its jump (wrong on the arm's path only, through the join two regions hold) |

## Fails-before

`od233_fails_before` (generated by `fails-before/make_fails_before.py` from
the fixture section, which uses only the pre-OD-233 API) ran in each helper
worktree (`scripts/fails_before.sh base|pre`), twice: first on the
fixture section before formatting (`a06-fb-base.log`, `a07-fb-pre.log`),
then on the committed one at `a8d1d38c6` (`a11a-fb-base.log`,
`a11b-fb-pre.log`, the copies they ran in `od233-run/fails-before/`). The
two copies differ only by trustfmt's changes (whitespace, trailing commas
and one closure body put in braces), and each rerun printed the same
`OD233_FAILS_BEFORE` lines, digests included, as the first run. The review
round ran it a third time, on the fixture section of the lane COMMIT
`5896ae541` (`git show`), the script refusing a helper at any other commit
or with any other change (`b05-fb-base.log`, `b06-fb-pre.log`; the copies
in `od233-run/fails-before/` are now these; the fixture file is the same
at `454963b4c`): every earlier line is reprinted byte for byte, and P8,
Q1, V9 and W6 are added. All verdicts
below are slice 9's samplers (on samples, no solver):

| fixture | `b30110fcd` (base) | `12ebba653` (pre) | head |
| --- | --- | --- | --- |
| P1 | part 2 of 3 refuted | part 2 of 3 refuted | 3 parts hold, 40 bytes defined |
| P1b | holds, digest `c2ac082b…` | holds, `c2ac082b…` | holds, nothing defined, `c2ac082b…` |
| P2 | part 2 of 3 refuted | part 2 of 3 refuted | holds, 40 bytes |
| P3 | part 2 of 2 refuted | part 2 of 2 refuted | holds, 16 bytes |
| P4 | holds | holds | holds, 1 item |
| P5 | holds | holds | holds, 8 bytes |
| P7 | holds | holds | holds, 12 bytes |
| P8 | holds, `50ab2c86…` | holds, `50ab2c86…` | holds, 16 bytes (8 at the arm, 8 at C, each of C's claimed on both of J's stated edges) |
| Q1 | part 2 of 3 refuted | part 2 of 3 refuted | holds over the quotient, 40 bytes |
| P6 `SlotConstU64` | parts 1-3 of 3 refuted | (no slice 25) | 6 parts hold, 88 bytes, 3 items |
| P6 `SlotConstAcrossBlocks` | parts 2-3 of 3 refuted | | 1 part holds, 40 bytes, 3 items |
| P6 `SlotStoreReloadU32` | parts 1-2 of 2 refuted | | 10 parts hold, 64 bytes, 6 items |
| V1-V9, V2b | hold, digests as the head's | hold, same digests | hold, nothing defined, same digests |
| W3-source (`TwoPredecessors`) | holds, `6fd33dd3…` | holds, `6fd33dd3…` | holds, 16 bytes and 1 item defined, `1bd1b02e…` (not a control: W3's source) |
| N1 | `NoObservable` | `NoObservable` | `NoObservable` |
| W1-W6 | refuted | refuted (W1-W4, W6) | refuted |

So P1, P2, P3, Q1 and the three P6 fixtures are the new acceptances, each
refuted on samples on both earlier trees. P4, P5, P7 and P8 hold on both
earlier trees as well: the real O2/O1 output of those shapes does not hit
the gap, so they are coverage of the rule (each defines inputs and holds),
not fails-before cases (*Deviations*).

Slice 25's fails-before record on `6c036f1de`
(`~/tcg-scratch/s25-run/logs/fails-before5.log`, SHA-256 `19bf2b1b…`)
found eleven decompositions refuted in parts (lines 1790-1809):

```text
1790: S25_FAILS_BEFORE decomposed=U64Index whole_holds=true whole=stated split=… | part 1 of 1 is refuted on samples
1792: S25_FAILS_BEFORE decomposed=U32Index whole_holds=true whole=stated split=… | part 1 of 1 is refuted on samples
1797: S25_FAILS_BEFORE decomposed=FieldDispU32 whole_holds=true whole=stated split=… | part 1 of 1 is refuted on samples
1799: S25_FAILS_BEFORE decomposed=StoreU32 whole_holds=true whole=stated split=… | part 1 of 1 is refuted on samples
1800: S25_FAILS_BEFORE decomposed=StoreU64 whole_holds=true whole=stated split=… | part 1 of 1 is refuted on samples
1802: S25_FAILS_BEFORE decomposed=F64Index whole_holds=true whole=stated split=… | part 1 of 1 is refuted on samples
1803: S25_FAILS_BEFORE decomposed=F32Index whole_holds=true whole=stated split=… | part 1 of 1 is refuted on samples
1804: S25_FAILS_BEFORE decomposed=ByteMerge whole_holds=true whole=stated split=… | part 1 of 1 is refuted on samples
1806: S25_FAILS_BEFORE decomposed=SlotConstU64 whole_holds=true whole=stated split=… | part 1 of 3 is refuted on samples
1807: S25_FAILS_BEFORE decomposed=SlotConstAcrossBlocks whole_holds=true whole=stated split=… | part 2 of 3 is refuted on samples
1809: S25_FAILS_BEFORE decomposed=SlotStoreReloadU32 whole_holds=true whole=stated split=… | part 1 of 2 is refuted on samples
```

(`…` is `Source-bound x86-64 whole-body theorem (System V, pre-RA ISel): the
replayed body theorem credits every covered value row`.)

### The eleven decompositions on the head

`print_od233_with_and_without_the_rule` states each one
(`slice25::decompose(&machine, false)`, cut at `every_point`) with the rule
and without it (`od233-off`). Every verdict here is on samples (slice 9's
samplers, no solver); no decomposition's part was replayed on AY:

| decomposition | `6c036f1de` | head, `od233-off` | head, with the rule | defined (bytes, items) | class |
| --- | --- | --- | --- | --- | --- |
| U64Index | part 1 of 1 refuted | 1 part, refuted | 2 parts hold | (0, 1): `x1v0 := (bvmul p1 8)` | the rule applies |
| U32Index | part 1 of 1 refuted | 1 part, refuted | 3 parts hold | (0, 1): `x1v0 := (bvmul p1 4)` | the rule applies |
| FieldDispU32 | part 1 of 1 refuted | 1 part, refuted | 4 parts hold | (0, 1): `x2v0 := (bvadd p0 16)` | the rule applies |
| StoreU32 | part 1 of 1 refuted | 1 part, refuted | 2 parts hold | (0, 1): `x1v0 := (bvmul p1 4)` | the rule applies |
| StoreU64 | part 1 of 1 refuted | 1 part, refuted | 2 parts hold | (0, 1): `x1v0 := (bvmul p1 8)` | the rule applies |
| F64Index | part 1 of 1 refuted | 1 part, refuted | 2 parts hold | (0, 1): `x1v0 := (bvmul p1 8)` | the rule applies |
| F32Index | part 1 of 1 refuted | 1 part, refuted | 3 parts hold | (0, 1): `x1v0 := (bvmul p1 4)` | the rule applies |
| SlotConstU64 | part 1 of 3 refuted | 3 parts, all refuted | 6 parts hold | (88, 3) | the rule applies |
| SlotConstAcrossBlocks | part 2 of 3 refuted | parts 2-3 of 3 refuted | 1 part holds | (40, 3) | the rule applies |
| SlotStoreReloadU32 | part 1 of 2 refuted | 2 parts, both refuted | 10 parts hold | (64, 6) | the rule applies |
| ByteMerge | part 1 of 1 refuted | 1 part, refuted | 1 part, refuted; statement byte-identical (`a589c2fe…`) | (0, 0) | OD-233b (demanded bits) |

Ten of the eleven hold in parts on samples on the head, each with inputs
defined.
In the first seven the defined item is the scaled index (or, for
FieldDispU32, the field address), a term over a parameter binding that
crosses the cut between the `imul` (`lea`) and the access; defined, the
suffix's address claim holds (U64Index's part 2 states `s1 := (bvadd p0
x1v0)` against the machine's `(bvadd e_rdi (bvmul e_rsi 8))`). In the
three slot fixtures it is the `imul` of two constants (`x3v0 := 8` in
SlotConstU64's first part) and the slot's bytes. ByteMerge defines nothing, and its
statement is the one without the rule. Its refuted part (printed with
`TCG_OD233_PRINT_TEXT=1`) is

```text
(declare-const x1v0 (_ BitVec 8))
(declare-const x1t0 (_ BitVec 56))
(assert (not (= true (= ((_ zero_extend 24) x1v0) (concat ((_ extract 23 0) x1t0) x1v0)))))
```

The cut item `x1v0` is the byte the `MovRM8` loaded from incoming memory
(not fixed for the run, so not definable), and `x1t0` is the cut's input
for the bits above it, which the merging 8-bit load leaves undefined in its
32-bit register; the source zero-extends. The two sides differ whenever
those undefined bits are not zero. No source term fixes them, so no
definition can: what ByteMerge needs is a relation that states only the
bits an observable demands, which is OD-233b's demanded-bits rule (design
§3.3), not built. (ByteMerge is synthetic: no selector path emits the
merging `MovRM8Sib` it decomposes.)

## The solver-free gate

The module `x86_source_bound_body::tests::od233::` (no solver: every
"holds" and "refuted" here is on samples; its lines from gate 2's
`--nocapture` run on `3ef06d6dd`, `b11-gates.log`, *Gates*; its 1176
`OD233_` lines, sorted and without times, are those of the same run on
`5896ae541`, `b07-gates.log`, line for line):

- `every_fixture_has_its_shape`: every fixture's asserted shape holds on
  the real pipeline's output (P8's and V9's stores into L, only V9's C
  reloading it; Q1's machine having fewer blocks than its LIR).
- `every_positive_fixture_holds_in_parts`: P1-P5, P7, P8, Q1 and P6 hold
  on every sampler with their inventory checking (`OD233_HOLDS`: P1, P2
  and Q1 40 bytes, P3 16, P4 1 item `x3v0`, P5 8 bytes, P7 12, P8 16,
  SlotConstU64 88 bytes and 3 items, SlotConstAcrossBlocks 40 and 3,
  SlotStoreReloadU32 64 and 6); P1b defines nothing, declares no cut-input
  name of L and keeps the statement it has without the rule; Q1 is stated
  over the merged-chain quotient; P8 has an edge stated in two regions.
- `every_wrong_lowering_is_refuted_in_parts`: W1 part 2, W2 part 1, W3
  part 3, W4 part 1, W6 part 2, W5 parts 1-3 refuted (`OD233_WRONG`), each
  with inputs defined (W1, W2 40 bytes; W3 16 bytes and 1 item; W4 8
  bytes; W6 16 bytes; W5 88 and 3), so the rule never hides a wrong
  lowering here.
- `every_free_input_control_keeps_its_statement`: V1-V9 and V2b define
  nothing and their statements are byte-identical with and without the
  rule (`OD233_CONTROL`, digests as in the fails-before table), and each
  control's candidate inputs (L's eight bytes at its cut; V4's earlier
  item `x1v0` too, V7's `x1v0h`/`x1v0l`, V8's `x1v2`) are declared in its
  statement and not defined; V9 has an edge stated in two regions; N1
  refuses `NoObservable` both ways.
- `every_definition_is_fixed_for_the_run_and_claimed_on_its_edges`: in the
  18 subjects that define inputs (P1-P5, P7, P8, Q1, W3-source, W1-W4,
  W6, the three P6 fixtures and W5), every defined term names only
  run-fixed inputs and no slot address, every defined name is declared
  once, every stated edge `(region, from, cut)` into its cut considers it
  exactly once (the theorem's record, `split::DefinitionRecord`, tests
  only), and every claim it states is a subterm of the statement
  (`OD233_AUDIT`: 573 names on one stated edge with one claim; 17 on two
  stated edges with two claims, P4's `x3v0` on its two forward edges and
  C's eight bytes in P8 and in W6, each on J's two stated edges; 16 on two
  stated edges with one claim stated, P5's and W4's L bytes at the loop
  header, whose back edge brings the name itself).
- `k2_is_checked_for_each_region_s_stated_edge`: P8 with the claims on its
  second region's copy of J's edge into C dropped
  (`od233-drop-repeat-claim`) is refused by K2, `cut point Block(4)'s
  defined input x4b0o0 is not claimed on the edge from Block(3) in region 1
  (OD-233)`; with K2 keyed by block and cut alone (`od233-k2-by-pair`, the
  keying before the review round) the same statement passes K2 and holds
  on samples, the claim missing (`OD233_K2 by block and cut alone:
  Ok(())`).
- `every_od233_mutant_fails_a_control` (*Mutants*).
- `the_defined_cut_inputs_trace_line_precedes_the_parts_and_bound_lines`:
  in a child process, the production verifier (`TCG_X86_BODY_TRACE=1`, no
  replay) on P1L prints `fn=od233_long_len_local merged chains=1
  absorbed=1`, then `defined cut inputs bytes=16 items=0` (the counts its
  owner defines through `slice22::fixture_owner`, the production planner),
  then `stated in parts=1`, and last `bound rows=325 …`; slice 16's
  `LongChain` (in parts, defining nothing) prints no `defined cut inputs`
  line.
- `defined_cut_inputs_never_stop_a_part_holding`: every correct fixture of
  slices 1 to 25 and of this module, cut at every block and at every clean
  point (`OD233_SWEEP compared=1102 defining=242 newly_holding=11
  recut=14`): no region that held on samples without the rule fails
  with it, no statement is refused with the rule that is stated without
  it, and every statement that defines nothing is byte-identical. The
  eleven regions that newly hold are slice 25's three slot fixtures at
  every point (regions 4, 6, 8 of 9; 6, 9 of 10; 5, 9 of 11) and P1, P2 and
  P3 (every block region 2, and P3's every-point region 5 of 7).
  Statements over the merged-chain quotient: 30, of which 16 define
  inputs (slice 24's `EntryChain`, `DenseSwitchTail`, `SparseSwitchTail`,
  `PreheaderChain`, `TenMembers`, `DeadChain` and `PartialMerge`, and slice
  25's `MergedAddInto`, each at every block and every point), none losing
  a region. The most distinct
  claims any part has is 180, with the rule and without it (a statement
  that defines nothing); no part of a statement that defines an input has
  more than 37 (SlotConstU64 at every point), under the claim split's 64. `od233-taint` (the choice's taint
  exclusion skipped) changes none of the statements. Each statement's
  digests both ways are printed (`OD233_SWEEP_DIGEST`; *The cross-tree
  digests*), and each re-cut's spelling (*The re-cuts*).
- `the_in_parts_golden_moves_only_where_an_input_is_defined`: slice 16's
  five size shapes (`LongChain`, `DiamondChain`, `BigLoop`, `ZeroArray`,
  `CallChain`, stated in parts by the production planner) define nothing
  and keep their golden statements.
- `an_observable_free_statement_still_refuses`: N1, whose bytes are
  definable (8 bytes with `od233-observable`), refuses `NoObservable`
  under the rule and without it.

The rest of the x86 body suite (gate 1) is unchanged, except slice 25's
in-parts test, whose `not_holding` is now `[ByteMerge]` (`S25_SPLIT_SUMMARY
stated=24 not_holding=[ByteMerge]`, from 21 and four), and slice 16's
every-point test, which now runs on the verifier's stack (*Deviations*;
`SLICE16_EVERY_POINT built=360 refused=8`).

### The re-cuts

The sweep prints how each of the 14 re-cut statements is spelled
without the rule and with it (`OD233_SWEEP re-cut`; `plain`: every part is
its region's claims as the statement has them, slice 9's restatement when
every region's spelled claims drop; `with_definition_claims`: parts that
keep a definition claim by name, which only a plainly stated part does):

| statement (every point unless named) | parts without → with (defined bytes, items) | plain without → with | most distinct claims in a part, with | parts keeping a definition claim, with |
| --- | --- | --- | --- | --- |
| s5 `PairSliceTail` | 2 → 3 (0 bytes, 4 items defined) | yes → yes | 3 | 3 |
| s8 `ParamTwoLanes` | 4 → 5 (0, 5) | yes → yes | 3 | 4 |
| s9 `LongChain` | 140 → 171 (0, 62) | yes → yes | 2 | 62 |
| s15 `NegAbsBits` | 2 → 3 (0, 3) | yes → yes | 2 | 3 |
| s16 `LongChain` | 360 → 372 (0, 118) | yes → yes | 3 | 112 |
| s20 `ManySlots` | 81 → 286 (421, 79) | yes → yes | 5 | 285 |
| s25 `FieldU32` | 3 → 4 (0, 2) | yes → yes | 2 | 2 |
| s25 `FieldBelowU32` | 3 → 4 (0, 2) | yes → yes | 2 | 2 |
| s25 `SlotConstU64` | 3 → 6 (88, 3); refuted 3 → 0 | no → yes | 37 | 5 |
| s25 `SlotConstAcrossBlocks` | 3 → 1 (40, 3); refuted 2 → 0 | no → no | 2 | 0 |
| s25 `SlotStoreReloadU32` | 2 → 10 (64, 6); refuted 2 → 0 | no → yes | 20 | 6 |
| P3 `SymbolLocal` (every block) | 2 → 1 (16, 0); refuted 1 → 0 | no → no | 2 | 0 |
| P3 `SymbolLocal` | 2 → 1 (24, 0); refuted 1 → 0 | no → no | 2 | 0 |
| P7 `NarrowReadBack` | 1 → 2 (12, 2) | no → no | 2 | 0 |

So the re-cuts have three measured shapes: (a) in eight statements every
part is its region's claims as the statement states them, without the rule
and with it (`plain`), and the definition claims stay in the parts as
stated, so each region the rule gives claims becomes a part (s20
`ManySlots`: 285 of its 286 parts keep a definition claim by name); (b) in
SlotConstU64 and SlotStoreReloadU32 the parts are spelled without the rule
and plain with it: once the definitions make every region's spelled
claims drop, slice 9's rule states every region plainly; (c) in
SlotConstAcrossBlocks and P3 the definitions turn a refuted region's
claims into identities (fewer parts), and in P7 the exact fold spells the
defined low byte differently from the source term (*Deviations*), so its
claim stays as a part. No re-cut has a refuted part with the rule. (`plain`
does not tell slice 9's restatement from a spelling that changes no claim;
for the eight, the parts are as stated either way.)

### The cross-tree digests

The base recorder (`od233_base_digests`, kind `base` of
`fails-before/make_fails_before.py`, `b05-fb-base.log`) states the same
1102 subjects at `b30110fcd`, and `scripts/digest_compare.py` compares
them with gate 2's sweep on `3ef06d6dd` (`digest-compare-b11.txt`; on
`5896ae541`, `digest-compare.txt`, the same line):

```text
DIGEST_COMPARE subjects base=1102 head=1102 off_equal_to_base=1102 defining=242 undefined_on_equal_to_base=860 mismatches=0
```

Every statement without the rule (`od233-off`) is the one slice 25's base
states, digest for digest (refusals included), so neither the rewritten
`run_fixed_term` nor anything else in the head moves a statement the rule
does not touch; and each of the 860 statements that define nothing is
the base's with the rule too.

## Mutants

Each `od233-*` switch is behind the test-only `quotient::mutant` seam.
`every_od233_mutant_fails_a_control` requires each control to pass
unmutated and, under its mutant, to fail with the stated text (review
round: before, any failure of any one control counted). Every line is from
gate 2's run (`OD233_MUTANT`):

| mutant | what it breaks | control | text its failure holds |
| --- | --- | --- | --- |
| `od233-off` | nothing is defined | P1 holds | `part 2 of 3 is refuted on samples` |
| `od233-forge` | the first defined byte's term off by one, in its definition alone | P1 holds | `part 1 of 3 is refuted on samples` |
| `od233-forge-byte` | the first defined byte's term off by one in the CHOICE (definition, K1 and claims all see it) | P1 holds | `part 1 of 3 is refuted on samples` |
| `od233-forge-item` | the first defined item's term off by one in the CHOICE | P4 holds; P6 `SlotConstU64` holds | `part 1 of 1 is refuted on samples`; `part 1 of 2 is refuted on samples` |
| `od233-no-claim` | no definition claim on any edge | P1 holds | K2: `cut point Block(1)'s defined input x1b0o0 is not claimed on the edge from Block(0) in region 0 (OD-233)` |
| `od233-drop-repeat-claim` | no definition claims on an edge whose block and cut another region already stated | P8 holds | K2: `cut point Block(4)'s defined input x4b0o0 is not claimed on the edge from Block(3) in region 1 (OD-233)` |
| `od233-no-claim-no-k2` | no claims and no K2 | a forged byte never holds; a forged item never holds | `Wtf8LenLocal holds with a forged definition`; `CommonCutParam holds with a forged item` |
| `od233-first-edge` | seeded from the first forward edge only, no shrink | V1 holds | `part 2 of 2 is refuted on samples` |
| `od233-no-shrink` | no shrink over the back edges | V3 holds | `part 1 of 1 is refuted on samples` |
| `od233-any-name` | every undefined name taken as fixed | V8 holds | K1: `cut point Block(1)'s input x1v2 is defined by a term that is not fixed for the run (OD-233)` |
| `od233-observable` | the claims count as observables | N1 refuses | `SymbolNoObservable is stated` |
| `od233-free` | a defined name is left free too | P1 holds | `premise constrains the free input x1b0o0` |
| `od233-late` | the definitions after the source definitions | P1 holds | `s1 uses x2b0o0 before its definition` |

Two switches are not in the table: `od233-k2-by-pair` (K2 by block and
cut alone) has its own test, above, since no correct construction drops a
claim; `od233-taint` (the taint exclusion skipped) is a measurement. It
changes none of the 1102 swept statements, so no fixture reaches the
exclusion. By reading (not measured), slice 7's tainted roots (a call's
bytes and results, an access's bytes, a load after an escape, a slot
address) have no term over the run's fixed inputs, so the resolution
drops them before the exclusion is consulted. No control can show it on
this corpus, and OD-233 does not count it as trusted.

## Qualification

Each lane in a process of its own, on the committed head `3ef06d6dd`
(`scripts/gates.sh`, gate 2 of `b11-gates.log`, with the same counts on
`5896ae541` in `b07-gates.log`; the replayed queries dumped
to `~/tcg-scratch/od233-run/qual-dump/`), with AY 0.27.0 build 13556
(commit `ebde49de3`) and Clean 5f09e36c from the overlay:

- `od233_qualification::host_qualification_replays_the_od233_parts`:
  **35 of 35 parts `result=Verified`**, no `FAILED`,
  `KNOWN_UNCERTIFIED_OD233` empty: P1 3 parts (40 bytes defined), P1b 3
  (nothing defined), P2 3 (40 bytes), P3 1 (16 bytes), P4 1 (1 item), P5 1
  (8 bytes), P7 1 (12 bytes), P8 2 (16 bytes), Q1 3 (40 bytes, over the
  quotient), SlotConstU64 6 (88 bytes, 3 items), SlotConstAcrossBlocks 1
  (40, 3), SlotStoreReloadU32 10 (64, 6). The slowest part is
  SlotConstU64's second (9.3 s; on `5896ae541` its fourth, 7.4 s). (Before the review round: 30 of 30, the
  same subjects without P8 and Q1.)
- `od233_qualification::host_qualification_refutes_the_od233_wrong_lowerings`:
  every wrong lowering is stated and refuted by AY with a counterexample:
  W1 part 2 (`e_rsi = 2^63 - 1`, `e_rcx = 2^63`), W2 part 1, W3 part 3, W4
  part 1, W6 part 2 (`e_rdi = 1`, `e_rsi = 0`: the arm's region does not
  keep `y != 0`, a path fact its cut forgets, and the store leaves L `y`
  where the source keeps `x + 1`), W5 parts 1-3 (each with an empty model); the other parts of W1-W3
  and W6 are `Verified`, as the fixture-level samples found.
- `od233_qualification::host_qualification_times_the_largest_recut_statement`
  (review round, ignored, a measurement; `b10-recut-time.log`, on
  `3ef06d6dd`): s20 `ManySlots` at every point, replayed part by part on
  AY without the rule (`od233-off`) and with it. Without: 81 parts, **81
  `result=Verified`**, 22.3 s in all, the slowest part 1.30 s. With: 286
  parts (421 bytes and 79 items defined), **286 `result=Verified`**, 46.7 s
  in all, the slowest part 1.06 s. One run on this host, so the times
  carry the host's run-to-run spread; what makes the total about twice as
  long (more parts, or parts that are each harder) is not separated. The
  lane's first run (`b08-recut-time.log`, on `5896ae541`) panicked before
  replaying anything: it looked for the fixture in slice 16's list, not
  slice 24's; `3ef06d6dd` fixes the lookup and nothing else.

## Gates

Every Cargo run went through `scripts/trust_cargo.sh` with the overlay's
`targo`, under `build-slot`, on the committed head `3ef06d6dd` (the review
round's code and tests), in the lane's own target directory
(`scripts/gates.sh`, `b11-gates.log`, 03:48-04:52 on 2026-11-07). Gate 6
(`jobs/b13-gate6.sh`, which prints the head and `git status --short`)
ran on the records tree at `454963b4c` (`b13`), on `c76048fa3` with a clean
tree (`b14-gate6-head.log`), and, run by hand without `build-slot` (it
builds nothing: `targo fmt --check`, a Python check and `targo
metadata`), on `78f602091` with a clean tree (`c01-gate6.log`), the
census record with its fact-check corrections. The commits after
`3ef06d6dd` change no Cargo input: `454963b4c` adds one entry to
`scripts/full_test_matrix_hosts.py`'s `IGNORED_TESTS`, which only the
matrix check reads, and the records commit changes this report, OD-233 and
LIMITATIONS. The census record's commits (`c0b828dcc`, `78f602091`)
change this report and its scripts, OD-233, LIMITATIONS, CHANGELOG and the
census table, none of them a Cargo input; the commit after `78f602091`
records that gate 6 run and changes only this report, `PAYLOADS.md` and
`scripts/payloads233.py`. Gates 1-5 had run on `5896ae541` before the timing lane's
fixture lookup was fixed (`b07-gates.log`, 01:50-03:22) with every count
below the same. (Before the review round the same gates ran on `a8d1d38c6`,
`a11-gates.log`: gate 1 491 passed, gate 2's module 9 and its replay lane
30 `result=Verified`.)

| gate | command (see `scripts/gates.sh`) | result |
| --- | --- | --- |
| 1 | `trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration` | `test result: ok. 493 passed; 0 failed; 29 ignored` (the 491 before, with the review round's two `od233::` tests) |
| 2 | `od233::` with `--nocapture`, then the two `od233_qualification::` lanes with AY/Clean, `--exact --test-threads=1`, one per process | module `test result: ok. 11 passed; 0 failed; 2 ignored`; replay lane 35 `result=Verified`, no `FAILED`; refutation lane 8 `CounterExample` (every wrong lowering refuted: W1-W4, W6, and W5's three parts) |
| 3 | slice 25's three, slice 24's three, slice 23's four and slice 22's four qualification lanes, one per process | 14 of 14 `test result: ok`, as before the round: slice 25's replay lane 100 `result=Verified` (its refutation lane 25 `CounterExample`), slice 24's 26 (refutation 3), slice 23's 9 and 3 generalizations (refutation 11), slice 22's 14 (refutation 12); the credit lanes pass |
| 4 | `trust_cargo.sh test --no-fail-fast -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus --test e2e_x86_64_differential --test e2e_x86_64_triple_oracle --test e2e_x86_64_mixed_width_shift --test e2e_x86_64_i128_stack_abi --test e2e_x86_64_internal_multi_result --test e2e_x86_64_sib_rmw -j2` with AY/Clean | `x86_source_bound_body` 11 passed, `must_refuse_corpus` 5, `e2e_x86_64_differential` 17, `e2e_x86_64_triple_oracle` 9, `e2e_x86_64_mixed_width_shift` 9, `e2e_x86_64_i128_stack_abi` 3, `e2e_x86_64_internal_multi_result` 13, `e2e_x86_64_sib_rmw` 2; 0 failed |
| 5 | `trust_cargo.sh test -p trust-cg-lower --lib -j2` | `test result: ok. 2133 passed; 0 failed; 1 ignored` |
| 6 | `TRUST_TARGO=<pkg 6808 targo> bash scripts/check_fmt.sh`; `python3 scripts/check_documentation.py --check`; `TRUST_TARGO=<overlay targo> python3 scripts/full_test_matrix_hosts.py --check` | last recorded on `78f602091`, a clean tree (`c01-gate6.log`, 14:01-14:05): `check_fmt: OK — every workspace file matches trustfmt`, `fmt-exit=0`; `Maintained file links, development records and the diagnostic code census are current.`, `docs-exit=0`; `matrix-exit=0`. The same three lines on `c76048fa3`, a clean tree (`b14-gate6-head.log`), and on the records tree (`b13-gate6.log`, at `454963b4c` with the records uncommitted). Its first run (`b12-gate6.log`, at `3ef06d6dd`) failed the matrix check, `trust-cg-verify/lib: #[ignore]d test(s) missing from IGNORED_TESTS: host_qualification_times_the_largest_recut_statement` (the review round's timing lane); `454963b4c` lists it with its reason |

The lint gate (`scripts/check_tippy.sh`) was not run: no `tippy` runs on
this host (UNAVAILABLE, not a pass).

`gates.sh` ends `the gates read 3ef06d6ddae8c4e2a8838673182c2700f2f715b4`:
the tree did not move while they ran.

## Deviations from the design

Each deviation is fail-closed or keeps the design's intent. None weakens a
refusal or relabels evidence.

- **The loops run at O1** (`level233`: P5, V3 and V8, so W4 too, which
  edits P5). At
  O2 `x86-loop-rotate` is unconditional, and the body theorem refuses a
  rotated loop (`machine blocks do not correspond one to one`, slice 26's
  scope), so an O2 loop fixture would test the refusal, not the rule. O1
  runs LICM, copy propagation, the peephole, DCE, if-conversion and branch
  layout, with no rotation and no `x86_slot_forward`. Every other fixture
  is O2.
- **P1 keeps `ptr`, `len` and B in separate slots** (`fn(ptr, len, begin,
  end)` with scalar slots instead of the design's 16-byte pair slot and
  `gep`), so that no scaled-index row enters a fixture the pre-slice-25
  tree must judge. `every_fixture_has_its_shape` asserts that no fixture
  has a SIB load or store row (a `LeaSib` address is allowed: P4 has one,
  and the code before slice 25 admits it).
- **P3, N1 and V4 were redesigned** to the real pipeline's output. P3's
  Block 2 reloads L, passes it to a call and returns (the design's shape
  was refused by the merged-chain clean split); N1 is one block storing a
  symbol's address into L and passing `&L` to a call, cut between the two
  (the design's shape was refused the same way);
  V4 reloads L at a join of two predecessors (the forwarded register the
  design's shape kept was paired with no loop-header parameter, a refusal).
- **P4, P5 and P7 are not fails-before cases.** The design expected them
  refuted before the rule; on the real output they hold at `b30110fcd` and
  at `12ebba653`. They stay as coverage: each defines inputs (P4 one item,
  P5 eight bytes, P7 twelve) and holds. So does the review round's P8 (16
  bytes): it exists for its shared edge, the shape K2's region keying is
  about, not for a refutation before the rule.
- **A definition does not always drop as an identity.** The design (§2.7)
  expected a definition claim on an edge whose source term is the defined
  term to vanish with slice 9's identity dropping, leaving every other
  statement's parts as before. Measured (`OD233_SWEEP re-cut`): 14 of the
  1102 swept statements (1096 before the review round's fixtures) are cut
  into a different number of parts, none with a part refuted. Two causes were read from the printed parts
  (`OD233_RECUT`): in slice 25's `FieldU32` at every point every region's
  claims become identities once the items are defined (`x1v0`, `x2v0` and
  `s0` all `(bvadd p0 p1)`), so slice 9's rule ("never by identities
  alone") states every region plainly; in P7 the defined term's exact fold
  spells the low byte differently from the source term (`(concat ((_
  extract 31 8) (bvadd e_rsi 1)) (bvadd ((_ extract 7 0) e_rsi) 1_8))`
  against `(bvadd ((_ extract 31 0) e_rsi) 1_32)`), so its claim stays.
  The review round measured all fourteen (*The re-cuts*). On the census
  one function is re-cut (O0 `digits_to_exp_str`, 11 → 10 parts; *Census*,
  *Statement growth on the census*).
- **The sweep compares regions, not parts.** When a statement is re-cut,
  its parts do not correspond one to one, so
  `defined_cut_inputs_never_stop_a_part_holding` judges each region's
  obligation (the cone of definitions its claims need,
  `split::part_obligation`) with the rule and without it, and fails on any
  region that held without the rule and does not with it. Where nothing is
  defined it requires the statements byte-identical.
- **`run_fixed_term` resolves on an explicit stack.** The recursive
  resolution was replaced while diagnosing the stack overflow below; it did
  not cause it, and the result is unchanged (a cycle resolves to nothing,
  as before).
- **`BEFORE_SLICE25` dropped.** The pre-slice-25 fails-before record runs
  every fixture, since none has a SIB row.
- **Slice 16's every-point test runs on the production verifier's
  stack.** With the rule, `slice16::every_earlier_fixture_cut_at_every_clean_point_holds_part_by_part`
  aborted with a stack overflow (`a02-suite.log`); it passes without it.
  Measured, in this order:
  - by phase (`a05-print.log`, a temporary diagnostic): with the rule the
    last phase printed before the abort is `s9 SlotJoin pooled statement`
    (slice 10's edge and slice 11's pooled samplers on the whole statement);
    with `od233-off` every fixture finishes;
  - with `RUST_MIN_STACK=536870912` the same diagnostic passes, and under
    lldb the overflowing frame is `SmtExpr::try_eval`, the recursive
    evaluator (`a08-lldb.log`, `a08-bt.txt`): depth, not a cycle;
  - the statements' depths over all 721 fixtures and cut sets stated both
    ways (`a09-depth.log`, `DEPTH233`): without the rule the deepest is
    160 (`s9 NestedTree` at every point); with it `s9 SlotJoin` at every
    point goes from depth 33 (31 top-level conjuncts) to 291 (290), with
    259 bytes and 13 items defined, and the next deepest is NestedTree's
    253, which passes. A definition claim on an edge with no guard and no
    stop term is a conjunct of its own (`under` with no condition), as the
    relation's claims there are, and the statement's conjunction is right
    nested, so each such claim is one level of the evaluator's recursion
    (about 7-8 KiB per level in this debug build, from 2 MiB between depth
    253 and 291).

  The production verifier evaluates on its 32 MiB stack
  (`resource_limits::run_on_proof_verifier_stack`, whose comment records
  the same hazard), and the workspace's other deep tests run on a big stack
  for the same reason (`source_bound_cell_caller_tests.rs`'s
  `on_big_stack`). The test now runs its body through
  `run_on_proof_verifier_stack` and passes (`SLICE16_EVERY_POINT built=360
  refused=8`, `a09-depth.log`). No statement and no verdict changed for
  it.
- **The census against the design's predictions** (§7, *Census*). O2
  254 → 253 with wtf8 promoted, 35 of 35 in-parts functions Valid, as
  predicted, but wtf8's trace reads `defined cut inputs bytes=16 items=0`,
  not `bytes=8`: the replayed parts show 8 of the 16 (slot 37's bytes at
  `Block(2)`), and where the other 8 are is not measured. O0 20 → 20 with
  `failed_roots.jsonl`, `refusals.jsonl` and every emitted object
  byte-identical, but the trace is not: 59 functions print the new line,
  and `digits_to_exp_str` is re-cut from 11 parts to 10. The design's "no
  part crosses 30 s" is false before and after OD-233 (`from_ascii_radix`'s
  parts, 60 s each). The stop rule's timeout item fired against
  `census-o0-s25` and was ruled host solver capacity on the paired control,
  compared part by part (*The O0 stop*); `census233.py` had compared
  per-function timeout counts with the earlier census alone, and against
  the control it still reports four functions (one race, three memo
  hits). The landing is left to the orchestrator.
- **Review round: the trace test's subject is P1L, not P1.** P1 is within
  the single-query bounds, so the production verifier states it as one
  query and prints no parts line; P1L (P1 with 300 calls before its
  return) is past them, and the production planner states it in parts
  over the quotient with 16 bytes defined.
- **Review round: Q1 is cut at every block start but the jump-only
  block's.** That block's one instruction is the `Jump` the merged-chain
  quotient removes, and a cut there is refused by name (`a cut point at the
  Jump that ends LIR block Block(2), which the merged-chain quotient
  removes`); the sweep's every-block and every-point cuts of Q1 are refused
  so, with the rule and without it.
- **Review round: V9's C reloads L.** Without a read in C, L's bytes are
  cut bytes C never reads; the relation states them on each edge (source
  against machine), but no name for them is declared, so the control would
  test nothing. With the reload they are declared inputs of C, and stay
  free.
- **Review round: the definition claims are not grouped.** Stating each
  edge's definition claims as one conjunct would bound the depth and the
  claim count by the edges, but it changes the spelling of every statement
  that defines an input, and the relation's own claims are emitted one per
  conjunct the same way; the growth is measured on the sweep (*The
  re-cuts*) and, in part, on the census (*Statement growth on the
  census*).
- **Review round: the fails-before copies were replaced.** The third run
  wrote `od233-run/fails-before/{base,pre}-x86_source_bound_body_od233_tests.rs`
  over the `a8d1d38c6` copies; it reprints their lines byte for byte, and
  [PAYLOADS.md](PAYLOADS.md) binds the new copies.

## Open issues

- **The O0 timeout ruling rests on one paired run** (*The O0 stop*). Six
  functions' extra timeouts against `census-o0-s25` are held to host
  solver capacity because the baseline dylib's run back to back with the
  OD-233 census, under comparable load, reproduces five of them, and
  OD-233 differs from it part by part in one whole-body race. Query
  identity there rests on smt2 byte lengths, not content. Re-running both
  O0 censuses on a quiet host would settle it.
- **Where wtf8's other 8 defined bytes are is not measured** (*Census*):
  the census prints only the counts, and parts 1 and 3 are byte-identical
  to `census-o2-s25`'s.
- **Statement growth** (*Deviations*, *The re-cuts*): one top-level
  conjunct per definition claim on an unguarded edge, and the statement's
  conjunction is right nested, so every recursive walk of a statement
  (`SmtExpr::try_eval`, printing, hashing) goes one level deeper per claim
  (s9 `SlotJoin` at every point: 33 → 291). Where every part is stated
  plainly (eight of the fourteen re-cuts both ways, two with the rule
  only), the definition claims stay in the parts unsubstituted, with no
  value numbering or inlining, a spelling slice 9's record found AY's
  strict certification handles worse; s20 `ManySlots` goes from 81 parts
  to 286, all 286 `result=Verified` on AY in 46.7 s against 81 parts in
  22.3 s without the rule (one run, *Qualification*). The production
  verifier walks on its 32 MiB stack. On the census (*Statement growth on
  the census*): one O0 function re-cut (11 → 10 parts), none at O2; the
  parts of defining functions certified during the census replay
  `Verified` (O0 64, the largest 16809 B, at most 3.39 s of AY and 4.64 s
  of Clean; O2 20, at most 3028 B, one of them wtf8's part 3, unchanged
  and certified for the first time); no census aborted. Not measured:
  those parts' sizes before OD-233 (except wtf8's part 2, 1273 B → 856 B,
  and part 3, 1872 B → 1872 B) and how deep a census function's statement
  gets.
- **The claim split's bound.** A part with more than
  `split::MAX_CLAIM_PARTS` (64) distinct claims gets no claim-by-claim
  replay fallback (OD-197). In the sweep the most distinct claims in a
  part is 180, with the rule and without it, in a statement that defines
  nothing; no part of a statement that defines an input has more
  than 37 (SlotConstU64 at every point), so the rule moves no swept part
  past the bound. The census prints a part's distinct claims only when it
  replays the part claim by claim, after its whole query fails (*Statement
  growth on the census*): at O0 at most 12 (`exp_u64`'s part 8, in a
  defining function), at O2 at most 4 (a whole-body query), all under 64.
  The parts that verified whole are unmeasured against the bound.
- **OD-233b is specified (design §3.3) and not built.** Its four
  residuals: an item with no stamped machine row that would be defined
  (the `cut_pairing` refusals), inputs defined over the cut's own other
  inputs (with a machine tie for the forwarded register), ByteMerge's
  undemanded bits (a demanded-bits relation; it keeps ByteMerge's
  decomposition refuted), and path facts a cut forgets. Its trigger: the
  count of `cut_pairing`'s `no machine row writes a register as the
  definition of …` refusals per census, 1 function (2 lines) at O2 in
  `census-o2-s25` and in the OD-233 census (0 at O0 in both), and 9
  functions (18 lines) under S26's proxy `census-o2lk-k3`; before the
  first residual is built, a test build that logs whether each unpaired
  item's source term is run-fixed measures its demand.
- **The lint gate is UNAVAILABLE on this host** (no `tippy` runs here); it
  was not run, and that is not a pass.

## Review round (2026-11-06)

A review of `e1163b5bc` raised 19 findings. Each was checked against the
code, and all 19 are real: K2 was weaker than its record (1), twelve are
evidence gaps (one of them a census-parser bug), and six are record errors.
None found a statement that credits a wrong body: on that head no
construction dropped one region's copy of a claim (reaching K2's gap took
the test-only `od233-drop-repeat-claim`). Every change fails closed. No
refusal was weakened, no test was flipped and no evidence was relabelled.
The code and tests are in commits `5896ae541`, `3ef06d6dd` (the ignored
timing lane's fixture lookup) and `454963b4c` (the timing lane listed
among the matrix's ignored tests), and the records are in the docs commit
after them. Gates 1-5 re-ran on `3ef06d6dd` and gate 6 on the records
tree at `454963b4c` (*Gates*).

| # | finding | real | what changed |
| --- | --- | --- | --- |
| 1 | K2 keyed `stated_edges`/`claimed_inputs` by `(from, cut)` without the region, so one region's claim satisfied K2 for a block two regions hold | yes | K2 now checks every `(region, from, cut)`; its refusal names the region. Fails before: `k2_is_checked_for_each_region_s_stated_edge` drops the claims on P8's second copy of its join's edge into C (`od233-drop-repeat-claim`): K2 refuses by name; with the old keying (`od233-k2-by-pair`) the same drop passes K2 and the statement holds on samples |
| 2 | no fixture has a defined input on an edge from a block two regions hold; no mutant drops one edge's claim; the audit's "no more edges than predecessors" was unchecked | yes | P8 `SharedJoinLocal` (holds on samples, 16 bytes defined; each of C's eight is claimed on both of J's stated edges), V9 `SharedJoinDiffers` (the arm re-stores L and C reloads it: L's bytes at C stay free, declared), W6 `StoresInArm` (P8 wrong on the arm's path: part 2 refuted on samples, and by AY with a counterexample, `e_rdi = 1, e_rsi = 0`); mutant `od233-drop-repeat-claim` (control P8, K2's text); the audit now checks exactly one claim record per name per stated edge; the predecessor bound was wrong (P8's join→C is stated twice from one predecessor) and is replaced by `0 < stated claims <= stated edges` |
| 3 | the sweep, the decompositions and the fails-before refutations were written as "hold"/"refuted" beside AY's `result=Verified` | yes | each now says "on samples" in LIMITATIONS, OD-233 and this report; `result=Verified` stays for the replayed parts only |
| 4 | `parts_census.py` ended an attempt at the `defined cut inputs` line (one attempt counted as two); design §2.5 said the parsers were unaffected | yes | the line is non-terminal and its counts recorded (`scripts/parts_census.py`, copied from the design's `work/`); on `census-o2-s25` it reads 70 attempts with parts, as its 70 `stated in parts=` lines; the reviewer's three-line attempt is one attempt; design §2.5 corrected |
| 5 | no OD-233 fixture is stated over the merged-chain quotient, and the sweep did not say whether any quotient statement defines | yes | Q1 `MergedLenLocal` (P1 behind a jump-only block O2 merges): refuted on samples at both earlier trees (part 2 of 3), and on the head stated over the quotient with 40 bytes defined, holding on samples, its three parts `result=Verified` on AY; the sweep prints `merged=` per statement: 30 swept statements are over the quotient, 16 of them define inputs, and none loses a region |
| 6 | the re-cuts' mechanism (slice 9's plain rule keeping the definition claims) and the OD-197 64-claim cap were unrecorded | yes | the sweep prints each re-cut's spelling both ways (`plain`, the most distinct claims a part has against `MAX_CLAIM_PARTS`, parts with a definition claim): 14 re-cuts (*The re-cuts*): eight plain both ways with the definition claims kept as stated, two (SlotConstU64, SlotStoreReloadU32) restated plainly only with the rule, four with fewer or other parts as spelled; the most distinct claims in a part of a statement that defines an input is 37, against the bound's 64 (the swept maximum, 180, is in a statement that defines nothing, both ways); AY time of the largest re-cut (`host_qualification_times_the_largest_recut_statement`, s20 `ManySlots`, on `3ef06d6dd`): 286 of 286 parts `result=Verified` in 46.7 s with the rule, 81 of 81 in 22.3 s without (one run); both risks in OD-233's Cost bullet and *Open issues*. Not regrouped: one conjunct per edge would change every defining statement's spelling, and the relation's own claims are emitted the same way |
| 7 | the census-facing trace line was pinned by no test | yes | `the_defined_cut_inputs_trace_line_precedes_the_parts_and_bound_lines` (child process, the production verifier): P1L prints `merged chains=1 absorbed=1`, `defined cut inputs bytes=16 items=0` (its owner's counts), `stated in parts=1`, then `bound rows=325 …`; slice 16's `LongChain` prints no such line |
| 8 | "byte-identical to before" rested on `od233-off` on the head, which keeps the rewritten `run_fixed_term` | yes | the base recorder now prints every swept statement's digest at `b30110fcd` (`od233_base_digests`); `scripts/digest_compare.py` requires the head's `od233-off` digest equal to the base's for every subject, and the head's with the rule wherever nothing is defined: 1102 of 1102 and 860 of 860 equal, no mismatch |
| 9 | the mutant campaign accepted any failure, so a reworded K1/K2 or a kill from another cause passed | yes | every mutant's every control must fail with its stated text (`MUTANTS233` carries the text; K1, K2, `is refuted on samples`, …) |
| 10 | no test forged a value item, so a claim on an item could regress unseen | yes | `od233-forge-item` forges the first defined item's term in the CHOICE (`cut_definitions`): P4 and P6 `SlotConstU64` refuted on samples; control `ForgeItemNeverHolds` under `od233-no-claim-no-k2` (a forged item holds without the claims); `od233-forge-byte` does the same for a byte. Forging the choice, not only the definition, is what reaches the reviewer's regression (a claim built from the chosen term) |
| 11 | the claim's term came from `edge_sources`, a second computation of OD-182's source term, trusted without saying so | yes | the claims now take the relation's own terms (`split_relation`: the item's value on the edge, each defined byte's source byte as the relation computes it); `edge_sources` only chooses; the remaining trusted fact (a run's whole store is the concatenation of its bytes, slice 7's reading) is in OD-233's and LIMITATIONS's trusted lists |
| 12 | the audit's doc promised more than its `claims > 0` | yes | the audit reads the theorem's record of stated edges and claims (`split::DefinitionRecord`, tests only): each defined name has exactly one claim record on each `(region, from, cut)` into its cut, and each stated claim is a subterm of the statement |
| 13 | the controls never asserted their candidate input was still at the cut; the taint exclusion had no mutant or control | yes | each control's candidate names (`candidates233`) must be declared and not defined; P1b declares none. Taint: `od233-taint` (the exclusion skipped) over the whole sweep changes none of the 1102 statements, so no corpus statement reaches it and no control can show it; recorded as not trusted (OD-233) |
| 14 | OD-233's Applied list stated the sweep and the decompositions without "on samples" | yes | as 3 |
| 15 | no test drove the production planner's in-parts route with a definition through the verifier | yes | as 7: P1L is past the single-query bounds and the production planner states it in parts; P1 itself is one query in production (*Deviations*) |
| 16 | the fails-before table put W3-source with the unchanged controls; "14 subjects" was 15 | yes | W3-source has its own row (holds at base and pre, `6fd33dd3…`; defines 16 bytes and 1 item on the head, `1bd1b02e…`); the audit count corrected (15 before the round; 18 now, with P8, Q1 and W6) |
| 17 | "the five single-query goldens" named slice 16's in-parts goldens | yes | corrected; single-query invariance rests on gate 1's `*_smt2_is_canonical_per_shape` golden tests (golden files and digests unchanged from `b30110fcd`) |
| 18 | OD-233b's status, trigger and fourth residual were missing | yes | OD-233 and *Open issues* record it as specified (design §3.3), not built, with all four residuals and its trigger (`cut_pairing`'s `no machine row writes a register as the definition of …`: 1 function, 2 lines, at O2 in `census-o2-s25`; 9 functions, 18 lines, under `census-o2lk-k3`) |
| 19 | the fails-before reproducer pinned neither commit and read the lane's working tree | yes | `fails_before.sh base|pre <lane sha>` refuses a helper not at `b30110fcd`/`12ebba653` or with any change but the generator's two files, and the generator reads the fixture section with `git show <lane sha>:…` |

## Reproducers and payloads

The scripts in `scripts/` and `fails-before/` are the ones that ran, with the
absolute paths of the measuring host:

- `scripts/fails_before.sh base|pre <lane sha>`: the fails-before record
  in a helper worktree, in the helper's own target directory; it refuses a
  helper not at `b30110fcd` (base) or `12ebba653` (pre), or with any change
  but the generator's two files (`fails-before/make_fails_before.py <lane>
  <lane sha> <helper> base|pre` copies the fixture section of the lane
  commit, `git show`, and adds the recorder tests; kind `base` adds
  `od233_base_digests`). The `a06`/`a07`/`a11a`/`a11b` runs were of the
  version before the review round, which read the lane's working tree and
  pinned no commit.
- `scripts/digest_compare.py <base log> <head log>`: the cross-tree digest
  comparison.
- `scripts/parts_census.py`: the census parser of the design's `work/`
  with the review round's fix (the `defined cut inputs` line is not an
  attempt's end); on `census-o2-s25` it reads 70 attempts with parts, as
  the log's 70 `stated in parts=` lines.
- `scripts/gates.sh`: gates 1 to 5 on the committed head, in the lane's own
  target directory; it refuses to run with uncommitted build inputs.
- `scripts/census.sh`: the census (*Census*), run as `BUILD_SLOT_MEM_GB=6
  build-slot -- zsh census.sh > ~/tcg-scratch/od233-run/logs/census.log
  2>&1`. It refuses a lane not at `c76048fa3` or with uncommitted build
  inputs, an existing census directory and a changed baseline dylib; builds
  the bridge (`~/tcg-scratch/build_bridge.t011.sh`); runs the OD-233 census
  and the baseline dylib's re-run at O2, then at O0
  (`~/tcg-scratch/census_t011_dylib.sh`, which runs
  `~/tcg-scratch/check_dylib_tools.sh`; all three bound in
  [PAYLOADS.md](PAYLOADS.md)); and compares them with slice 15's
  `census_compare.py`, `root_classes.py`, `parts_census.py`,
  `census233.py`, an inline object comparison, at O0 slice 25's
  `trace_diff.py`, and `part_times.py`.
- `scripts/census233.py <baseline dir> <new dir> <out dir>`: the stop
  rule's items (named mismatches, refuted bodies, K1, K2 and `(OD-233)`
  texts, new NoObservable, more attributed timeouts, bound attempts that
  lost Valid), wtf8's trace, the `cut_pairing` texts, part-count changes
  and the defining functions; exits 1 if any stop item holds. Run as
  `census.sh` runs it, and by hand for the O0 stop's two comparisons
  (`stop-diagnosis/base-vs-rerun/`: `census-o0-s25` against
  `census-o0-s25-st`; `stop-diagnosis/rerun-vs-od233/`:
  `census-o0-s25-st` against `census-o0-od233`).
- `scripts/part_times.py <OD-233 census dir> <re-run dir> <out dir>`: each
  part's AY and Clean time on the body theorem's obligations, the smt2
  byte length its solve lines print (its "query bytes"; a length, not the
  content) and its promotion results, paired across the two runs by
  (function, attempt, part).
- `scripts/six_parts.py <stderr.log>`: the six functions' solve and replay
  lines (*The O0 stop*), run on the OD-233 census, the re-run,
  `census-o0-s24c` and `census-o0-s25` (`stop-diagnosis/six-parts.txt`); a
  verbatim copy of the bound `stop-diagnosis/six_parts.py`.
- `scripts/fact_checks233.py <runs dir> <census.log> <wtf8 cert dir> <out
  file>`: the census record's fact checks after its review (no compiler,
  no solver), run as `python3 -I scripts/fact_checks233.py
  ~/tcg-scratch/runs ~/tcg-scratch/od233-run/logs/census.log
  ~/tcg-scratch/od233-run/census/wtf8
  ~/tcg-scratch/od233-run/fact-checks/fact_checks.txt`: every function
  whose attributed timeouts differ between the O0 censuses, in either
  direction (A); named functions' solve events (B); the six functions'
  routes to Valid (C); every claim split (D); AY and Clean seconds on and
  off the body theorem (E); the Clean checks not accepted (F); wtf8's
  certificates against `dump-o2-s25` (G); the paired O0 promotion
  results (I); `census.log`'s load lines (H). `fact-checks/host.txt` is
  `sysctl`'s CPU counts of the host.
- `scripts/payloads233.py`: regenerates [PAYLOADS.md](PAYLOADS.md)'s table.
- `scripts/server.sh`: the job server every job ran through, inside one
  `build-slot` hold (`BUILD_SLOT_MEM_GB=6 build-slot -- bash server.sh`):
  it runs `~/tcg-scratch/od233-run/queue/*.sh` oldest first and logs each
  to `logs/<name>.log`, ending `== JOB-EXIT=<rc>`.
- `scripts/jobs/`: the jobs as they ran (`a01`-`a05` the module and suite
  runs while the fixtures were settled; `a05` and `a08` the overflow
  diagnosis by phase, `a08` with a 512 MiB stack and under lldb; `a09` the
  depth measurement and slice 16's every-point test; `a10` slice 25's
  in-parts test and the printers with the parts' texts; `a11a`/`a11b` the
  fails-before reruns; `a11` the gates and the printers on the head;
  `a12` gate 6; the review round's `b01` the sweep before the commit,
  `b02`-`b04` the module while the new fixtures were settled, `b03` with a
  temporary diagnostic printing V9's statement, removed before the commit,
  `b05`/`b06` the fails-before reruns, `b07` the gates on `5896ae541`,
  `b08` the re-cut timing lane's failed first run and `b08b` the printers
  on `5896ae541`, `b10` the timing lane and `b11` the gates on
  `3ef06d6dd`, `b12` gate 6's failed first run and `b13` gate 6 on the
  records tree; `b14` gate 6 on `c76048fa3` was `b13-gate6.sh` again,
  queued as `b14-gate6-head.sh`, and the census record's `c01` gate 6 on
  `78f602091` ran the same script by hand into
  `logs/c01-gate6.log`).
  `a05`, `a08` and `a09` ran temporary diagnostics, removed before the
  commit; their sources are `jobs/phase233_diagnostic.rs.txt` and
  `jobs/depth233_diagnostic.rs.txt`.
