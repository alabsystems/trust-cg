# Darwin x86-64 `library/core` census — slice 5 (pairs, symbols, compares), 2026-09-29

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

One proof row on the host and toolchains of the
[slice-4 census](../2026-09-28-darwin-x86-64-census-slice4/README.md): native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this host
against the stage-1 `stage0-sysroot` (`targo --unverified build --release
--locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs
required (the bridge default), `-Ztrust-ir-cg-args=x86-body-trace` and
`-Ztrust-ir-cg-args=x86-body-dump=DIR`. Nothing here is a completion claim.

| Row | trust-cg | Mode | Failed roots | Distinct reasons |
| --- | --- | --- | --- | --- |
| `core-x86_64-darwin-O0-proof-slice5` | slice-5 branch (see Tree) | proofs required | 2115 | 1 |
| `core-x86_64-darwin-O0-proof-slice5-ab/main-a77f920dc` | `main` `a77f920dc` | proofs required | 2708 | 2 |
| `core-x86_64-darwin-O0-proof-slice5-ab/slice5-7ad4cee62` | slice 5 merged, review fixes `7ad4cee62` | proofs required | 2115 | 2 |

The last two rows are the controlled A/B
([below](#re-measured-after-review-controlled-ab)); they pass
`x86-body-trace` but not `x86-body-dump`.

## What was measured

- **Tree.** The bridge was built from the slice-5 commit `a02232b8b`. After
  the build only a comment in the owner, tests and documentation changed.
  `backend.sha256` is the dylib's digest. The census tool's
  `provenance.json` records `trust_cg_rev` = `de1f19099`: that is the
  `~/trust` superproject's pin, not the measured tree.
- **Baseline.** `main` at `db6c150ee` (the slice-4 tree): 2708 failed roots,
  all `[TCG-PROOF-465]`, measured on this host with the same compiler and
  replay tools and the same flags except `x86-body-dump`, which only this
  row passed (it writes the queries and changes no verdict). This is NOT a
  controlled A/B of slice 5: the slice-5 commit's parent is `main` at
  `61f2bb580`, 230 commits after `db6c150ee`, which change the bridge,
  lowering and verifier sources the census exercises (85 files under
  their `src/`, +15339/-1552). Every one of the 593 promoted roots did have a
  slice-5-class body-trace refusal on the baseline (the attribution table
  below), but the 593 and the "0 newly fail" are this tree against an
  older one. The controlled A/B, on the merged tree after review, is
  [below](#re-measured-after-review-controlled-ab).
- **Replay tools.** The toolchain AY recorded by the bridge build (`ay
  0.27.0+build.10530`) and the default checker discovery, which takes the
  owning toolchain's Clean first: the stage-1 `bin/clean` (sha256
  `7bd0a366…`, built from Clean `faf434b73`), NOT `~/clean-checker/bin/clean`
  (sha256 `949365b6…`, Clean `5f09e36c`), which the library tests'
  host qualification names through `TCG_EXTERNAL_CLEAN_CHECKER`. The
  Alethe certificates minted by the bridge in the baseline run, in both
  slice-5 runs and in the review's probe compile all record
  `external-clean-checker-sha256:7bd0a366…`, so baseline and slice 5 used
  the same checker; an earlier version of this report named the wrong one.
- **Memory.** The census started with 712871 free pages, and no
  `[TCG-COMPILE-DRIVER]` resource-budget refusal occurred. (A first attempt
  after a lint build started at 2679 free pages and was stopped before it
  produced anything; the page cache was released by a short-lived 3 GiB
  allocation before the measured run.)
- **Wall time** was 4398 s, against 2073 s for the baseline (single runs on
  a shared four-core host, so a trend, not a measurement). The rise is the
  bodies AY does not certify, not the 1270 that replay Valid (677 before).
  A Valid body is solved and Clean-checked once; when its codegen unit's
  batched compile fails and the unit is recompiled per function, the
  fallback finds it in the process's proof memo. AY's `(:reason-unknown
  (incomplete self-check-rejected))` is never memoised
  (`unknown_reason_is_memoizable_certification_gap` in `ay_bridge.rs`: the
  outcome is not a function of the query bytes, see the end of this
  report), so each of the 162 self-check rejections is solved in full by
  the batched compile, again by the fallback, and again for every
  byte-identical body: the 165 dumped non-certifying queries are 95
  distinct texts. A three-function probe crate
  (`u32::overflowing_mul`, a pair swap and a compare; `no_std`, O0, proofs
  required, `-Ztrust-ir-cg-args=solve-trace`) compiles in 6.2 s through the
  baseline's bridge and in 148.6 s through this one: the 3180-byte body query
  of `overflowing_mul` (the crate's function and `core`'s local copy) goes
  to AY four times, 22.0 s each, and ends `incomplete self-check-rejected`
  every time, while each of the two Valid bodies is solved once and is a
  memo hit in the fallback. Memoising that rejection is the decision
  LIMITATIONS.md records (the negative memo of 2026-09-30): the same bytes certify on a retry often enough
  (the `SlotFoldedOffset` replays below) that a memo would turn a retry's
  credit into a refusal. An earlier version of this report
  attributed the rise to replaying the 1270 Valid bodies twice. An earlier
  run of this row was killed by the census harness's default 3600 s
  timeout (435 objects emitted, and a summary reading "failed roots: 0");
  the measured run passes `--timeout 14400`.

## Result

2115 failed roots, all `[TCG-PROOF-465]`, against the baseline's 2708:

- **593** roots newly promote (`core-x86_64-darwin-O0-proof-slice5/promoted.txt`).
- **0** roots newly fail (`newly_failing.txt` is empty). Every failed root
  here is also a baseline root.
- No `[TCG-SOURCE-BOUND-X86-MISMATCH]` occurred, and no function that
  replayed Valid on the baseline stopped doing so.

The promoted roots, by the body-trace refusal their function had on the
baseline:

| Roots | Baseline refusal | Slice-5 rule |
| ---: | --- | --- |
| 359 | two results (a `ScalarPair` return) | RAX:RDX pair return |
| 115 | `GlobalRef` | symbol address, direct |
| 10 | `ExternRef` | symbol address, GOT |
| 83 | `Icmp` (41 `Equal`, 13 `NotEqual`, 12 signed `>=`, 7 signed `<`, 5 unsigned `<=`, 3 unsigned `<`, 1 unsigned `>=`, 1 unsigned `>`) | branch-free compare |
| 26 | a call with two results | pair call result |

The four `core` panic helpers whose first instruction is a `GlobalRef` to a
`.const.alloc` (`panicking::panic_in_cleanup`, `panicking::panic_cannot_unwind`,
`cell::lazy::panic_poisoned`, `slice::sort::shared::smallsort::panic_on_ord_violation`)
replay Valid (19, 19, 75 and 75 bound rows) and promote.

## Body trace

Per function (the first classification line of each of the 3446 traced
functions; every bound body is judged twice, by the batched compile and its
per-function fallback, 2870 bound-body trace lines in all):

| Class | Baseline | Slice 5 |
| --- | ---: | ---: |
| bound, replays Valid | 677 | 1270 |
| bound, no independently checked proof | 70 | 165 |
| not a bounded unconditional chain (control flow) | 514 | 766 |
| sret-arg callee | 423 | 423 |
| non-scalar register parameter | 235 | 235 |
| two results | 734 | 0 |
| non-scalar result (renamed refusal, same functions) | 221 | 227 |
| no result, call or access (renamed refusal, same functions) | 69 | 69 |
| `GlobalRef` / `ExternRef` | 142 / 10 | 0 / 0 |
| `Icmp` | 95 | 0 |

Where the 734 two-result functions went: 359 replay Valid, 252 are control
flow (they passed the result gate and stop at the chain gate), 81 are bound
but not certified, and the rest stop at another instruction (a private
slot's address escaping, `Bnot`, an untyped call result) or at a non-scalar
lane (6). The 290 functions refused on the baseline for "requires exactly
one ... result" are the same functions under the corrected wording: 221 have
a non-scalar result and 69 have no result, call or incoming access (no-op
bodies such as `drop_in_place::<char>`). The 235 "register parameters"
refusals are unchanged: they are not scalar pairs. A pair parameter is two
scalar LIR parameters, which main already admitted (the fails-before probe
below builds a theorem for `PairParamLast` and `PairCallArgs` on main); these
functions take a parameter the bridge declares as an aggregate, a float or
an `i128`.

**The 165 bodies that do not certify** (`body_trace_gaps.tsv`, with each
raw outcome): 70 are the baseline's gaps, 95 are newly bound. 162 are AY
rejecting its own proof in strict certification (`computed UNSAT rejected
by mandatory strict certification: strict UNSAT proof validation failed:
step t1 uses unverified trust rule` or `... uses unsupported hole rule` /
`unknown` / `(:reason-unknown (incomplete self-check-rejected))`,
`proof_gate` class SOUNDNESS), the class slices 3 and 4 recorded; 3 are an
incomplete certificate (`unproved_steps=1`, the three
`core::fmt::num::imp::*::_fmt` bodies, class PENDING(solver-capacity)).
None is a counterexample and none timed out. The new ones are mostly many
observed items (39 of the 165 state 7 items, 37 state 10; slice 3 measured
the same AY rejection for a seven-item concatenation) and multiplies (the
recorded slice-2 gap: `NonNull::add`, `overflowing_mul`,
`carrying_mul_add`, `get_offset_len_noubcheck`). `core-gaps/` holds two
representative dumped queries; replayed on the toolchain AY with
`--strict-proofs`:

| Query | Body | AY outcome | AY time |
| --- | --- | --- | ---: |
| `str_get_unchecked_range.smt2` | `str::get_unchecked::<Range<usize>>` (138 rows, 7 items: a pair result, a pair call and a symbol) | `step t1 uses unverified trust rule` / `unknown` | 1.5 s |
| `u32_overflowing_mul.smt2` | `u32::overflowing_mul` (a `(u32, bool)` pair) | `step t1 uses unsupported hole rule` / `unknown` | 12.4 s |

The rows of these bodies stay Unverified, never credited; the encoding is
not reshaped per function.

## Remaining blockers

The 2115 failed roots by their function's body-trace class:

| Roots | Refusal |
| ---: | --- |
| 764 | control flow (not a bounded unconditional chain) |
| 423 | a call to an sret callee |
| 235 | a non-scalar parameter |
| 227 | a non-scalar result (float, `i128`, aggregate) |
| 165 | bound, AY does not certify (above) |
| 138 | a private slot's address escaping (into a call: 117, into a store: 21) |
| 23 | a private byte read before written |
| 19 | an indirect call |
| 16 | a call result with no scalar type |
| 13 | no result, call or incoming access |
| 12 / 11 / 7 | `CtPop` / an `i128` load / `Select` |
| 62 | other causes (none more than 7 roots; 4 have more than six register parameters) |

## Re-measured after review (controlled A/B)

The row above compares the slice-5 tree with an older `main`. After review,
both sides were measured back to back on the same host, with the same
compiler (stage-1 `trustc` d7f143f3b), flags (O0, `-Cpanic=abort`, one CGU,
proofs required, `-Ztrust-ir-cg-args=x86-body-trace`, no dump), replay
tools (the toolchain AY 0.27.0 build 10530 and, by the default discovery,
the stage-1 `bin/clean`) and `--timeout 14400`:

| Row | Tree | Failed roots | Wall |
| --- | --- | ---: | ---: |
| `main` | `a77f920dc` (`origin/main`, the parent the branch merged) | 2708 | 2597 s |
| slice 5 | `7ad4cee62` (slice 5 merged with `a77f920dc`, plus the review fixes) | 2115 | 4726 s |

- **593** roots promote and **0** newly fail
  (`core-x86_64-darwin-O0-proof-slice5-ab/promoted.txt`, `newly_failing.txt`).
  The promoted set is exactly the first row's 593, and the slice-5 failed
  roots are exactly the first row's 2115. On both sides 14 of the roots
  fail with `[TCG-DYN-REF-IDENTITY]` (a `main` change after `db6c150ee`),
  the rest with `[TCG-PROOF-465]`.
- No `[TCG-COMPILE-DRIVER]` resource-budget refusal on either side (the
  runs started with 690421 and 1236081 free pages; during the slice-5 run
  a concurrent build took free pages down to 3615 once, and a short 1.5
  GiB allocation released the page cache).
- Body trace, per function (3432 traced on both sides): 677 -> 1270
  replay Valid, 70 -> 165 bound without an independently checked proof,
  1494 -> 2870 bound-body trace lines; every function Valid on `main` is
  Valid on slice 5.
- The review fixes do not change what the bridge compiles: the bridge
  carries a pair's `bool` lanes as masked `i32` values, so no bridge body
  has a `B1` call-result lane, and the slice-5 cross-backend matrix at O0
  (below) prints the same 1282 values in all four cells with this bridge.
- The two single runs shared the host with other builds; wall time is a
  trend, not a measurement.

## Cross-backend matrix

`cross-backend/s5_xback.py` builds a callee crate whose seventeen functions
are all inside the slice-5 domain (four pair returns, a `(i16, i64)` pair, a
pair call, six compares at 64/32/16/8 bits signed and unsigned, a compare
against a constant, a compare widened to `u64`, a stored compare, a static's
address and a load through it) with LLVM and with trust-cg WITH PROOFS
REQUIRED, and callers with LLVM and with trust-cg (`no-proof-certs`, the
caller's `main` being outside the lane), in all four rlib x bin cells, over
64 argument pairs at the ordering boundaries (0, 1, 2, 5, 0x7f, 0x80, 2^63,
2^64-1). At O0 every callee function replays Valid, the trust-cg rlib
promotes, and all four cells print the oracle's 1282 values
(`s5_xback_O0.txt`). At O1 and O2 the compares and symbols still replay
Valid, but the six pair bodies make no claim: the optimizer's two-operand
`xor r, r` zeroing idiom is a row form no slice admits (only three-address
ALU rows are), so the proof-required rlib is refused there
(`s5_xback_O1_O2.txt`), while the LLVM-rlib cells agree. Re-run at O0 with
the review bridge (`7ad4cee62`), the output is identical to
`s5_xback_O0.txt`. The `llvm-rlib+tcg-bin` cell is where a trust-cg caller
reads the `bool` lane of an LLVM pair callee (`pair_u64_bool`); through the
bridge that lane is a masked `i32`, not a `B1` call result.

The review found that a TRUST-IR producer is not covered by this matrix: a
trust-ir call with a `(u64, bool)` result is a `B1` call-result lane, which
the selector read as a clean byte and the theorem credited. That is fixed
and tested in-tree (`crates/trust-cg-codegen/tests/e2e_x86_64_pair_bool_lane.rs`
links five caller shapes at O0-O3 against the exact instruction sequences
LLVM emits for such callees; before the fix they returned 2, 3, 254 and 255
for x = 2, 3, 0xfe and 0xff where the source value is `x & 1`).

## Fails-before

`fails-before/probe_test.rs` is a temporary unit test (never committed as
a test) over the slice-5 fixtures and the new-rule mutants, using only API
present before and after this slice. Run against `main`'s owner
(`61f2bb580`, `fails_before_main_61f2bb580.txt`), 33 of the 35 fixtures are
refused as outside the domain and every mutant is refused as Unsupported
(except an RDX read after a one-result call, already a named undefined
read). Against this branch (`fails_before_branch_2aae89705.txt`) every
fixture builds a theorem that holds on samples, and the mutants end as the
new named mismatches (`ReturnValue { lane }`, `UndefinedReturn { register:
"rdx" }`, the pair call's `CallMetadata`, `Symbol` for an unreferenced
symbol and for the other form, an undefined `rflags` read) or as a theorem
refuted on samples (swapped symbols, `setcc` without `movzx`, an unsigned
order for a signed compare).

The review fixes were each checked the same way, reverting one and keeping
the rest. With the verifier's clean-byte model of a pair call's `bool`
lane restored, `a_bool_lane_of_a_pair_call_defines_bit_zero_alone` fails
(`h0` is 56 bits, not 63) and the unmasked-lane refutations hold on samples.
With the selector's mask removed, the selector unit tests fail, the fixed
theorem refutes the selector's own output for all five `bool`-lane shapes
(`slice_five_theorems_hold_on_samples`), and `e2e_x86_64_pair_bool_lane`
returns `x`'s low byte at O0-O3. With the sampled oracle's boundary values
restored, `a_u64_compare_made_at_32_bits_is_refuted` fails on all three
truncated compares. With the new library gate removed from
`scripts/soundness_check.sh`, `scripts/test_soundness_check.sh` reports
`required Cargo gate missing from --list`.

## Observed while merging with `main`

After merging `main` (`46aaf9023`) into the branch, one run of the slice-4
`host_qualification_replays_the_memory_body_theorems` failed:
`SlotFoldedOffset` came back `(:reason-unknown (incomplete
self-check-rejected))` after 9.1 s, where every earlier run had it
`Verified` in about 4 s. Its query is byte-identical on both sides of the
merge (the memory golden file only gained the `LocalBool` section).
Replayed directly on the toolchain AY (`-smt2 Q --strict-proofs --proof P
--proof-format alethe`), the same bytes certified on 1 of 3 runs while the
host was busy and on 9 of 10 runs at rest; the others end `computed UNSAT
rejected by mandatory strict certification: strict UNSAT proof validation
failed: step t1 uses unverified trust rule` / `unknown`. The test passed on
rerun. The replayer's outcome is therefore not a function of the query
bytes alone (LIMITATIONS.md).

## Files

- `core-x86_64-darwin-O0-proof-slice5/`: `gap_table.md` and
  `provenance.json` (home directory shortened to `~`, the census scratch
  directory to `<scratch>`), `failed_roots.jsonl.gz`,
  `body_trace_gaps.tsv`, `promoted.txt`, `newly_failing.txt` and the
  bridge's `backend.sha256`.
- `core-x86_64-darwin-O0-proof-slice5-ab/`: the controlled A/B, one
  directory per row (`gap_table.md`, `provenance.json`,
  `failed_roots.jsonl.gz`, `backend.sha256`), and its `promoted.txt` and
  `newly_failing.txt`.
- `core-gaps/`: the two dumped queries above.
- `cross-backend/`: the matrix script and its O0 and O1/O2 outputs.
- `fails-before/`: the probe and its two outputs.
