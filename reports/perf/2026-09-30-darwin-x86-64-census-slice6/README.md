# Darwin x86-64 `library/core` census — slice 6 (acyclic control flow), 2026-09-30

One proof row on the host and toolchains of the
[slice-5 census](../2026-09-29-darwin-x86-64-census-slice5/README.md): native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this host
against the stage-1 `stage0-sysroot` (`targo --unverified build --release
--locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs
required (the bridge default), `-Ztrust-ir-cg-args=x86-body-trace`,
`--timeout 14400`. Replay tools: the toolchain AY the bridge build records
(`ay 0.27.0+build.10530`, sha256 `9a149c35…`) and the default checker
discovery, as in the baseline row. Nothing here is a completion claim.
The record's payloads (root lists, provenance, outcome tables, logs) are out
of tree under the durable evidence policy; [PAYLOADS.md](PAYLOADS.md) lists
each with its size, SHA-256 and the commit that holds it, and this README
states the numbers they carry.

| Row | Bridge built from | Bridge sha256 | Failed roots | Distinct reasons | Wall |
| --- | --- | --- | ---: | ---: | ---: |
| [`core-x86_64-darwin-O0-proof-73e5a69f5`](../2026-09-27-darwin-x86-64-census/README.md) (baseline) | `main` `73e5a69f5` | `0c7ee18d…` | 2114 | 2 | 3994 s |
| `core-x86_64-darwin-O0-proof-slice6` | slice-6 branch `00c860e40` (base `915fff712`) | `ccb9b4fd…` | 1816 | 2 | 7054 s |

## What was measured

- **Trees.** The baseline bridge (`~/tcg-scratch/runs/main-73e5.dylib`,
  sha256 `0c7ee18d…`, built 05:08 on 2026-09-30) is `main` `73e5a69f5`. The
  slice-6 bridge (`s6.dylib`, sha256 `ccb9b4fd…`) is the
  slice-6 commit `00c860e40` on `915fff712`, which is NOT `73e5a69f5` plus a
  report alone: it also carries `e6288b598` (the x86-64 LEA-writeback
  collapse turned on by default, a post-allocation pass that runs at O0
  too; bridge knob and pipeline change) through the merge `47f63ec1d`. The
  rows therefore compare slice 6 PLUS `e6288b598`, with the same compiler,
  flags, replay tools and host. The review recomputed the verdicts from
  the two runs' outputs and they stand: 2114 -> 1816, 298 promoted, 0 newly
  failing. Each row's `provenance.json` (payload) records `trust_cg_rev`
  `de1f19099`: that is the `~/trust` superproject's pin, not either bridge
  tree.
- **Owner changes after the census bridge.** The final tree's owner
  differs from `00c860e40`'s in ways that accept no less at O0: the
  recorded successors of a block are compared with its transfers as a set,
  not in order ([below](#o1-and-o2-a-false-mismatch-found-and-fixed));
  machine blocks are paired with LIR blocks by provenance instead of by id;
  the exact affine refusal applies to one-path bodies only; and `TestRI` is
  admitted on 64-bit registers only ([review](#review-fixes)). At O0 the
  census run named no mismatch, nothing emits `TestRI`, and the offline
  probe below binds the same 1813 of the census's 3445 functions with
  byte-identical theorems under the reviewed (`5c5389e2c`) and the final
  pairing ([below](#review-fixes)), so no row
  verdict changes. The census was not re-run on the final tree.
- **Memory.** The census started with 1305672 free pages; other agents'
  builds took free pages down to about 9000 during the run. No
  `[TCG-COMPILE-DRIVER]` resource-budget refusal occurred.
- **Wall time** was 7054 s against the baseline's 3994 s (single runs on a
  shared four-core host, other builds running: a trend, not a
  measurement). Of the +3.06 ks, about 1.3 ks is the first solve of the
  newly bound bodies (the 345 several-path theorems' offline replay, AY and
  Clean once each, took 1256 s), about 0.5-0.7 ks (about 20 %) the
  per-function fallback's second solve of the 79 newly uncertified bodies,
  which the tree measured did not memoise, and about 1 ks is not attributed
  (host load, and `e6288b598` in the measured tree). The negative memo now
  on `main` (LIMITATIONS.md) answers those second solves without AY.

## Result

| Row | Failed roots | `[TCG-PROOF-465]` | Other | Promoted | Newly failing | Emitted objects | Bridge sha256 |
| --- | ---: | ---: | --- | ---: | ---: | ---: | --- |
| baseline `73e5a69f5` | 2114 | 2113 | 1 (`VaListInner`) | — | — | — | `0c7ee18d808156806bd216111d5b63893315547fc6e8d69f0a6b42825b55fd27` |
| slice 6 `00c860e40` | 1816 | 1815 | 1 (`VaListInner`) | 298 | 0 | 1628 | `ccb9b4fd2312957bbbb20fad834537c2795a36aea66cdbea923a43bf969d1caf` |

The rebuilt bridge of the review section (`7dd7c6761`) has sha256
`3925259218b213f6261e363256a16aa6657c263d6d94ed4b66c7f62770be0abc`. The
census run's `provenance.json` records exit 1 (a library with failed roots),
1628 emitted objects, wall 7053.9 s, generated 2026-09-30T20:29:46Z. The
promoted list (298 symbols) and the empty newly-failing list are the
payloads `promoted.txt` (SHA-256 `c84a249a…`) and `newly_failing.txt`.

1816 failed roots against the baseline's 2114: 1815 `[TCG-PROOF-465]` and
the baseline's one `VaListInner` lowering refusal (`Place deref memory store
from Rvalue::Ref`).

- **298** roots newly promote
  (payload `core-x86_64-darwin-O0-proof-slice6/promoted.txt`).
- **0** roots newly fail (the payload `newly_failing.txt` is empty); every failed root
  here is a baseline root.
- No `[TCG-SOURCE-BOUND-X86-MISMATCH]`, and every function that replayed
  Valid on the baseline replays Valid here.

The promoted roots, by the body-trace refusal their function had on the
baseline:

| Roots | Baseline refusal | Slice-6 rule |
| ---: | --- | --- |
| 284 | LIR source is not a bounded unconditional chain | acyclic control flow |
| 7 | a private stack byte read before it is written | frame bytes `f_k` |
| 7 | `Select { cond: NotEqual }` | `cmovcc` select |

## Body trace

Per function (3445 traced on both sides; a function's class is its bound
verdict if it has one, else its first refusal):

| Class | Baseline | Slice 6 |
| --- | ---: | ---: |
| bound, replays Valid | 1271 | 1569 |
| bound, no independently checked proof | 165 | 244 |
| not a bounded unconditional chain (control flow) | 766 | — |
| control flow: more than sixteen blocks | — | 76 |
| control flow: a loop | — | 64 |
| control flow: a path of more than 256 instructions | — | 33 |
| a private slot's address escaping into a call | 117 | 185 |
| a call result with no scalar type | 16 | 49 |
| `Checked*` arithmetic (six opcodes) | 13 | 80 |
| `GuardDivZero` / `AtomicLoad` / `Udiv` | 0 / 0 / 0 | 11 / 11 / 7 |
| a private byte read before written | 23 | 0 |
| `Select` | 7 | 0 |
| a trap that does not follow a diverging call | 10 | 0 |
| more than 256 machine rows | 6 | 1 |

Where the 766 control-flow functions went: 345 are bound (284 replay
Valid, 61 do not certify), the number the offline probe of the same
modules predicted (below); 76 have more than sixteen blocks, 64 a loop, 23
a path of more than 256 instructions; the rest stop at an instruction the
lane does not admit on any path: a private slot's address escaping into a
call (68), a call result with no scalar type (33), `Checked*` arithmetic
(65), `GuardDivZero` (11), `AtomicLoad` (11), `Bnot` (10), a variable
shift (10), `Udiv`/`Urem` (10), ... Of the 23 private-byte functions, 7
replay Valid, 12 do not certify and 4 have a path over 256 instructions. The
ten bare-trap functions: 6 are bound (none certifies) and 4 have nothing to
observe. The six "more than 256 rows" functions are now refused earlier,
at their source path's length.

**The 244 bodies that do not certify** (payload `body_trace_gaps.tsv`, with each
raw outcome; `base` = already uncertified on the baseline): 165 are the
baseline's, 79 are newly bound. 216 end in AY rejecting its own proof in
strict certification (`(:reason-unknown (incomplete self-check-rejected))`,
`proof_gate_class=SOUNDNESS`), 28 on an incomplete certificate
(`unproved_steps=1`). None is a counterexample and none timed out. Their
rows stay Unverified; the encoding is not reshaped per function.

## Remaining blockers

The 1816 failed roots by their function's body-trace class:

| Roots | Refusal |
| ---: | --- |
| 423 | a call to an sret callee |
| 244 | bound, AY does not certify (above) |
| 235 | a non-scalar parameter |
| 227 | a non-scalar result (float, `i128`, aggregate) |
| 185 | a private slot's address escaping into a call |
| 76 | control flow: more than sixteen blocks |
| 62 | control flow: a loop |
| 80 | `Checked*` arithmetic |
| 49 | a call result with no scalar type |
| 33 | control flow: a path of more than 256 instructions |
| 24 | a private slot's address escaping into a store |
| 21 | an indirect call |
| 15 / 14 / 14 / 11 / 11 | `CtPop` / `GuardBoundsCheck` / `Bnot` / `GuardDivZero` / `AtomicLoad` |
| 14 | no result, call or incoming access |
| 78 | other causes (none more than 10 roots) |

## Encoding (offline, `encoding/`)

The encoding was chosen before this run, on the several-path theorems of
the same `core` modules: `-Ztrust-ir-cg-args=dump-trust-ir=DIR` at O0 on
`main` `73e5a69f5`, every function translated, selected with the real
selector and judged by the slice-6 owner (`census_probe.rs`, `probe.sh`),
each theorem written as SMT-LIB and replayed by `replay_dir.py` (the
toolchain AY with `--strict-proofs --proof-format alethe`, then
`clean cert verify-external` with Clean `5f09e36c`). Per spelling (the
per-theorem outcome tables are payloads):

| Spelling | Theorems | Verified | AY self-check rejected | Incomplete certificate | Refuted |
| --- | ---: | ---: | ---: | ---: | ---: |
| canonical: `or`/`not` claims, no name for a copy, only the definitions the claims need (`canonical.tsv`) | 345 | 281 | 44 | 20 | 0 |
| the same with copies defined (`copies_defined.tsv`) | 345 | 162 | 163 | 18 (2 unknown) | 0 |
| every definition stated (`every_definition_first244.tsv`) | 244 | 104 | 130 | 9 (1 unknown) | 0 |
| the definitions' cone only (`cone_only_first244.tsv`) | 244 | 125 | 96 | 22 (1 unknown) | 0 |

No theorem that certifies with copies defined fails without. On the 119
canonical failures of the first run (`case_split_and_per_path.tsv`,
`variants_batch.py`): the nested-`ite` case split of the observable
certifies 4; splitting the theorem into one obligation per path certifies
every part of 28 (not built: the lane replays one theorem per function).
The census bound the same 345 functions and 284 replayed Valid, three
more than the offline replay's 281 (the batched compile and its fallback
are two attempts; the replayer's outcome is not a function of the query
bytes alone, see below). The `=>` spelling of a claim is rejected on every
fixture (`HOLEY_IMPLIES` in the qualification test: AY prints its proof
with a `hole` step, `unproved_steps=1`).

## Cross-backend matrix (`cross-backend/`)

`s6_xback.py` builds a callee crate of sixteen branchy functions (min/max
diamonds, `abs`, an early return, a branch on a `bool` parameter, a nested
`if`, a two-diamond `clamp`, a three-way `sign`, `match` compare chains on
`u64` and `u8`, `if c { d } else { false }`, a `u8` zero test, a call on one
arm, a panic arm, a store on one arm) with LLVM and with trust-cg WITH
PROOFS REQUIRED, and callers with LLVM and with trust-cg (`no-proof-certs`,
the caller's `main` being outside the lane), in all four rlib x bin cells,
over ten boundary values per argument. At O0 every callee function replays
Valid (`rows=11..27 replay=Valid`), the trust-cg rlib promotes, and all four
cells print the oracle's 2500 lines (payload `s6_xback_O0.txt`).

### O1 and O2: a false mismatch, found and fixed

The payload `s6_xback_O1_O2_before_fix.txt` is the same matrix at O1 and O2 through the
census bridge. The proof-required rlib is refused, as expected where the
optimizer merged or if-converted the arms, but seven functions at each
level were refused with `[TCG-SOURCE-BOUND-X86-MISMATCH] ... block Block(0)
records successors [Block(1), Block(2)] where its jumps and fallthrough give
[Block(2), Block(1)]`: the branch-layout pass inverts a `jcc` and swaps its
fallthrough without reordering the block's recorded successors, and the
owner compared them in order. That lowering is correct; a mismatch
diagnoses a miscompile. The owner now compares them as a set (a missing or
extra edge is still named, `a recorded edge missing` in
`wrong_control_is_named_or_refused`). Fails-before:
the payload `fails-before/successor_order_before_fix.txt` is the slice-6 library gate
with the ordered comparison restored: the new
`optimized_slice_six_fixtures_are_judged_without_false_mismatches` (every
fixture through the real x86 optimizer at O1, O2 and O3) fails on
`EarlyReturn at O1`, and `slice_six_variants_hold_on_samples` on the
fallthrough variant, which now keeps the selector's successor order. With
the fix, 13 of the 25 fixtures build a theorem that holds on samples at
each of O1-O3 (`EarlyReturn`, `NestedIf`, `PairJoin`, `TrapArm`,
`PanicArm`, `CallThenBranch`, `LoadBranch`, the four switches other than
`SwitchBool`, and both selects) and 12 make no claim (arms merged or
if-converted, a row form outside the slice, or, since the review, a block
without the provenance correspondence); an earlier version of this report
said 14 and 11, a miscount the review reproduced three times.
The payload `s6_xback_O0_O1_O2_after_fix.txt` is the matrix re-run at O0, O1 and O2
through a bridge rebuilt with the fix (`7dd7c6761`, dylib
sha256 `39252592…`): no mismatch at any level; at O1 and O2
`match3`, `match_u8`, `checked_index` and `store_min` (and `abs_i64` in one
of its two O1 compiles) replay Valid and the others make no claim, so the
proof-required rlib is still refused there while the LLVM-rlib cells agree;
the O0 cells are unchanged (all four print the oracle's 2500 lines).

### Native O0-O3 evidence for exactly the credited code (`cross-backend/native/`)

Run by the integration review's orchestrator through the `7dd7c6761`
bridge: `s6_credited_native.py` compiles the matrix's callee crate once with
`x86-body-trace` to find the functions whose body theorem replays Valid at
each level, then builds a proof-required rlib of exactly those functions
(so its code is exactly the credited code) and runs the four rlib x bin
cells against the LLVM oracle (`s6_xback_orig.py` is `../s6_xback.py`
without its final `main()` call). At O0 all 16 are credited and all four
cells print the oracle's 2500 lines; at O2 and O3 `checked_index`,
`match3`, `match_u8` and `store_min` are credited and all four cells print
its 400 lines (payload `credited.txt`). At O1 `abs_i64` is credited too, but its
proof-required rlib is refused: it calls `core::num::wrapping_neg` out of
line at O1, and that callee has no credited body; without `abs_i64`
(`DROP_ABS=1`), the other four match in all four cells (payload
`credited_o1.txt`).

## Review fixes

An integration and no-exceptions review of `2fbf2548f` found no credit
route other than a Valid replayed theorem, and these defects; each fix has
a test that fails on the reviewed tree: the slice-6 library gate with the
fixed tests and `5c5389e2c`'s owner (the reviewed owner merged with `main`)
fails 5 of 13 tests (payload `fails-before/review_fixes_before_5c5389e2c.txt`):

```text
renamed_machine_blocks_are_paired_by_provenance: MinU64 renamed {...}: source-bound x86-64
  body mismatch: machine block layout is inconsistent: the machine's first block Block(3)
  is not the LIR entry block Some(Block(0))
path_conditioned_values_are_judged_by_the_theorem: call argument: source-bound x86-64 body
  mismatch: call 0 passes a different argument 0 than its LIR source (exact affine evaluation)
a_test_with_an_immediate_is_admitted_only_at_the_emitted_width: a 32-bit test with an
  immediate: an out-of-domain pair built a body theorem
a_renumbered_optimized_body_is_never_a_mismatch: O2: source-bound x86-64 body mismatch:
  block Block(1) (row None) transfers control to Some(Block(2)) where the source path
  continues to block Block(4)
wrong_control_is_named_or_refused: wrong arm value: source-bound x86-64 body mismatch: the
  machine returns a different value in result lane 0 than its LIR source (exact affine
  evaluation)
```


1. **Block ids are not a pairing at O1+.** `renumber_blocks_contiguous`
   (`x86_if_convert.rs`, `x86_cmov_swap.rs`, `x86_bounds_check_elim.rs`,
   called by `x86_block_merge.rs` too) renames the surviving machine blocks
   to `0..n` after a pass deletes some, so a machine block can carry another
   LIR block's id. Through the bridge,
   `fn dom(i: u64, n: u64) -> u64 { if i < n { if i < n { i } else { unsafe {
   core::hint::unreachable_unchecked() } } } else { 0 } }` at `-Copt-level=2
   -Zmir-opt-level=0` was refused with `[TCG-SOURCE-BOUND-X86-MISMATCH] block
   Block(1) transfers control to Block(2) where the source path continues
   to block Block(4)` while its `no-proof-certs` build matches LLVM. The
   owner now pairs blocks through the rows' TV-1 provenance stamps, which
   every pass carries with the row: a machine block lowers LIR block B when
   all its source-attributed rows are stamped with B, and the pairing needs
   one such block per LIR block, no other laid-out block, the entry
   lowering the entry, and each block's successors equal (through what they
   lower) to its LIR block's. Without that correspondence there is no
   claim, never a named mismatch; a one-path source with a `jcc`-free
   machine is the slice 1-5 chain again, id-free. Soundness never rested on
   the pairing (every paired step is a real machine transfer and the
   theorem states each `jcc`'s condition); it decided which machine path a
   source path was judged against, so a wrong pairing could only refute or
   name a mismatch, never credit. Tests: `a_renumbered_optimized_body_is_never_a_mismatch`
   (the repro's LIR exactly as the bridge hands it over, MIR block ids and
   layout `0, 1, 4, 5, 2, 3`, through the real O1-O3 optimizer: the
   reviewed owner names the same `Block(1) ... Block(4)` mismatch at O2; the
   fix makes no claim at O2 and O3 and builds an unrefuted theorem at O0 and
   O1) and `renamed_machine_blocks_are_paired_by_provenance` (every fixture
   with its blocks renamed by layout position and in reverse builds its
   byte-identical theorem; the reviewed owner refused the first with a
   layout mismatch). On the census's O0 modules, offline, both pairings bind
   the same 1813 of 3445 functions with byte-identical theorems and refuse
   the rest with the same text (the census probe over the dumped O0
   modules, run once with each owner):

   ```text
   functions 3445; owner in old: 1813, in new: 1813; both 1813; only old 0; only new 0
   same OWNER bound_rows line: 1813/1813
   smt2 files 1810 / 1810; same names True
   byte-different theorems: 0
   refusal text changed for 0 non-owner functions
   ```

   (1810 files for 1813 functions: three names collide after the probe's
   file-name sanitizing; both runs write the same 1810.)

   Through a bridge rebuilt from the fixed tree (`b4e9f8d1b`, sha256
   `0cca3bf3a17cf02b352d57552bc1b9a0d883c595f2e86a0ee5b2ef9a582ab58f`), the
   repro itself, proofs required, `-Zmir-opt-level=0`: `dom` replays Valid
   at O0 (`bound rows=25`) and O1 (`bound rows=10`; the crate compiles),
   and at O2 and O3 makes no claim (`the machine blocks do not correspond
   one to one with the LIR blocks: machine block Block(1) has no row
   attributed to a LIR instruction` at O2, `machine block Block(0) lowers
   rows of several LIR blocks` at O3), so the crate is refused with
   `[TCG-PROOF-465]`, never `[TCG-SOURCE-BOUND-X86-MISMATCH]`. (At O0 the
   crate is refused for core's `unreachable_unchecked::precondition_check`,
   a body with nothing to observe, not for `dom`.) The cross-backend matrix
   through the same bridge at O0, O1 and O2 names no mismatch: at O0 every
   callee function replays Valid and all four cells print the oracle's 2500
   lines; at O1 `abs_i64`, `checked_index`, `match3`, `match_u8` and
   `store_min` replay Valid and at O2 the last four, the rest make no claim,
   and the LLVM-rlib cells agree (outputs not kept in tree).
2. **The new gate row was red.** The `slice6::` filter matched the ignored
   fixture printer, which `matrix_results.py check-cargo-gate` counts as a
   skip. The printer now lives in `slice6_qualification`. The gate's exact
   command (`trust_cargo.sh test --locked -p trust-cg-verify --lib
   'x86_source_bound_body::tests::slice6::' -- --show-output
   --test-threads=1`) and parser, before and after (payload
   `fails-before/gate_row_slice6.txt`):

   ```text
   before: skipped: rc=0; 9 captured passes; 0 failed; 1 ignored; 0 runtime SKIPs; 4570 filtered; 1 suites; 0 incomplete suites   (parser rc=1)
   after:  pass: rc=0; 13 captured passes; 0 failed; 0 ignored; 0 runtime SKIPs; 4599 filtered; 1 suites; 0 incomplete suites    (parser rc=0)
   ```
3. **Provenance of this report.** Corrected above: the slice-6 bridge's base
   also carries `e6288b598`, and `trust_cg_rev` is `~/trust`'s pin.
4. **Wall time.** Corrected above.
5. **Fixture counts at O1-O3**: 13 hold and 12 make no claim, not 14 and 11.
6. **The affine refusal ignored the path condition.** It compares a value's
   two sides over all inputs, so a correct machine that returns 7 where the
   source returns `x + 7` on its `x == 0` path was named a `ReturnValue`
   mismatch, and likewise call arguments and stored values. It now names a
   mismatch only for a one-path body; on several paths the theorem judges.
   Test: `path_conditioned_values_are_judged_by_the_theorem` (the constant
   call argument, stored value and returned value on the `x == 0` path, alone
   and together, hold; the same rows with a wrong constant are refuted).
7. **`TestRI` width.** The owner modelled a 32-bit `TestRI` at 32 bits, but
   the encoder emits `test r/m64, imm32` (REX.W) for every register class.
   Only a 64-bit `TestRI` is admitted now (nothing emits `TestRI` today).
   Test: `a_test_with_an_immediate_is_admitted_only_at_the_emitted_width`.

The controls the provenance pairing turns from named mismatches into no
claim (a dead laid-out block, an extra machine branch, both edges of a
branch to one arm, a return before the path ends) and the wrong arm value
that the theorem now refutes instead of the affine refusal are updated in
`wrong_control_is_named_or_refused`; the extra machine branch left the
AY-replayed refutations (20, from 21).

An independent library-level credit attack on `2fbf2548f` ran 6,643 unique
mutants over 18 fixtures (`MinU64`, `MaxI32`, `AbsI64`, `NestedIf`,
`TwoDiamonds`, `EarlyReturn`, `TrapArm`, `PanicArm`, `Switch3`, `SwitchU8`,
`SwitchI32Neg`, `SwitchWide`, `SwitchBool`, `SelectU64`, `SelectI32`,
`BoolParam`, `U8Test`, `EdgeCopies`) x the plain selector, O1, O2, O3 and the
variant forms: swapped successors, inverted, signed/unsigned and
strict/non-strict codes on `jcc`/`setcc`/`cmov`, retargeted `jcc`s, deleted
compares, a flag writer before a `jcc` or `cmov`, `ud2` <-> `ret` and more.
3,501 were Unsupported, 460 Mismatch, and 2,682 built theorems (1,999
distinct: 1,603 CounterExample, 396 Valid); 709 were credited, and every
credited one is semantically equivalent per an independent concrete x86
interpreter (1,200 inputs x 2 seeds, with garbage upper bits). It found no
false Mismatch on the 44 real selector and optimizer outputs. Completeness
notes: 7 correct mutants are refuted because the theorem requires the
source's path (`setb` -> `setbe` where the operands are equal), and 7
correct synthetic mutants were named Mismatch (a `ret` after a diverging
call where the source traps, and a branch past a block that computes an
equal value; the provenance pairing turns the latter into no claim).

## Fails-before (`fails-before/`)

- payload `fails_before_main_915fff712.tsv`: a temporary probe (`make_probe.py`
  assembles it from the slice-6 fixture builders and `probe_tail.rs`; it
  is never committed as a test) run against `main`'s owner. Every slice-6
  fixture, variant, refutation mutant and control is refused, as `LIR
  source is not a bounded unconditional chain` or, for the selects, as a
  `Select` outside the domain: no slice-6 body built a theorem before. (The
  controls `a recorded edge missing` was added after that run; `main`
  refuses its LIR source, the unchanged `MinU64`, before looking at the
  machine.) The payload `fails_before_branch.tsv` is the same probe on this branch:
  every fixture and variant builds a theorem, each refutation mutant
  builds a theorem the sampled oracle refutes (three are named mismatches
  first) and every control ends as a named mismatch or an unsupported body.
- payload `review_fixes_before_5c5389e2c.txt`: the review fixes' fails-before
  ([above](#review-fixes)). Payload `successor_order_before_fix.txt`: the set
  comparison's ([above](#o1-and-o2-a-false-mismatch-found-and-fixed)).
- payload `mutants.txt` (the first version's rules, `00c860e40`; `make_probe.py`
  and `mutate.py` apply to that tree's files): each of seven walk rules
  disabled one at a time by
  `mutate.py` (one build, `TCG_S6_MUTANT` selects the rule), with the
  slice-6 library gate run under each. Every mutant fails at least one test:
  flags reset at a block boundary (`flags from another block` builds a
  theorem), a laid-out block no path reaches (`a dead laid-out block`
  builds a theorem), the machine's `jcc` literals in the claim (six tests,
  the refutations among them), an ALU flag writer's clobber (`flag clobber
  between cmp and jcc`), a call's clobber of the flags (`jump on flags set
  before a call`), a `ret` before the source path ends (still refused, but
  as `the return observes rax, which holds no defined value`) and a `jcc`
  whose fallthrough reaches its target (still refused, but as a control
  mismatch). The last two are therefore naming rules, not soundness guards,
  and a dead block is not a soundness issue either (the claims already
  force the machine onto the paired paths); the other four are load-bearing.

## Observed

- The slice-4 `host_qualification_replays_the_memory_body_theorems` failed
  once during this work, `SlotFoldedOffset` ending `(:reason-unknown
  (incomplete self-check-rejected))` while the host was loaded, on the
  byte-identical query that certifies at rest (the slice-5 report records
  the same); it passed on the rerun. The ABI-envelope test
  `envelope_theorems_certify_on_the_admitted_pair` fails on this host on
  every run here, on this branch (twice: `void_return_saves` return target
  byte 1) and on `main` `915fff712` (once, with this host's replay tools:
  byte 0), always `incomplete AY proof certificate ... unproved_steps=1`,
  while its golden-query test passes: a pre-existing gap of the admitted
  AY (sha256 `9a149c35…`) on that envelope, whose recorded
  `KNOWN_UNCERTIFIED` rows name another AY. Slice 6 does not build either
  query.

## Files

In tree (Markdown and reproducer sources):

- `core-x86_64-darwin-O0-proof-slice6/gap_table.md`: the census tool's gap
  table (home directory shortened to `~`, the census scratch directory to
  `<scratch>`).
- `encoding/`: the offline census probe (`census_probe.rs`, `probe.sh`) and
  the replay and respelling scripts (`replay_dir.py`, `coi.py`,
  `coi_dir.py`, `sexp.py`, `variants_batch.py`).
- `cross-backend/`: the matrix script `s6_xback.py`; `native/`, the review
  orchestrator's credited-only native run (`s6_credited_native.py`,
  `s6_xback_orig.py`).
- `fails-before/`: the probe pieces and the mutation script
  (`make_probe.py`, `probe_tail.rs`, `mutate.py`).

Out of tree ([PAYLOADS.md](PAYLOADS.md)): the census row's provenance,
failed roots, body-trace gaps, promoted and newly-failing lists and bridge
digest; the encoding outcome tables and the O0 pairing comparison; the
cross-backend and native outputs; and the fails-before outputs.
