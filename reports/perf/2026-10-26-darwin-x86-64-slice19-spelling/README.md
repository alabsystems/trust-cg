# Darwin x86-64 `library/core` — slice 19 (the full canonical spelling), 2026-10-26

Slice 19 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`,
`x86_source_bound_body/split.rs` and the new
`x86_source_bound_body/normal.rs`) extends slice 18's canonical spelling to
the "bound, not certified (AY)" residue of census-ay13556: 41 of its 106
failed roots are bodies bound on both sides whose theorem, or a part of it,
AY build 13556 does not certify within 30 s. All 41 still fail on main
`fc03f94f2` (census-s20, slice 20's row: 90 failed roots). The design and its
measurement are in `~/tcg-scratch/s19-ay-design/` (README, `data/`): 36
distinct failing queries, by operator class K 14 (a division by a constant
computed as a multiply-high), N 14, O 10 (a 128-bit product's overflow
check), D 2, P 1; its Python spelling recovers 32 of the 41 by the census
route, 39 with route changes. This record holds the implementation in three
stages, each its own commit and ruling, the real-bytes measurement each was
migrated on, the golden migration and its review, the controls with their
fails-before evidence, and the qualification ledger.

| Stage | Ruling | What it does |
| --- | --- | --- |
| 1 | OD-195 | the rest of slice 18's normalizer, ten new identity groups and `peel`, as one exact pipeline after slice 18's cascade, on single theorems (one-path theorems too) and on parts; a name for bits of a wider-than-64-bit term without a product stays a name |
| 2 | OD-196 | `magic`: a constant-divisor multiply-high rewritten to the quotient it computes, only when the Granlund-Montgomery inequality holds for the instance's own constants; the quotient range and `uremdef` |
| 3 | OD-197 | route changes, both fail-closed: an obligation with no verdict replayed again claim by claim; a resident AY deadline followed by one fresh replay, with the negative memo's schema v5 |

Host: the shared x86_64 Mac (4 cores), the coordinator's landing and census
lanes and this lane's builds beside the replays (1-minute load 3-8, stated
per replay in the result files); every build through
`scripts/trust_cargo.sh` with the `x86-stage1-ay13556` overlay (`targo
--unverified`, `nice -n 19`, `-j2`; no proof claim about any build).
Replayer pair: AY 0.27.0 build 13556 (`ebde49de3`) with Clean 5f09e36c, the
overlay's `bin/ay` and `~/clean-checker/bin/clean` (byte-identical to the
overlay's). Branch `feat/x86-body-slice19-spelling` from origin/main
`bf5d4b2c9`, moved onto `fc03f94f2` when slice 20 (OD-191 to OD-194) landed
before any commit of this lane: every measurement below the "real bytes"
heading is of the merged code, and slice 20's golden and fixtures are
re-rendered and swept with the others. Payloads are out of tree;
[PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.


| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-5d732f441-ay13556` (baseline) | `main` `5d732f441` | 13556 | `ce09ce31…` | 89 | 1264 s |
| `core-x86_64-darwin-O0-proof-slice19-ay13556` | this branch, `427a6f3d6` (slice 19 on `5d732f441`) | 13556 | `88feb28f…` | **48** | 2782 s |

**41 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
41 bodies bound on both sides that main's census did not certify now replay
Valid; the slice-19 census dumped 2 uncertified bodies (main's, 219). Both rows
were built by `census13556.sh`, each bridge in its own tree, with no
resource-budget refusal; the slice-19 bridge carries negative memo v5 and the
one-shot retry, so a resident-route timeout no longer sticks.

## In short

| | stage 1 (OD-195) | stage 2 (OD-196) | stage 3 (OD-197) |
| --- | ---: | ---: | ---: |
| the 41 roots certified, AY 13556, one-shot (0 on main) | 20 | 27 as first committed; **31** with the final wide-bits rule | **39** |
| the same by the census route (resident first) | 20 | 27; **31** | 37 without the retry, **39** with it |
| the design's Python spelling, census route | 19 (before `peel`) | 32 | 37 (without the retry) |
| golden theorems and part shapes changed (of 410) | 172 | 2 | 0 |
| whole core: census-s20-certified functions whose bytes change, still certifying one-shot (final code) | 1152 of 1152 | | |
| recorded gaps that certify now (final code) | 4: slice 1's `Mul/commuted`, slice 10's `MulU64`, slice 20's `U128LiveAcrossCut` and `U128CutParam` | | |
| recorded gaps that join (final code) | 0 | | |

Every changed golden theorem and part is proved equivalent to its previous
spelling by z3 in both directions and an evaluation sweep; every rewrite is
swept against an exact SMT-LIB evaluator over every fixture and
wrong-lowering family (slice 20's included); every wrong lowering stays
refuted; every rule has a mutant that fails a control or is shown
equivalent. The 2 roots left are `align_offset::<u8>` and
`u64::overflowing_pow`, one AY timeout each on a single claim.

## The real bytes, before any golden moved

AY's outcome depends on exact bytes, so each stage was first re-dumped
through the real builder and replayed offline:

1. **The trust-ir dump of `core`** census-s20 compiled (`runs/core-ir-s20`,
   the slice-16 probe's input since slice 18).
2. **The probe** (slice 16's `probe/x86_body_probe.rs`, built local only in
   `crates/trust-cg-verify/examples/`, never committed; `census/build_probe.sh`,
   `census/run_probe.sh`), restricted to the 41 roots. **Control:** built on
   main `fc03f94f2` without this lane's change, it reproduces census-s20's
   208 dumped queries of the 41 roots byte for byte
   (`census/compare_probe.py`). Stage 3's probe also writes each split
   obligation's claim queries (`S19_CLAIMS=1`).
3. **The replay**, sequential, one solver at a time, waiting before every
   query while `quiet.request` exists, a census runs or any other AY runs
   (`replay/replay19.py`, `~/tcg-scratch/ay-fix/land3/replay3.py`'s routes;
   `replay/measure.py` keys every result by the query's SHA-256 so a query
   is replayed once): one-shot (`ay -smt2 Q --strict-proofs --proof P
   --proof-format alethe`, then `clean cert verify-external`, 30 s each),
   then the resident leg (`ay --incremental`, whose `unsat` the bridge
   replays one-shot) on the queries the one-shot route certifies.

### Stage 1

The 41 roots state 203 queries (main: 208; parts the spelling empties drop
out). Before this lane moved onto main `fc03f94f2`, the same stage on
`bf5d4b2c9` dumped the same 203 queries but two, byte for byte the design's
measured Python spelling for every query but one part the builder keeps in
slice 18's spelling (the Python spelling broke its claim skeleton) and
unused argument declarations.

| route, AY 13556 + Clean, 30 s | roots certified (of 41) |
| --- | ---: |
| main (census-s20) | 0 |
| one-shot | **20** |
| resident, then one-shot | **20** |

**The 128-bit halves, and the one departure from the design.** A
whole-core check of stage 1's first spelling (`replay/regress.py`: every
census-certified function whose bytes change) found seven functions whose
theorem compares the halves of a 128-bit sum or difference. Replayed
one-shot on main's bytes and stage 1's:

| function | main | stage 1, design's inlining | stage 1 as committed |
| --- | --- | --- | --- |
| `i128::wrapping_sub` (the `SubU128` shape) | 2.3 s | **timeout** | 1.8 s |
| `i128::overflowing_add` | 2.0 s | 1.3 s | 1.7 s |
| `i128::overflowing_sub` | 3.5 s | 2.2 s | 2.6 s |
| `u128::checked_sub` | 2.9 s | 1.6 s | 3.3 s |
| `u128::overflowing_add` | 2.3 s | 1.6 s | 1.5 s |
| `u64::carrying_mul_add` (one of the 41) | timeout | not replayed | 4.9 s |
| `CarryingMulAdd::carrying_mul_add` (one of the 41) | timeout | 13.2 s | 13.2-14.3 s (same bytes) |

`i128::wrapping_sub`'s low-half claim is an identity under its definitions,
which leaves one claim, the high half of the 128-bit difference; the
design's pipeline inlines that half's single-use name, and AY 13556 does
not certify the inlined claim within 30 s (main's spelling: 2.3 s). The
same claim with the half named certifies in 1.5 s offline. So
`inline_single_use` keeps a name defined as an `extract` of a term wider
than 64 bits (`Terms::wide_bits`); keeping a name is exact. (The slice's
last code commit narrows the rule to terms without a product, below; the
seven functions' bytes on the final code are the last column's.) It
changes 2 of the 41 roots' 203 queries (both certify, as before the rule) and 10 of slice 11's
golden theorems (`AddU128`, `SubU128`, `NegI128`, `XorU128`, `NotU128`,
`MulU128`, `SelectU128`, `NarrowConst`, `SlotU128`, `ParamArrayU128`).

## Stage 1 (OD-195): the golden migration

Every golden but ArrayGep's moves, slice 20's included.
`census/golden_write.sh` re-rendered each through the stage's test binary
(`TCG_X86_BODY_SNAPSHOT_WRITE=1`) and pinned the printed digest, and every
changed theorem was reviewed against main's spelling by two independent
checks (`review/review19.py`, the slice-18 design's `smtq.py` parser and
evaluator): a 256-input evaluation sweep (equal claim values, every kept
definition equal to the old definition of its name) and z3 4.15.4 in both
directions (A: the old premises and the negation of the new premises with
equal claims; B: the new premises with the eliminated names' old
definitions and the negation of the old premises with equal claims). A parts
golden is compared per shape, the conjunction of its parts, since a part
the spelling empties renumbers the rest.

| golden | theorems (shapes) | changed | sweep or z3 failures | main SHA-256 | stage-1 SHA-256 |
| --- | ---: | ---: | ---: | --- | --- |
| `snapshots.smt2` | 65 | 6 | 0 | `a4e5c826cdc7…` | `d43b7611015f…` |
| `memory_snapshots.smt2` | 35 | 5 | 0 | `b1b7b2a7e954…` | `45a5b165ca2b…` |
| `slice5_snapshots.smt2` | 40 | 21 | 0 | `16e1d2c77803…` | `f573f241a3c8…` |
| `slice6_snapshots.smt2` | 25 | 22 | 0 | `d264c23281c2…` | `d96b1d589ede…` |
| `slice7_snapshots.smt2` | 15 | 4 | 0 | `6b3fdaed9079…` | `e8786dda1488…` |
| `slice8_snapshots.smt2` | 22 | 4 | 0 | `2be134f07bbb…` | `5b69318d28c2…` |
| `slice9_snapshots.smt2` | 15 | 13 | 0 | `0a635a0af906…` | `9ad06e11b73f…` |
| `slice10_snapshots.smt2` | 25 | 15 | 0 | `5447f01315e1…` | `88b63d82e6cb…` |
| `slice11_snapshots.smt2` | 36 | 16 | 0 | `91fbcb2c12ad…` | `ae5edd6cbc07…` |
| `slice12_snapshots.smt2` | 20 | 20 | 0 | `a006b6dc84f3…` | `18a4647c1c57…` |
| `slice13_snapshots.smt2` | 20 | 2 | 0 | `7b8a48e3b34e…` | `5e5cd1ef121b…` |
| `slice14_snapshots.smt2` | 28 | 23 | 0 | `2d9eea931477…` | `7e0ac184147e…` |
| `slice15_snapshots.smt2` | 22 | 1 | 0 | `7d037264e29d…` | `10a4d42227f5…` |
| `slice16_parts_snapshots.smt2` | 5 | 2 | 0 | `3be10a8e747e…` | `99bf2be7aa53…` |
| `slice20_snapshots.smt2` | 19 | 18 | 0 | `72b649229806…` | `cdb89e3a9b9c…` |
| `arraygep_snapshots.smt2` | 18 | 0 | 0 | `144a12d55cde…` | `144a12d55cde…` |
| total | 410 | 172 (30 one-path) | 0 (344 of 344 z3 UNSAT) | | |

The builder's own spelling counts come from
`slice19::the_slice_eighteen_spelling_reproduces_every_golden_before_slice_nineteen`
(it prints each theorem's `Spelling`), which also pins the historical
custody: the test-only `with_normal_groups(Groups::NONE)` re-renders every
golden of main, slice 20's included, byte for byte. Old certificates,
verdict-memo and negative-memo entries are keyed by query bytes and simply
miss; the first census after landing re-solves every changed theorem once.

## Stage 1: the controls

- **Each group alone, exhaustively**
  (`every_identity_group_is_exact_exhaustively`): every shape a group
  rewrites, every value of every input at widths 1 to 5, the normalized term
  keeping width and value: `ext` 524 rewritten instances, `fold` 2574,
  `bool` 56, `bit1` 32, `ovf` 8, `subz` 12, `arith` 60, `mullo` 10, `addlo`
  60, `shr` 28, `cmp` 36, `ovf2` 54, `sovf` 54, `mulpow2` 20, `itepull` 44,
  `peel` 32 (the measured inputs per group are in the gate log);
  `the_identity_groups_leave_what_they_do_not_rewrite` checks the near
  misses.
- **Random terms and theorems** (`the_full_normalizer_is_exact_on_random_terms`,
  `the_full_spelling_is_exact_on_random_theorems`,
  `the_definition_steps_merge_one_value_behind_two_names`): the whole
  pipeline against the exact evaluator.
- **Every fixture and wrong lowering through the builder**
  (`the_full_spelling_preserves_every_fixture_theorem`): every fixture of
  slices 1-17, ArrayGep, the bool sign extension and slice 20 with their
  machine variants, and every wrong-lowering family the production owner
  builds, canonical against the plain spelling of the same pair: 174
  conjunctive and 44 one-path fixture theorems, 211 conjunctive and 81
  one-path wrong-lowering theorems swept, 0 mismatches; 274 wrong lowerings
  falsified on a sample keep that sample's value.
- **Every part** (`every_part_spelled_canonically_is_its_slice_eighteen_part`):
  every earlier fixture cut at every block start and the slice-16 size
  shapes, 491 slice-18 parts, 264 spelled again and swept, 223 emptied (each
  holding on every sampled input), 160 functions changed.
- **The wide-bits name** (`a_single_use_name_for_bits_of_a_wide_term_is_kept`).
- **Construction controls on slice 18's spelling.** Tests that inspect how
  claims are built (slices 7, 11, 12 and 17 and the memory tests) read
  slice 18's spelling
  through `with_normal_groups`; each owner test re-runs the owner's own
  structural check.

## Stage 1: fails-before

`fails-before/mutate19.py <worktree> 1` guards each rule behind
`TCG_S19_MUTANT=<name>`; one test build serves every mutant, and
`fails-before/run_mutants19.sh` runs the 84 spelling controls
(`fails-before/controls.txt`: every snapshot, refutation, theorems-hold and
owner test and the slice-18 and slice-19 tests) once per mutant (the
unmutated run passes all 84). On `bf5d4b2c9`:

| mutant | what it breaks | controls failed |
| --- | --- | ---: |
| `ext-above-sign-zero` | zeros above a sign extension | 11 |
| `ext-low-kind` | the low bits of a sign extension rebuilt as a zero extension | 15 |
| `ext-concat-half` | an extract inside a concatenation's low half read from its high half | 30 |
| `ext-zero-high` | `concat(0, x)` a sign extension | 10 |
| `fold-distinct-true` | an equation of two distinct constants `true` | 6 |
| `bool-eq-false` | `(= x false)` is `x` | 9 |
| `bool-ite-negated` | `(ite c true false)` is `(not c)` | 1 |
| `bit1-polarity` | the one-bit encoding's polarity ignored | 13 |
| `ovf-offset` | the widening overflow test read from bit `n-1` | 1 |
| `subz-any-constant` | `(= (bvsub x y) C)` is `(= x y)` for any `C` | 1 |
| `arith-and-zero` | `x & 0` is `x` | 6 |
| `arith-sub-self` | `x - x` is `x` | 5 |
| `mullo-udiv` | the low bits of a quotient taken as the quotient of the low bits | 4 |
| `addlo-lshr` | the low bits of a logical shift taken from the operands' low bits | 1 |
| `shr-sign` | a logical right shift fills with the sign bit | 22 |
| `cmp-strict` | `bvule` as `bvult` | 13 |
| `cmp-or-direction` | `(or (bvult p q) (= p q))` as `(not (bvult p q))` | 11 |
| `ovf2-unchecked` | `ovf2`/`sovf` without checking that the extended term is the product's low bits | 1 |
| `sovf-top` | the sign test reads from bit `n`, not `n-1` | 7 |
| `mulpow2-off` | a product by `2^k` a shift by `k+1` | 16 |
| `look-window` | `look` reads the definition's low bits whatever the window | 9 |
| `itepull-mixed` | an `ite` of a zero and a sign extension pulled as the first's | 1 |
| `peel-window` | `peel` for any extract from bit 0 of a narrower width | 10 |
| `drop-any-equation` | `drop_identities` drops every equation | 29 |
| `claims-drop-true-guard` | an item whose guard has a literal normalized to `true` dropped | 1 |
| `moves-bits-add` (exact) | a definition that adds substituted as a bit move | 5 |
| `no-normal-parts` | parts not spelled again | 4 |
| `no-normal-one-path` | one-path theorems not spelled | 10 |
| `normal-unchecked` | a spelled theorem that fails the structural check kept | 7 |
| `ext-sext-of-zext` | the sign extension of a zero extension by 0 rewritten too | 0: **equivalent**, an earlier `ext` rule removes every extension by 0 |
| `cse-operand` | a term renamed to its first operand's name | 0: **equivalent**, the bottom-up rewrite renames the operand first |
| `cse-operator-only` (added for `cse`) | `cse` renames a term to an earlier kept name of the same operator and width | 24 |
| `wide-bits-off` (exact, on `fc03f94f2`) | a single-use name for bits of a wide term inlined | 4: its unit test, slice 11's golden and the two custody tests |

## Stage 1: qualification

Every tool-gated x86 body test, one per process (`qual/qualify19.sh` over
`qual/listed.txt`; an in-process session memo would otherwise answer
sibling tests), on AY 13556 + Clean 5f09e36c from the overlay
(`TCG_X86_BODY_QUALIFY_AY`, `TCG_EXTERNAL_CLEAN_CHECKER`), `nice -n 19`,
each test's replayed queries kept (`TCG_X86_BODY_QUALIFY_DUMP`), on stage 1
over `bf5d4b2c9` before the wide-bits rule: 40 tests, 34 passing unchanged;
the six failing were the lanes of three moves. Slice 1's `Mul/commuted` (a
one-path theorem, now spelled as its one claim) certifies in 0.07 s and
slice 10's `MulU64` in 2.9 s: both leave their tables
(`KNOWN_UNCERTIFIED`, `KNOWN_UNCERTIFIED_SLICE_TEN`, now without them).
Slice 11's `SubU128` timed out: the regression the wide-bits rule removes
(above). Every wrong lowering stayed refuted with a counterexample, slice
17's mis-models included. The qualification of the whole slice on its final
code is the last section of this record.

## Stage 2 (OD-196): the real bytes

`magic` and its two companions change 25 of the 203 queries (divisions by
a constant in `__fmt_inner`, `exp_u64`, `int_log10`, `grisu`,
`DecimalSeq`, `enc_16lsd` and `Duration`'s `Debug`):
2 of them certified before, 16 now (median 0.9 s of AY). The roots:

| route, AY 13556 + Clean, 30 s | roots certified (of 41) |
| --- | ---: |
| stage 1 | 20 |
| one-shot | **27** |
| resident, then one-shot | **27** |

The seven new roots: `Part::offset_from_unsigned`, `DecimalSeq::left_shift`,
`u32::__fmt_inner`, `u32`/`u64` `int_log10`, `grisu::format_exact_opt`
and `Duration`'s `Debug`. Nine changed queries still time out: parts of the
`u128`, `u64` and `i64` `__fmt_inner`, `exp_u64` part 8 and the two
`enc_16lsd` parts; stage 3 takes them claim by claim.

## Stage 2 (OD-196): the goldens and the controls

One golden moves: slice 14's (`7e0ac184147e…` to `48e7d6648a4b…`). With
the quotient in place of the multiply-high, every claim of `UdivConst` and
`UremConst32` is an identity under the definitions, so the spelling
empties them, and by slice 9's rule (never stated by identities alone) they
keep slice 18's spelling: both reviewed against stage 1's spelling as in
stage 1 (sweep 0 mismatches, z3 UNSAT both ways), and both stay recorded
AY gaps. No other golden changes.

- **The condition against its definition**
  (`the_magic_condition_is_the_granlund_montgomery_inequality`): for every
  `n` in 1..=8, every multiplier below `2^(n+3)` and every shift up to
  `2n+3`, `magic_divisor` is `Some(d)` exactly when `d = ceil(2^k/m)` has
  `1 <= d < 2^n` and `(2^n - 1)(m d - 2^k) < 2^k`, computed directly; and
  whenever it is, `floor(x m / 2^k) = floor(x / d)` for every `x`: 5652
  admitted instances, 960638 inputs; 1560 instances are exact without the
  condition holding (it is sufficient, not necessary: left unrewritten).
- **Every census instance** (`every_census_magic_instance_computes_its_quotient`):
  the eleven distinct multiply-high constants of the 41 roots (divisors 10,
  24, 100, 1000, 10^4, 10^5, 10^6, 10^10; plain and add shapes, 32 and 64
  bits), the replaced formula in exact integers, independently of the rule,
  against `floor(x / d)` on 2^16 seeded inputs and every input within one of
  a multiple of `d` at both ends of the range.
- **Exhaustive at small widths** (`magic_is_exact_exhaustively_at_small_widths`):
  every plain shape (`x` of 1 to 6 bits, extensions by 1 to 5, every
  constant, every window: wrapping products included), every add shape,
  the add shape behind a kept name, every quotient range and every
  remainder by a constant, normalized and checked on every input: 1439
  plain, 411 add, 111 add-through-a-name, 998 range and 120 `uremdef`
  rewritten instances.
- **The add shape's own `x`** (`the_add_shape_reads_its_own_x`): the add
  shape with another input in `y - h`, exhaustive over both inputs (700
  instances), keeps its value.
- **The controls where the inequality fails**
  (`a_wrong_magic_constant_or_shift_is_not_rewritten_and_stays_refuted`): the
  divide-by-10 constant plus or minus one, and its shift two or three less,
  are never rewritten, and a theorem equating each with the quotient by 10
  stays refuted (its spelling keeps a claim false on some input); the right
  constant and shift empty the theorem; one shift less computes the
  quotient by 5, is rewritten to it, and the theorem stays refuted.

## Stage 2: fails-before

`fails-before/mutate19.py <worktree> 2`, one build, each mutant over the 88
spelling controls (`fails-before/controls2.txt`; the unmutated run passes
all 88), on `bf5d4b2c9`; the two marked `fc03f94f2` ran in the merged
build (`mutate19.py all`, `fails-before/controls2b.txt`: the 88 and the two
tests added after them):

| mutant | what it breaks | controls failed |
| --- | --- | --- |
| `magic-unchecked` | the Granlund-Montgomery inequality skipped: any `d = ceil(2^k/m)` below `2^n` | 12, the condition test and the small-width sweep among them |
| `uremdef-swapped` | a remainder by a constant defined as its quotient | 12 |
| `range-unbounded` | the quotient range without its bound | 1 (the small-width sweep) |
| `magic-add-other-x` (`fc03f94f2`) | the add shape's `x - h` not checked to read the multiplied `x` | 1: `the_add_shape_reads_its_own_x`, added for it |
| `magic-wrap` | the plain shape's no-wrap check off | 0: **equivalent** |
| `magic-high-bits` | the plain shape's high-bits check off | 0: **equivalent** |
| `magic-wrap-high` (`fc03f94f2`) | both off | 0: **equivalent** |
| `magic-add-window` | the add shape read through any window `[hi:lo]` | 0: **equivalent** |
| `magic-no-names` (exact) | `magic` does not look through kept names | 0: completeness only; on every fixture `peel` exposes the multiply-high first |

The four equivalent mutants are equivalent by argument, not by a missing
control: an extract `[hi:lo]` inside the product's width `W` reads the same
bits of the product wrapped to `W` bits and of the exact product, which is
`floor(x C / 2^lo) mod 2^(hi-lo+1)`; under the inequality that is
`floor(x / d) mod 2^(hi-lo+1)`, the quotient's low bits, which
`quotient_as` states (the add shape's sum is exact, so its windows are the
same). So the checks only narrow what `magic` rewrites; they stay as
defence in depth, and the ruling does not count them as trusted.

## Stage 3 (OD-197): the route changes

### (a) The claim split

After the existing spelling, a replayed obligation (the theorem, or a part)
whose whole replay is neither Valid nor refuted is replayed again claim by
claim. `split::claim_parts` cuts it mechanically: one obligation per
distinct claim, over the cone of the obligation's definitions that claim
reaches, named `<name> | claim i of m`; none for a one-path theorem, a single
claim (or one repeated) or more than 64. Each claim passes the part check.
The claims are replayed serially through the same route, stopping at the
first without a Valid replay; the obligation is credited only when EVERY
claim certifies (an AY Alethe proof Clean accepts), refuted when one claim
is, and otherwise keeps its whole replay's outcome. The export records which
obligations were credited claim by claim and publishes their claims in their
place; every consumer re-derives them (`check_x86_body_claims`).

**The real bytes.** Stage 3's probe (`S19_CLAIMS=1`) wrote, for every split
obligation of the 41 roots, its claim queries (1984 in all); the whole
queries are stage 2's, byte for byte. `replay/claims_seq.py` replayed the
claims of every whole query that does not certify one-shot, in order,
stopping at the first that does not certify, as the bridge does:

| | count |
| --- | ---: |
| distinct whole queries (theorems or parts) that do not certify at stage 2 | 21 |
| credited claim by claim (every claim certifies) | **19** |
| claim replays (one-shot), median / largest AY time | 202, 0.23 s / 10.2 s |
| stopped: `align_offset::<u8>` (claim 15 of 25), `u64::overflowing_pow` (claim 8 of 15) | 2 |

The resident leg of every certified claim (135 distinct claim queries) then
ran as the census's first route does: 133 answer `unsat`, and the two claim
queries 9 of parts 8 and 9 of `i64::from_ascii_radix` (byte for byte
`isize::from_ascii_radix`'s) time out at 30 s on the resident route while
the one-shot route certifies them in 4.7 and 4.4 s: the design's §3.3,
which (b) answers.

| route, AY 13556 + Clean, 30 s | roots certified (of 41) |
| --- | ---: |
| stage 2 | 27 |
| one-shot, claim by claim | **39** |
| the census route without (b): resident, then one-shot, claim by claim | 37 |
| the census route with (b) (a resident deadline followed by one one-shot replay) | **39** |

The design's measurement predicted the same 39 one-shot and 37 by the
census route without (b). The two left are AY timeouts of single claims of
the two theorems above. Cost: a theorem or part that times out whole now
pays the resident deadline, the one-shot retry (b) and then its claims: on
these 41 roots, 21 such queries at about 60 s each and 202 claim replays
(median 0.2 s, plus Clean), against 30 s each before; on the final code
(below) 14 such queries and 134 claim replays (median 1.1 s).

### (b) One fresh replay after a resident deadline, and the negative memo v5

For the x86-64 body owner's queries only (the theorem, its parts, its
claims: `SourceBoundReplay::fresh_after_resident_timeout`), a resident AY
deadline no longer ends the replay: the query is replayed once by the
one-shot route, with a new budget, which alone produces the exact proof
Clean must accept. Every other owner keeps the resident deadline as its
conclusive timeout. The design measured the resident route timing out on
per-claim overflow queries in 15 of 15 runs that the one-shot route
certifies in 2.8-4.6 s (§3.3).

The coordinator's census of main `bf5d4b2c9` drifted 106 → 108 from two
roots answered `negative memo (AY not run): AY TIMEOUT`
(`u64::leading_zeros`, `Big32x40::clone` part 2): a resident-route timeout
that used its CPU budget was recorded, and the memo key does not separate
the routes, so every later replay of those bytes skipped AY on both routes;
with (b), such an entry would also have withheld the fresh retry. The memo
is now consistent with the route:

- a replay's `Timeout` is recorded only when EVERY deadline it saw used its
  budget in CPU time (the memo's existing rule, 90% of the budget in the
  solver process group's CPU time); a body query's replay sees the resident
  deadline AND the fresh retry's, so both routes must have held the
  processor for their budgets;
- a fresh retry that certifies credits and deletes any entry; one starved by
  the host records nothing;
- the schema moves to v5 (`tcg-source-bound-negative-memo-v5`, per-box
  directory `source-bound-negative-v5`): v4 entries, recorded under the
  resident-only policy, are never read; the key carries the owner's route
  flag, and the replay protocol description (`source-bound-replay-v6`, part
  of every key) states the retry.

## Stage 3: the controls and fails-before

On the real replay path (request capture,
`live_source_bound_replay_explained`, the exact-query funnel), with a fixture
AY and Clean (`x86_source_bound_body_negative_memo_tests.rs`); the resident
route on, the fixture's resident server computing in eight processes of its
group until its 500 ms deadline:

- `a_resident_timeout_the_fresh_replay_certifies_credits_and_records_nothing`:
  one resident server, one fresh replay; every covered row credited with a
  reusable report, every row exported; no negative entry.
- `a_timeout_on_both_routes_is_remembered_and_answers_without_ay`: both
  routes time out using their budgets; one `timeout` entry with the larger
  expiry's CPU time (at least 450 ms); the next occurrence runs no AY on
  either route and returns the same rows.
- `a_resident_timeout_whose_fresh_replay_was_starved_is_solved_again`: the
  fresh replay times out waiting; nothing recorded; the next occurrence
  solves again on both routes.
- `an_obligation_every_claim_of_which_certifies_is_credited_claim_by_claim`
  and `an_obligation_one_claim_of_which_does_not_certify_is_not_credited`:
  a slice-16 body in parts whose one part's whole replay is uncertified and
  whose claims each certify is credited with a reusable report, each export
  carrying the claim record, which checks and publishes the claims in the
  part's place; with its second claim uncertified the replay stops there
  and nothing is credited or exported.
- `the_store_format_is_strict`: a v4 entry (and v1 to v3) is foreign.
- `ay_bridge::tests::test_resident_timeout_replays_fresh_when_the_owner_asks`:
  a resident deadline is followed by exactly one fresh start.
- The claim split's library tests: `every_claim_split_is_the_conjunction_of_its_claims`
  (645 obligations of every fixture, wrong lowering and every-block cut,
  2019 claims, each claim part checked, the conjunction's value equal to the
  obligation's on 256 inputs), `a_claim_split_refuses_what_it_cannot_split`,
  `the_claim_by_claim_credit_rule`,
  `an_export_credited_claim_by_claim_publishes_its_claims` (a claim missing,
  a short record, a foreign claim each refused).

`fails-before/mutate19.py <worktree> all` (one build on `fc03f94f2`), each
mutant over these 23 controls (`fails-before/controls3.txt`; the unmutated
run passes all 23):

| mutant | what it breaks | controls failed |
| --- | --- | --- |
| `claims-drop-last` | the last claim of a split never stated (credit without it) | 2: the split's sweep and its refusal test |
| `claims-any-valid` | an obligation credited at its first Valid claim | 3: the credit rule, both real-path claim controls |
| `claims-record-unchecked` | a published claim record not re-derived | 1: the export test (a claim missing, a short record, a foreign claim accepted) |
| `fresh-retry-off` | (liveness, main's route) a resident deadline ends the replay | 4: the three resident-route memo controls and `ay_bridge`'s retry test |
| `fresh-expiry-unnoted` | the one-shot route's deadline not noted: a resident deadline alone records a timeout | 4: the starved-retry control and three one-shot memo controls |
| `memo-any-exhausting` | a timeout recorded when ANY deadline used its budget | 1: the starved-retry control |
| `memo-reads-v4` | a v4 entry read | 1: `the_store_format_is_strict` |

Every stage-3 mutant fails a control. The coordinator's two cases each have
a fails-before: with the retry off (main's route), the resident-deadline
control whose one-shot replay certifies credits nothing and records a
timeout, and the both-routes control replays nothing one-shot; the
starved-retry control fails when either the one-shot deadline is not noted
or any one used deadline suffices.

## The wide-bits rule without products (the slice's last code commit)

Stage 2's real bytes fell five roots short of the design's v19p spelling
(27 against 32): `enc_16lsd::<23>` and `::<7>`, the `u64` and `usize`
`__fmt_inner` and `exp_u64`. Their failing queries differed from the
design's certifying ones only by names the wide-bits rule kept: the high
halves of 128-bit products (the multiply-highs of their divisions by a
constant), whose definitions kept the 128-bit products in the query after
`magic` had rewritten every use of them. The rule now keeps a name only for
bits of a wide term that holds no product (`Terms::wide_bits`); a half of a
128-bit product is inlined, as the design does. Re-dumped through the
builder on the final code (`redump/s3c`):

| | first form (stages 1-3 as first committed) | final code |
| --- | ---: | ---: |
| queries of the 41 roots that differ | | 10, each byte for byte stage 2's bytes before the rule (the design's) |
| roots certified whole, one-shot (stage 2's spelling) | 27 | **31** (design: 32) |
| whole queries that fail one-shot / credited claim by claim | 21 / 19 | 14 / 12 |
| claim replays (median AY) | 202 (0.23 s) | 134 (1.1 s) |
| roots certified one-shot, claim by claim | 39 | **39** |
| by the census route without / with the retry (b) | 37 / 39 | 37 / **39** |
| the seven 128-bit add/sub functions | all certify | the same bytes |
| goldens | | slice 11's `MulU128` returns to its spelling before the rule (`ae5edd6cbc07…` to `95df1a8b970a…`) |

Two of the ten are deadline-bound on this host: `u128::__fmt_inner` part 4
certifies in 29.5 s and the `u64`/`usize` part 2 in 27.4 s; where they time
out, their claims certify (stage 3). `exp_u64` part 8 still times out whole
and is credited claim by claim. The changed golden theorem is reviewed
against main's spelling as in stage 1 (slice 11: 16 changed theorems, 0
sweep or z3 failures). The product case is in the rule's unit test, and the
first form fails it and slice 11's `MulU128` golden by construction
(`fails-before/mutate19.py`'s `wide-bits-products` names it). On the final
code the slice-19, slice-18, slice-11 and golden tests pass (59 of 59); the
fixture sweep spells 172 conjunctive and 44 one-path fixture theorems and
211 and 81 wrong-lowering theorems with 0 mismatches, and the parts sweep
262 parts (225 emptied, 158 functions changed).

## The whole core (final code)

`replay/regress.py`: the probe over every function of the `core` trust-ir
dump on main `fc03f94f2` (`all/base20`) and on the final code (`all/s3c`);
every function whose theorem bytes change, with its census-s20 outcome
(the census's body trace). 1195 functions change; the census certified 1152
of them, whose 1571 new queries (1071 distinct) were replayed one-shot on AY
13556 + Clean, 30 s: **all 1152 still certify, none lost**. The resident leg
was not replayed for them: with stage 3's retry a resident deadline, an
`unsat` or a bare `unknown` is followed by the one-shot replay, so the
census route certifies what the one-shot route does.

## Qualification of the final code

Every tool-gated x86 body test, one per process (`qual/qualify19.sh` over
`qual/listed.txt`, 43 tests, slice 20's three lanes included), on AY 13556
+ Clean 5f09e36c from the overlay, `nice -n 19`, at 1-minute loads of 2-5,
on the final code (the stage-3 tree with the wide-bits rule without
products). 40 pass unchanged; the three that fail are the lanes of records
that move, each a gain:

| slice | record | before | final code |
| --- | --- | --- | --- |
| 1 | `KNOWN_UNCERTIFIED` | `MulI16`, `Mul/commuted` | `MulI16` (`Mul/commuted` certifies in 0.07 s: a one-path theorem now spelled as its one claim) |
| 1 | `PRESERVED_TAIL_OUTCOMES` (encoding evidence) | the commuted add with the tail: `unknown` / `proof-trusted` | `Verified` |
| 10 | `KNOWN_UNCERTIFIED_SLICE_TEN` | `MulU64` | empty (`MulU64` certifies in 2.9 s) |
| 11 | `KNOWN_UNCERTIFIED_SLICE_ELEVEN` | `MulU128` | the same; `SubU128` certifies in 3.1 s (the wide-bits rule) |
| 14 | `KNOWN_UNCERTIFIED_SLICE_FOURTEEN` | `UdivConst`, `UremConst32` | the same (slice 18's spelling, OD-196) |
| 20 | `KNOWN_UNCERTIFIED_SLICE_TWENTY` | `U128LiveAcrossCut`, `U128CutParam` (Clean rejected an `equiv_simplify` step of AY's proof) | empty: both certify, in 3.8 s and 0.2 s |
| 9, 16, 20 | deadline-bound and parts records | `LongChain`, slice 16's `LongChain` parts, slice 20's three variable `I128` shifts | the same |

No gap joins any table. Every wrong lowering of every lane is refuted
(291 refutation lines name a counterexample; slice 16's lanes report each
mis-model `refuted=true`, and the in-parts refutations of slices 16 and 20
refute a later part), slice 17's and slice 20's mis-models and the envelope
mutants included. The records were updated from this run only and the three
lanes re-run on the rebuilt tests: all three pass (`qual/final-rerun`). The
per-host records of `x86_64-unknown-linux-gnu` and `aarch64-apple-darwin`
were measured on earlier spellings and are re-qualified only by a run on
their own host.

The other gates on the final code: the solver-free body gate (every
`x86_source_bound_body::` library test but the qualification, credit and
migration-pair lanes) 375 passed, 0 failed, 16 ignored; the `ay_bridge::`,
`source_bound_negative_memo::`, `source_bound_replay::`, `verdict_db::` and
`function_request::` library tests 311 passed and 16 failed, the same 16
that fail on main `fc03f94f2` built and run the same way (13 `ay_bridge`
tests whose floating-point and array queries AY 13556 does not certify, and
3 that hand this overlay build a fixture checker, which it refuses by
design); `trust-cg-lower --lib` 2113 passed, 0 failed; `trust-cg-codegen
--test x86_source_bound_body --test must_refuse_corpus` both pass (5 and 5,
with the overlay's AY and Clean), and again after merging origin/main
`5d732f441`, whose `trust-cg-irmid` change reaches codegen;
`scripts/check_fmt.sh`, `scripts/check_documentation.py --check` and
`scripts/full_test_matrix_hosts.py --check` clean. `targo tippy` could
not run on this host: the installed Trust package's (6808) refuses the
`compiler_timeout_secs` field of the pinned AY dependency's manifest before
linting, and the overlay's `targo` has no `tippy`; the two touched packages
are not linted here.
