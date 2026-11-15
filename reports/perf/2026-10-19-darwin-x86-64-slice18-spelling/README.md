# Darwin x86-64 `library/core` — slice 18 (the canonical theorem spelling), 2026-10-19

Slice 18 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs` and
`x86_source_bound_body/split.rs`) changes how a theorem is spelled, never what
it states. The design and its measurement are in `~/tcg-scratch/s18-design/`
(README, DESIGN-DRAFT, RULING-DRAFT, `data/summary.md`): 125 of census-s17's
191 failed roots are bodies AY build 12713 does not certify within 30 s, 91 of
them single-query theorems, most of whose claims are true by the definitions
alone. This record holds the implementation in three stages, each its own
commit and ruling, the real-bytes measurement each was migrated on, the golden
migration and its review, the controls with their fails-before evidence, and
each slice's re-run qualification ledger.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-4a65bc3cf-ay12713` (baseline) | `main` `4a65bc3cf` | 12713 | `560cd0dd…` | 187 | 7958 s |
| `core-x86_64-darwin-O0-proof-slice18-ay12713` | this branch, `ab1f6051d` (slice 18 on `4a65bc3cf`) | 12713 | `f0731fdd…` | **114** | 4832 s |

**78 roots promoted, 5 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`).
The 78 are bodies bound on both sides that now replay Valid. The 5 newly
failing are AY timeouts of re-spelled theorems, never a credit; replayed
offline on a quiet host, 30 s budget unless noted (payload
`newly_failing/replay.out`):

| Root | AY 12713 | AY 13556 |
| --- | --- | --- |
| `i128::wrapping_sub` (the `SubU128` shape, single theorem) | timeout at 30 s and at 120 s | certified, 1.9 s |
| `TypeId::as_u128`, part 1 of 2 | timeout at 30 s; certified at 120 s in 37.4 s | certified, 25.3 s |
| `Big32x40::clone`, part 1 of 4 | certified, 0.45 s (the census's live solve timed out under load and the negative memo repeated it) | certified, 0.7 s |
| two `EscapeDebug` chain functions, part 1 of 4 | not replayed offline | not replayed |

The move of `QUALIFIED_AY` to build 13556, which follows this slice,
recovers at least the first two. Both rows were built by `census12713.sh`,
each bridge in its own tree, with no resource-budget refusal.

| Stage | Ruling | What it spells |
| --- | --- | --- |
| 1 | OD-187 | every single-query theorem whose source side is `true`, as slice 17 spells an in-bounds theorem (bit moves, value numbering, inlining, identities dropped), cascading to slice 16's part spelling, then the plain one; one claim suffices |
| 2 | OD-188 | the cascade's new first step: the same spelling with constant folding and the `bvsub`-zero identity |
| 3 | OD-189 | each slice-16 part spelled again: bit moves and a second value-numbering round |

Host: the shared x86_64 Mac (4 cores) of the slice-17 record, an AY landing
agent building at `-j2` beside this lane throughout (1-minute load 4-6);
every build ran through `scripts/trust_cargo.sh` with the local overlay
`x86-stage1-ay12713` (`targo --unverified`, `nice -n 19`, `-j2`; no proof
claim about any build). Replayer pair: AY 0.27.0 build 12713 with Clean
5f09e36c (`QUALIFIED_AY`, the overlay's `bin/ay` and `bin/clean`, Clean
binary SHA-256 `949365b6…`). Branch `feat/x86-body-slice18-spelling` from
origin/main `190b3e53d`, with origin/main merged as it moved (`ff44162f3`:
the trust-ir pin `6382da38` and main's deadline-bound qualification lanes).
Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md) binds each by size and
SHA-256.

## In short

| | stage 1 (OD-187) | stage 2 (OD-188) | stage 3 (OD-189) |
| --- | ---: | ---: | ---: |
| census-s17 single theorems certified, AY 12713, one-shot (of 91; 0 before) | 52 | 64 (72 when the deadline-bound `can_not_overflow` query makes it) | 64 |
| the same by the resident route | 51 | 63 | 63 |
| split bodies with every part certified (of 34; 0 before) | 0 | 0 | 9 |
| the 125 roots of the class, one-shot / resident | 52 / 51 | 64 / 63 | **73 / 72** |
| AY build 13556, singles one-shot / resident (for the coordinator) | 54 / 54 | 73 / 73 | 73 / 73 (the singles keep stage 2's bytes) |
| golden theorems changed (of 386; and of the 13 parts) | 184 | 104 | 0 (4 parts) |
| recorded gaps that certify now | 9 | 1 | 0 (1 unrefuted part refuted) |
| recorded gaps that join | 0 | 0 | 0 |

Every changed golden theorem and part is proved equivalent to its previous
spelling by z3 in both directions and an evaluation sweep; every rewrite is
swept against an exact SMT-LIB evaluator over every fixture and
wrong-lowering family; every wrong lowering stays refuted with a
counterexample (and slice 16's one unrefuted part becomes refuted); every
rule has a mutant that fails a control.

## The real bytes, before any golden moved

The design measured a Python re-implementation of the Rust spelling. AY's
outcome depends on exact bytes, so each stage was first re-dumped through the
real builder and replayed offline:

1. **A trust-ir dump of `core` from census-s17's own bridge**
   (`runs/s17.dylib`, `ac8424004`, trust-ir `dc2b8073`):
   `census/dump_core_ir.sh` runs trustc with the bridge and
   `dump-trust-ir=`, and stops it once the main CGU's module is written (no
   AY runs; 166 modules).
2. **The probe** (slice 16's `probe/x86_body_probe.rs`, built local only in
   `crates/trust-cg-verify/examples/`, never committed), restricted to the 125
   functions (`census/run_probe.sh`). **Control:** built on main without this
   lane's change (at `190b3e53d` and again at `ff44162f3`), it reproduces all
   361 census queries (91 single theorems, 270 parts) byte for byte
   (`census/compare_probe.py`).
3. **The replay**, sequential and `quiet.request`-aware
   (`replay/run_replays.py`, the design's driver over
   `~/tcg-scratch/ay-nd/runs/replay_nd.py`'s routes): one-shot (`ay -smt2 Q
   --strict-proofs --proof P --proof-format alethe`, then `clean cert
   verify-external`, 30 s each), then the resident leg (`ay --incremental`,
   whose `unsat` the bridge replays one-shot) on the queries the one-shot
   route certifies.

### Stage 1

The re-dump against the design's queries (ignoring the design's trailing
newline, which the bridge does not write):

| census single theorems | count |
| --- | ---: |
| the design's v17 or v16 query, byte for byte | 82 |
| the same assertion; the builder also declares unused argument registers (`e_rdi` ...; the Rust builder always declares a scalar argument's register in an untrimmed theorem, the Python only what is read) | 8 |
| `is_power_of_two`: a one-path theorem `(= S M)`, which the design's script re-spelled and the design (and the builder) keeps plain | 1 |

The parts (270) are unchanged, as stage 1 intends.

| route, AY 12713 + Clean, 30 s | design (Python bytes) | real bytes | today |
| --- | ---: | ---: | ---: |
| one-shot | 54 | **52** | 0 |
| resident, then one-shot | 53 | **51** | 0 |

For the coordinator, the same real bytes on AY main `ebde49de3` (build
13556, the resident-route and circuit-lane fixes; Clean 5f09e36c, the same
routes, `replay/chain_B_13556.sh`): **54 one-shot and 54 by the resident
route**, the 52 of build 12713 plus `cgu-0-1520` (`overflowing_add`, a timeout
on 12713, 3.0 s) and `cgu-0-2199` (Clean rejected 12713's proof; 17.6 s).
The slice stays qualified on build 12713.

The two the real bytes lose: `is_power_of_two` (above: today's spelling, a
Clean overrun at 30 s, as today) and `cgu-0-2202`, byte-identical to the
design's query, which certified there in 26.8 s of AY and timed out here: a
deadline-bound query, not a byte difference. No query that certifies in the
design's run certifies only there for a byte reason; no query that
certifies today stops (none certifies today).


### Stage 2

Census-s17's bodies re-dumped through the builder with OD-188's folded first
step (`probe-C`): 68 of the 84 single theorems the design's Python
fold-and-`bvsub`-zero spelling rewrites are its query byte for byte, 2 more
differ only by the unused argument registers' declarations, and 13 differ in
their assertion because the builder folds more than the Python did (a
concatenation of two constants, for one: the Python's rule order left
`(concat #x00 #x00)` unfolded when its extension identities were off); every
one of those 13 has the design's outcome. `is_power_of_two` stays one-path.
The cascade's later steps take the other 7 singles (2 slice-17, 5 slice-16
spellings), as the design's cascade did.

| route, AY 12713 + Clean, 30 s | design (Python bytes) | real bytes | stage 1 |
| --- | ---: | ---: | ---: |
| one-shot | 73 | **64** | 52 |
| resident, then one-shot | not run | **63** | 51 |

No single theorem stage 1 certifies stops certifying. Of the design's 73,
the real bytes lose `is_power_of_two` (one-path) and 8 of the 12 copies of
`can_not_overflow::<T>`: the twelve are one query, byte for byte, which AY
took 24-28 s on in the design's run and 26-30 s here, at loads 4-6 with this
lane's mutant runs beside it: four certify (26.3-29.4 s) and eight time out.
It is deadline-bound, not a byte difference; on a run where it certifies the
stage reaches 72 (on a quiet host, load 3, it certifies in 23.5-23.9 s, 3 of
3 runs). The census, whose negative memo replays one copy's outcome for all
twelve, will show it either way. On AY build 13556 (`ebde49de3`, for the
coordinator; `replay/chain_C_13556.sh`) the same bytes certify **73 one-shot
and 73 by the resident route**: all twelve `can_not_overflow` copies in
21.2-26.6 s, and `cgu-0-1520` as at stage 1.

### Stage 3

Census-s17's 34 split bodies re-dumped through the builder with each part
spelled again (`probe-D`): their 253 parts are the design's measured `v17p`
queries byte for byte, aligned by region (a part that empties renumbers the
rest, so the comparison maps each new part to its original region through
the design's record of which parts empty), and the same 17 parts empty. The
91 single theorems keep stage 2's bytes.

| route, AY 12713 + Clean, 30 s | parts certified (of 253) | split bodies with every part certified (of 34) |
| --- | ---: | ---: |
| before (stage 2: slice 16's parts) | (the design: 160 of 270 old parts) | 0 |
| one-shot | 164 | **9** |
| resident, then one-shot | 164 | **9** |

The design measured the same 9 bodies. With stage 2's singles, the class of
125 roots moves 64 + 9 = 73 on AY 12713 at load 4-6 (81 with the
deadline-bound `can_not_overflow` copies), 63 + 9 = 72 by the resident
route the census takes.

## Stage 1 (OD-187): the golden migration

Every one of the 14 golden files moves, as the design predicted to the
theorem. `TCG_X86_BODY_SNAPSHOT_WRITE=1` rewrote each (its test fails,
printing the new digest), each digest was pinned by hand, and each changed
theorem was reviewed by two independent checks against its old spelling
(`review/review_goldens.py`, the design's `smtq.py` evaluator and
`z3_equiv.py`): a 256-input evaluation sweep (equal claim values, every kept
definition equal to the old definition of its name) and z3 4.15.4 in both
directions (A: the old premises and the negation of the new premises with
equal claims; B: the new premises with the eliminated names' old definitions
and the negation of the old premises with equal claims).

| golden | theorems | changed (bit moves / part spelling) | kept: conjunctive / one-path | one claim left | definitions | bytes | old SHA-256 | new SHA-256 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `snapshots.smt2` | 65 | 9 (9 / 0) | 10 / 46 | 5 | 81 → 2 | 9258 → 4301 | `f06ba2d67278…` | `39c7194779fb…` |
| `memory_snapshots.smt2` | 35 | 16 (9 / 7) | 11 / 8 | 15 | 129 → 0 | 13677 → 5925 | `594d8c1ed893…` | `072f916a16a1…` |
| `slice5_snapshots.smt2` | 40 | 13 (11 / 2) | 12 / 15 | 11 | 144 → 1 | 14178 → 6248 | `2a5af3f931b5…` | `b5e0c8fdc8f7…` |
| `slice6_snapshots.smt2` | 25 | 23 (23 / 0) | 0 / 2 | 0 | 259 → 38 | 32181 → 17362 | `ac1853fe9522…` | `21969b669f6b…` |
| `slice7_snapshots.smt2` | 15 | 4 (4 / 0) | 10 / 1 | 1 | 61 → 5 | 8994 → 3548 | `f5e4c539bebf…` | `7a63bc1b62f6…` |
| `slice8_snapshots.smt2` | 22 | 4 (3 / 1) | 4 / 14 | 3 | 54 → 4 | 5478 → 1878 | `ea1102610f9e…` | `0a447cc39f02…` |
| `slice9_snapshots.smt2` | 15 | 14 (14 / 0) | 0 / 1 | 0 | 489 → 340 | 104125 → 79666 | `394a3d17a4e7…` | `478348efdd22…` |
| `slice10_snapshots.smt2` | 25 | 11 (10 / 1) | 2 / 12 | 7 | 128 → 9 | 21276 → 14180 | `668d5f6b65cd…` | `040671630059…` |
| `slice11_snapshots.smt2` | 36 | 24 (24 / 0) | 3 / 9 | 2 | 304 → 32 | 29219 → 14377 | `f4aa144e7903…` | `1a55291368bd…` |
| `slice12_snapshots.smt2` | 20 | 20 (20 / 0) | 0 / 0 | 0 | 101 → 62 | 28635 → 21667 | `6ecce29f4268…` | `bd73454d67d9…` |
| `slice13_snapshots.smt2` | 20 | 5 (2 / 3) | 10 / 5 | 4 | 45 → 0 | 4447 → 1864 | `f8f924fe2242…` | `2fea3df139c6…` |
| `slice14_snapshots.smt2` | 28 | 28 (28 / 0) | 0 / 0 | 1 | 319 → 64 | 46198 → 31730 | `6f1e3a64a1fa…` | `7f034d26a3bc…` |
| `slice15_snapshots.smt2` | 22 | 6 (6 / 0) | 5 / 11 | 1 | 81 → 0 | 8744 → 4365 | `15d951964213…` | `7d037264e29d…` |
| `arraygep_snapshots.smt2` | 18 | 7 (0 / 7) | 7 / 4 | 7 | 109 → 0 | 9414 → 3301 | `4616eedc1b3e…` | `144a12d55cde…` |
| total | 386 | 184 (163 / 21) | 74 / 128 | 57 | 2304 → 557 | 335824 → 210412 | | |

(Definitions and bytes are summed over the changed theorems.) The review:
184 of 184 changed theorems with 0 sweep mismatches and z3 UNSAT in both
directions (368 of 368). The spelling counts come from the builder itself
(`slice18::the_legacy_spelling_reproduces_every_golden_before_slice_eighteen`
prints each theorem's `Spelling`), and that test pins the historical
custody: the test-only legacy spelling (`with_legacy_spelling`, slice 17's
`ValueNumbering::InBounds`) re-renders all 14 old goldens byte for byte.
Old certificates, verdict-memo and negative-memo entries are keyed by query
bytes and simply miss; nothing is re-tagged, and the first census after
landing re-solves every x86 body theorem once.

## Stage 1: the controls

- **The sweep** (`slice18::canonical_spelling_preserves_every_fixture_theorem`,
  solver-free): every fixture of slices 1-17, ArrayGep and the bool sign
  extension, with the machine variants, and every wrong-lowering family (slices
  1, 4-17, ArrayGep, the bool sign extension, slice 16's control and size
  mis-models, slice 17's unbounded ones), each built canonically and with the
  cascade from its second step, against the plain spelling of the same pair,
  by an exact SMT-LIB evaluator written in the test (`exact_eval`, widths to
  128, division by zero as SMT-LIB defines it). On the final code: 420
  spelled fixture theorems and 392 spelled wrong-lowering theorems, 0
  mismatches; 377 of the latter are falsified on some sample, and keep that
  sample's value.
- **Construction controls on the plain spelling.** Tests that inspect how the
  claims are built (an item's width, the caller views, a merged byte's
  definition, the structural refusals of a tampered theorem) now read the
  plain spelling (`plain_theorem`), since the canonical spelling only
  re-spells those claims; each owner test re-runs the owner's own structural
  check (`owner_check`: the part rule for a spelled theorem), and the
  structural-refusal control asserts each tampered theorem is refused under
  both rules. The encoding evidence that restates a theorem (slice 1's
  UF-world and concatenated forms, slice 6's implies and case-split forms,
  slice 9's uninlined and untrimmed spellings) restates the plain spelling,
  so its recorded outcomes keep their meaning; all reproduce.
- **The solver-free body gate** (`x86_source_bound_body::tests::`, the
  qualification lanes skipped): 320 passed, 0 failed, 15 ignored.

## Stage 1: fails-before

`fails-before/mutate.py <worktree> 1` guards each rule behind
`TCG_S18_MUTANT=<name>`; one test build serves every mutant, and
`fails-before/run_mutants.sh` runs the solver-free body gate once per mutant
(the unmutated run: 320 passed). Every mutant fails a control:

| mutant | what it breaks | failing controls |
| --- | --- | --- |
| `bitnorm-other-operand` | `bit_normalized` concatenates adjacent extracts of two different terms as one extract | slice 16's `the_part_spelling_rewrites_only_by_identities` (no fixture concatenates two terms' adjacent extracts; stage 2's random-term sweep is the sweep that names it) |
| `unify-operator-only` | `unify_definitions` numbers a right-hand side by its operator and width | 75, the slice-18 sweep and every theorems-hold control among them |
| `drop-any-equation` | the spelling drops every equation claim, not only identities | 19: the sweep, slices 12 and 17's wrong lowerings no longer refuted, 14 goldens |
| `bitmoves-extract-offset` | an extract of an extract loses the inner offset | 8: the sweep, slice 8's theorems-hold and qualification controls, the goldens |
| `bitmoves-bvadd` | a definition that adds is substituted as a bit move (an exact substitution: bytes move, values do not) | 10: slice 17's `bit_moves_are_substituted_exactly`, 7 goldens |
| `no-cascade` | an emptied slice-17 spelling goes straight to the plain one | 8: the 6 goldens with a theorem the second step spells |
| `min-two` | a spelled theorem must keep two claims | 13: 11 goldens |
| `in-bounds-only` | only a theorem with an in-bounds claim is spelled (slice 17's predicate) | 17: 14 goldens, the sweep's coverage floor |
| `identities-stated` | an emptied spelling is stated with its identities, its check skipped | 65: the owners refuse (the outer structural check), every owner and theorems-hold control |

## Stage 1: qualification

Every tool-gated x86 body test, one per process (`census/qualify.sh` over
`census/tool_gated_tests.sh`'s 37 tests; an in-process session memo would
otherwise answer sibling tests), on AY 12713 +
Clean 5f09e36c, `TCG_X86_BODY_QUALIFY_AY` and `TCG_EXTERNAL_CLEAN_CHECKER`
from the overlay, `nice -n 19`, at 1-minute loads of 3-6, each test's replayed
queries kept (`TCG_X86_BODY_QUALIFY_DUMP`). The first run (37 tests) failed
exactly the six lanes whose recorded gaps certify now; with the tables updated
from that run, those six (and slices 1, 6 and 9's other lanes) pass:

| slice | recorded gaps before | after | moved |
| --- | --- | --- | --- |
| 1 | `MulI16`, `Mul/commuted` | the same | none (one-path theorems, unchanged bytes) |
| 9 | `Diamonds5`, `Diamonds6`, `GuardChain9`, `SwitchChain`, `LongArm`, `LongChain`, `CallJoin`, `LoadDag` | `LongChain` | seven certify, in 2.99, 3.97, 6.06, 3.95, 0.25, 3.01 and 4.18 s |
| 10 | `MulU64`, `MulPanics` | `MulU64` | `MulPanics` certifies in 4.7 s |
| 11 | `SubU128`, `MulU128`, `SlotU128` | `SubU128`, `MulU128` | `SlotU128` certifies in 2.6 s |
| 12 | `EarlyExit` | the same | none |
| 14 | `UdivConst`, `UremConst32` | the same | none |
| 16 | `LongChain` parts 1-3; unrefuted: the inverted branch's part 2 | the same | none (parts unchanged) |
| 4, 5-8, 13, 15, 17, ArrayGep, bool sign extension | none | none | none |

No gap joins any table. `SubU128` stays a timeout, as recorded (the design's
preview had it certifying at 27.8 s only in the old spelling). The six
remaining gaps whose bytes moved were replayed offline with a 300 s budget
(`set-option :timeout 300000`, one at a time) for their recorded tool output:
`MulU64` certifies in 68.4 s, `SubU128` in 138.6 s and `EarlyExit` in 70.1 s
(each proof Clean accepts); `MulU128`, `UdivConst` and `UremConst32` answer
`unknown` / `timeout` at 300 s. Every wrong lowering is refuted with a
counterexample in every lane, slice 17's mis-models included; slice 16's
inverted branch stays the one recorded unrefuted part.

The per-host records of `x86_64-unknown-linux-gnu` and
`aarch64-apple-darwin` were measured on the old spelling. Their lanes are
re-qualified only by a run on their own host; `SlotU128`'s two
`CERTIFIED_HERE_BY_HOST` entries were dropped as vacuous (it is no gap of the
table now, so every host holds it to certifying).

## Stage 2 (OD-188): the golden migration

Twelve of the 14 goldens move again (ArrayGep's and slice 15's do not: no
theorem there folds). Each changed theorem was reviewed against its stage-1
spelling exactly as in stage 1 (`review/review_goldens.py`): 104 of 104 with
0 sweep mismatches and z3 UNSAT in both directions (208 of 208).

| golden | theorems | changed against stage 1 | folded / slice-17 / slice-16 / plain / one-path | definitions | bytes | stage-1 SHA-256 | stage-2 SHA-256 |
| --- | ---: | ---: | --- | ---: | ---: | --- | --- |
| `snapshots.smt2` | 65 | 2 | 8 / 1 / 0 / 10 / 46 | 2 → 2 | 1998 → 1876 | `39c7194779fb…` | `a4e5c826cdc7…` |
| `memory_snapshots.smt2` | 35 | 5 | 9 / 0 / 7 / 11 / 8 | 0 → 0 | 2497 → 2036 | `072f916a16a1…` | `b1b7b2a7e954…` |
| `slice5_snapshots.smt2` | 40 | 6 | 11 / 0 / 2 / 12 / 15 | 1 → 1 | 3377 → 3196 | `b5e0c8fdc8f7…` | `16e1d2c77803…` |
| `slice6_snapshots.smt2` | 25 | 23 | 23 / 0 / 0 / 0 / 2 | 38 → 38 | 17362 → 15910 | `21969b669f6b…` | `d264c23281c2…` |
| `slice7_snapshots.smt2` | 15 | 4 | 4 / 0 / 0 / 10 / 1 | 5 → 5 | 3548 → 3316 | `7a63bc1b62f6…` | `6b3fdaed9079…` |
| `slice8_snapshots.smt2` | 22 | 1 | 2 / 1 / 1 / 4 / 14 | 2 → 2 | 654 → 597 | `0a447cc39f02…` | `2be134f07bbb…` |
| `slice9_snapshots.smt2` | 15 | 14 | 14 / 0 / 0 / 0 / 1 | 340 → 334 | 79666 → 73044 | `478348efdd22…` | `0a635a0af906…` |
| `slice10_snapshots.smt2` | 25 | 3 | 10 / 0 / 1 / 2 / 12 | 6 → 6 | 8559 → 2281 | `040671630059…` | `5447f01315e1…` |
| `slice11_snapshots.smt2` | 36 | 4 | 24 / 0 / 0 / 3 / 9 | 12 → 12 | 3684 → 3179 | `1a55291368bd…` | `91fbcb2c12ad…` |
| `slice12_snapshots.smt2` | 20 | 20 | 20 / 0 / 0 / 0 / 0 | 62 → 62 | 21667 → 20427 | `bd73454d67d9…` | `a006b6dc84f3…` |
| `slice13_snapshots.smt2` | 20 | 1 | 2 / 0 / 3 / 10 / 5 | 0 → 0 | 422 → 342 | `2fea3df139c6…` | `7b8a48e3b34e…` |
| `slice14_snapshots.smt2` | 28 | 21 | 28 / 0 / 0 / 0 / 0 | 46 → 46 | 27078 → 25281 | `7f034d26a3bc…` | `2d9eea931477…` |
| `slice15_snapshots.smt2` | 22 | 0 | 6 / 0 / 0 / 5 / 11 | 0 → 0 | 0 → 0 | `7d037264e29d…` | `7d037264e29d…` |
| `arraygep_snapshots.smt2` | 18 | 0 | 0 / 0 / 7 / 7 / 4 | 0 → 0 | 0 → 0 | `144a12d55cde…` | `144a12d55cde…` |
| total | 386 | 104 | 161 / 2 / 21 / 74 / 128 | 514 → 508 | 170512 → 151485 | | |

161 golden theorems take the folded step (57 of them unchanged against stage
1: nothing in them folds); two fall to slice 17's spelling (the folded one
fails the structural check). The legacy spelling still re-renders every
golden before slice 18 byte for byte. Stage 2 also adds a golden for the
parts, `slice16_parts_snapshots.smt2` (the 13 parts of the five slice-16 size
shapes, digest `acfc09b8…`), which stages 1 and 2 leave untouched and the
custody test pins at its legacy digest.

## Stage 2: the controls and qualification

- The fixture and wrong-lowering sweep now covers the folded step: 630
  spelled fixture theorems and 588 spelled wrong-lowering theorems, 0
  mismatches (564 of the latter falsified on a sample).
- `every_constant_fold_is_the_value_of_its_operator`: each folded operator
  over sampled constants (0, 1, all ones, the sign bit, the width, random)
  at widths 1, 7, 8, 16, 31, 32, 56, 63, 64, 65, 127 and 128, against the
  exact evaluator; each operator folds at least once, and an `ite`, a
  Boolean connective, an equation of equal constants and a node with a
  variable operand are never folded.
- `the_bvsub_zero_identity_is_exact`: either way round, at widths 1 to 128,
  nested with folds; an extract of a difference compared with zero, and a
  difference compared with another constant, are never rewritten to an
  equation of the operands.
- `the_normalizers_are_exact_on_random_terms` (4000 seeded terms over
  extracts, extensions, concatenations of adjacent extracts of one term and
  of two terms, arithmetic, an `ite` and `bvsub`-zero tests, widths 1 to 128,
  through `bit_normalized`, `bit_moves_normalized` and `folded`) and
  `the_definition_steps_are_exact_on_random_definitions` (600 random
  definition lists with renamings, constants and repeated right-hand sides,
  through `substitute_bit_moves`, `unify_definitions` and
  `folded_spelling`): every value kept, against the exact evaluator.
- `folded_claims_keep_every_claims_value`: 3000 random guarded and plain
  claims, their guard literals folding to `true`, to `false` or reading a
  variable, each kept to its value (or dropped only where it always holds).
- **The constant folds against z3**, an SMT-LIB implementation independent
  of this lane's evaluator: a local test (never committed; its source is a
  payload) prints every fold the fold sweep makes, 32651 of them, each
  checked `(assert (not (= <node> <folded>)))` unsat by z3 4.15.4 under
  push/pop (`review/z3_folds.py`): 0 not unsat, division and remainder by
  zero, signed division and shifts past the width among them. A planted
  wrong fold (`(bvudiv 5 0)` to 0) answers `sat`.
- The solver-free body gate: 324 passed, 0 failed (`gate-C4`, before the
  guarded-claims sweep and the parts golden were added; both are in the
  final gate below).

Qualification, one test per process, as for stage 1: slice 12's `EarlyExit`
certifies in 4.6 s and leaves `KNOWN_UNCERTIFIED_SLICE_TWELVE` (now empty;
re-run with the table updated: both lanes pass). Nothing else moves, every
wrong lowering stays refuted with a counterexample, and slice 16's inverted
branch stays the one recorded unrefuted part. `UdivConst` and `UremConst32`,
re-spelled again, still answer `unknown` / `timeout` at a 300 s budget. On a
quiet host (load 3) the twelve-copy `can_not_overflow::<T>` query certifies
in 23.5-23.9 s (3 of 3 runs).

## Stage 2: fails-before

`fails-before/mutate.py <worktree> 2` (with `mutants_stage2.py`), one build,
each mutant run over the 84 spelling controls of the body gate
(`fails-before/stage2_filters.sh`: every snapshot, refutation, theorems-hold and owner
test and the slice-18 tests; the unmutated run passes all 84):

| mutant | what it breaks | failing controls |
| --- | --- | --- |
| `fold-sub-as-add` | a constant `bvsub` folds to the sum | the fold sweep and both random sweeps |
| `fold-shift-modulo` | a shift by the width or more folds modulo the width | the fold sweep and both random sweeps |
| `fold-udiv-zero` | a division by zero folds to 0 (not SMT-LIB's all ones) | the fold sweep |
| `fold-equal-false` | an equation of equal constants folds to `false` | the fold sweep |
| `subz-through-extract` | a difference compared with zero through an extract becomes an equation of its operands | the `bvsub`-zero sweep |
| `subz-any-constant` | a difference compared with any constant becomes an equation of its operands | the `bvsub`-zero sweep and both random sweeps |
| `claims-drop-equations` | `folded_claims` drops every equation | 23: the fixture sweep, wrong lowerings of slices 6, 9, 10, 12, 14 and 17 no longer refuted, 11 goldens |
| `claims-drop-true-guard` | `folded_claims` drops an item whose guard has a literal folded to `true` | none of the 84 (no fixture has such a guard); `folded_claims_keep_every_claims_value`, added for it, fails |
| `no-fold-cascade` | an emptied folded spelling goes straight to the plain one | 9: 6 goldens |
| `fold-off` | the folded step is never taken | 14: 11 goldens |

Stage 1's sweep mutants, re-run on this code: the merge of two terms'
adjacent extracts (`bitnorm-other-operand`), which only slice 16's unit test
caught at stage 1, now also fails both random sweeps; an offset lost from an
extract of an extract fails the fixture sweep and both random sweeps; a bit
move that adds still moves goldens only.

## Stage 3 (OD-189): the parts golden and the controls

No single-query golden moves. The slice-16 parts golden (stage 2's
`acfc09b8…`) moves to `3be10a8e…`: 4 of its 13 parts change
(`DiamondChain` parts 1-3, 94/94/39 definitions to 93/93/37; `BigLoop` part
1, 25 to 24), each proved equivalent to its slice-16 spelling by z3 in both
directions and the 256-input sweep (`review/review_goldens.py`). The legacy
spelling skips the second spelling (`with_legacy_spelling`), and re-renders
the old parts golden byte for byte.

`every_part_spelled_again_is_its_slice_sixteen_part` states every earlier
fixture, cut at every block start, and every slice-16 size shape in parts in
both spellings, and checks that the canonical parts are exactly the legacy
parts spelled again by `respelled_part` (kept where the second spelling fails
the part check, dropped where it empties), in order: 507 legacy parts, 337
spelled again and swept against their legacy part (every claim value and
kept definition equal on 256 inputs), 170 emptied (each holding on every
sampled input), and 177 functions whose parts change; every inventory checks
(`check_x86_body_parts`, which the verifier and the exporter run, re-derives
the parts through the same `split_parts`). The slice-16 and slice-18 library
tests pass, 33 of 33.

## Stage 3: qualification and fails-before

Qualification, one test per process (`census/qualify.sh`), AY 12713 + Clean
5f09e36c, on the final code: every slice's lanes, 37 tests. 36 pass
unchanged, no recorded gap joining or leaving. Slice 16's host lane fails on
its recorded set only: the one recorded unrefuted part,
`a branch inverted mid-chain` part 2 (a `Timeout` at every stage before), is
now refuted with a counterexample, and the test asks for the record to be
reviewed. Its second spelling is the one the live replay's resident AY ran
out its 30 s on; refuted, it leaves `KNOWN_UNREFUTED_SLICE_SIXTEEN`, which is
now empty, and the lane re-run with the shrunk record passes. `LongChain`'s
three parts keep their bytes and stay the recorded timeouts of slice 9. Both
parts lanes (`host_qualification_replays_the_slice_sixteen_parts` and
`verifier_credits_every_bound_row_of_a_function_in_parts`) re-derive the
parts through `split_parts`, so they replay the re-spelled parts.

`fails-before/mutate.py <worktree> 3` (with `mutants_stage3.py`), one build,
each mutant run over the slice-16 and slice-18 library tests (33; the
unmutated run passes all 33):

| mutant | what it breaks | failing controls |
| --- | --- | --- |
| `respell-off` | no part is spelled a second time | the parts golden, the parts sweep, the custody test |
| `respell-no-bit-moves` | the second spelling skips the bit moves | none of the 33 (the parts golden's changes come from the second numbering round alone); `the_second_spelling_substitutes_the_bit_moves`, added for it, fails (`the byte claim is an identity once the bit moves are substituted`) and passes unmutated |
| `respell-drop-equations` | the second spelling drops every equation claim | the parts sweep (slice 16's refutation controls refute the statement either way, so they do not isolate a part) |
| `respell-empty-kept` | an emptied second spelling keeps the first instead of dropping the part | the parts sweep |
| `respell-fail-dropped` | a part whose second spelling fails the part check is dropped instead of keeping its first spelling | **none: an equivalent mutant**. No part tried reaches the branch: the second spelling's steps keep a well-formed part well formed (each name defined once, in order, at its width; every name declared; at least one claim), so the fallback is defensive |

The final solver-free body gate (`gate-D4`, a clean build of the stage-3
code, every `x86_source_bound_body::` library test but the solver-gated
qualification, credit and migration-pair lanes): 328 passed, 0 failed, 15
ignored. Against stage 2's `gate-C4` it adds the guarded-claims sweep and
the parts golden (stage 2) and the parts sweep and the bit-move unit test
(stage 3).
