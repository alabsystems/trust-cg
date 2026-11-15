# Darwin x86-64 `library/core` census — slice 12 (loops cut at their headers), 2026-10-05

Slice 12 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) admits loops. A
source whose CFG is reducible is cut at its loop headers; each region
between cut points is a DAG stated with slice 9's machinery, and every edge
into a header states the cut-point relation. This record holds the
measurement that chose the scope, the theorem and its soundness argument,
the controls and their fails-before evidence, the mutation robustness probe
and the census row. Host: the x86_64 Mac of the
[slice-11 census](../2026-10-03-darwin-x86-64-census-slice11/README.md)
(4 cores, 16 GB, shared with other agents' builds and censuses), native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, `targo --unverified` (no
proof claim about any build). The work was qualified first on the replayer
pair of its base, AY 0.27.0 build 10530 with Clean 5f09e36c, and then, once
main moved the x86 qualification host to AY build 12713 (`b1b0b9de0`) through
local overlay toolchains (ruling OD-85,
[AY 12713 requalification](../2026-10-05-darwin-x86-64-ay12713-requalification/README.md)),
requalified on that pair; each section names the pair it ran on. The census
bridge is built against the overlay (`~/tcg-scratch/build_bridge.ay12713.sh`)
and runs on the root overlay's `trustc`: `-Ztrust-verify=off`, O0,
`-Cpanic=abort`, one CGU, proofs required (the bridge default),
`x86-body-trace` and `x86-body-dump`. Nothing here is a
completion claim. Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md)
lists each with its SHA-256, and this README states the numbers they carry.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-slice13-ay12713` (baseline: slice 13's row, `main` `360eecafa`'s owner) | `90608b684` | 12713 | `01fa4c3a…` | 493 | 6253 s |
| `core-x86_64-darwin-O0-proof-slice12-ay12713` | this branch, `5bc8bd533` (slice 12 on `360eecafa`) | 12713 | `2af4a7f1…` | 443 | 8447 s |
| `core-x86_64-darwin-O0-proof-main-f6dcad152-ay12713` (landing baseline) | `main` `f6dcad152` | 12713 | `856d8260…` | 447 | 10433 s |
| `core-x86_64-darwin-O0-proof-slice12-landing-ay12713` | this branch merged onto `f6dcad152`, `fca48f987` | 12713 | `f9d3f9b9…` | **373** | 5998 s |

**Landing row: 74 roots promoted against main `f6dcad152` (447 to 373),
0 newly failing, 0 named mismatches, 0 bound bodies refuted (Census,
"The landing row").** The earlier row on slice 13's base promoted 54 and
had 4 roots newly failing, each with a theorem byte-identical to main's (a
timing victim). The census also found a false refutation in an
earlier bridge, a loop-carried `bool` register whose upper bits the header
left free; the fix (clean loop-carried registers) is part of the theorem
below, with its controls and mutants.

## The class, measured first

On the slice-9 census (`runs/census-s9b`, 1166 failed roots), 161 failed
roots name a function the body trace refuses with "LIR source control flow
is outside the acyclic domain: a loop", 163 functions in all
(`census/loop_roots.py`). The probe (`probe/x86_body_probe.rs`, mode
`--loops`, added here) read each of them from the slice-9 dump of `core`'s
trust-ir (`runs/core-ir-s9`, 88 modules) and printed its loop structure
(`census/loop_profile.py`; payloads `loops_main.tsv`, `loop_profile.txt`):

| | |
| --- | --- |
| functions | 163, all reducible (every back edge's target dominates its source) |
| loops per function | 1 loop: 144; 2: 10; 3: 5; 4: 3; 5: 1 |
| nesting depth | 1: 156; 2: 5; 3: 2 |
| loops in all | 196: 179 with one latch, 17 with 2 to 5 |
| blocks per loop | 3 to 85 (median 7) |
| exits per loop | 1 to 48 edges (median 4: most are panic paths) |
| calls in the loop | 179 of 196 loops (an iterator's `next`, a formatter) |
| memory in the loop | 143 loops access private slots and incoming memory, 36 private slots only, 11 incoming memory only, 6 neither |
| header parameters | none: 52 loops (all state in private slots); `I64` only: 85; with an `I8`/`I16`/`I32`/`bool`: 55; with an `I128`: 4 |
| other operations | 152 functions run only slice 1-11 operations in their loops; 11 divide (`Udiv`/`Urem` and `GuardDivZero`) |
| machine | every function's O0 machine has the provenance block correspondence |

So **calls and private memory carried across iterations are the class**:
179 of the 196 loops call a function, and 179 read or write a private
slot, 52 of them keeping every loop-carried value in one (an `Iterator`'s
state in a stack slot, advanced by `next(&mut it)`); the iterator slot
usually escapes to the call inside the loop. Nesting and multiple latches
are rare but present.

**Scope chosen**: every reducible CFG, nested loops and several latches
included, calls and incoming and private memory in the loop under the slice
3, 4 and 7 models carried across iterations, every integer, pointer and
`bool` loop-carried value up to 64 bits (and a float's bit pattern, which
the same rule admits and no fixture carries); refused by name: an irreducible cycle, a loop headed by
the entry block, a header entered from more than one edge outside its loop,
an `I128` loop-carried value and one an edge gives a private stack address
(and, after the merge with slice 13, a byte a loop changes that holds a
stored private address). Division and the other operations outside slices
1-11 stay refused by their own rules.

## The theorem

The owner's module documentation ("Loops (slice 12)") is the full
statement; this is its summary.

**Cut points and regions.** `source_cfg` finds the retreating edges of a
depth-first walk; each must be a back edge (its target dominates its
source, Cooper-Harvey-Kennedy dominators) and no target may be the entry
block. `natural_loops` builds each header's natural loop (the union over
its latches). The cut points are the entry block and the headers, and the
region of a cut point (`source_regions`) is every block a run reaches from
it before it reaches a cut point again. A region is a DAG (a cycle would
pass a header), and an edge into a cut point ends the region's run (a CUT
EDGE). Each region is stated with slice 9's machinery: guards `c{H}x{B}`
relative to the region's run, joins merged by the edges' guards, slice 3,
4 and 7's call, memory and escape models. The adapter lowers a header's
block arguments to `Copy` rows before the `Jump` into it (in order, with a
temporary when the copies form a cycle); `edge_copy_count` takes those
trailing copies out of the block and the region's cut edge runs them, in
order, to define the header's parameters on that edge.

**The relation.** At header `H` the source and the machine share a free
input per parameter (`x{H}v{i}`) and per header byte (`x{H}b{slot}o{off}`,
a private byte some edge into `H` leaves other than the entry edge does).
The parameter's machine register is the destination of the machine copy
that the TV-1 stamp names as the LIR copy of that parameter on `H`'s one
entry edge (`loop_pairing`; refused by name: no such copy, a callee-saved
or narrower register, two parameters in one register). At `H` the
register's low bits are the parameter (`ParamRoot::template`) and the bits
above it a free input of its own (`x{H}t{i}` under the psABI walk,
`x{H}c{i}` under the clean-bool walk). The stated bits are the
parameter's: 64 for `I64`/`F64`/a pointer, 32 for `I32`/`F32`, 8 or 16 for
`I8`/`I16`, and for a `bool` 32 (the clean carrier, 0 or 1) under the
clean walk and 8 under the psABI walk (the caller's bits 8 and up are
garbage in a `bool` argument register). On every cut edge into `H`, under
that edge's guard, the theorem states each parameter's value on the edge
equal to the low bits of its register at the end of the edge's machine
walk, and each header byte's source byte equal to the machine's. A
parameter whose register every edge into the header leaves zero above the
parameter's own bits (judged from the term's shape, through the machine's
named definitions: `zero_above`) is assumed to hold exactly the
zero-extended parameter, with no free input above it. That assumption is a
greatest fixpoint: it is dropped, and every region walked again, when some
edge breaks it, and by induction over a run's visits of the header it holds
at each (the census found why it is needed; see Census).

**What a region may assume, checked.** Every other value, register and
byte the region reads is what the entry edge brought:

- a source value is defined once (only the header's parameters are
  redefined, by the edge copies);
- a machine register some edge into `H` writes and no parameter pairs is
  `RegValue::Carried`: reading it is a named refusal ("which its loop
  carries paired with no loop-header parameter"), so the machine's
  loop-carried registers are exactly the source's parameters;
- a private byte some edge changes is a header byte on both sides; a byte
  the machine's loop changes and the source's does not is refused ("the
  machine changes private stack slot … which its LIR source does not"), as
  is a slot the machine lets escape where the source does not;
- a header parameter an edge gives a value slice 7's retention rule taints
  (derived from an escaped slot) is tainted at the header.

The header assumptions (tainted parameters, header bytes, escaped slots,
written registers) are a fixpoint over every edge into each header: each
round only grows them, and more than 64 rounds is a named refusal.

**Escapes at joins.** Slice 9 refused a join of paths on which different
private slots escaped. Slice 12 needs it (a loop's header joins its entry
edge, where the iterator slot has not escaped yet, with its back edges,
where it has), so a slot that escaped on some path into a join or a header
is escaped after it, on both sides. On a path on which it had not escaped,
every later call observes its bytes (an item both sides must state equal)
and redefines them as that call's free inputs. The run's real bytes, which
a callee that could not reach them leaves unchanged and which that item
makes equal, are one value of those inputs, so the theorem only gains
claims.

**With slice 13.** Slice 13 landed on main first and edits the same owner:
a private address stored as data (`SlotByte::Address`, the machine byte's
`frame`), the same escaped union at a DAG join (closed under the addresses
the slots hold), the stack argument areas, the C memory routines as calls
and scalar atomics. The merge (`9d6308215`) keeps both slices' rules, and
slice 12 adds four seams for slice 13's: a byte a loop changes that holds a
stored private address is a named refusal on both sides (an address is
tracked, never a free input a header assumes, as at slice 13's join); a
machine edge into a header with an outgoing argument area open is refused
(the selector opens and closes one around a single call); a header's
escaped slots are closed under the stored addresses on both sides; and the
machine's byte comparison at a header includes the stored address. The
control `a_stored_address_a_loop_changes_is_a_named_refusal` and the mutant
`header-address` cover the first; the other three are reached by no
selector output (an outgoing area never spans a block, and the closure and
the comparison only refuse).

## The claim and its soundness

**Claim** (OD-84 in `docs/decision-record.md`). For every run of the
source, terminating or not, the machine runs the paired path of each
region instance with an equal world trace (calls with their arguments and
observed bytes, incoming accesses) and ends the same way: equal return
bits, or a trap. A source run that never ends is matched by a machine run
that never ends, with the same trace. trust-ir's `behaviour_refines`
counts divergence as an outcome, so the claim is no weaker than the
refinement the source's semantics asks for; the theorem does not prove
termination, and does not need to.

**Soundness**, by induction over the region instances of a run. At the
start of an instance of `H`'s region the two states satisfy the relation
(the cut edge that entered stated it), every value and register the
region assumes from the entry edge still holds what it held when the loop
was entered (nothing changed it: the checks above; a nested loop's entry
is inside one iteration of the enclosing loop) and the worlds are equal
(the traces so far are). So the actual pair of states is one assignment of
the theorem's free inputs: the header inputs are the actual parameters and
bytes, the entering instance's inputs its actual values, and each call or
load site's input is its result in this instance (a region is a DAG, so a
site runs at most once in an instance). The region's claims hold of that
assignment, so the instance ends at an exit with equal observables, or at
a cut edge, where the relation holds for the next instance. A region's
claims are a conjunct of their own, universally quantified over every
input it shares with other regions (`forall` distributes over `and`), so
one theorem states every region. A machine that loops where the source
exits (or the reverse) takes a different edge out of some instance, which
the paired edge guards refute.

**Trusted, in addition to slices 1-11.** The natural-loop analysis and the
regions; the meaning of the adapter's edge copies (run in order); the
checks that what a region assumes is unchanged on every edge into its
header (term for term); that a run between two visits of a header runs
only its loop's blocks (the region construction); and the escape
over-approximation at joins and headers.

## Qualification

**Fixtures** (`x86_source_bound_body_slice12_tests.rs`, real adapter and
selector output; `LoopShape`): a counting loop, a sum below a bound,
Fibonacci (three carried values), a swap of two carried values (a copy
cycle the adapter breaks with a temporary), a carried `bool` toggled by
`xor`, a carried `u8` counter, a call per iteration, a load per iteration
from incoming memory, a store per iteration, a counter kept in a private
slot, nested loops, a loop with an early exit, two loops in sequence, a
`Switch` in the loop, a do-while, an iterator slot that escapes to the
call in the loop, a trap in the loop, a bound kept in a private slot, and
(added after the census, below) a `bool` the loop computes and passes to a
callee each iteration.
Host qualification
(`host_qualification_replays_the_slice_twelve_body_theorems`), on the
merged tree (`9d6308215`, slices 12 and 13 with the AY move) and the
qualified pair, AY build 12713 with Clean 5f09e36c through the overlay
(payload `qualification_12713.log`, on `55e42a730`): **18 of the 19
certify**. `EarlyExit`
is the recorded gap (`KNOWN_UNCERTIFIED_SLICE_TWELVE`): it times out at the
30 s deadline, and offline with a 200 s budget it certifies after 171 s and
Clean accepts the proof (payload `earlyexit_long.tsv`). Its body multiplies
the counter by 3, which the selector computes as `lea r, [r + r*2]`: the
word-level multiply class of slices 1 and 10, not the loop. All 20 wrong
lowerings (`slice_twelve_refutations`) get an AY counterexample.
`verifier_credits_every_bound_slice_twelve_row_with_the_replayed_body_theorem`
credits every covered row of the 18 certified shapes (loop bodies and the
`jcc` of every edge, back edges included) as body-theorem Formal, the
functions are promotable and their exports bind the ABI; every covered row
of every refutation fails; `EarlyExit`'s rows stay `Unverified`, never
credited and never failed.

Before the AY move, on the branch's base pair (toolchain AY 0.27.0 build
10530, payload `qualification_b10530.log`), 16 of the first 18 certified:
`StoreFill` and `EarlyExit` left one unproved step in AY's certificate
(`proof_gate` class PENDING(solver-capacity)), and the same 20 refutations
got counterexamples. Build 12713 certifies `StoreFill` in under a second.

**Offline, by size** (the slice-12 owner before the merges, over the
slice-9 dump of `core`, `probe/x86_body_probe.rs`; queries `q2/`, AY
`--strict-proofs` with Clean, `census/replay_dir.py` and
`census/size_rates.py`, `census/size_outcomes.py`; payloads `replay_q2.tsv` on build 10530 and
`replay_q2_12713.tsv` on build 12713). The owner binds 80 functions main
refused, 59 in the loop class and 21 in the escape-join class, and none is
satisfiable on either AY:

| Class | Bound rows | Bodies | Certify, build 10530 | Certify, build 12713 | Other outcomes on build 12713 |
| --- | --- | ---: | ---: | ---: | --- |
| loop | 0-99 | 16 | 16 | 16 | |
| loop | 100-199 | 15 | 13 | 15 | |
| loop | 200-299 | 19 | 4 | 19 | |
| loop | 300-399 | 5 | 1 | 3 | 1 timeout, 1 proof AY cannot render |
| loop | 400-512 | 4 | 0 | 1 | 2 strict self-check rejections, 1 timeout |
| escape join | 200-299 | 6 | 4 | 6 | |
| escape join | 300-399 | 9 | 2 | 5 | 4 timeouts |
| escape join | 400-512 | 6 | 0 | 3 | 2 timeouts, 1 trusted step |
| **all** | | **80** | **40** | **68** | |

On build 10530 the bodies above 200 rows were AY rejecting its own proof
(OD-72's class); build 12713's word-level certification takes every loop
body under 300 rows. Neither outcome depends on the loop encoding.

## Controls and fails-before

The library gate (`x86_source_bound_body::tests::slice12::`, 10 tests, no
AY call) holds every control (20 fixtures on the final tree):

| Test | What it checks |
| --- | --- |
| `owner_builds_every_slice_twelve_shape_over_its_regions` | every fixture is admitted with a loop and its theorem holds on the structured sampler |
| `every_slice_twelve_refutation_is_refuted` | each of the 20 wrong lowerings builds a theorem the sampler refutes |
| `a_register_the_loop_writes_is_never_assumed_unchanged` | a register the latch overwrites (the bound's, with the counter) and no parameter pairs is a named refusal when read, never the entry value |
| `a_private_byte_only_the_machine_changes_in_a_loop_makes_no_claim` | a latch that stores the counter over the slot the source keeps its bound in is refused, never assumed unchanged |
| `a_value_carried_from_after_an_escape_stays_tainted` | a loop-carried pointer a call returns once a slot escaped is tainted at the header, so the load through it is refused |
| `an_entry_header_and_an_irreducible_cycle_are_named_refusals` | a back edge into the entry block, and a cycle no block dominates |
| `a_stored_address_a_loop_changes_is_a_named_refusal` | (the merge with slice 13) a loop that stores another private address into a slot is refused at its header, never assumed |
| `every_header_input_the_theorem_reads_is_declared` | header inputs are declared exactly where the query reads them, each names a header, and the fixtures read every kind (`v`, `t`, `c`, `b`) |
| `slice_twelve_smt2_is_canonical_per_shape` | the pinned golden digest of every fixture's theorem, independent of the function's name |
| `loop_theorems_are_deterministic` | building a pair again gives the same theorem |

Slice 12 also changed three earlier controls: slice 9's join of different
escapes is now admitted (`a_join_of_different_escapes_escapes_on_every_path`:
its merges are non-empty and its theorem holds on samples), and slice 6's
and slice 9's loop refusals now use an irreducible cycle (a counting loop
is admitted).

`fails-before/mutate.py` guards each slice-12 rule behind
`TCG_S12_MUTANT=<name>` in a scratch copy of the owner, and
`fails-before/run_mutants.sh` runs the library gate's `slice12::` filter
and the two slice-9 controls slice 12 changed, once per mutant from one
build. On the final tree (`0cfb5189b`, the owner restored afterwards;
payload `mutants.txt`) every one of the 20 mutants fails at least one
control; the targeted control is named first:

| Mutant (the rule disabled) | Controls that fail |
| --- | --- |
| none | none (12 pass) |
| `no-back-edge-relation` (the relation stated only on a header's entry edge) | `every_slice_twelve_refutation_is_refuted` ("a wrong increment": the wrong lowering's theorem holds), digest |
| `no-entry-relation` (not on the entry edge) | the refutations ("a missing first iteration" holds), digest |
| `no-header-bytes` (no private byte becomes a header byte) | `owner_builds_…` (`SlotCounter` refused: the machine changes slot 0 where the source no longer does), the refutations ("a slot counter advanced by the wrong step" makes no claim), the header-input test, determinism, digest |
| `no-machine-byte-check` | `a_private_byte_only_the_machine_changes_in_a_loop_makes_no_claim` |
| `no-written-roots` (a register the loop writes keeps its entry value) | `a_register_the_loop_writes_is_never_assumed_unchanged` |
| `no-param-taint` | `a_value_carried_from_after_an_escape_stays_tainted` |
| `no-header-escape-union` | `owner_builds_…` (`EscapeLoop` refused: the machine lets slot 0 escape where the source does not), the refutations ("a slot read after the loop as its value before it" makes no claim), 5 in all |
| `join-escape-refusal` (slice 9's rule back) | `slice9::a_join_of_different_escapes_takes_their_union` |
| `parallel-edge-copies` (edge copies read the state before all of them) | `owner_builds_…` (`Swap`: a header parameter undefined on the back edge), 4 in all |
| `no-edge-copy-temps` | `owner_builds_…` (`Swap`: "redefines an SSA value"), 5 in all |
| `psabi-bool-32` (a `bool` at 32 bits under the psABI walk too) | `owner_builds_…` (`BoolToggle`'s correct stream refuted: the psABI caller's bits 8 and up), digest |
| `full-width-relation` (every register stated at 64 bits) | `owner_builds_…`, the header-input test (no `t`/`c` input read), digest |
| `pairing-copy-source` (the register the entry copy reads) | `owner_builds_…` (`CountUp` refused: its entry copy reads an immediate), 5 in all |
| `no-entry-header-check` | `an_entry_header_and_an_irreducible_cycle_are_named_refusals` |
| `no-irreducible-check` | the same, and `slice9::loops_and_the_size_bounds_are_named_refusals` |
| `one-round` (the header fixpoint stops after one round) | `a_value_carried_from_after_an_escape_stays_tainted` (admitted), `owner_builds_…` (`SlotCounter`'s theorem fails), digest |
| `header-address` (the merge: a stored private address in a byte the loop changes) | `a_stored_address_a_loop_changes_is_a_named_refusal` (admitted) |
| `no-clean-registers` (no header assumes a register zero above its parameter) | `owner_builds_…` (`BoolCarriedToCall`'s correct stream refuted: the census's false refutation), digest |
| `no-upper-bound` (a register is clean only bit by bit) | `owner_builds_…` (`ByteBoolCarried`'s correct stream refuted: `(byte + 255) >> 8`), digest |

Five mutants fail by refusing a correct fixture rather than by a wrong
verdict (`parallel-edge-copies`, `no-edge-copy-temps`,
`pairing-copy-source`, `no-header-escape-union` on its machine side, and
`no-header-bytes`); each disables a rule the admission needs, and a
refusal is the fail-closed outcome. The two rules the relation rests on
(the relation on each kind of edge) and the three that keep a region's
assumption honest (written registers, machine-only bytes, carried taint)
fail a control on the verdict; the clean-register rules fail by refuting a
correct stream, the incompleteness they remove. The first 17 mutants ran
on the branch before the merges too (`2316cdeac`, payload
`mutants_premerge/`), with the same outcome but for the join mutant's
control, then slice 9's former refusal under its old name.

## Mutation robustness

`robustness/x86_source_bound_body_slice12_robust_tests.rs` is a diagnostic
test, ignored and not part of the tree's test modules. To run it, plug it
in with a temporary `#[path]` module beside `slice12` in
`x86_source_bound_body_tests.rs` (the path is
`../../../reports/perf/2026-10-05-darwin-x86-64-census-slice12/robustness/x86_source_bound_body_slice12_robust_tests.rs`),
then run `ROB12_NO_REPLAY=1 fails-before/qualify.sh <log>
x86_source_bound_body::tests::slice12_robust:: --ignored`. Without
`ROB12_NO_REPLAY` the run also replays every theorem with AY and Clean and
asks the verifier for credit (`ROB12_CAP=3` keeps three mutants per class
and stream).

The probe mutates the real machine streams of the slice-12 fixtures: O0
selection, plus the x86 optimizer's output at O1-O3 where it differs (75
bases for the 20 fixtures of the final tree). Fourteen mutation classes cover the control flow (C1-C5,
C9, C10: a branch or exit condition, swapped successors, a retargeted,
extra or removed edge, a trap swapped with a return, a branch value's
condition) and the values the loops carry (C6: a loop-carried copy that
reads another register; C7: a compare operand or bound; C8: a dropped row;
C11: an increment or an initial value; C12: two loop-carried copies'
registers swapped; C13: a back-edge copy into another register). Each
mutant is judged by the owner, by the library gate's solver-free sampler,
and against an independent concrete interpreter of the LIR and of the
pre-RA stream that runs the loops (400 random argument vectors and directed
boundary vectors, every constant of either stream and its neighbours, under
both `bool` caller conventions; `step(p)` decrements the 8 bytes at `p`, so
a loop that calls it ends).

A loop makes the ground truth's own bound part of the judgment. The source
runs at most 2,000 LIR instructions and the machine at most 40,000 rows: a
machine that has not ended where the source has is wrong. Where the source
has not ended, the machine runs to 8,000 rows; if it ends, the source runs
again to eight times the rows the machine ran (a nested loop does quadratic
work on a modest bound). A vector on which the machine ends and the source
still has not is UNDECIDED: the source might end later with the same
result, or (a signed bound compare at a bound of 2^63 or more) run for 2^63
iterations. A mutant with an undecided vector and no wrong one is counted
apart. An earlier version (its log not kept) skipped every vector on
which the source had not ended, and so called the signed-for-unsigned
bound compares correct, which are wrong exactly where the source runs 2^63
iterations (the theorem refuted every one); the undecided column replaced
it. A fixed retry pool then left four nested-loop mutants undecided, and
the retry proportional to the machine's rows resolved them (payloads
`robustness_no_replay_first.log` without a retry, `_second.log` with the
pool).

**Sampler only** (final tree `0cfb5189b`, 20 fixtures, every mutant;
payload `robustness_no_replay_merged.log`). GT-wrong splits the mutants
the ground truth finds wrong by how slice 12 judged them (refused / named
mismatch / theorem refuted by the sampler / theorem NOT refuted):

| Class | Mutants | Owner refuses | Named mismatch | Theorem | Sampler refutes | GT-wrong: refused / mismatch / refuted / **not refuted** | GT-correct but refuted | GT n/a | Undecided: refuted / **holds** |
| --- | ---: | ---: | ---: | ---: | ---: | --- | ---: | ---: | --- |
| C0 original | 75 | 42 | 0 | 33 | 0 | 0: 0 / 0 / 0 / **0** | 0 | 19 | 0: 0 / **0** |
| C1 branch or exit condition changed | 391 | 290 | 0 | 101 | 77 | 186: 122 / 0 / 64 / **0** | 1 | 123 | 39: 12 / **0** |
| C2 successors swapped | 143 | 102 | 0 | 41 | 41 | 109: 68 / 0 / 41 / **0** | 0 | 34 | 0: 0 / **0** |
| C3 edge retargeted | 595 | 595 | 0 | 0 | 0 | 454: 454 / 0 / 0 / **0** | 0 | 113 | 0: 0 / **0** |
| C4 extra edge | 388 | 388 | 0 | 0 | 0 | 143: 143 / 0 / 0 / **0** | 0 | 81 | 0: 0 / **0** |
| C5 edge removed | 151 | 151 | 0 | 0 | 0 | 94: 94 / 0 / 0 / **0** | 0 | 53 | 0: 0 / **0** |
| C6 loop-carried copy from another register | 194 | 77 | 3 | 114 | 100 | 149: 53 / 3 / 93 / **0** | 1 | 17 | 8: 6 / **0** |
| C7 compare operand or bound changed | 339 | 206 | 0 | 133 | 132 | 255: 123 / 0 / 132 / **0** | 0 | 75 | 5: 0 / **0** |
| C8 row dropped | 401 | 255 | 113 | 33 | 22 | 297: 162 / 113 / 22 / **0** | 0 | 87 | 0: 0 / **0** |
| C9 trap and return swapped | 83 | 83 | 0 | 0 | 0 | 62: 62 / 0 / 0 / **0** | 0 | 21 | 0: 0 / **0** |
| C10 branch value's condition changed | 75 | 4 | 0 | 71 | 67 | 50: 1 / 0 / 49 / **0** | 2 | 2 | 16: 16 / **0** |
| C11 increment or initial value changed | 256 | 80 | 0 | 176 | 170 | 235: 66 / 0 / 169 / **0** | 1 | 13 | 0: 0 / **0** |
| C12 loop-carried copies' registers swapped | 39 | 11 | 0 | 28 | 28 | 26: 8 / 0 / 18 / **0** | 10 | 1 | 1: 0 / **0** |
| C13 back edge copy into another register | 207 | 93 | 58 | 56 | 56 | 191: 78 / 58 / 55 / **0** | 1 | 14 | 0: 0 / **0** |
| **all** | 3337 | 2377 | 174 | 786 | 693 | 2251: 1434 / 174 / 643 / **0** | 16 | 653 | 69: 34 / **0** |

**No wrong stream holds and no undecided one does.** The ground truth
finds 2251 mutants wrong; slice 12 refuses each, names a mismatch, or
builds a theorem the sampler refutes. Of the 69 undecided mutants (each a
signed bound compare where the source's is unsigned, or a carried value
that differs only at a bound of 2^63 or more), the owner refuses 35 and
the sampler refutes 34; none holds. Every O0 original builds a theorem
that holds, and so do the 13 O1 streams the owner admits (none is a named
mismatch); the other 42 O1-O3 streams are refused, by the slice-6 block
correspondence (the optimizer's loop rotation and block merges) or by a
row outside the lane (`inc`, SIB loads and stores, vector loads). The 653
"GT n/a" mutants come from those streams' rows the interpreter does not
model; slice 12 refuses or refutes every one of them. (An earlier run of
this table counted a refuted mutant the interpreter could not run among
the "correct but refuted" ones, and did not model `movzx r32, m8`; both are
fixed. The run on the branch before the merges, `2316cdeac`, 18 fixtures
and 3033 mutants, gave the same verdicts: 2040 wrong, none holding;
payload `robustness_no_replay_final.log`.)

**Conservative verdicts (16)**, all refuted although the ground truth
finds them correct:

- 10 swap two loop-carried copies' destination registers on the entry
  edge, where both carried values start equal (0): the machine computes
  the same result with the registers' roles exchanged, but the TV-1 stamp
  pairs each parameter with the register its own copy writes, and the
  relation then fails on the back edge. The pairing is chosen by the
  stamps and checked by the theorem; a pairing the stamps do not name is
  refuted, never credited (as designed).
- 3 change a loop-carried copy or its register to another one holding the
  same value on entry (`StoreFill`), or start an inner counter at 1 where
  the source starts it at 0 and the first iteration adds 0 (`Nested`): the
  same result on another path.
- `Nested`'s inner `setl` for `setb` compares the inner counter with the
  outer one, which a run never takes to 2^63; the theorem has no loop
  invariant, so it judges the header's free inputs at every value.
- `EarlyExit`'s `setbe`/`ja` for `setb`/`jae`, which differ only at
  equality, where both arms agree.

**With the AY replay** (the branch before the merges, `2316cdeac`, 18
fixtures, `ROB12_CAP=3`: 1827 mutants of 67 streams; AY 0.27.0 build 10530
`--strict-proofs` with Clean 5f09e36c, the pair of that tree, and the
verifier's crediting; payload `robustness_replay.log`):

| Class | Mutants | Theorem | Sampler refutes | AY countermodel | AY countermodel the sampler missed | AY certifies | Credited | GT-wrong: refused / mismatch / refuted / **credited** | Undecided: refuted / **holds** |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| C0 original | 67 | 29 | 0 | 0 | 0 | 26 | 26 | 0: 0 / 0 / 0 / **0** | 0: 0 / **0** |
| C1 branch or exit condition changed | 187 | 74 | 53 | 53 | 0 | 18 | 18 | 88: 44 / 0 / 44 / **0** | 18: 9 / **0** |
| C2 successors swapped | 119 | 37 | 37 | 37 | 0 | 0 | 0 | 95: 58 / 0 / 37 / **0** | 0: 0 / **0** |
| C3 edge retargeted | 201 | 0 | 0 | 0 | 0 | 0 | 0 | 151: 151 / 0 / 0 / **0** | 0: 0 / **0** |
| C4 extra edge | 192 | 0 | 0 | 0 | 0 | 0 | 0 | 50: 50 / 0 / 0 / **0** | 0: 0 / **0** |
| C5 edge removed | 121 | 0 | 0 | 0 | 0 | 0 | 0 | 81: 81 / 0 / 0 / **0** | 0: 0 / **0** |
| C6 loop-carried copy from another register | 132 | 75 | 71 | 71 | 0 | 4 | 4 | 104: 38 / 1 / 65 / **0** | 7: 5 / **0** |
| C7 compare operand or bound changed | 183 | 78 | 78 | 78 | 0 | 0 | 0 | 143: 65 / 0 / 78 / **0** | 3: 0 / **0** |
| C8 row dropped | 194 | 17 | 11 | 11 | 0 | 6 | 6 | 146: 88 / 47 / 11 / **0** | 0: 0 / **0** |
| C9 trap and return swapped | 75 | 0 | 0 | 0 | 0 | 0 | 0 | 56: 56 / 0 / 0 / **0** | 0: 0 / **0** |
| C10 branch value's condition changed | 50 | 50 | 48 | 48 | 0 | 2 | 2 | 35: 0 / 0 / 35 / **0** | 13: 13 / **0** |
| C11 increment or initial value changed | 142 | 78 | 76 | 76 | 0 | 0 | 0 | 126: 50 / 0 / 76 / **0** | 0: 0 / **0** |
| C12 loop-carried copies' registers swapped | 38 | 27 | 27 | 27 | 0 | 0 | 0 | 26: 8 / 0 / 18 / **0** | 1: 0 / **0** |
| C13 back edge copy into another register | 126 | 43 | 43 | 43 | 0 | 0 | 0 | 117: 46 / 29 / 42 / **0** | 0: 0 / **0** |
| **all** | 1827 | 508 | 444 | 444 | 0 | 56 | 56 | 1218: 735 / 77 / 406 / **0** | 42: 27 / **0** |

- **AY certifies no wrong stream and no undecided one.** The ground truth
  finds 1218 of the mutants wrong, and none is credited.
- **The sampler refutes everything AY refutes:** none of AY's 444
  countermodels is one the sampler missed.
- **The 30 credited mutants are rewrites that keep the result:** `ja`
  for `jne` and `seta` for `setne` after a compare against 0 (unsigned
  `x > 0` is `x != 0`); a dropped `movzx` or `and 1` of a `setcc` result
  that is already 0 or 1; a loop-carried copy from another register that
  holds the same value; `setl` for `setb` on zero-extended `u8` counters.
- **26 of the 29 original streams with a theorem certify.** The other 3
  are the recorded gaps `StoreFill` and `EarlyExit` and `EarlyExit`'s O1
  stream (AY's certificate keeps one unproved step).

## Census

**Final row: 443 failed roots against main's 493. 54 roots are promoted,
every one a function main refused at a loop that slice 12 binds and AY
certifies; no mismatch is named; no bound body is refuted; 4 roots newly
fail, each a timing victim whose theorem slice 12 does not change
(below).** The census started with 1,967,541 free + inactive + speculative
pages and recorded no resource-budget refusal; other agents' builds shared
the host (load 6 to 16), so wall time is a trend. Of the 170 functions main
refused at a loop, 56 are bound and certify, 6 are bound without an
independently checked proof (`checked_pow` and `overflowing_pow`, the
multiply class; `Big32x40::add_small`, a 30 s timeout; `memchr_aligned`,
`TwoWaySearcher`'s search and a parser closure), and the other 108 stop at
the refusals in Next levers.

The baseline is slice 13's row on AY build 12713 (`runs/census-s13-12713`,
493 failed roots): its bridge was built from `90608b684`, whose owner is
byte-identical to `main` `360eecafa`'s (the later main commits change no
bridge code; `d53e115fa` only lints the owner). Every row below is the
Darwin `core` O0 census with the same flags, on bridges built against the
AY 12713 overlay and run on the root overlay's `trustc`
(`census/census_s12.sh` with `TRUSTC`, tag in the first column), compared
by `census/census_compare.py`.

| Row | Bridge built from | Bridge sha256 | Failed roots | Promoted | Newly failing | Refuted bodies | Wall |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| `census-s13-12713` (baseline) | `90608b684` (= `main` `360eecafa`'s owner) | `01fa4c3a…` | 493 | | | | 6253 s |
| `census-s12m` | `9d6308215` (the merge with slice 13) | `27f77f10…` | 445 | 52 | 4 | 2 functions | 7638 s |
| `census-s12f` | `55e42a730` (the first clean-register fix) | `1b395ece…` | 443 | 53 | 3 | 2 functions | 9229 s |
| `census-s12z` (final) | `5bc8bd533` (slice 12 on `360eecafa`) | `2af4a7f1…` | **443** | **54** | 4 | **0** | 8447 s |

No row names a mismatch. Two earlier rows on the pre-merge pair are
superseded and not tabled: `census-s12o` (the branch before slice 13, on
the overlay) was stopped at 2511 of about 2900 objects when slice 13
landed, and the build-10530 row was never started once the AY move was
announced.

**The refutation the census found, and its fix.** `census-s12m` and
`census-s12f` refuted `core::num::bignum::Big32x40::add_small` and its
test twin `Big8x3::add_small` (payloads `refuted/`, `refuted_final/`).
Neither is a miscompile. The loop carries `carry: bool` in a register and
passes it to `carrying_add` each iteration; the header assumed the
register's bits above the `bool` free (`x4t0` under the psABI walk), and
AY's countermodel sets bit 8, which no run reaches: on every edge the
register holds `(byte + 255) >> 8` of a byte the loop stored as `u8`
(slice 13's `bool` read), 0 or 1. `55e42a730` lets a header assume a
register zero above its parameter when every edge leaves it so bit by bit
(a greatest fixpoint, sound by induction over the header's visits); that
did not cover `(byte + 255) >> 8`, which `5bc8bd533` adds as a bound on
the term's value. On the slice-9 dump's LIR both theorems are then unsat
(`Big8x3`'s certifies; `Big32x40`'s runs out of the 30 s budget), and the
fixtures `BoolCarriedToCall` and `ByteBoolCarried` keep both shapes
(mutants `no-clean-registers` and `no-upper-bound` refute their correct
streams).

**The newly failing roots are timing.** The final row's four newly
failing roots (`DisplayBuffer::new`, `Parser::read_socket_addr`,
`EscapeIterInner::printable`, `fmt::num::format_into`; `census-s12f` had
the other three, `census-s12m` all four) are bound on both sides, Valid on main and without an
independently checked proof here. All four are acyclic (no loop: slice
12's machinery never runs on them). Their theorems under main's owner
(`6b6a72b11`) and slice 12's, built over the same LIR (the slice-9 dump,
`probe/x86_body_probe.rs --cf` against each owner; payload
`newly_failing_cmp/`), are byte-identical (SHA-256 `5eda3f65…`,
`375d7e12…`, `051ee1a5…`, `7f414d87…`). The queries the census dumped certify offline
on AY 12713 with Clean in 49-66 s of wall time on the loaded host
(payload `newly_failing.tsv`), against the replay's 30 s budget: the
requalification record's load-dependent credit.

**The landing row.** Slice 12 merged slice 15 and then main `f6dcad152`,
whose `71c2eb632` balances every canonical proof conjunction; slice 12's
snapshots took the same migration (the 20 theorems differ from the
right-spine ones only in how nested `and`s group: flattened, they are
byte-identical). Both rows were built by `~/tcg-scratch/census12713.sh`
(bridge against the AY 12713 overlay, census on the root overlay's
`trustc`, `x86-body-trace` and `x86-body-dump`), one after the other on a
host whose other agents were held to niced single-job builds; neither
recorded a resource-budget refusal, and they started with 2,854,785 and
2,169,710 free + inactive + speculative pages.

| Row | Bridge built from | Bridge sha256 | Failed roots | Promoted | Newly failing | Named mismatches | Refuted bodies | Wall |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `census-main-f6dc` (baseline) | `main` `f6dcad152` | `856d8260…` | 447 | | | | | 10433 s |
| `census-s12-land` | `fca48f987` (slice 12 on `f6dcad152`) | `f9d3f9b9…` | **373** | **74** | **0** | 0 | 0 | 5998 s |

`census/census_compare.py` (payload `compare_land/`): 73 of the promoted
roots are functions main refused at a loop that now replay Valid; the
74th was bound on both sides and replays Valid here, where main's replay
did not certify within its budget. Of the 170 functions main refused at a
loop, 75 replay Valid, 5 are bound without an independently checked proof,
and 90 stop at another refusal: 31 over 512 machine rows, 29 a private
stack address offset by a non-constant amount (26 defined by a `Bitcast`,
3 by an `Imul`), 13 a division or its guard (11 `GuardDivZero`, 2
`Udiv`), 8 over 1024 LIR instructions, 6 an `I128` loop-carried value, and
one each of a header entered from two outside edges, a join and a header
whose paths leave a private slot holding different values, one of them a
private stack address.

## Gates

On the landing tree (slice 12 merged onto main `f6dcad152`), built with
the stage-1 `targo --unverified` through the AY 12713 overlay (no proof
claim about any build; payload `gates_land.log`):

| Gate | Result |
| --- | --- |
| verify body and envelope library (`gates_full_stage1.sh`) | pass after the two migrations below |
| codegen body and must-refuse | 5 + 5 pass |
| IR, lowering and optimizer libraries | 552, 2022 and 4427 pass (2 ignored) |
| codegen library | 4702 pass (1 ignored) |
| CLI must-refuse | pass |
| `--lib --tests --keep-going` build | every target but the three kernel-JIT fixtures, which need an exact Rust 1.95.0/1.97.1 or the certified Trust compiler |
| `scripts/check_fmt.sh` (managed `targo fmt`) | OK |
| `scripts/check_documentation.py --check` | OK |
| `scripts/check_tippy.sh` | cannot run on this host |

The verify library's first run failed six tests, all from main's balanced
canonical conjunctions (`71c2eb632`), which slice 12 had not yet merged:
the slice-12 snapshot digest and the qualification matrix's slice-12
family (the theorems regroup their `and`s only; re-pinned), and the slice
9 and slice 11 host qualification and verifier-credit tests. Those four
replay against the AY 12713 ledger, which main's change did not requalify
(its record ran another AY on another host). Run alone on this host, each
in its own process (payloads `qual_live.log`, `qual_9_11_ledger.log`), the
balanced spellings move two outcomes: slice 9's `NestedTree` certifies
(13.8 s; its right spine exceeded AY's rendering bound) and slice 11's
`SlotU128` runs past the 30 s deadline. Paired runs on the same AY show
the spelling is the cause: the right spine certifies in 1.7 s, the
balanced one in 32.3 s; AY `8d6d17ad1` (the requalification follow-up
fixes on AY main) certifies the balanced one in 1.7 s. The ledgers and
LIMITATIONS.md record both moves.

## Next levers

Where the 170 functions main refused at a loop stand in the final census
(`census/levers.py` over `compare_z/slice12_transitions.tsv`):

| Slice-12 outcome | Functions |
| --- | ---: |
| bound, replays Valid | 56 |
| bound, no independently checked proof | 6 |
| a load or store through an address that may derive from an escaped slot (slice 7's retention rule; an iterator's `next` result read through) | 41 |
| a private slot offset by a non-constant amount (an index into a stack array) | 29 |
| division (`GuardDivZero`, `Udiv`) | 12 |
| more than 512 machine rows | 10 |
| more than 1024 LIR instructions | 8 |
| an `I128` loop-carried value | 6 |
| a header entered from two edges outside its loop | 1 |
| a stored private address in a byte the loop changes | 1 |
| **all** | **170** |

So the next levers for loops are memory, not control flow: the retention
rule (a call's result that may point into an escaped slot) and a
non-constant slot offset are 70 of the 108 still refused. Slice 13 already
took the slot address stored as data (24 functions before it). Division
is slice 10's open item and the size bounds are OD-72's; an `I128`
loop-carried value needs the register pair in the relation (slice 11's
halves, two registers per parameter).

## Reproducers (in tree)

- `census/`: `loop_roots.py` (the class's roots and functions from a
  census), `loop_profile.py` and `param_kinds.py` (the loop profile),
  `cf_compare.py`, `newly_bound.py` and `loop_refusals.py` (the owner over
  the dump, main against slice 12), `replay_dir.py`, `replay_split.py` and
  `size_rates.py` and `size_outcomes.py` (offline AY/Clean replays by
  size), `levers.py` (the census outcomes by class), `census_s12.sh` (the
  census; it waits for free + inactive + speculative pages above 1.6M, no
  other census and no quiet request), `census_compare.py`, `payloads.py`.
- `probe/x86_body_probe.rs`: the probe (mode `--loops` added); copy it to
  `crates/trust-cg-verify/examples/` to run it.
- `fails-before/`: `mutate.py`, `run_mutants.sh`, `qualify.sh`.
- `robustness/`: the mutation probe (plugged in by a temporary `#[path]`
  module; see Mutation robustness) and `table.py`, which renders its table.
