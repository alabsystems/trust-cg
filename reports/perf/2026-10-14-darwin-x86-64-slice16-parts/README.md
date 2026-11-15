# Darwin x86-64 `library/core` — slice 16 (size via cut points; one theorem replayed in parts), 2026-10-14

Slice 16 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs` and its child module
`x86_source_bound_body/split.rs`) states a function past the single-query
bounds (more than 128 LIR blocks, 1024 LIR instructions, 128 machine blocks or
512 machine rows) as ONE theorem replayed in PARTS, one per region between
cut points. Every function within the bounds keeps its theorem byte for byte.
The design, the measurement of the class (101 failed roots of slice 12's
landing census) and the measured mask are in `~/tcg-scratch/s16-design/`
(README §1-§7); this record holds the implementation, its soundness
argument, the controls and their fails-before evidence, the host
qualification and the measured outcome on the size class (the design's 101
and current main's 121). Ruling OD-182 in
`docs/decision-record.md`. Host: the
x86_64 Mac of the [slice-12 census](../2026-10-05-darwin-x86-64-census-slice12/README.md)
(4 cores, 16 GB, shared; while a census chain and then an AY lane's quiet
window ran, every build ran at `nice -n 19`, `-j1`, and no solver ran;
afterwards builds ran at `-j2`),
the local overlay `x86-stage1-ay12713` (`targo --unverified`, no proof claim
about any build), AY 0.27.0 build 12713 with Clean 5f09e36c (the pair
`QUALIFIED_AY` pins). Branch `feat/x86-body-slice16-size`, from slice 14
(`feat/x86-body-slice14-definedness`, rulings OD-178..181 after their
renumbering on landing), with origin/main merged in twice.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-2854ce3e3-ay12713` (baseline) | `main` `2854ce3e3` | 12713 | `867e506f…` | 813 | 7229 s |
| `core-x86_64-darwin-O0-proof-slice16-ay12713` | this branch, `5b5b1d105` (slice 16 on `2854ce3e3`) | 12713 | `94f555ff…` | **763** | 5761 s |

**50 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
35 refused past 512 machine rows and 11 past 1024 LIR instructions now
replay Valid in parts; 4 more were bound on both sides and certify here.
Fewer than the 86 measured offline: main's census rose from slice 14's 342
to 813 because its bridge now spells array-element addresses as `ArrayGep`,
which the body lane does not yet admit, and that refusal stops many size-class
functions first. Both rows were built by `census12713.sh`, each bridge in its
own tree, with no resource-budget refusal.
Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md) lists each with its
size and SHA-256.

## The theorem

**Who is split.** `source_bound_x86_body` keeps its single theorem for every
pair within the single-query bounds (`split::fits_one_query`: at most 128 LIR
blocks, 1024 LIR instructions, 128 machine blocks and 512 machine rows), and
that theorem is unchanged byte for byte: every earlier slice's golden digest
test passes on this tree. A pair past one of them is stated in parts
(`split::source_bound_split`) when the source is within the split bounds
(1024 blocks, 8192 instructions, 8192 machine rows) and is otherwise admitted
by the slices 1-15 rules with the size bounds lifted
(`split::source_admits_split`, which the verifier's request path uses).

**Cut points.** The cut points are the entry, every loop header (slice 12)
and the points a deterministic plan chooses (`split::plan_points`, a port of
the design's measured plan). First every block with more rows than a
quarter of the region budget is cut into pieces at clean stamp boundaries
near even splits, each the boundary with the fewest live values that are not
fixed for the run; then, while a region (slice 12's construction, over the
pieces) is over budget (256 machine rows, 1024 LIR instructions, 128
blocks), the over-budget region with the most rows gets one more cut, at the
piece that keeps its head the largest that fits (failing that, the cut that
makes the largest region smallest). A point `(B, k)` inside block `B` is CLEAN
(`split::clean_split_row`) at the first machine row stamped with an LIR index
of at least `k` when every earlier row of the block is stamped below `k` or
unstamped, at least one is stamped, no row before it transfers control or
leaves an outgoing argument area open, and no row from it on reads a physical
register (other than a callee-saved one, or a return register that a row of
the block writes before its `ret`) or the flags before a row writes them.
More than 32 regions refuses by name. A planned cut whose interface refuses
(a slot holding different stored private addresses on its edges, an `i128`
live across it) is banned and the plan made again, at most four times. A
block no source path reaches (main's dead-block exclusion, `SourceCfg::dead`)
is never a cut point: the plan works over the reachable blocks, and a test
policy's point in a dead block cuts nothing. Any cut set that contains the
entry and the loop headers is sound; the plan only affects how much is
refused or refuted, and what each query costs.

**Pieces.** A point inside a block makes the block two on both sides
(`split::rewrite_pieces`): the LIR block keeps its instructions before `k`
and ends in a synthetic `Jump` to a new block holding the rest (its source
locations and trust-ir origins split with it); the machine block keeps its
rows before the split row and falls through to a new block laid out right
after it, its rows' stamps renumbered to the new LIR block. The rewrite is
checked: the cut machine stream, in layout order, is the original's rows in
the original order, so each row keeps its walk ordinal, and the audit maps
translate every piece back to its original block and index.

**The interface at a cut** (`split::CutInterface`, built by
`split::admitted_cuts` as a fixpoint over the edges into each cut, at most
64 rounds). At every cut point but the entry:

- every LIR value live there and every parameter of the cut block is an
  ITEM (`x{C}v{i}`, one free input both sides share), unless it is CLOSED:
  an `Iconst` (not `I128`), a parameter of the function, a symbol's address
  or a private address. A closed value is carried as its exact term, which
  must be the same term on every edge into the cut, or the function makes
  no claim;
- every private byte some edge into the cut wrote is an item
  (`x{C}b{slot}o{offset}`), unless it is closed: a byte stored from a
  closed constant or parameter, a byte of an aggregate parameter's
  register, or a byte of a stored private address (which must be the same
  address on every edge). A byte no edge wrote is the frame's initial byte
  (`f{k}`, fixed for the run);
- an item of type `i128`, or a value whose defining rows write no virtual
  register, refuses by name.

**The relation.** On EVERY edge into a cut, under the edge's guard and where
the source has not stopped (slice 14's stop terms), the theorem states each
value item equal to the low bits of its machine register at the end of the
edge's machine walk, and each byte item equal to the machine's byte at the
same frame address (runs of bytes within an eightbyte compared as whole
stores where both sides stored them whole). The register of a value item is
the one the last machine row stamped with its LIR definition writes; for a
parameter of the cut block, the one its edge copy writes
(`split::cut_pairing`); a physical register, a narrower one, or two items in
one register refuse by name. The stated bits are the value's own (a `bool`:
the clean 32-bit carrier, or its byte under the psABI view, as at a loop
header); the bits above are a free input (`x{C}t{i}` / `x{C}c{i}`) unless
every edge leaves them syntactically zero (slice 12's `zero_above`, the same
greatest fixpoint).

**What a region assumes.** A region starts (`split::machine_cut_start`) from
the interface: each item's register its template; every other machine
register the term every edge leaves in it when that term resolves, through
the machine's definitions, to a term of at most 64 nodes over inputs fixed
for the run (entry registers and incoming stack eightbytes, symbols, slot
addresses, initial frame bytes, a `bool` parameter's views, parameter
bindings), else `Carried` (reading it refuses by name), and absent where
some edge leaves it undefined; each byte item the shared input and each
closed byte its term; the flags unmodelled; no outgoing area (an edge with
one open refuses); and the source's escaped slots (an edge on which the
machine lets a slot escape that the source does not refuses); nothing is
stopped. A byte the machine writes on an edge that the cut does not relate,
because the source does not write it, refuses by name.

**Parts.** `build_theorem` states the regions in the order of their cut
points with slice 12's machinery and records how many top-level claims each
region contributes. The STATEMENT is the uninlined theorem (every definition
a premise, every claim a conjunct; checked definitional, never replayed).
`split::split_parts` cuts it mechanically: region `r`'s claims are one part,
`(= true (and K_1 ... K_m))`, under the cone of the statement's definitions
its claims reach, value-numbered (`split::unify_definitions`: a definition
that renames a name or an input, or is a constant, is that term, and one
whose right-hand side is the same term as an earlier definition's is that
earlier name, each right-hand side first normalized by three exact
bit-vector identities, `split::bit_normalized`: adjacent extracts of one
term concatenate, a full-width extract is the term, and the original width
of a zero extension extracted is the original) and then
spelled as slice 9 spells a theorem (each definition used once substituted
into its use, every claim those substitutions make an identity dropped; a
part whose spelling fails the structural check is stated without them). A
region with no claim, or whose claims all become identities, is no part,
unless every region's do: a theorem is never stated by identities alone
(slice 9's rule), and then every region is stated without the
substitutions. A part declares exactly the statement's free inputs it reads, in the
statement's order, and is named `<statement> | part k of n`.
`check_x86_body_parts` re-derives the parts from the statement and the
region claim counts and compares them exactly; it runs when the owner is
built, before any replay (`x86_body_parts_verdict`) and before any export
(`SourceBoundArithmeticObligation::replayed_obligations`, which the proof
emitter calls).

**Credit.** `FunctionRequest::x86_body` replays the parts through the
existing serial multi-part protocol (`original_parts`, as the A64 memory
decompositions are replayed): each part is one AY query with its own budget
and one Clean check; the function's rows are credited only when every part
is Valid, a refuted part fails every covered row, and anything else leaves
them uncredited. The proof emitter publishes the parts, one `.smt2` each,
named by the part's name and the SHA-256 of its query, never the statement,
and the lowering sidecar carries the parts. The verifier's body trace keeps
its `bound rows=N replay=...` line and adds `stated in parts=N`.

## The claim and its soundness

The claim is OD-84's: for every run of the source, terminating or not, the
machine runs the paired path of each region instance with an equal world
trace and ends the same way. The function's theorem is the conjunction of
its parts, and it is the single theorem with the same claims: the
statement's definitions are a definitional extension (each name defined
once, in order, over earlier names and free inputs), so `forall inputs. defs
=> (C_1 and ... and C_n)` holds exactly when, for each group `r`, `forall
inputs. cone(C_r) => C_r` holds; substituting a definition into its single
use and dropping a claim that became `t = t` preserve each part's meaning.

Soundness is OD-84's induction over region instances, with the non-loop cuts
as further induction points. At the start of an instance of `C`'s region the
two states satisfy the interface: the edge that entered stated the relation
for every item (a claim of the entering region's part, under that edge's
guard), every closed value and byte is the same exact term on every edge
(checked term for term), every unpaired machine register the region reads
holds a term of the run's fixed inputs that every edge agrees on (checked)
or is unreadable, and nothing else is readable. So the actual pair of states
is one assignment of the region's free inputs (each item input the actual
value, the bits above it what the register holds), and the region's part,
proved for every assignment, gives the region's claims for this instance,
including the relation on the edge that leaves it. A value the liveness
misses is undefined in the region (a read of it refuses), a wrong pairing
makes the relation false on the edge that states it (refuted), and the plan
only places the cuts. The flags never cross a cut: the clean split rule
refuses a reader before a writer, and every region starts with them
unmodelled.

## Controls

Every test below runs without a solver (the library gate
`x86_source_bound_body::tests::slice16::`); the replay on AY and Clean is in
Qualification. Fixtures are real: LIR from the trust-ir adapter, the machine
stream from the real x86-64 instruction selector. A small fixture is stated in
parts by a test policy that cuts it at chosen points; the production planner
states only functions past the bounds in parts.

**Correct lowerings.**

- `every_earlier_fixture_cut_at_every_block_holds_part_by_part` and
  `..._at_every_clean_point_...`: every fixture of slices 1 to 15 that the
  single theorem binds, cut at every block start (and, the second, at every
  clean point inside its blocks too), is either stated in parts with every
  part and the statement holding on the samplers, or refused by name; no
  mismatch is named. Of the 368 fixtures, cut at every block 361 are stated
  in parts and 7 refused (every region's claims become identities: no
  observable, OD-115); cut at every clean point too, 343 and 25 (17 an
  `i128` live across a cut, 6 no observable, 1 a `bool` load from a byte
  that crossed a cut, 1 a non-constant slot offset the cut exposes).
- `every_control_stated_in_parts_holds`: the five control shapes (`Handoff`:
  two computed values cross the cut in registers; `SlotHandoff`: a slot's
  written bytes cross it, one eightbyte never written; `ClosedJoin`: a
  constant and a join parameter; `NarrowHandoff`: a byte; `CompareHandoff`: a
  compare's `bool`), each cut at its returning block, state two parts that
  hold.
- `the_production_planner_states_every_large_shape_in_parts` and
  `sources_past_the_lir_bounds_are_stated_in_parts`: five shapes past the
  row bound (a 90-step straight-line chain, 34 diamonds, a loop whose body
  is 70 steps, a 200-element local array zeroed element by element, 110
  calls through a local; 581 to 724 rows, 3 or 4 parts each), and chains past the LIR
  instruction and block bounds, are stated in parts by the production
  planner, every region within the region bound, every part holding.
- `a_dead_source_block_is_never_a_cut_and_stays_accounted_for`: main's
  dead-block fixtures (an unreachable LIR block, a laid-out machine block
  lowering it) stated in parts with a point in the dead block: built, parts
  holding; with a live block that jumps into the dead machine block: never
  credited.
- `a_function_in_parts_binds_its_rows_at_their_original_ordinals`,
  `theorems_in_parts_are_deterministic`,
  `a_function_within_the_bounds_is_never_stated_in_parts` (every earlier
  fixture keeps its single theorem; the golden digest tests of slices 1-15
  pass unchanged).

**Mis-models** (each a wrong lowering, or a wrong cut rule, that must never
be credited):

| Control | The wrong lowering | Outcome |
| --- | --- | --- |
| `a_mismatch_hidden_by_a_cut_is_refuted_by_its_relation` | `Handoff` computing `a = x + 0x56` before the cut; only the region after it consumes `a` | refuted in the first part (the relation on the cut edge) |
| `values_swapped_across_a_cut_are_refuted` | `a` and `c` computed into each other's registers before the cut, subtracted after it | refuted |
| `a_value_read_from_another_register_after_a_cut_is_refuted` | after the cut, the machine reads `x`'s parameter copy where the source reads `a` | refuted (the second part) |
| `a_slot_byte_changed_before_a_cut_is_refuted_by_its_relation` | `SlotHandoff` storing `y` where the source stores `x`, before the cut | refuted (a byte item's relation) |
| `the_relation_is_stated_on_every_edge_into_a_cut` | `ClosedJoin` copying `x` into the join parameter's register on one of the two edges into the cut | refuted (the relation on that edge) |
| `upper_bits_an_edge_does_not_clear_are_never_assumed_zero` | `NarrowHandoff` truncating with a 32-bit copy before the cut and returning the register's 32 bits after it without the zero extension | refuted (the bits above the byte are a free input) |
| `a_machine_only_store_before_a_cut_makes_no_claim` | `SlotHandoff` with a machine-only store into `t[1]` (never written by the source) before the cut | refused: a byte the machine writes and the source does not |
| `a_register_that_differs_on_the_edges_into_a_cut_makes_no_claim` | `ClosedJoin` with the constant's register set to 8 on one edge (7 on the other) | refused: the register is carried, not closed, and the region reads it |
| `a_flag_read_across_a_cut_makes_no_claim` | `CompareHandoff` with its `setcc` stamped after the cut point | refused: no clean split (a flag reader before a writer) |
| `every_slice_sixteen_mis_model_is_never_credited` | the six refuted controls above, and a wrong lowering of each size shape stated by the production planner (a chain constant changed, a diamond's branch inverted, a store offset changed in the loop, element 3 of the array zeroed at element 4's address, a call argument replaced) | refuted in some part |
| `every_earlier_refutation_stated_in_parts_is_never_credited` | every wrong lowering of slices 6 to 15, cut at every block | refused, a mismatch named, or refuted in some part |
| `the_parts_credit_rule_needs_every_part_valid` | the credit rule over part outcomes: a refuted part after a Valid one, an unproven part, an inventory that does not check | Valid only when every part is; refuted by any refuted part; no verdict otherwise; nothing replayed without the inventory |
| `a_missing_or_regrouped_part_fails_the_inventory_check`, `an_export_missing_a_part_is_refused` | a part dropped, the claims regrouped; an export payload missing a part | the inventory check fails; the export is refused |

The solver-free samplers here are slice 9's keyed sampler and slices 10-11's
edge-word and pooled samplers; every correct fixture's parts hold on all
three, so a refutation by any is one a correct lowering never gets.

## Fails-before

`fails-before/mutate.py` guards each slice-16 rule behind
`TCG_S16_MUTANT=<name>` in the working tree (one test build serves every
mutant; the files are restored with `git checkout` afterwards and never
committed), and `fails-before/run_mutants.sh` runs the slice-16 library gate
once per mutant (the whole x86 body gate, every slice's golden digests
included, for `split-small`). On the final tree (payload
`mutants_final/mutants.txt`, with each run's log), the unmutated build
passes all 24 slice-16 tests and every one of the 11 mutants fails at least
one control (an earlier run on `887f24723`, before value numbering, gave the
same verdicts: payload `mutants.txt`):

| Mutant (the rule disabled) | Controls that fail |
| --- | --- |
| `no-cut-relation`: no relation on any edge into a cut | `a_mismatch_hidden_by_a_cut_is_refuted_by_its_relation`, `a_slot_byte_changed_before_a_cut_is_refuted_by_its_relation`, `the_relation_is_stated_on_every_edge_into_a_cut`, `every_slice_sixteen_mis_model_is_never_credited`, `every_earlier_refutation_stated_in_parts_is_never_credited`, `a_dead_source_block_is_never_a_cut_and_stays_accounted_for` |
| `relation-first-edge-only`: the relation only on the first edge into each cut | `the_relation_is_stated_on_every_edge_into_a_cut`, `every_slice_sixteen_mis_model_is_never_credited`, `every_earlier_refutation_stated_in_parts_is_never_credited` |
| `carry-first-edge`: an unpaired register starts as the first edge's term | `a_register_that_differs_on_the_edges_into_a_cut_makes_no_claim` |
| `no-byte-items`: byte items shared but their relation not stated | `a_slot_byte_changed_before_a_cut_is_refuted_by_its_relation`, `every_slice_sixteen_mis_model_is_never_credited`, `every_earlier_refutation_stated_in_parts_is_never_credited` |
| `machine-bytes-unchecked`: a byte only the machine writes starts unwritten | `a_machine_only_store_before_a_cut_makes_no_claim` |
| `upper-zero-unchecked`: an item's register assumed zero above it | `upper_bits_an_edge_does_not_clear_are_never_assumed_zero`, `every_slice_sixteen_mis_model_is_never_credited` |
| `part-credit-any`: credited when any part is Valid | `the_parts_credit_rule_needs_every_part_valid` |
| `no-inventory-check`: parts replayed although the inventory does not check | `the_parts_credit_rule_needs_every_part_valid` |
| `parts-incomplete-export`: an export's parts published unchecked | `an_export_missing_a_part_is_refused` |
| `split-small`: every function stated in parts | `a_function_within_the_bounds_is_never_stated_in_parts` and every slice's golden digest test (80 tests of the body gate fail) |
| `split-flags`: a mid-block point is clean although a flag reader follows it | `a_flag_read_across_a_cut_makes_no_claim` |

Rules no selector output reaches, kept as guards and named here rather than
mutated: the check that a closed value's term is the same on every edge
into a cut (a closed value is a leaf with one SSA definition, so its term
cannot differ by edge); the refusal of a machine edge that lets a slot
escape the source does not; the refusal of an open outgoing argument area
at a cut (the selector opens and closes one around a single call, inside a
block); and the check that a cut machine stream is the original's rows in
order (the rewrite builds it so).

## Qualification (AY build 12713 with Clean)

The two tool-gated tests ran on the qualification pair the tree pins
(`QUALIFIED_AY`: AY 0.27.0 build 12713, Clean 5f09e36c, through the
`x86-stage1-ay12713` overlay), one test per process
(`census/qualify.sh`), on the final merge `0b190ac9c`, after the census
chain and the AY agent's quiet window had ended (payloads
`qualification/`, with every replayed query; the same outcomes on the
tree before that merge).

`host_qualification_replays_the_slice_sixteen_parts` builds every
qualification pair through the real owner and replays every part:

| Pair | Parts | Outcome |
| --- | ---: | --- |
| `Handoff`, `SlotHandoff`, `NarrowHandoff` (cut at the returning block) | 2 each | all Verified, 0.07-0.7 s |
| `ClosedJoin`, `CompareHandoff` | 1 each (the other region's claims are identities once value-numbered) | Verified, 0.45 s and 0.1 s |
| `DiamondChain` (616 rows, production plan) | 3 | Verified: 16.4 s, 17.5 s, 5.3 s |
| `BigLoop` (581 rows) | 1 (the loop body's regions are identities) | Verified, 6.5 s |
| `ZeroArray` (610 rows) | 3 | Verified, 0.08-0.7 s |
| `CallChain` (666 rows) | 3 | Verified, 0.2-0.3 s |
| `LongChain` (724 rows) | 3 | **Timeout** at 30 s, and `unknown` (timeout) offline at 300 s: recorded gaps (`KNOWN_UNCERTIFIED_SLICE_SIXTEEN`, `PENDING(solver-capacity)`). Its machine spells the source's ninety `x ^ (x << 3)` / `+ k` steps step for step, so every region's claims become identities and the theorem is stated plainly (never by identities alone), ninety-step chains under different names on each side |

Mis-models, every part replayed (not stopping at the first):

| Mis-model | AY |
| --- | --- |
| a mismatch a cut would hide | counterexample `e_rdi = 0` (the region before the cut) |
| values swapped across a cut | counterexample `x1v0 = 0, x1v1 = 1` |
| a value read from another register after a cut | counterexample `e_rdi = 1, x1v0 = 0, x1v1 = 0` |
| a slot byte changed before a cut | counterexample `e_rdi = 0, e_rsi = 1` |
| a wrong value on one edge into a join cut | counterexample (`e_rdi = 0, e_rsi = 1`, the edge's guard `c0x0t2 = 1`) |
| bits an edge leaves above a byte, returned after a cut | counterexample `x1v0 = 0, x1t0 = 1` (the free bits above) |
| a constant changed mid-chain (`LongChain`) | counterexample (the changed region is the only non-identity one) |
| a store offset changed in the loop (`BigLoop`) | counterexample |
| element 3 zeroed at element 4's address (`ZeroArray`) | counterexample over the frame's initial bytes `f0..f7` |
| a call argument replaced (`CallChain`) | counterexample `e_rdi = 0, r54 = 1` |
| a branch inverted mid-chain (`DiamondChain`) | **no verdict in the live replay**: part 2 times out at 30 s in the replay's resident (`--incremental`) AY, where one-shot `ay -smt2` answers `sat` in 0.1 s; recorded (`KNOWN_UNREFUTED_SLICE_SIXTEEN`), and the function is never credited |

`verifier_credits_every_bound_row_of_a_function_in_parts` asks the x86
function verifier for credit: every covered row of `DiamondChain`,
`BigLoop`, `ZeroArray` and `CallChain` is Formal under its theorem in
parts, the function is promotable, and each export's
`replayed_obligations()` is the complete part inventory; `LongChain`'s rows
stay unverified with no export. Of the size mis-models, the four refuted
ones fail every covered row (723, 577, 609 and 555 rows) and the inverted
branch leaves all 513 unverified (the serial replay stops at its part 2);
none exports.

## Measured outcome on the size class (probe, then offline AY with Clean)

**The class, re-measured on current main.** The slice-12 landing census
gave the design its 101 size-refused functions. Main's own census of
`main-a902` (this host, 2026-10-14, `runs/census-main-a902`, the bridge of
the census chain) has 121: the 101 and 20 more (13 absent from the
design's list, 7 that it counted bound in one query and that now exceed
512 rows), with 94 bound-uncertified controls (the design's script
`size_roots.py`; payload `class_main/`).

**The input.** A fresh `core` trust-ir dump from that same bridge
(`dump_core_ir.sh`: the census compile with `dump-trust-ir`, stopped once
the main CGU's module is written; `runs/core-ir-s16`; it is a solver run:
the bridge proves the per-item modules before the main CGU, AY and Clean
included, as the slice-20 design measured on 2026-10-20). The
probe (`probe/x86_body_probe.rs`, the slice-12 probe with slice 16's part
output) ran this branch's owner over it, restricted to the 215 class
functions (`S16_ONLY_NAMES=1`); nothing needed re-spelling and no function
was dropped. Every built part was checked on 600 samples and written out.
Payload `measure6/` (`census/measure_s16.py`).

| class | functions | stated in parts | non-constant private-slot offset | refused at a cut | other |
| --- | ---: | ---: | ---: | ---: | --- |
| rows>512 | 79 | **78** | 0 | 1 (an `i128` live across a cut) | |
| lir>1024 | 38 | **26** | 9 | 1 (a `bool` loaded from a byte that crossed a cut) | 1 machine row outside the domain; 1 join of different stored private addresses |
| blocks>128 | 4 | **2** | 1 | 0 | 1 `i128` division |
| **size, all** | **121** | **106** | 10 | 2 | 4 |
| bound-uncertified (control) | 94 | 0: all keep one query | | | |

No mismatch is named and no part is refuted on samples. Of the design's
101, 87 are stated in parts.

**Parts:** 563 over the 106 functions; per function median 4, p90 9, max
22; per part median 9 definitions, 7 claims and 3.5 KB of query, p90 33,
19 and 9.4 KB, max 73, 37 and 34.9 KB. Wall: 215 functions in about three
minutes on one thread.

**Offline certification.** Every part replayed with AY build 12713 in its
strict Alethe mode within the live 30 s budget, then checked by Clean
(`census/replay_dir.py`, two at a time, on a host other lanes were
compiling on; payload `replay_parts_core.tsv`):

| | parts | Verified (AY `unsat`, Clean PASSED) | Timeout | unknown | functions with every part Verified |
| --- | ---: | ---: | ---: | ---: | ---: |
| final spelling | 563 | **496** (88%) | 65 | 2 | **86 of 106** (rows>512 67 of 78, lir>1024 18 of 26, blocks>128 1 of 2) |
| without value numbering (first build, same dump) | 643 | 539 (84%) | 91 | 2 (+11 AY self-check rejections) | 63 of 106 |

A Verified part took 1.8 s at the median and 7.9 s at p90 (AY and Clean).
Seven more functions are one part short. The value numbering came from
this measurement: AY timed out (30 s, and 300 s) on parts whose only
claims were `(bvadd p0 k) = (bvadd e_rdi k)` under `p0 := e_rdi`
(bisected: without those claims the same part answers in under a second), and on
the machine's byte-wise reassembly of an entry register beside the
register itself; the remaining timeouts include 128-bit multiplies of
checked arithmetic (the overflow test of `2 * x`), the solver-capacity
class slice 14 records.

**On slice 9's dump.** Before the fresh dump, the same owner (before value
numbering) ran over the design's input, slice 9's dump, re-spelled for the
pinned adapter (the four constant spellings of the design's §1.5.1 and the
older bridge's store-form `insertfield`, which WS7.1 (b) now refuses, in
138 functions): 82 of the design's 101 stated in parts, 80 of them the
design's lifted-bound 81 with the same bound rows (payloads `measure2/`,
and `measure1/` before the replanning commit, when `memchr::memrchr` was
refused at a cut).
## Gates

- Whole x86 body library gate, solver-free (`x86_source_bound_body`,
  skipping the tool-gated qualification, credit, negative-memo and
  canonical-migration tests): 265 passed, 0 failed on the final merge
  (`0b190ac9c`), every slice's golden digest test included (payload
  `gate_body.log`); the slice-16 filter alone: 24 passed.
- `env -u TRUST_TARGO bash scripts/check_fmt.sh`: OK.
- `python3 scripts/check_documentation.py --check`: OK.
- Lint (`targo tippy`) cannot run on this host and was not run.
- `trust-cg` CLI unit tests (`emit_proofs`) with AY build 12713 and Clean:
  21 passed, including `x86_body_queries_survive_export_and_metadata_cannot_grant_authority`
  (16 exported bodies, 7 forged-metadata refusals, the withdrawn checker
  refused). With the solver disabled, the three AArch64 export tests fail
  (their objects need replayed certificates); they are not slice 16's.

## Open gaps

- **Census.** No census row: the owner runs the census and lands the
  branch. The 106 and 86 are measured offline on a fresh dump of main
  a902's bridge; a census of a slice-16 bridge is the measurement that
  counts (it also replays parts through the live protocol, whose resident
  AY answered one refutation more slowly than one-shot AY, below).
- **Solver capacity.** 65 of the 563 parts time out at 30 s (20 of the 106
  functions are not fully certified, 7 of them one part short), and
  `LongChain`'s qualification parts time out at 300 s. Among them are
  128-bit multiplies of checked arithmetic (the overflow test of `2 * x`)
  and chains the machine spells step for step under its own names; the
  theorem of a function whose every region is such a chain is stated
  plainly (never by identities alone), so value numbering does not help
  it. The region bound (256 rows) is the design's, not re-qualified here.
- **Live replay of a refutation.** The inverted `DiamondChain` branch is
  not refuted by the live replay (its resident `--incremental` AY times
  out at 30 s where one-shot `ay -smt2` answers `sat` in 0.1 s); the
  function is never credited, but no counterexample is reported for it.
- **Cut-specific refusals.** 2 of the 121 stop at a cut by name: an
  `i128` live across a cut, and a `bool` loaded from a byte whose bool
  store a cut does not carry (`read_ipv6_addr`'s closure). On slice 9's
  dump, a slot holding different stored private addresses on the edges
  into a cut that four replans could not avoid stopped `parse_decimal_seq`
  (on the fresh dump it stops earlier, at a DAG join). Each is a
  completeness gap; none is a credit.
- **Trusted spelling.** The value numbering, the three bit identities and
  the identity dropping of the parts' spelling are trusted rewrites (as
  slice 9's identity rule), swept by a unit test, not checked by Clean; a
  region whose claims all become identities is credited without a solver
  call when another region of its function is not (never when none is).
- **Tiny functions in parts.** A function within the bounds is never
  stated in parts. Cut by a test policy, 7 small fixtures state nothing in
  parts (every claim an identity once constants are carried exactly) and
  are refused as having no observable; the production path never does
  this.
- **Export test.** The CLI's x86 export test compiles small functions only
  (none in parts); the part inventory at export is covered by the verify
  crate's `an_export_missing_a_part_is_refused`,
  `x86_source_bound_body::tests::slice16_qualification::verifier_credits_every_bound_row_of_a_function_in_parts`
  (every export's `replayed_obligations()` is the complete inventory) and
  the emitter's `rule_files` path, not by an end-to-end compile of a
  function in parts.
- **Decision-record numbering.** Slice 14's rulings are OD-178..181 (main);
  slice 16's ruling is OD-182, above main's maximum. OD-58, OD-145, OD-146
  and OD-155 are duplicates on main itself.

## Reproducers (in tree)

- `fails-before/mutate.py`, `fails-before/run_mutants.sh`: the rule
  mutants and their runner.
- `census/measure_s16.py`: the probe run classified per function.
- `census/replay_dir.py`: offline replay of a query directory on AY build
  12713 with Clean, each query within the live 30 s budget.
- `census/qualify.sh`: one tool-gated test per process on the qualification
  pair.
- `census/dump_core_ir.sh`: the fresh `core` trust-ir dump from a census
  bridge, stopped once the main CGU's module is written (a solver run: the
  bridge proves the per-item modules before the main CGU with AY and Clean).
- `census/payloads.py`: the PAYLOADS.md table.
- `probe/x86_body_probe.rs`: the probe (a copy; place it in
  `crates/trust-cg-verify/examples/` to build it). Its run:
  `S16_ONLY_NAMES=1 RAYON_NUM_THREADS=1 x86_body_probe --cf
  ~/tcg-scratch/runs/core-ir-s16 cf_s16.tsv <smt2 dir> <names>`, the names
  the first column of the class list (`S16_RESPELL=1` for slice 9's older
  dump).
