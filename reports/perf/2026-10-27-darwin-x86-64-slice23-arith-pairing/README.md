# Darwin x86-64 `library/core` — slice 23 (arithmetic congruence pairing and the arithmetic leaf), 2026-10-27

Slice 23 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`,
`x86_source_bound_body/normal.rs`, `x86_source_bound_body/split.rs` and the
replay route in `function_request.rs`) targets the 3 AY-capacity roots of
census-s22 (23 failed roots on AY build 13556 with Clean 5f09e36c; the other
20 are OD-115 no-observable bodies, which stay refused by ruling):
`core::ptr::align_offset::<u8>`, `u64::overflowing_pow` and
`wide_mul_u128::scalar_mul`, as designed and measured in
`~/tcg-scratch/s23-design/` (README §1-§7).

| Ruling | Stage | Rule | Design |
| --- | --- | --- | --- |
| OD-205 | 23a | arithmetic congruence pairing: a machine row whose TV-1 stamp names a source operation of its operator key, and whose own transcription is `K(c, d)`, is spelled as the source's `K(a, b)`, and the theorem claims `a = c` and `b = d`; the theorem without the pairing decides a paired theorem's refutation | §2.1, §2.2, §6.1 |
| OD-206 | 23b | an obligation whose exact replay is neither Valid nor refuted is replayed once as its generalization over arithmetic leaves; Valid credits, anything else leaves the exact outcome | §2.3, §6.2 |

Host: the shared x86_64 Mac (4 cores, Darwin 22.6, macOS 13.7.8 22H730,
i7-7920HQ), 1-minute load 3-6 during the measurements (each record keeps its
own; other lanes built and replayed throughout); every build through
`scripts/trust_cargo.sh` with the local overlay `x86-stage1-ay13556`
(`targo --unverified`, `nice -n 19`, `-j2`, through `build-slot`; no proof
claim about any build). Replayer pair: AY 0.27.0 build 13556 with Clean
5f09e36c (`QUALIFIED_AY`, the overlay's `bin/ay` and `bin/clean`). Branch
`feat/x86-body-slice23` (worktree `~/tcg-scratch/wt-s23`) from main
`f7881289c` (slices 1-22), merged with origin/main four times, last at
`7dc9b3ef3` (among them slice 22's hostile review, OD-210/OD-211, and
OD-216 to OD-219). Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.

**Census:**

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-1fb7620a5-ay13556` (baseline) | `main` `1fb7620a5` | 13556 | `71236c17…` | 23 | 4360 s |
| `core-x86_64-darwin-O0-proof-slice23-ay13556` | `f2a032c4d` (slice 23 on `1fb7620a5`, the landed head) | 13556 | `e01bfcec…` | **20** | 1957 s |

Both bridges were built in their own detached trees with the `t011` engineering targo over the
AY 13556 lane's compiler, sysroot and tools (Clean 5f09e36c). `census_compare.py`: 3 promoted
(`ptr::align_offset::<u8>`, `u64::overflowing_pow`, `wide_mul_u128::scalar_mul`, each bound with
no independently checked proof → bound, replays Valid), 0 newly failing, 0 named mismatches,
0 refuted bodies, no resource-budget refusal. All 20 remaining roots are of the `no observable`
class (`root_classes.py`): the OD-115 floor. The baseline's `failed_roots.jsonl` is byte-identical
to census-s22's (sha `46541325…`).

An earlier census of `9f7aa5b2b` (before the review fixes and before main's OD-210/216 path fix
and OD-223's checker deadline) also had 23: the same 3 promoted, and 3 newly failing that were not
slice 23's. `exp_u128` and `parse_decimal_seq` hit an AOT walk that named no module; main
`451c75834` fixed it. `u64::leading_zeros` hit a Clean re-check that ran past the solve budget;
main `1fb7620a5` (OD-223) fixed it. Neither theorem changed.

## Soundness notes first

- **Nothing is trusted in addition** (both rulings), and since the hostile
  review of `9f7aa5b2b` (§9) that holds for OD-205 by re-derivation, not by
  argument alone. OD-205 is congruence of one SMT-LIB function (`K(a, b) =
  K(c, d)` when `a = c` and `b = d` at the bits `K` reads), with the operand
  equations CLAIMED and proved, never assumed. The review found that the
  step making the congruence apply was builder code no consumer re-derived:
  the export carried the paired statement alone, whose canonical spelling
  has value-numbered every paired name into the source's, so check (3) (a
  paired name's walk definition is its part of `K(c, d)`), the new
  definitions and the operand claims could not be re-checked. A paired
  theorem now carries its pairing record (each paired row's key and
  operands, each paired name's WALK definition read from the walk's table,
  and the theorem before its spelling with the spelling's choices); the
  verifier, before any replay, and every export, before any publication,
  re-derive from it check (3), the new definitions, the unconditional
  operand claims and that the statement is the record's spelling, which
  binds the record to the published bytes. A record that does not
  re-derive, or none, and the paired theorem is never replayed or
  published. What stays trusted is slices 1 to 22's (the walk's and the
  source's definitions and claims, the spelling). OD-206 is instantiation (a
  claim proved for every value of a fresh input holds for the operation's
  value), and every consumer re-derives the generalization before
  publishing it.
- **A concern found and fixed in the implementation (false refutation, not
  false credit).** The design's operand claims are unconditional, which is
  stronger than the theorem needs: a correct lowering whose operand differs
  from the source's where the operation's value does not matter has a
  REFUTED paired theorem. It happens: the selector's signed division divides
  by its fixed-up divisor (1 where the source divides by -1), so pairing an
  `idiv` row refutes a correct `i64 % i64` (`SremPaired`, tests only). Two
  departures close it: no `idiv` row is ever paired, and **the arbiter**: a
  paired theorem's refutation (whole, part or claim) is decided by the
  theorem without the pairing (the exact spelling of slices 1 to 22), so a
  refutation only ever comes from the exact spelling.
- **The pairing admits nothing.** The theorem without the pairing is built
  and checked first; its refusal is the body's. A body slices 1 to 22 refuse
  (the 20 OD-115 floor roots among them) stays refused, and a paired body
  always has its arbiter.
- **The definitions-only build is no theorem.** OD-205's gate (§2) builds
  the paired definitions WITHOUT operand claims (`ArithPairs::
  DefinitionsOnly`) only to compare its bytes with the theorem without the
  pairing; it is dropped, never replayed, exported or checked, and its only
  effect is to choose between two sound theorems (the paired one, with its
  claims, or the unpaired one).
- **The first implementation's gate missed the target on the real bytes** (a
  completeness fault, found before any credit): a gate on each row alone
  (the canonical spelling of `(= K(a, b) K(c, d))` over the definitions it
  reads) called both of `align_offset`'s shifts and its product one term and
  paired nothing, while the theorem's own spelling states the four barrels
  apart. The gate is now the theorem's (§2).
- **OD-206 never refutes and never replaces.** A satisfying model of a
  generalization is no counterexample (OD-200's rule); an exact refutation
  is never generalized; the generalization is never the default spelling
  (a mutant that makes it so fails the range-fact control: u8
  `carrying_mul_add`'s claim needs the product's range).
- A source stated path by path (slice 6) and the merged spelling (evidence
  only) pair nothing.

## In short

- **Real bytes** (§1): on census-s22's own `core` dump the three roots close
  with the production route on the qualification pair: `align_offset::<u8>`
  whole (paired) **4.7 s** (Clean 8.8 s; slice 22's bytes time out),
  `u64::overflowing_pow` by its whole generalization **0.76 s** (the exact
  theorem: AY `unknown`, self-check rejected), `scalar_mul` by its whole
  generalization **4.5 s** (the exact theorem times out).
- **Whole core** (§4): 16 functions' theorems change; 15 are
  census-certified and all 15 still certify.
- **Goldens** (§5): 5 earlier theorems move, each reviewed equivalent
  (256-input sweep, z3 unsat).
- **Controls** (§2, §3, §9): 13 fixtures, 11 wrong lowerings refuted, 20 rule
  mutants each failing a control (none passes all of them; with no mutant all
  55 controls pass).
- **Qualification** (§6): all 54 tool-gated lanes pass on the reviewed head,
  one test per process; slice 23 records four exact gaps, three credited
  through their generalizations. After the review (§9) the 7 lanes the fixes
  touch pass again.
- **The hostile review** (§9): OD-205's pairing is now re-derived by every
  consumer from a pairing record (check (3), the new definitions, the
  operand claims and the statement as the record's spelling); check (3) has a
  meaning-level control; shift keys are 32- and 64-bit ones only; the arbiter
  in parts has a real-path control; two surviving mutants now fail. No `core`
  theorem's bytes move, before or after the merge with origin/main.

## 1. The three roots on the real builder's bytes

**The dump.** `census/dump_core_ir.sh` (slice 22's script on the AY 13556
overlay; it runs AY, so it ran with no other replay of this lane) over
`runs/s23.dylib` (sha256 `0f232201…`), a release bridge built from this
branch at `addf2c93f` (`~/tcg-scratch/build_bridge.sh`, `targo
--unverified`): `runs/core-ir-s23`, 88 files, **every file byte for byte
census-s22's dump `runs/core-ir-s22`** (slice 23 changes the verifier, not
the trust-ir the bridge emits). The three roots' slice-22 theorems over it are
byte for byte census-s22's own `x86-body-dump=` queries (the design's
`data/dump_sha256.txt`), so the real bytes below are the census's.

**The probe.** `probe/x86_body_probe.rs` is slice 22's probe with one
addition, an OD-206 generalization writer (`S23_GENERAL=1`: every unit's and
every claim's `replay_generalized`), and the arbiter's theorem
(`<h>.unpaired.smt2`). Built from the branch at each stage
(`probe/build_probe.sh`, never committed) and run over the dump restricted
to the three names (`probe/run_probe.sh`). `census/measure23.py` replays
each unit one-shot (`ay -smt2 Q --strict-proofs --proof P --proof-format
alethe`, then `clean cert verify-external`, 30 s each, the bridge's command
lines) by the production route: the unit exact; without a verdict its
generalization; then claim by claim, each exact, then its generalization.

| root | slice 22 (census-s22) | p1: the row-level gate | p2: the theorem-level gate (OD-205 + OD-206) |
| --- | --- | --- | --- |
| `align_offset::<u8>` | timeout (claims 15, 24 of 25) | bytes unchanged (nothing paired) | **whole 4.67 s** (Clean 8.81 s) |
| `u64::overflowing_pow` | timeout (claim 8 of 15) | = p2 | exact `unknown` 3.5 s (self-check rejected); **whole generalization 0.76 s** |
| `wide_mul_u128::scalar_mul` | timeout (claim 1 of 4) | = p2 | exact timeout; **whole generalization 4.55 s** |
| **roots closed** | 0 | 2 | **3** |

p3 (merged with origin/main `4bf54e061`, whose OD-210 makes the probe name
the module: `core` defines none of the trusted routines, and its dump names
none) and p4 (the final code, merged with `c06393ad6`, OD-216 to OD-218)
state the three roots' queries byte for byte as p2, and so do their
whole-core runs (§4); the last merge changes no verifier file.

Every other query of the three roots, replayed for the record
(`census/replay_all.py`, one-shot, load 4-5), so that the route has an
answer wherever the whole theorem misses:

- `align_offset::<u8>`: slice 22's theorem (the arbiter, `.unpaired`) times
  out as in the census; the paired theorem's generalization is `sat` (0.12
  s: no verdict, OD-200), and all 24 distinct claims certify exact (max 2.9
  s, claims 12 and 13, a remainder whose generalization is `sat`: they need
  its bits). The three shift operand claims are one conjunct after the
  spelling (`(= ((_ extract 5 0) s23) ((_ extract 5 0) m40))`), as the
  design measured it (1.0 s alone).
- `u64::overflowing_pow`: claim 8 (the census's stop) times out exact and
  its generalization certifies in 0.12 s (the design: 0.12 s); claims 9, 14
  and 15 certify exact (5.8, 9.8, 3.1 s) and generalized (0.13, 0.38, 0.12 s);
  the other 11 certify exact (at most 0.13 s).
- `scalar_mul`: claims 1 and 2 time out exact, their generalizations certify
  in 3.2 and 3.9 s (the design: 2.8 and 3.5 s); claims 3 and 4 certify exact
  (0.59, 0.55 s).

## 2. OD-205: arithmetic congruence pairing

**Claim.** An operator key is an operation, its operand width and its
signedness (`ArithKey`): `mullo(w)` (a product's low half; `imul r, r`,
`mul`'s RAX), `umulwide(n)` (`mul`'s RDX:RAX, the overflow result of
`CheckedUmul`), `udiv`/`urem(w)` (`div` of OD-178's canonical dividend),
`shl`/`lshr`/`ashr(w)` at w = 32 or 64 (`shl`/`shr`/`sar r, cl` with a
count the walk does not know, the barrel `shift_modulo_width` reads at
log2(w) bits, the bits of CL x86 reads at those widths; an 8- or 16-bit row
is refused by name, §9). The walk
records each such row (`MachineArith`: stamp, key, operands `(c, d)`, the
names it defines). A row is paired when its TV-1 stamp names exactly one
source operation of the theorem's units with the same key (`same_key`: the
key itself, width and signedness included), no operand on either side is a
constant by value (`closed_term`), every name it defines is, as the walk
defined it, its part of `K(c, d)` (its own transcription; a stamp alone
never pairs), and `K(a, b)` and `K(c, d)` are not one term already. Its
names are then defined as the same part of the source's `K(a, b)`, and the
theorem claims `a = c` and `b = d` (a shift: the counts' low log2(w) bits),
each a claim of its own, unconditionally, first among its unit's claims
(OD-197 splits them; a part states them in its region). A commutative key's
operands are matched by position, or crossed when that makes more of them
one spelling. OD-178/179's stop terms and the machine's #DE read the
operands as before; a row of another key keeps its exact term; slice 14's
`(ite C S X)` keeps every division this rule does not pair.

**The departures from the design, each measured:**

- **The gate is the theorem's** (`owner_theorems`). The theorem without
  the pairing is built and checked first (its refusal is the body's). A
  paired build that is refused or fails its check leaves that theorem, and
  so does a pairing the theorem's spelling absorbs: the paired rows'
  definitions with no operand claim (`ArithPairs::DefinitionsOnly`, no
  theorem) give the theorem without the pairing byte for byte. The first
  implementation gated each row (`spelled_alike`: the canonical spelling of
  `(= K(a, b) K(c, d))` over the definitions it reads); a traced probe
  (`probe/trace_pairing.py`, `trace_pairing2.py`, PAYLOADS) showed it calling
  both of `align_offset`'s shifts, its product and its divisions one term,
  over the definitions they read and over all of them (65-69 ms each), while
  the theorem's own spelling, whose amount `s23` is a kept name of several
  uses, states the barrels apart: p1's bytes were census-s22's. The
  absorbed control is `MulOverflowPaired` (`a.overflowing_mul(b).1` by
  `mul`): its paired build's operand claims are identities the spelling
  drops, but they leave a conjunction against `true` where the theorem
  without the pairing is the one equation `(= S M)`; its paired definitions
  alone are that theorem byte for byte, and the owner states it. With the
  comparison off (the mutant `pairing-never-absorbed`) its golden moves; on
  the whole `core` dump it changes nothing (a probe built with the mutants
  and run with `TCG_S23_MUTANT=pairing-never-absorbed` states every query
  byte for byte as p3). `MergedAmountAbsorbed` (`align_offset`'s merged
  amount without its trailing-zero guards) pairs nothing the spelling keeps:
  there the theorem's spelling names each shift once with the source's. In
  four variants of it (counts in the entry block, the trailing-zero pattern,
  separate blocks, the alignment guard) the owner pairs nothing either, so
  no unit fixture reproduces the real bytes' kept-apart amount, which the
  real-bytes probe measures instead.
- **No `idiv` row is paired.** The selector's signed division divides by
  its fixed-up divisor (`select_div`: 1 where the source divides by -1), so
  the divisor claim would refute a correct lowering (`SremPaired`, paired
  only inside `with_signed_division_pairing`, tests only). `bvsdiv` and
  `bvsrem` stay leaves for OD-206.
- **The arbiter.** A paired theorem whose replay (whole, part or claim) is
  refuted is decided by the theorem without the pairing, replayed by the
  same route: its Valid credits (the export carries it), its refutation
  refutes, anything else is no verdict.
- A source stated path by path (slice 6) and the merged spelling (evidence
  only) pair nothing.

| Control | Kind |
| --- | --- |
| `ImulPairedOperandSpelling` (`i32::wrapping_mul`: operands through the 64-bit registers), `ShrClPaired`, `SarClPaired`, `ShlClPaired` (a variable shift with the selector's count mask edited out: equal in the low 5 or 6 bits only), `AlignOffsetU8` (two shifts and a product of their difference) | fixtures, paired (`PAIRED`), each theorem holds on samples |
| `MulOverflowPaired`, `UdivPaired`, `SremPaired`, `U64OverflowingPowLeaf`, `ScalarMulLeaf`, `U8CarryingMulAdd`, `MergedAmountAbsorbed` | fixtures, unpaired (one term already, or absorbed, or an `idiv`) |
| `a_shift_pairs_at_its_count_bits` | the paired `ShrClPaired` states one barrel and holds; the whole counts claimed equal would refute it |
| `a_pairing_the_spelling_absorbs_leaves_the_theorem_without_it` | `MulOverflowPaired`: paired build differs (its shape), definitions alone absorbed, owner unpaired (slices 1-22's bytes); `MergedAmountAbsorbed`: paired build already slices 1-22's; `AlignOffsetU8` and slice 18's `Mul/commuted`: not absorbed, owner paired |
| `a_refuted_paired_theorem_is_decided_by_the_theorem_without_the_pairing` | `SremPaired` paired (tests only) is refuted on samples; its arbiter holds and is slices 1-22's theorem |
| `every_fixture_the_pairing_moves_keeps_its_verdict` | every earlier fixture (slice 18's inventory, slices 14 and 22) and wrong lowering whose paired build differs: correct ones still hold, wrong ones still refuted |
| `the_operator_keys_are_distinct_functions`, `the_keys_pair_only_at_one_width_and_signedness` | every two keys at 1-8 bits are distinct functions; a key pairs only with itself |
| `the_canonical_forms_are_identities_exhaustively` | commutative order and the low half of a widening product, every operand pair at 1-8 bits |
| `a_row_of_another_key_is_not_paired` | a key-differing row keeps its exact term |
| wrong lowerings, hand-built LIR (`slice_twenty_three_refutations`): a product's wrong operand; a 32-bit product of the low halves for the 64-bit product (another key, unpaired); `div` by a wrong divisor; `idiv` for `div`; `sar` for `shr`; a shift count from another register; `div` with a stale high half | refuted on samples (`every_slice_twenty_three_refutation_is_refuted`) and by AY with counterexamples (§6) |
| `a_refuted_paired_theorem_whose_unpaired_theorem_certifies_is_credited`, `a_refutation_the_theorem_without_the_pairing_confirms_stands` | real-path controls of the arbiter (fixture AY and Clean, as OD-197's) |

| Mutant (`fails-before/mutate23.py`, `TCG_S23_MUTANT`) | Fails (the slice-23 and negative-memo controls; with no mutant all 45 pass) |
| --- | --- |
| `pair-no-operand-claims` | 6: `every_slice_twenty_three_refutation_is_refuted` (the product's wrong operand certified), `every_fixture_the_pairing_moves_keeps_its_verdict`, `a_shift_pairs_at_its_count_bits`, the arbiter, the absorbed control, the golden |
| `key-no-width` | 9: `the_keys_pair_only_at_one_width_and_signedness`, `a_row_of_another_key_is_not_paired`, the root shapes, the range fact, the golden, ... |
| `key-no-signedness` | 4: `the_keys_pair_only_at_one_width_and_signedness`, `a_row_of_another_key_is_not_paired`, `every_slice_twenty_three_refutation_is_refuted` (`sar` for `shr` certified), `every_fixture_the_pairing_moves_keeps_its_verdict` (slice 10's `ShrU64/sar` certified) |
| `pair-stamp-only` | `a_row_of_another_key_is_not_paired` |
| `shift-key-full-count` | 6: `a_shift_pairs_at_its_count_bits` (the correct unmasked count refuted), the owner, the arbiter, the golden, ... |
| `comm-creation-order` | `the_product_operand_order_is_independent_of_creation_order` |
| `paired-refutation-stands` | both arbiter real-path controls |
| `pairing-never-absorbed` | 4: the absorbed control (`MulOverflowPaired` paired), `pairing_moves_exactly_the_paired_shapes`, the arbiter, the golden |

## 3. OD-206: the generalization over arithmetic leaves

**Claim.** `split::generalize` (`normal::generalized`): the obligation's
canonical terms, `comm` (a product's non-constant operands in one order by
a STRUCTURAL key, never creation order) and `wide` (an n-bit product where
the widening product of the same operands occurs is its low half), then
every arithmetic node (a product of two non-constant terms, a quotient or
remainder by a non-constant divisor, a variable shift's barrel, recognized
from `shift_modulo_width`'s stages) a fresh free input `ar{k}` of its width,
numbered by structural first occurrence; a definition that becomes a bare
leaf is that leaf; the definitions no claim reaches drop; a claim that
becomes an identity drops; none is stated without an arithmetic node and a
claim. The route (`x86_claims_after`): whole exact, then (neither Valid nor
refuted) its generalization once; then OD-197's claims, each exact, then
its generalization. `x86_generalized_verdict`: Valid credits what it
generalizes; any other outcome, a satisfying model included
(`X86_BODY_GENERALIZED_SAT`), leaves the exact outcome; an exact refutation
is never generalized. The export records each crediting generalization
(`X86UnitGeneralized`), and every consumer re-derives it
(`X86BodyClaims::check_generalized`) before publishing it. The negative
memo key carries the route (`generalized`), so a memo hit on the exact
obligation does not stop the generalization.

| Control | Kind |
| --- | --- |
| `the_generalization_is_an_instantiation` | every fixture's generalization, instantiated at its nodes' values, evaluates as the exact obligation on samples |
| `the_root_shapes_generalizations_hold`, `the_range_fact_generalization_is_satisfiable_and_the_exact_theorem_holds` | the three roots' shapes generalize and hold; u8 `carrying_mul_add`'s generalization is falsified on samples (`u8*u8 < 2^16` is lost), its exact theorem holds |
| `the_leaves_are_numbered_by_first_occurrence`, `the_product_operand_order_is_independent_of_creation_order` | one spelling whatever order the table created its terms in |
| `a_generalization_needs_an_arithmetic_node_and_a_claim`, `the_arithmetic_nodes_are_the_keys` | none without a node; the nodes are exactly the keys' terms |
| `the_generalization_verdict_rule`, `a_forged_generalization_record_is_refused`, `the_generalization_is_a_replay_route_of_its_own` | Valid credits, `sat` neither credits nor refutes; a record that is not the re-derived generalization is refused; the memo key's route |
| `an_exact_replay_without_a_verdict_whose_generalization_certifies_is_credited`, `a_satisfiable_generalization_credits_nothing_and_refutes_nothing`, `an_exact_refutation_is_never_generalized`, `a_memo_hit_on_the_exact_obligation_still_runs_its_generalization` | the four real-path controls the task named (fixture AY and Clean, as OD-197's) |

| Mutant | Fails |
| --- | --- |
| `generalized-sat-refutes` | `a_satisfiable_generalization_credits_nothing_and_refutes_nothing` (a correct lowering reported refuted), `the_generalization_verdict_rule` |
| `generalize-not-rederived` | `a_forged_generalization_record_is_refused` |
| `leaf-creation-order` | `the_leaves_are_numbered_by_first_occurrence` |
| `generalize-first` | 19, `the_range_fact_generalization_is_satisfiable_and_the_exact_theorem_holds` (u8 `carrying_mul_add` loses its exact theorem) and every real-path control among them |

## 4. The whole core

`probe/run_probe_all.sh` over every function of the dump (3,457 functions,
4,013 queries), against slice 22's probe at 22c over the same dump
(`s22-run/all/c`, = census-s22's bytes), `census/regress.py` (each function
whose theorem bytes change, with its census-s22 body-trace outcome) and
`census/measure23.py` over the census-certified ones:

| | functions whose theorems change | census-certified among them | still certify |
| --- | ---: | ---: | ---: |
| slice 22 → slice 23 | 16 (`align_offset::<u8>` and 15 others) | 15 | **15** |

The whole-core runs of p3 and p4 (the final code, over `runs/core-ir-s23`)
are byte for byte p2's (4,013 queries, every verdict column alike).

| function | changed units | still certify (one-shot, max) |
| --- | --- | --- |
| `i32::wrapping_mul`, `u64::wrapping_mul`, `usize::wrapping_mul` | whole | 0.27, 0.067, 0.067 s |
| `u32::carrying_mul_add` | whole | 0.17 s |
| `rotate_left::<u64>` (intrinsic), `u64::rotate_left` | whole (25,331 → 775 bytes) | 0.18, 0.07 s |
| `u32::div_ceil`, `usize::is_multiple_of` | whole | 3.0, 4.1 s |
| both `unicode_data::bitset_search` | whole | 4.7, 4.7 s |
| `dec2flt::lemire::compute_float::<f64>`, `<f32>` | parts 2, 4, 6 of 6 | 3.3, 3.4 s |
| `DecimalSeq::right_shift` | parts 1, 2, 5 of 5 | 2.8 s |
| `grisu::format_exact_opt` | part 3 of 12 (22,547 → 11,727 bytes) | 3.0 s |
| `grisu::format_shortest_opt` | part 7 of 12 | 2.7 s; its part 12 (unchanged bytes, a 64-bit widening product) timed out at load 6 and its generalization certifies in 2.2 s |

The design expected 2 (`i32::wrapping_mul`, `u32::carrying_mul_add`) plus
`align_offset`; its prototype paired on the final bytes. Every change is a
pairing the theorem's spelling does not absorb; none costs a credit.

## 5. Goldens

The pairing moves 5 theorems of earlier goldens: slice 1's `Mul` and
`MulU32` (operands spelled through the registers: two operand claims),
slice 10's `ShrU64` and `SarI32` (12,079 → 266 bytes: the barrel is the
source's, the theorem is the count's low 6 bits), slice 14's `DivOnOnePath`
(the division on one path paired). Every one reviewed by
`review/review23.py` (slice 22's symmetric review: a 256-input sweep of the
union of free inputs, equal claim values and equal shared definitions; z3
4.15.4 on both theorems with their defined names renamed apart, asserting
the claims or a shared name differ): **0 mismatches, 5 of 5 unsat**. The
design expected `I64OverflowingMul`, `U64CarryingMulAdd` and every
`pair_divisions` fixture to keep their bytes; all do but slice 14's
`DivOnOnePath`, whose division on one path the theorem without the pairing
states through slice 14's `(ite C S X)`. Slice
23's own golden (`slice23_snapshots.smt2`, 20 theorems: each fixture and,
where it has one, its generalization; the review's `ShrClCleanBool` and its
generalization appended, §9, no earlier byte moved) is new. The custody tests of slices
18, 19 and 22 (each earlier spelling re-renders every earlier golden) build
their canonical side without the pairing, which a spelling without the
canonical groups never applies.

## 6. Qualification

Every tool-gated x86 body test, one per process and each through
`build-slot` (`census/qualify23.sh` over `census/qual_list.txt`: every
slice's replay, refutation and credit lanes, slice 9's spellings, the
canonical migration pair, the envelope's two lanes and slice 22's new
module-routine lane, 53 tests; then `census/qualify_ignored.sh`, the
explicit deadline-bound lane at its 300 s budget), on AY 13556 + Clean
5f09e36c from the overlay (`TCG_X86_BODY_QUALIFY_AY`,
`TCG_EXTERNAL_CLEAN_CHECKER`), `nice -n 19`, each test's replayed queries
kept (`TCG_X86_BODY_QUALIFY_DUMP`), at 1-minute load 2.9-4.9, on the final
code (`testbin_tB4`, `75a1f5eac`): **all 54 pass**.

- **The earlier slices' recorded gaps keep their outcomes** (slice 1's
  `MulI16`, slice 9's `LongChain`, slice 11's `MulU128`, slice 14's two
  constant divisions, slice 16's `LongChain` parts, slice 22's
  `U128MulConst`); none leaves and none joins. Slice 20's three variable
  `I128` shifts (deadline-bound) certify in the explicit 300 s lane in 27.0,
  20.5 and 20.0 s. The moved goldens' theorems (slice 1's `Mul`, `MulU32`,
  slice 10's `ShrU64`, `SarI32`, slice 14's `DivOnOnePath`) certify in their
  lanes. A first run on the code before the last merges failed slice 1's
  evidence lane for the concatenated encoding: its plain spelling counted
  `Mul`'s and `MulU32`'s operand claims as observed items; that lane now
  builds slices 1 and 2's evidence without the pairing (OD-205's claims are
  no observable).
- **Slice 23's exact theorems:** 8 of 12 fixtures certify (0.1-1.0 s); four
  are recorded gaps (`KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE`, each with its
  offline 300 s output): `SremPaired` (an `idiv`, never paired; still no
  answer at 300 s), `U64OverflowingPowLeaf` (AY's self-rejection, as the
  real root), `ScalarMulLeaf` (a timeout; offline `unsat` after 59.4 s, as
  the real root) and `U8CarryingMulAdd` (a 32-bit `imul` against the
  source's 16-bit product, two keys; offline AY's self-rejection after
  57.4 s).
- **Their generalizations:** `SremPaired` 1.1 s, `U64OverflowingPowLeaf`
  0.2 s and `ScalarMulLeaf` 14.1 s certify, and the credit lane credits
  their rows through the route with a generalization record every consumer
  re-derives; u8 `carrying_mul_add`'s is satisfiable (`ar1 = 32768`: the
  product's range lost), so its rows stay unverified, never refuted.
- **All 7 slice-23 wrong lowerings** are refuted by AY with
  counterexamples (0.1-1.3 s), and no row of one is credited.

## 7. Gates

On the final code (`75a1f5eac`, merged with origin/main `c06393ad6`; the
branch's last merge, to `7dc9b3ef3`, changes no `trust-cg-verify` file and
none of these gates' tests):

| Gate | Result |
| --- | --- |
| the solver-free x86 body suite (`x86_source_bound_body::tests::`, every library test but the tool-gated lanes) | **440 passed, 0 failed, 20 ignored** (`logs/suite_final.log`) |
| the slice-23 and negative-memo controls with no mutant (`mutants3`, `none`) | 45 passed |
| `trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus` | 9 passed and 5 passed (`logs/codegen_final2.log`) |
| `trust-cg-lower --lib` | 2113 passed (on `bac0efc68`; slice 23 changes no lowering crate and the later merges none of its tests) |
| `scripts/check_fmt.sh` (the 6808 package's `targo fmt`) | OK |
| `targo tippy -p trust-cg-verify --lib --tests` (the 6808 package) | not run: that package's `targo` cannot resolve the workspace (it refuses the `[trust] compiler_timeout_secs` field of the pinned AY manifest, then finds no `ay-pb`), as on this host since slice 19 (`logs/tippy_verify.log`) |
| `python3 scripts/check_documentation.py --check` | OK |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK (the two slice-23 printers are in `IGNORED_TESTS`) |

## 8. Reproducers (this directory)

| File | What |
| --- | --- |
| `probe/x86_body_probe.rs`, `probe/build_probe.sh`, `probe/run_probe.sh`, `probe/run_probe_all.sh` | the local probe (never committed; it names a module that defines none of the trusted routines, OD-210) and its runs over the three roots and the whole core |
| `probe/trace_pairing.py`, `probe/trace_pairing2.py` | the temporary traces (never committed) that found the row-level gate's miss |
| `census/dump_core_ir.sh` | the fresh `core` dump from the branch's bridge |
| `census/measure23.py`, `census/replay_all.py`, `census/probe_run.py` | the production route over a probe run's queries (exact, generalization, claims) and the replay of every query; `probe_run.py` is the design's runner |
| `census/regress.py` | the whole-core regression set against census-s22 |
| `census/qualify23.sh`, `census/qualify_ignored.sh`, `census/qual_list.txt` | one tool-gated test per process on the qualification pair, each through `build-slot` |
| `census/run.sh`, `census/build_test.sh`, `census/chain_final.sh`, `census/mutants_final.sh`, `census/final2.sh` | the lane's build wrapper and the gate chains (`final2.sh`: the final one) |
| `census/payloads23.py` | the PAYLOADS.md table |
| `review/review23.py`, `review/golden_write.sh` | the golden review and the golden rewrite with digest pinning |
| `fails-before/mutate23.py`, `fails-before/run_mutants.sh` | the 20 rule mutants and their run |
| `review-fixes/` | the review's fixes (§9): the lane's build and probe wrappers (`run.sh`, the t011 targo; `build_test.sh`, `build_probe.sh`), the chains (`chain_w2.sh`: build, controls, probe before the merge; `chain_mut.sh`: the mutants; `chain_final.sh`: the gates, the probe and the qualification after the merge; `chain_final4.sh` and `chain_final5.sh`: the same after the second and third merges), the probe's pairing re-derivation (`x86_body_probe.pairing.diff`), and the review's two z3 scripts (`stale_rdx.py`, `shift_sem.py`) |

## 9. The hostile review of `9f7aa5b2b` and its fixes (2026-10-28 to 2026-11-02)

The review of the head `9f7aa5b2b` found five things; each is closed here,
each with a control that fails under the mutant written for it (the
fails-before table below; `fails-before/mutate23.py` now holds 20 rule
mutants).

1. **Trust: the pairing was builder code no consumer re-derived.**
   `retain_x86_body` exported the paired statement alone, so check (3) (a
   paired name's walk definition is its part of `K(c, d)`), the new
   definitions and the operand claims were trusted code, against OD-205's
   "trusted in addition: nothing", while OD-206's generalization was
   re-derived. Re-derivation turned out to be feasible: the spelling of
   slices 6 to 19 (the cone, single-use inlining, slice 17/18's value
   numbering cascade and slice 19's canonical spelling) is a deterministic
   function of the theorem's definitions, its two sides and a handful of
   choices, now one function (`spell_statement`, the builder's tail moved
   byte for byte; the whole-core probe below is the proof that it moved
   nothing). A paired theorem now carries its **pairing record**
   (`X86BodyPairing`): each paired row (key, the source's `(a, b)`, the
   row's `(c, d)`, a commutative crossing, and each name with its part and
   its WALK definition, read in `build_theorem` from the walk's own table,
   never from `pair_arithmetic`), and the theorem as built before its
   spelling with the spelling's choices (`SpellingChoice`).
   `X86BodyPairing::check` re-derives check (3), each paired name's
   definition as the same part of the same key's `K(a, b)` (in a theorem
   definitional in order, `a`, `b`, `c`, `d` reading only earlier names),
   each operand claim of the bits `K` reads (`ArithKey::read_operand`) as an
   unconditional conjunct, and that the statement is the recorded theorem's
   spelling, which binds the record to the published bytes; a paired
   theorem without a record is refused (`X86ExportPairing::Paired(None)`).
   The verifier runs it before it replays a paired theorem
   (`SourceBoundX86Body::check_pairing` in `x86_body_explained`): a theorem
   whose record does not re-derive is never replayed, and the theorem
   without the pairing decides, as for a paired build that fails its check.
   Every export carries what publication needs, and
   `replayed_obligations` (which the proof emitter now also calls for every
   paired export) runs `check_x86_body_pairing` first. OD-205's "trusted in
   addition" is therefore nothing again, by re-derivation; what stays
   trusted is slices 1 to 22's (the walk's and the source's definitions and
   claims, a paired name's walk definition among them, and the spelling,
   OD-187). That `K` reads only the claimed bits is fixed code, now swept:
   `a_shift_key_reads_its_amount_at_its_claimed_bits` (exhaustive at 4 and 8
   bits over every 8-bit amount; at 32 and 64 bits the barrel reads its
   amount only through single-bit extracts of its low 5 or 6 bits).
2. **Check (3) had no meaning-level control.** The wrong lowering
   `udiv/high-half-divisor-minus-one` (`mov rdx, b; sub rdx, 1; div b` for
   `xor edx, edx; div b`: it never faults, its quotient is wrong; the
   review's `stale_rdx.py`: the exact theorem `sat`, the stamp-only paired
   theorem `unsat`) is refuted on samples and never paired
   (`every_slice_twenty_three_refutation_is_refuted`,
   `check_three_keeps_a_stamped_div_of_another_dividend_unpaired`); paired
   on its stamp alone (the test switch `with_stamp_only_pairing`, the
   pairing of the mutant `pair-stamp-only`) its theorem holds on samples,
   and its record fails the re-derived check (3), so on the real replay
   path the verifier never replays it
   (`a_paired_theorem_is_replayed_only_once_its_record_re_derives_it`).
3. **Shift keys.** x86 masks CL to 5 bits for an 8-, 16- and 32-bit shift
   and to 6 for a 64-bit one (`shift_sem.py`: the barrel equals x86 at 32
   and 64 bits and differs at 8 and 16, e.g. `shl al, cl` with CL = 8), so a
   shift key is a 32- or 64-bit one only (`ArithKey::admits`), and the walk
   refuses an 8- or 16-bit variable shift row by name
   (`narrow_variable_shift` in `check_row_shape`, before its shift arm,
   which also states 32 and 64 bits only). The selector emits no such row
   (its variable shifts are 32- and 64-bit virtual registers; a narrow shift
   runs in a 32-bit carrier), so no theorem changes. Controls:
   `a_shift_key_is_a_32_or_64_bit_one`,
   `a_narrow_variable_shift_row_is_refused_by_name`.
4. **The arbiter in parts.** `srem_in_parts_pair` (a signed remainder, then
   slice 16's 90-step chain in a block of its own, past the single-query
   bounds) is stated in parts by the production owner, unpaired; with its
   `idiv` paired (tests only) a paired part is refuted on samples and the
   theorem without the pairing, in its own parts, holds. On the real replay
   path (`a_refuted_paired_theorem_in_parts_is_decided_by_the_unpaired_theorem_in_parts`,
   fixture AY keeping every query) the paired parts before the refuted one
   certify, it is refuted, and the queries AY receives next are exactly the
   unpaired theorem's parts; every covered row is credited with exports
   carrying that theorem and its parts. The mutant
   `unpaired-units-are-paired` replays the paired parts again.
5. **Mutants that survived.** `shift-no-value-claim` (a shift claims its
   count but not its shifted value): the wrong lowerings
   `shr/wrong-shifted-value`, `shl32/wrong-shifted-value` and
   `clean-bool/wrong-shifted-value` (the value from another register, the
   count right) are refuted (on samples, and by AY with counterexamples),
   and hold on samples under the mutant.
   `pair-psabi-walk-only` (the clean-bool walk pairs nothing): the new
   fixture `ShrClCleanBool` (a bool parameter and result, so both walks are
   stated) pairs its shift in both walks (two rows of its record, one
   barrel left in the theorem), and the mutant leaves the clean-bool walk's
   barrel apart. (Pairing fewer rows is sound, so this control is
   structural; the other is meaning-level.)

**Fails-before** (`review-fixes/chain_mut.sh`: `fails-before/mutate23.py`
applied, one mutant test build, the files restored, then
`fails-before/run_mutants.sh`, each mutant one process through `build-slot`;
the 55 slice-23 and negative-memo controls on `9068ce11a`, before the merge
with origin/main, which changes no slice-23 file). With no mutant all 55
pass; every one of the 20 mutants fails at least one. The mutants of the
review's findings and the three of the pairing record (bold) now fail:

| Mutant | Controls failing (of 55) |
| --- | --- |
| `pair-no-operand-claims` | 13, among them `every_slice_twenty_three_refutation_is_refuted`, `every_paired_owner_re_derives_its_pairing` (the record's claims), `a_forged_pairing_record_is_refused`, the three arbiter real-path controls, the record's and the golden |
| `key-no-width` | 13, among them `the_keys_pair_only_at_one_width_and_signedness`, `a_row_of_another_key_is_not_paired`, `check_three_keeps_a_stamped_div_of_another_dividend_unpaired`, `every_paired_owner_re_derives_its_pairing` and the golden |
| `key-no-signedness` | 4: `a_row_of_another_key_is_not_paired`, `every_fixture_the_pairing_moves_keeps_its_verdict`, `every_slice_twenty_three_refutation_is_refuted`, `the_keys_pair_only_at_one_width_and_signedness` |
| **`pair-stamp-only`** | 3: `every_slice_twenty_three_refutation_is_refuted` (`udiv/high-half-divisor-minus-one: a wrong lowering holds on samples`), `check_three_keeps_a_stamped_div_of_another_dividend_unpaired`, `a_row_of_another_key_is_not_paired` (before: the last only, a structural one) |
| `shift-key-full-count` | 10, among them `a_shift_pairs_at_its_count_bits`, `the_clean_bool_walk_pairs_its_rows_too` and the record controls |
| `comm-creation-order` | 1: `the_product_operand_order_is_independent_of_creation_order` |
| `generalized-sat-refutes` | 2: `a_satisfiable_generalization_credits_nothing_and_refutes_nothing`, `the_generalization_verdict_rule` |
| `generalize-not-rederived` | 1: `a_forged_generalization_record_is_refused` |
| `leaf-creation-order` | 1: `the_leaves_are_numbered_by_first_occurrence` |
| `generalize-first` | 26 |
| `paired-refutation-stands` | 3: the three arbiter real-path controls, the one in parts among them |
| `pairing-never-absorbed` | 4: `a_pairing_the_spelling_absorbs_leaves_the_theorem_without_it`, `a_refuted_paired_theorem_is_decided_by_the_theorem_without_the_pairing`, `pairing_moves_exactly_the_paired_shapes`, the golden |
| **`shift-no-value-claim`** | 4: `every_slice_twenty_three_refutation_is_refuted` (`shr/wrong-shifted-value: a wrong lowering holds on samples`), `every_paired_owner_re_derives_its_pairing` and `a_forged_pairing_record_is_refused` (a record without the value claim), `a_paired_theorem_is_replayed_only_once_its_record_re_derives_it` |
| **`pair-psabi-walk-only`** | 3: `the_clean_bool_walk_pairs_its_rows_too`, `every_paired_owner_re_derives_its_pairing` (one row, not two), the golden |
| **`unpaired-units-are-paired`** | 2: `a_refuted_paired_theorem_in_parts_is_decided_by_the_unpaired_theorem_in_parts` (real path), `a_refuted_paired_theorem_in_parts_has_an_unpaired_theorem_in_parts` |
| **`shift-key-any-width`** | 1: `a_shift_key_is_a_32_or_64_bit_one` |
| **`narrow-shift-row-generic`** | 1: `a_narrow_variable_shift_row_is_refused_by_name` |
| **`pairing-not-rederived`** (the consumer accepts a record without re-deriving it) | 3: `a_forged_pairing_record_is_refused`, `check_three_keeps_a_stamped_div_of_another_dividend_unpaired`, `a_paired_theorem_is_replayed_only_once_its_record_re_derives_it` (real path) |
| **`pairing-unbound`** (the record re-checked, the statement not compared) | 1: `a_forged_pairing_record_is_refused` (the statements the record does not spell) |
| **`record-walk-from-key`** (the record's walk definitions computed as `K(c, d)`, not read from the walk) | 2: `check_three_keeps_a_stamped_div_of_another_dividend_unpaired`, `a_paired_theorem_is_replayed_only_once_its_record_re_derives_it` (real path) |

**No `core` theorem's bytes move.** The whole-core probe (`probe/run_probe_all.sh`
over `runs/core-ir-s23`, 3,457 functions, 4,013 queries), built from this
lane twice, is byte for byte `9f7aa5b2b`'s run (`s23-run/all/p4`): every
query file identical (`diff -r` empty) and the outcome table identical, on
`2acc76c22` (the fixes, before the merge: `review-fixes/chain_w2.sh`), on
`1ee686147` (merged with origin/main `9d9e1a372`, whose trust-ir pin moves
to `1e05bd01`: `review-fixes/chain_final.sh`), on `e83dccc2c` (merged
again, with origin/main `451c75834`, the unnamed-module lane:
`review-fixes/chain_final4.sh`) and on `33cb58a2b` (merged a third time,
with origin/main `1fb7620a5`, OD-223, whose trust-ir pin moves to
`f4683868`: `review-fixes/chain_final5.sh`). The second probe also
re-derives every paired owner's pairing record as the verifier does before a
replay (stderr only, `review-fixes/x86_body_probe.pairing.diff`): **30
paired owners on the whole core, every record re-derives, none refused**
(19 of them stated in parts; the 16 functions whose bytes slice 23 moved
are among them, and a paired theorem in parts whose parts' bytes the
pairing does not move is a paired owner too). `u64::leading_zeros`, the
third newly failing root of the census of `9f7aa5b2b`, pairs nothing and
its theorem is byte for byte slice 22's (`s22-run/all/c`): slice 23 did not
change it.

**Toolchain after the merge.** origin/main's pin brings AY `7ed2ea1da`,
whose manifest carries `[trust] backstop`, which the `x86-stage1-ay13556`
overlay's targo (`d7f143f3b`) refuses (`unknown field backstop`). The
post-merge builds use the `x86-stage1-ay13556-t011` overlay's targo
(`review-fixes/run.sh`): the same stage-1 trustc `d7f143f3b`, the same AY
13556 and Clean 5f09e36c (identical SHA-256), only targo replaced by one
that reads `backstop`; `targo --unverified` only, no proof claim about any
build. The qualification runs AY and Clean from the `x86-stage1-ay13556`
overlay as before.

**Qualification after the review** (`review-fixes/chain_final.sh`, the
lanes the fixes touch, one test per process through `build-slot`, AY 13556
and Clean 5f09e36c from the `x86-stage1-ay13556` overlay, on `1ee686147`,
and again on `e83dccc2c` and on the final head `33cb58a2b`): **7 of 7 pass
each time**: slice 23's four (its body theorems, now with
`ShrClCleanBool`, which certifies in 0.5 s; its generalizations; every
wrong lowering refuted with a counterexample, the four new ones among them
(`shr`/`shl32`/`clean-bool/wrong-shifted-value`, 0.07-0.10 s, and
`udiv/high-half-divisor-minus-one`, 1.5 s); the credit lane, which now also checks
that every export of a paired theorem carries a record that re-derives it),
and the credit lanes of the three slices whose goldens the pairing moved
(slice 1's canonical lane, slices 10 and 14), which credit paired theorems
through the verifier's new pre-replay check. Under the mutant
`pair-stamp-only` (the mutant test binary, `TCG_S23_MUTANT`), on the same
pair: the refutation lane FAILS, AY verifying
`udiv/high-half-divisor-minus-one`'s paired theorem in 0.54 s (the wrong
quotient credited at the theorem, as `stale_rdx.py` predicts), and the
credit lane PASSES: no row of any wrong lowering is credited, because the
verifier re-derives check (3) from the stamp-only pairing record, refuses
it, never replays that theorem, and the theorem without the pairing refutes
the row.

**Gates after the review** (on `1ee686147`, merged with origin/main
`9d9e1a372`; the rows marked † again on `e83dccc2c`, merged with
`451c75834`, which adds two body tests and two codegen tests; the rows
marked ‡ on the final head `33cb58a2b`, merged with `1fb7620a5` (OD-223,
nine more body tests; the merge's conflicts were the negative memo's key
test, which now mutates both OD-223's checker deadline and slice 23's
generalization route, and the CHANGELOG)):

| Gate | Result |
| --- | --- |
| the solver-free x86 body suite (`x86_source_bound_body::tests::`, every library test but the tool-gated lanes) | **450 passed, 0 failed, 20 ignored** (440 before: the review's 10 new controls); † 452 passed; ‡ **461 passed, 0 failed, 20 ignored** |
| the negative memo's unit tests (`source_bound_negative_memo::`) | ‡ 25 passed |
| the slice-23 and negative-memo controls with no mutant | 55 passed (on `9068ce11a`) |
| `trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus` | 9 passed and 5 passed; † and ‡ 11 passed and 5 passed |
| `trust-cg-lower --lib` | 2113 passed |
| `trust-cg-cli` (`--bin trust-cg emit_proofs`, the proof emitter's tests) | 22 passed; † and ‡ 22 passed |
| `scripts/check_fmt.sh` (the 6808 package's `targo fmt`) | OK; † and ‡ OK |
| `python3 scripts/check_documentation.py --check` | OK; † and ‡ OK |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK with `TRUST_TARGO` naming the 6808 package's targo; from PATH it now stops before any check (`PATH trustc and targo must both be atpkg launcher shims or both be package files`): aterm rewrote the PATH `targo` shim at 09:27 on 2026-11-02, after this lane's earlier runs passed from PATH, a host change, not this lane's |
