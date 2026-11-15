# Darwin x86-64 `library/core` — slice 20 (the remaining domain rules), 2026-10-26

Slice 20 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`,
`x86_source_bound_body/split.rs` and `x86_source_bound_body/indexed.rs`)
admits the domain refusals of census-ay13556 that need no new trust. The
design and its measurement are in `~/tcg-scratch/s20-design/` (README §1-§8,
`data/measured.tsv`, `data/estimate_all.txt`): of census-ay13556's 106 failed
roots, 33 are domain refusals in 11 classes. Slice 20 takes the design's
plan "without 20a": 20c (a switch's binary-search blocks), 20d (a stored
address dead at a DAG join), 20b (`I128` loop-carried values and cut items as
two 64-bit halves), the three singleton rules and the two bounds. Slice 20a
(`I128` division as a runtime-routine contract) is deferred: it would add the
routine contract to what a Formal credit trusts, and closes one root alone
until the 128-bit product certifies (design §6, §7).

| Ruling | Rule | Design |
| --- | --- | --- |
| OD-191 | a `Switch`'s binary-search blocks are dispatch blocks of its block | §3.3 (20c) |
| OD-192 | a stored private address dead at a DAG join is left out (OD-184 at joins) | §3.4 (20d) |
| OD-193 | `I128` loop-carried values and cut items are two 64-bit halves | §3.2 (20b) |
| OD-194 | a variable `I128` shift with an own-range bound; a `bool` read of any stored byte past a join, header, cut or indexed store; undefined bits a non-loop row introduces fixed for the run; slots bounded by their bytes; 1024 candidates | §3.5, §3.6 |

Two more commits ride on the branch, each its own: the x86-64 selector
declares the `I128` division libcall's argument registers (§4, no emitted
byte changes), and the slice 16-18 records' `dump_core_ir.sh` copies no
longer say "No AY runs" (a dump proves the per-item modules before the main
CGU, AY and Clean included, as the design measured).

Host: the shared x86_64 Mac (4 cores), other agents' builds and AY runs
beside this lane throughout (1-minute load 2.6-6.1); every build through
`scripts/trust_cargo.sh` with the local overlay `x86-stage1-ay13556`
(`targo --unverified`, `nice -n 19`, `-j2`; no proof claim about any build).
Replayer pair: AY 0.27.0 build 13556 with Clean 5f09e36c (`QUALIFIED_AY`, the
overlay's `bin/ay` and `bin/clean`). Branch `feat/x86-body-slice20` (worktree
`~/tcg-scratch/wt-s20`), the interrupted lane's WIP `77155d0f6` merged with
origin/main `bf5d4b2c9` (430 commits, among them another lane's owner
changes: `bt r, imm8`, the row-allowlist refusal's operands, `MovMRSib`
general memory; no conflict). Payloads are out of tree;
[PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-bf5d4b2c9-ay13556` (baseline) | `main` `bf5d4b2c9` | 13556 | `c2f8144d…` | 108 | 3157 s |
| `core-x86_64-darwin-O0-proof-slice20-ay13556` | this branch, `104f7bf39` (slice 20 on `bf5d4b2c9`) | 13556 | `e4cb5f44…` | **90** | 3342 s |

**18 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
4 `I128` loop-carried values, 3 functions past the old slot count, 3
binary-search switches (machine blocks that did not correspond one to one), 2
stored-address joins, one each of the masked `I128` shift, the `bool` read of
any stored byte, an `I128` cut item, an indexed store with 784 candidates and a
machine row now in the domain, and 1 bound body now certifying. Both rows were
built by `census13556.sh`, each bridge in its own tree, with no
resource-budget refusal.

## In short

- **Every earlier golden theorem is unchanged** (the solver-free body gate:
  every slice's digest-pinned golden passes byte for byte). The slice-20
  golden is new: 19 fixtures, 30 theorems and parts.
- **Controls.** 19 fixtures over real adapter and selector output (each
  stated, holding on the sampler) and 8 variants (refused by name, or
  stated where the rule says so); 20 wrong lowerings, each refuted by AY with
  a counterexample on the qualification pair; 22 rule mutants, each failing
  at least one control.
- **Qualification** (AY 13556 + Clean, one test per process): all three
  slice-20 lanes pass. Of the 30 fixture theorems and parts, 25 certify
  (0.1-3.7 s); the three variable `I128` shifts are deadline-bound on this
  host (28-38 s of AY; the explicit 300 s lane certifies all three), and
  two one-query production theorems of the `I128` cut fixtures, whose parts
  certify, are recorded gaps (AY proves them, Clean rejects an
  `equiv_simplify` step). Every wrong lowering is refuted with an AY
  counterexample, and every covered row of every certified fixture is
  credited Formal by the production verifier.
- **The 33 roots** (the design's probe on the census bridge's `core` dump,
  this branch's owner, no lift): the 19 that need no `I128` division build a
  theorem, the 14 that do (10 divisions, 1 `I128` guard, 3 cut functions
  that also divide an `I128`) are refused by name, and no other
  root's verdict moves. Replayed one at a time on the qualification pair at
  the 30 s deadline, **16 of the 19 close** (every query Verified): the
  design predicted 17 for this plan. The three that do not are the
  design's: `unchecked_shl` (30.5 s, deadline-bound, as its fixture),
  `wide_mul_u128` (one part times out; the design measured it at 77 s) and
  `fmt_decimal` (a 64-bit division by a variable times out, and Clean
  rejects one part's `poly_simp` step).

## 1. The rules: claim, controls, fails-before

The library gate is `x86_source_bound_body::tests::slice20::` (solver-free;
it runs in the full x86 body suite). The tool-gated lanes are
`slice20_qualification::`. Mutants: `fails-before/mutate.py` guards each rule
behind `TCG_S20_MUTANT=<name>`; one test build serves all of them, and
`fails-before/run_mutants.sh` runs the slice-20 tests and slice 16's
every-point control once per mutant (the unmutated run passes every test).

### OD-191: a switch's binary-search blocks (20c)

**Claim.** For a `Switch` the selector lowers as a balanced binary search
(`emit_switch_bst`: five or more distinct cases in `[0, i32::MAX]`, no jump
table), a machine block of that `Switch`'s LIR block that is neither the
machine's first block nor a jump-table dispatch block, every row stamped with
that `Switch`, made of `cmp r, imm` and `jcc` rows ended by one `jmp`, and
reached only from the switch's other machine blocks (never from itself), is
a SEARCH block: it lowers no LIR block of its own. A route from the switch's
block to a target runs depth first through the search blocks, each `jcc`
taken or not, every compare and branch walked with its Intel SDM meaning
(the flags of `cmp`, `je`'s ZF, `jl`'s SF xor OF; flags reset at each block
boundary, so each search block's own `cmp` is what its `jcc` reads); OD-180's
edge literal is the disjunction of the routes (the default has one per leaf).
A source with such a switch is stated over its DAG (decided from the source
alone). Trusted in addition: nothing; the recognizer only chooses.

| Control | Kind |
| --- | --- |
| `SparseMatch5`, `SparseMatch7`, `SparseMatchShared`, `SparseMatchU8` (`movzx` first), `SparseMatchHighSelector` (cases to 2,000,000,000; a selector with bit 31 set reaches the default through the signed `jl`) | fixtures, every one certified |
| a case under the wrong half; a wrong pivot (the root compares 13 where the median is 34); two leaves' targets swapped; a leaf comparing another value; the default taken on a hit; the signed `jl` over a case above `2^31` (hand-built: the selector keeps its chain for one) | AY counterexamples |
| the same hand-built tree with the unsigned `jb` | holds (the solver judges the order) |
| a tree block with another row; one also reached from an arm's block; one that branches to itself | named correspondence failures |
| `a_searched_switch_is_stated_over_its_dag` | the DAG encoding for a searched switch |

| Mutant | Fails |
| --- | --- |
| `search-any-shape` (any stamped block of the switch's LIR block) | `a_tree_block_outside_the_search_shape_is_no_dispatch_block` |
| `search-any-predecessor` (no predecessor clause) | `a_tree_block_outside_the_search_shape_is_no_dispatch_block`, by its self-looping leaf (added for this mutant: on the first run it failed no control, because a search block another LIR block's machine block reaches already fails the correspondence's successor check) |
| `search-first-route-only` | 6 (the fixtures, the golden, slice 16's every-point control, ...) |
| `searched-switch-per-path` | 6 (`a_searched_switch_is_stated_over_its_dag`, the refutation controls, the fixtures, ...) |

### OD-192: a stored address dead at a DAG join (20d)

**Claim.** At a DAG join, a private byte the incoming paths leave holding
different values, one of them a stored private address, is DEAD after the
join on both sides when no path from the join reads it before a store
overwrites it, by slice 17's one byte liveness (`split::live_bytes`, which
counts every load, indexed access, call or C memory routine while its slot may
have escaped, untracked access and other address use as a read). Dead, it is
unreadable: a source read refuses, a machine read makes no claim. A live one
keeps slice 13's refusal, by name. A liveness error only refuses. Trusted in
addition: nothing new in kind (OD-184's liveness).

| Control | Kind |
| --- | --- |
| `MatchArmTempAddress` (`decode_repr`'s shape: an arm stores `&local` in a temporary it passes to one call) | fixture, certified; its temporary's 8 bytes are dead at the join |
| `MatchArmTempAddressRead` (the temporary read after the join) | refused by name (slice 13's refusal) |
| a machine read of the dead bytes at the join | refused by name, never credited |
| the local the temporary points to holding another value at the call it escapes to | AY counterexample |

| Mutant | Fails |
| --- | --- |
| `join-dead-always` (every such byte dead) | `a_stored_address_dead_at_a_join_leaves_the_relation` (the read variant then refuses at the dead read, not by slice 13's name: never a credit) |
| `join-dead-keeps-first` (the source keeps the first edge's address) | 6 (the machine-read control, the read variant's refusal, the fixtures, the golden, ...) |
| `join-dead-machine-keeps` (the machine's join ignores the dead set) | 6 (the machine refuses at the join: the fixture is not stated) |

### OD-193: `I128` items as two halves (20b)

**Claim.** An `I128` loop-header parameter (slice 12) or cut item (slice 16)
is, at its region's start, two free 64-bit inputs `x{H}v{i}l` and
`x{H}v{i}h`, the source's value their concatenation; on the machine, the pair
of 64-bit virtual registers the rows stamped with the item's copy or
definition leave as their result: the last two OUTPUTS of that group (the
registers whose last write no later row of the group names), the lower
virtual register the low half. On every edge both halves are related and
both registers must hold bits. The stamps only choose: a wrong pair is
refuted or a named refusal. The design's rule ("the last two registers
written") took a 128-bit product's partial products: slice 11's `MulU128`
cut at every clean point was refuted on samples (slice 16's every-point
control), so the outputs rule replaced it. Trusted in addition: nothing.

| Control | Kind |
| --- | --- |
| `U128ShiftLoop`, `U128RadixLoop` (with a 16-byte indexed buffer, slice 17), `U128AccLoop` (`add`/`adc` across the back edge), `U128LiveAcrossCut`, `U128CutParam` | fixtures; every one certified as the library gate states them (loops whole, the cut shapes in parts); the cut shapes' one-query production theorems are the two recorded gaps (§2) |
| no theorem name wider than 64 bits; both halves declared | `an_i128_item_is_two_named_halves` |
| the halves swapped on the back edge; the high half not copied on it; the low half copied into both registers; another `I128`'s low half in the high register; a cut parameter's halves swapped on one edge; the high half overwritten with the low before a cut | AY counterexamples |
| every slice-11 `I128` fixture cut at every clean point | holds part by part (slice 16's control) |

| Mutant | Fails |
| --- | --- |
| `i128-high-unrelated` (no relation for the high register) | `every_slice_twenty_refutation_is_refuted` (the not-copied high half is no longer refuted), the golden |
| `i128-high-pairing-from-low` | 6 (a named refusal at the loops, refuted parts at the cuts) |
| `i128-pair-order-swapped` | 3 |
| `i128-start-halves-swapped` | 3 |
| `i128-machine-high-unset` | 6 |
| `i128-pair-last-two-written` (the design's rule) | slice 16's every-point control (`MulU128`) |

### OD-194: three singleton rules and two bounds

**Claims.** A variable `I128` shift is slice 10's shift modulo 128 (OD-57),
admitted when its amount's own definition bounds it below 128
(`indexed::shift_amount_bound`); a byte any store wrote is `bool`-readable
past a join, header, cut or indexed store as a direct read takes it
(`byte != 0`); an undefined-bits input a machine row outside every natural
loop introduces is fixed for the run (one name per row across every part, the
row runs at most once), so a term of it and the run's fixed inputs is a
closed term at a cut; slots are bounded by their bytes in all (262,144: 64
slots of 4,096 bytes, so every frame admitted before still is) instead of
their count; an indexed access may have 1024 candidates and a function 4096.
Trusted in addition: nothing.

| Control | Kind |
| --- | --- |
| `U128ShlMasked`, `U128LshrMasked`, `I128AshrMasked` (`x << (n & 127)` etc.) | fixtures; deadline-bound on this host (§2) |
| `UnmaskedShl`, `WideMaskShl` (`& 255`) | refused by name; built without the finder, refuted |
| the shift's `shift == 0` select dropped; its `>= 64` selects swapped; the unmasked shift built without the finder | AY counterexamples |
| `CallBoolThroughSlot`, `CallBoolAcrossCut` (`read_ipv6_addr`'s closure) | fixtures, certified |
| `BoolThroughSlotUnwritten` / `BoolThroughSlotTwo` | refused by name / holds for the selector's `(byte + 255) >> 8` |
| a `bool` read of a stored 2 as bit 0 | AY counterexample |
| `F32ParamAcrossCut` (the `f32` parameter's `movss` upper bits past a cut) | fixture, certified |
| `F32CopyInLoop` (a loop row's `movss` read past a cut) | refused by name (carried) |
| the `f32` parameter's register overwritten (`movq`) before the cut | AY counterexample |
| `ManySlots` (70 one-byte slots) / a frame past 262,144 bytes | certified / refused by name |
| a slot's read-back reading another slot past 64 slots | AY counterexample |
| `WideIndexedStore` (784 candidates) / `TooWideIndexedStore` (1100) | certified / refused by name |
| the 784-candidate store one byte past its element | AY counterexample |

| Mutant | Fails |
| --- | --- |
| `shl128-no-bound` | `an_unbounded_i128_shift_is_refused_and_its_theorem_refutes_it` |
| `boolread-any-byte` | `a_bool_read_past_a_join_of_an_integer_store_byte_is_byte_not_zero` |
| `boolread-bool-store-only` (slice 19's rule) | 5 |
| `ufixed-in-loop` | `undefined_bits_a_loop_row_introduces_stay_carried` |
| `ufixed-none` (slice 19's rule) | 4 |
| `slots-count-64` / `slots-total-unbounded` | 4 / `private_slots_are_bounded_by_their_bytes` |
| `candidates-256` / `candidates-unbounded` | 4 / `an_indexed_access_has_at_most_1024_candidates` |

The tables are the second mutant run (`mutants2/`), on the final controls
(one mutated build of commit `8e6816b6c`; each run the slice-20 library tests
and slice 16's every-point control, the unmutated run 19 of 19 passing): all
22 mutants fail at least one control. The first run (`mutants/`, before the
self-looping-leaf control and the five later wrong lowerings) found every
other mutant failing a control too.

## 2. Qualification

`census/qualify.sh` runs each tool-gated lane in a process of its own on
the overlay pair (`TCG_X86_BODY_QUALIFY_AY` and `TCG_EXTERNAL_CLEAN_CHECKER`
its `bin/ay` and `bin/clean`, `TRUST_TARGO` its `bin/targo` for the build).
Five runs, at 1-minute loads 2.9-5.7 (payloads `qual1/` to `qual5/`):

| Run | Code | Outcome |
| --- | --- | --- |
| 1 | the rules and first fixtures | 15 refutations refuted; gaps `U128RadixLoop` (Timeout: a 128-byte indexed buffer carried around the loop), `ManySlots` (`proof-unrenderable`: a 70-term sum), `I128AshrMasked` (Timeout); the shifts `U128ShlMasked`, `U128LshrMasked` Verified at 40.4 and 41.3 s with Clean |
| 2 | the radix buffer at 16 bytes (the real formatters write theirs through a derived address, a 5 KB theorem), three of the 70 slots read back; 20 refutations | both resized fixtures certify (3.6 s, 0.4 s); the three shifts Timeout |
| 3 | the shifts as deadline-bound entries | the gap lane passes; the credit lane stops at `U128LiveAcrossCut`, whose one-query production theorem no lane had replayed |
| 4 | the gap lane replays those production theorems | `U128LiveAcrossCut` and `U128CutParam`: AY `unsat`, Clean rejects an `equiv_simplify` step (`t1.packed.13410`, `t1.packed.10931`) |
| 5 | the two recorded as gaps (`KNOWN_UNCERTIFIED_SLICE_TWENTY`) | **all three lanes pass**: 25 of 30 theorems Verified (max 3.7 s), the 3 shifts Timeout (deadline-bound), the 2 gaps as recorded; 20 refutations with counterexamples; every covered row of every certified shape credited, the gap shapes' rows all awaiting replay |

The explicit lane
`host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget`
(`--ignored`, 300 s budget) certifies the three shifts in 50.2, 51.6 and
71.4 s with Clean at load 4.4-5.4 (`qual5x/`). Offline
(`offline/shifts_*.tsv`, `census/replay_one.py`): at the 30 s budget
`U128ShlMasked` certifies twice in 28.4-28.8 s of AY, `U128LshrMasked`
answers `unsat` after 31.0 and 33.7 s (AY past its own timeout),
`I128AshrMasked` `unknown` at 30.5 s once and `unsat` at 36.5 s once; at
300 s 28.4, 32.7 and 37.5 s; proofs 40-67 MB, Clean 6.5-8.0 s. So they are
`DEADLINE_BOUND_HERE_BY_HOST` entries for `x86_64-apple-darwin` (answers
Verified or Timeout), which slice 20's lanes now read as slices 1, 12 and 14
do (`settle_here`, `gap_branch_here`). The other hosts' records
(`x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`) hold no slice-20 entry
and are qualified only by a run on their own host.

## 3. The 33 roots

`probe/x86_body_probe.rs` is the design's probe, unchanged
(`~/tcg-scratch/s20-design/probe/`), built from this branch as an example;
`probe/run_probe.sh` runs its `--cf` mode over the census bridge's `core`
dump (`runs/core-ir-s20`) restricted to census-ay13556's 106 failed roots,
with no lift set: the rules are the branch's, the binary search is the
selector's own (the design's probe replaced it by the chain). The 73 roots
outside the 33 keep the design control's verdicts, every one. Of the 33:

| Class (roots) | Branch probe | Closes on the replay |
| --- | --- | ---: |
| switch binary search (3) | built | 3 |
| stored address at a join (3) | built | 2 (`fmt_decimal`: as designed, part 1's 64-bit division by a variable times out and Clean rejects part 2's `poly_simp`) |
| `I128` loop-carried (4) | built (halves) | 4 (2.3-3.5 s) |
| `I128` cut item (5) | 2 built, 3 refused at their `I128` division (20a) | 1 (`checked_pow`; `wide_mul_u128` part 2 times out, as designed) |
| `I128` division (10), `I128` guard (1) | refused by name (20a) | 0 |
| variable `I128` shift (1) | built | 0 (30.5 s: deadline-bound, design 23.9 s) |
| `bool` load past a cut (1), undefined bits (1), slots (3), candidates (1) | built | 6 |
| **all (33)** | **19 built, 14 refused** | **16** |

`census/replay_queries.sh` replayed the 19 roots' 92 queries one at a time
(`census/replay_one.py`, the design's: strict Alethe one-shot, then Clean) at
1-minute load 3-6; `census/roots33.py` sums them per root. The probe's
sampler flags parts 2 and 3 of `checked_pow` (a 128-bit source definition the
evaluator does not answer); z3 4.15.4 decides all three parts `unsat`, and
AY certifies all three.

## 4. The selector's `I128` division libcall

`select_i128_div_libcall` now declares RDI, RSI, RDX and RCX at 64 bits as
the call's argument registers (`call_arg_regs`), which every other call
declares and which the register allocator's MISCOMPILE #53 guard reads as
the call's implicit uses (`pipeline.rs`, the reserved setup span); the
selector's unit test asserts them. It lands as its own commit after a
commit that backs it out of the WIP. Evidence that no emitted byte changes:
`libcall/dump_tests.sh` appends two temporary `#[ignore]` dumpers (never
committed) that write object bytes: the four `e2e_x86_64_i128_div` modules
and a richer module (four libcalls, operands and results live across them)
at O0-O3, and the codegen body end-to-end fixture module (slices 1-15, the
slice-11 and slice-14 functions among them) for both x86-64 triples at
O0-O3. Built before and after the fix: **all 28 objects byte for byte
identical**, the after build reproduced twice (`before.sha256`,
`after.sha256`). The native differential `e2e_x86_64_i128_div` (cc link and
run against clang's `__int128`) passes 4/4 before and after.

## 5. Gates

| Gate | Result |
| --- | --- |
| the solver-free x86 body suite (`x86_source_bound_body::tests::`, every library test but the tool-gated lanes) | 352 passed, 0 failed, 16 ignored (`logs/gate-q5.log`) |
| `trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus` | 5 passed and 5 passed (`logs/codegen-gate-final.*`) |
| `trust-cg-codegen --test e2e_x86_64_i128_div` (native) | 4 passed |
| `trust-cg-lower --lib` | 2113 passed |
| `scripts/check_fmt.sh` (the 6808 package's `targo fmt`) | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK (the slice-20 printer is in `IGNORED_TESTS`) |

## 6. Reproducers (this directory)

| File | What |
| --- | --- |
| `fails-before/mutate.py`, `fails-before/run_mutants.sh` | the 22 rule mutants and their run |
| `census/qualify.sh` | one tool-gated test per process on the qualification pair |
| `census/replay_queries.sh`, `census/replay_one.py`, `census/roots33.py` | the 33 roots' replay and its per-root sum |
| `probe/x86_body_probe.rs`, `probe/run_probe.sh` | the design's probe (a copy; place it in `crates/trust-cg-verify/examples/`) and its run |
| `libcall/dump_tests.sh` | the two temporary object dumpers of §4 |
| `census/payloads.py` | the PAYLOADS.md table |
