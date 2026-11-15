# Darwin x86-64 `library/core` census — slice 9 (acyclic control flow over the DAG), 2026-10-02

Slice 9 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) lifts the
control-flow bounds of slice 6. A several-path source past them (more than
sixteen blocks, more than sixteen entry-to-end paths, or a path of more
than 256 instructions) is stated over its DAG, in size linear in its
blocks, and a one-path chain may run past 256 instructions. This record
holds the measurement that chose the scope, the encoding and its
qualification, the controls and their fails-before evidence, the mutation
robustness probe and the census row. Host and toolchains as in the
[slice-8 census](../2026-10-02-darwin-x86-64-census-slice8/README.md): native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this
host against the stage-1 `stage0-sysroot` (`targo --unverified build
--release --locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU,
proofs required, `-Ztrust-ir-cg-args=x86-body-trace`. Qualification tools:
AY 0.27.0 build 10530 (`d14080122`) and Clean 5f09e36c. Nothing here is a
completion claim. Payloads are out of tree ([PAYLOADS.md](PAYLOADS.md)).

| Darwin `core` O0 census | failed roots | promoted | newly failing | named mismatches |
| --- | ---: | ---: | ---: | ---: |
| main `cffb7e876` (slices 1-8, 10) | 1198 | | | |
| slice 9 (`5f06edfdd`, merged with that main) | **1166** | **32** (28 slice 9, 4 load) | **0** | **0** |

## The class, measured first

The baseline is `main`'s census of `ac0481810` (`runs/census-main-ac04`,
1272 failed roots). Its `[TCG-X86-BODY-TRACE]` lines attribute 183 failed
roots to a function refused for "N blocks (the lane admits 1 to 16)", 88 to
"a path of N instructions (the lane admits at most 256)" and one to more
than sixteen paths (`census/root_classes_s9.py`). To measure their shape,
`census/dump_core.sh` dumped `core`'s trust-ir at O0 with the baseline bridge
(no proof certificates; 88 modules, every function translated), and the
probe (`probe/x86_body_probe.rs`, mode `--cf`) printed every function's
LIR shape, machine size and verdict under the slice-9 owner
(`census/offline_classes.py`, payload `offline_t.txt`). Of the 272
functions, 171 are in the dump under their own names:

| Baseline class | Functions | Shape | Slice-9 verdict |
| --- | ---: | --- | --- |
| more than 16 blocks | 110 | 17-24 blocks: 51, 25-32: 25, 33-48: 11, 49-64: 5, 65-128: 16, over 128: 2; 67 have a loop; the 43 acyclic ones have 1-16 paths (27; a long path), 17-64 (12) or 65-256 (4) | a loop 63, a join of different escapes 18, bound 5, checked arithmetic 6, division 3, a bound of slice 9 5, other instructions 10 |
| a path over 256 instructions | 60 | 1-16 blocks and paths; longest path 257-384: 27, 385-512: 12, 513-768: 10, 769-1024: 7, over 1024: 4 | bound 47, a join of different escapes 6, the instruction bound 4, other instructions 3 |
| more than 16 paths | 1 | 17-64 paths | checked arithmetic |

So **paths were never the obstacle**: no class function has more than 256
paths, and with the path bound gone the per-path theorem would fit; what
grows is the body. Loops (67) and joins of paths on which different
private slots escaped (24) are the largest classes the bounds hid.

**Scope chosen.** Every acyclic body over the DAG, with no path bound; a
one-path chain past 256 instructions; loops stay refused by name (a later
slice), and so does a join of different escapes (it needs an escape
condition per slot, so that a later call reads a slot only on the paths
that let it escape; 24 functions, the next lever).

## The encoding

The owner's module documentation states the encoding and its claim; in
short:

- **Admission** (`admitted_dag`) runs each LIR block once, in a
  topological order, from the state the paths into it share: its one
  predecessor's end state, or at a join the merge of its predecessors'
  (`merge_admitted`). A value every incoming edge defines at one carrier is
  kept; a private byte the edges leave differently becomes a merged byte
  (`SlotByte::Merged`); an unwritten one is the slot's initial byte. A join
  of different escapes, a `Switch` with two cases of one value, a
  redefinition after a join and a loop are named refusals.
- **Machine walk** (`walk_dag`): the machine block that lowers each LIR
  block under the slice-6 correspondence is walked once per outgoing source
  edge, over the rows that run on the way to the edge's target
  (`block_rows`), from its entry state; at a join the incoming states are
  merged by the SOURCE edges' guards (`merge_machine`). Flags never cross a
  block boundary. A register the edges leave holding different kinds of
  value is `RegValue::Mixed`, and reading one makes no claim.
- **Theorem**: 1-bit guards. The entry block's guard is `#b1`, a join's is
  `c{J} = (bvor G_e1 ... G_ek)`, a conditional edge's is `c{B}t{S} = (bvand
  g_B (ite T_e #b1 #b0))` and a `Jump` edge's is `g_B`. Joined values,
  registers and bytes are `(ite (= G_e1 #b1) v_1 (ite ... v_k))`. In
  topological order, each block's observed items are stated as `(or (not (=
  g_B #b1)) O_B)` and each conditional edge's machine `jcc` literals as
  `(or (not (= G_e #b1)) M_e)`, all in one conjunction against `true`.
- **Claim**: EQUIVALENT, input by input, to the slice-6 per-path
  conjunction `(and (or (not C_P) (and M_P O_P)) ...)` over every path.
  The edge tests partition the runs, so exactly one path's guards hold.
  Every joined value is that path's on both sides, and every other claim's
  guard is 0. The library gate checks this equivalence by sampling, on every
  slice-6 fixture, refutation and variant and on every slice-9 fixture
  (`the_dag_theorem_is_equivalent_to_the_path_claims`).
- **Trusted, in addition to slices 1 to 8**: the topological admission and
  walk, the merge rules, the guard definitions and the partition of a
  block's runs by its edges' tests. The machine is untrusted. A wrong branch
  condition, a swapped, retargeted, extra or missing edge, or another arm's
  value is refuted, or it breaks the correspondence (no claim).
- **Spelling** (qualification below): a DAG's theorem, and a one-path chain
  past 256 instructions, define no name for a copy and state only the
  definitions their claims reach (trimmed). Every definition used at most
  once is substituted into its use (inlined; the owner falls back to the
  trimmed spelling if inlining would make a claim non-definitional). A
  several-path source within the slice-6 bounds keeps the per-path theorem,
  byte for byte (`slice6_snapshots.smt2` unchanged).

## Qualification and certification by size

**Offline, by size.** The probe wrote the theorem of every function the
slice-9 owner bound before the row bound existed (52 of the 171), in four
spellings (`encoding/respell.py`, `encoding/inline.py`). `census/replay_dir.py`
replayed each query with AY 0.27.0 build 10530 (`--strict-proofs`, the
certificate checked by Clean). `census/replay_join.py` joined the outcomes
with the bound machine rows:

| Bound rows | Bodies | Every copy and definition | Trimmed | Trimmed and inlined (canonical) | Untrimmed and inlined | AY branch `9ad05eb80`, untrimmed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 100-199 | 2 | 1 | 1 | 2 | 2 | 2 |
| 200-255 | 1 | 0 | 0 | 0 | 0 | 1 |
| 256-383 | 24 | 0 | 0 | 13 | 8 | 0 |
| 384-511 | 12 | 0 | 5 | 7 | 7 | 0 |
| 512-767 | 7 | 0 | 0 | 0 | 0 | 0 |
| 768-1023 | 6 | 0 | 0 | 0 | 0 | 0 |
| **all** | **52** | **1** | **6** | **22** | **17** | **3** |

No replay of any spelling found a countermodel. Every uncertified outcome
is one of three things. Most often AY rejects its own UNSAT proof:
`self-check-rejected` with `step tN uses unverified trust rule`, most of
them within 0.1 s. Some certificates carry a `hole` step. A few queries
reach the replay's 30 s timeout (2 trimmed, 3 untrimmed and inlined, 3 on
the branch, which also has one `proof-unrenderable`).
`encoding/pad.py` reproduces the trigger on its own. A certified slice-6
theorem padded with twenty definitions that no claim reads is rejected
the same way. So the spelling decides what certifies: trimming removes
the copies and the definitions no claim reaches, and inlining removes the
single-use definitions. No theorem of 512 or more rows certifies in any
spelling, so the owner refuses a machine stream of more than 512 rows by
name (`MAX_MACHINE_ROWS`), and a body of that size costs no solve that
could not credit it.

**Fixtures.** `slice9_qualification` replays the fifteen fixture theorems
of real selector output (`SLICE_NINE`) with AY and Clean. It also
replays the fourteen wrong lowerings, each of which must be refuted with a
countermodel, and the verifier's crediting of every bound row. Measured on
the merged tree, four fixtures certify:

- `CallChain5` (32 paths of conditional calls);
- `XorChain5` (conditional `xor`s joined);
- `StoreJoin` (conditional stores joined);
- `SwitchTree`, a switch search tree. It certifies since inlining's
  identities are dropped; before that its theorem fell back to the
  uninlined spelling.

The other eleven are recorded gaps, `KNOWN_UNCERTIFIED_SLICE_NINE`: ten
are `self-check-rejected`, and for `BoolDag` the certificate is
`incomplete`. Their theorems carry 64-bit arithmetic across joins, and some
reach the strict certification's 3 s wall, which depends on load. Which of
AY's two self-rejections a gap shows varies with load too: `SwitchTree`
showed both before it certified, so the test accepts either for a recorded
gap. All fourteen wrong lowerings are refuted with countermodels.
`host_qualification_records_the_slice_nine_spellings` records each
fixture under five spellings: canonical, Boolean-connective guards
(`bool_guards`), the slice-6 per-path claims of the same pair, no
inlining, and an untrimmed chain:

| Spelling | Fixtures certified (merged tree) |
| --- | --- |
| canonical (trimmed, inlined, identities dropped, 1-bit guards) | 4 (`CallChain5`, `XorChain5`, `StoreJoin`, `SwitchTree`) |
| Boolean-connective guards | 3 (`StoreJoin` certified on an earlier run) |
| slice-6 per-path claims | 0 |
| trimmed, not inlined | 1 (`CallChain5`) |
| untrimmed | 1 (`CallChain5`) |

On the 25 slice-6 fixtures, the DAG theorem and the per-path theorem
certify alike (25 of 25 each). Those fixtures keep the per-path spelling,
and `slice6_snapshots.smt2` is unchanged.

## Controls and fails-before

The library gate (`x86_source_bound_body::tests::slice9::`, 20 tests, no
AY call) holds every control. `fails-before/mutate.py` guards each slice-9
rule behind `TCG_S9_MUTANT=<name>` in a scratch copy of the owner and of
the test file. `fails-before/run_mutants.sh` runs the gate once per
mutant from one build. Every mutant fails at least one control. The
targeted control is named first. Nineteen mutants ran on the slice-9
tree before the merge of slice 10 (`c38082dd6`). `none` and
`flags-cross-blocks` ran again on the merged tree, with `alu-flags-cross`,
which the merge added. `none`, `no-inline-fallback` and
`no-drop-identities` ran on the final tree (`5f06edfdd`; 20 tests):

| Mutant (the rule disabled) | Controls that fail |
| --- | --- |
| none | none (19 pass; 20 on the final tree) |
| `no-edge-literals` (an edge's `jcc` literals not stated) | `every_slice_nine_refutation_is_never_credited`, construction refused ("the DAG states fewer than two claims"), 9 in all |
| `unguarded-items` (block items not under the block's guard) | `a_join_reached_on_some_paths_is_judged_under_its_guard`, `the_dag_theorem_is_equivalent_to_the_path_claims`, digest |
| `constant-join-guard` (every join reached) | `a_join_reached_on_some_paths_is_judged_under_its_guard`, digest |
| `first-edge-phi` (a joined source value is the first edge's) | the equivalence test, `slice_nine_theorems_hold_on_samples`, `merged_slot_bytes_…`, the optimizer test, 6 in all |
| `machine-first-phi` (a joined register is the first edge's) | the same 6 |
| `no-merged-bytes` (source) | `merged_slot_bytes_are_joined_by_the_edges_guards` ("two 8-byte slots merged": 0, expected 16), 9 in all |
| `no-machine-merged-bytes` | `merged_slot_bytes_are_joined_by_the_edges_guards` (the theorem of a correct stream no longer holds), the equivalence test, 5 in all |
| `merged-bool-any` | `a_bool_read_of_a_merged_byte_needs_a_bool_byte_on_every_edge` |
| `flags-cross-blocks` | `flags_never_cross_a_dag_block_boundary` |
| `no-escape-agreement` | `a_join_of_different_escapes_is_refused` |
| `no-mixed-roots` | `a_root_of_different_kinds_at_a_join_makes_no_claim` |
| `no-switch-distinct` | `a_switch_with_two_cases_of_one_value_is_refused` |
| `no-redefinition-check` | `a_value_redefined_after_a_join_is_refused` |
| `no-size-bounds` | `loops_and_the_size_bounds_are_named_refusals` |
| `same-edge-test` (every edge takes the first edge's test) | 9, the equivalence test among them |
| `no-inline` (spelling) | the pinned digest `slice_nine_smt2_is_canonical_per_shape` |
| `no-inline-fallback` | 8 before identities were dropped; on the final tree 5: the owner refuses `LongChain`, whose one equation inlining makes an identity (`owner_builds_every_slice_nine_shape_over_its_dag`, `every_slice_nine_theorem_is_inlined_without_identities`, digest) |
| `no-drop-identities` (an identity inlining makes is kept; final tree) | `every_slice_nine_theorem_is_inlined_without_identities` (`SwitchTree` and `NestedTree` fall back to the uninlined spelling), digest |
| `no-cone` (spelling) | the pinned digest |
| `alu-flags-cross` (flags a slice-10 `add`/`sub`/`imul`/`mul` wrote cross a block boundary; added with the merge of slice 10) | `flags_never_cross_a_dag_block_boundary` (its `sub` variant: "a sub's flags across a block boundary") |
| `fixed-stride` (the sampler's old stride; the test file) | `the_sampler_gives_every_input_every_constant`, `every_slice_nine_refutation_is_never_credited` (the third switch's wrong case) |

Some mutants fail a control by crashing the theorem builder rather than
by a wrong verdict: `no-merged-bytes` panics on a missing merged byte, and
`no-edge-literals` is refused by the construction check. Each of them also
fails its targeted control on the verdict.
`the_dag_theorem_is_equivalent_to_the_path_claims` samples both theorems
of every slice-6 fixture, refutation and variant and of every slice-9
fixture. A slice-6 fixture of at most sixteen paths has both theorems, so
the equivalence is tested on real pairs, wrong ones included.

## Mutation robustness

`robustness/x86_source_bound_body_slice9_robust_tests.rs` is a diagnostic
test. It is ignored and is not part of the tree's test modules. To run it,
plug it in with a temporary `#[path]` module beside `slice9` in
`x86_source_bound_body_tests.rs`, then run `ROB9_NO_REPLAY=1
fails-before/qualify.sh <log> x86_source_bound_body::tests::slice9_robust::
--ignored`. Without `ROB9_NO_REPLAY`, the run also replays the theorems
with AY and Clean.

The probe mutates the real machine streams of the fifteen slice-9
fixtures: O0 selection, plus the x86 optimizer's output at O1-O3 where it
differs, 37 bases in all. There are eleven mutation classes. Each mutant
is judged three ways: by the owner, by the library gate's solver-free
sampler, and against an independent ground truth. The ground truth is a
concrete interpreter of the LIR and of the pre-RA stream. It runs on 400
random argument vectors and on directed boundary vectors (every constant
of either stream and its neighbours at every argument register), under
both `bool` caller conventions. At most 12 mutants per class and stream
are kept, spread evenly. The solver-free table below ran on the slice-9
tree before the merge of slice 10, with the sampler fix described below;
the replayed table ran on the merged tree. Columns: GT-wrong is the number
of mutants the
ground truth finds wrong, split by how slice 9 judged them (refused /
named mismatch / theorem refuted by the sampler / theorem not refuted).

| Class | Mutants | Owner refuses | Named mismatch | Theorem | Sampler refutes | GT-wrong: refused / mismatch / refuted / **not refuted** | GT-correct but refuted |
| --- | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| C0 original | 37 | 13 | 0 | 24 | 0 | 0: - | 0 |
| C1 branch condition changed | 254 | 18 | 0 | 236 | 166 | 178: 18 / 0 / 160 / **0** | 6 |
| C2 successors swapped | 136 | 7 | 0 | 129 | 129 | 136: 7 / 0 / 129 / **0** | 0 |
| C3 edge retargeted | 322 | 322 | 0 | 0 | 0 | 308: 308 / 0 / 0 / **0** | 0 |
| C4 extra edge | 313 | 313 | 0 | 0 | 0 | 161: 161 / 0 / 0 / **0** | 0 |
| C5 edge removed | 168 | 168 | 0 | 0 | 0 | 158: 158 / 0 / 0 / **0** | 0 |
| C6 join value from another register | 136 | 0 | 74 | 62 | 60 | 134: 0 / 74 / 60 / **0** | 0 |
| C7 compare operand changed | 308 | 66 | 20 | 222 | 221 | 288: 58 / 20 / 210 / **0** | 11 |
| C8 row dropped | 427 | 183 | 202 | 42 | 15 | 359: 156 / 194 / 9 / **0** | 6 |
| C9 trap and return swapped | 108 | 108 | 0 | 0 | 0 | 94: 94 / 0 / 0 / **0** | 0 |
| C10 branch value's condition changed | 90 | 0 | 0 | 90 | 75 | 71: 0 / 0 / 71 / **0** | 4 |
| **all** | **2299** | | | | | **1887: 960 / 288 / 639 / 0** | **27** |

**No wrong stream holds.** The ground truth finds 1887 mutants wrong.
Slice 9 refuses each of them, names a mismatch, or builds a theorem that
the sampler refutes. Every original stream with a theorem holds on the
samples.

**What the probe found.** The first run found two wrong streams whose
theorems the sampler did not refute. Both were `SwitchChain` (O0 and
O1) with the third switch's case 33 compared against 34. The cause was
the sampler, not the theorem. Its constant phase stepped the input of
rank `r` through the constants at a fixed stride `2r + 1`. For the third
argument register (stride five), a theorem with a multiple of five
constants was sampled at only a fifth of them. The owner and the
theorems are unchanged. The sampler now gives every input every constant
and neighbour, at a stride coprime with the number of constants.
`the_sampler_gives_every_input_every_constant` is its control: it fails
under the old stride (mutant `fixed-stride`). The mutant itself is now
the fourteenth slice-9 refutation (`a third switch's case against the
wrong constant`), refuted by AY with a countermodel. The first run's
ground truth also used only random words, which miss a case of 70 or a
compare against 69. It has gained the directed boundary vectors, `bt`
and the `tick` callee, so no mutant is left without a ground truth.

**Conservative verdicts (35).** The ground truth finds 27 refuted
mutants and 8 named mismatches correct. Each takes a different PATH
with the same observable result. The theorem requires the machine to take
the source's path (the slice-6 path correspondence, which slice 9 keeps
input by input), so these are refused, as by design. Examples:

- `BoolDag` `cmp d, -1` for `cmp d, 0`: the other arm runs when `d = 0`,
  where both arms compute `acc`.
- `LoadDag` `setbe`/`ja` for `setb`/`jae`: these differ only at equality,
  where both arms agree.
- `SwitchTree` compares in the search tree moved by one.
- `SwitchTree` `MovRR` into RAX dropped: the return reads a register the
  walk has no value for (a named mismatch), although on these inputs it
  happens to hold the right one.

**With the AY replay** (merged tree `661334dfe`, `ROB9_CAP=3`: at most 3
mutants per class and stream, 728 mutants of the same 37 streams; AY
0.27.0 build 10530 `--strict-proofs` with Clean, and the verifier's
crediting):

| Class | Mutants | Theorem | Sampler refutes | AY countermodel | AY countermodel the sampler missed | AY certifies (credited) | GT-wrong: refused / mismatch / refuted / **credited** |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| C0 original | 37 | 24 | 0 | 0 | 0 | 6 | 0 |
| C1 branch condition | 74 | 65 | 36 | 36 | 0 | 6 | 44: 9 / 0 / 35 / **0** |
| C2 successors swapped | 69 | 64 | 64 | 64 | 0 | 0 | 69: 5 / 0 / 64 / **0** |
| C3 edge retargeted | 87 | 0 | 0 | 0 | 0 | 0 | 81: 81 / 0 / 0 / **0** |
| C4 extra edge | 87 | 0 | 0 | 0 | 0 | 0 | 48: 48 / 0 / 0 / **0** |
| C5 edge removed | 69 | 0 | 0 | 0 | 0 | 0 | 64: 64 / 0 / 0 / **0** |
| C6 join value | 36 | 11 | 10 | 10 | 0 | 0 | 35: 0 / 25 / 10 / **0** |
| C7 compare operand | 83 | 58 | 58 | 58 | 0 | 0 | 78: 16 / 7 / 55 / **0** |
| C8 row dropped | 111 | 8 | 3 | 3 | 0 | 1 | 97: 40 / 56 / 1 / **0** |
| C9 trap and return swapped | 51 | 0 | 0 | 0 | 0 | 0 | 47: 47 / 0 / 0 / **0** |
| C10 branch value's condition | 24 | 24 | 18 | 18 | 0 | 2 | 17: 0 / 0 / 17 / **0** |

The results:

- **AY certifies no wrong stream.** The ground truth finds 580 of the
  mutants wrong, and none is credited.
- **The sampler refutes everything AY refutes:** no countermodel is one
  the sampler missed.
- **The nine credited mutants are rewrites that do not change the
  result:**
  - `ja` for `jne`, or `seta` for `setne`, after a compare against 0
    (unsigned `x > 0` is `x != 0`);
  - `jbe` for `je` after a compare against 0;
  - `CallChain5`'s `and eax, 1` dropped, on a `bool` that is already 0 or 1.
- **6 of the 24 original streams certify.** The other 18 are AY rejecting
  its own proof: the recorded fixture gaps, and their O1/O3 variants.

## Census

The baseline is main `cffb7e876`'s census (slice 10 merged; the slice-10
bridge's run, `runs/census-s10`, 1198 failed roots). The slice-9 census
runs `census/census_s9.sh` on a bridge built from the slice-9 tree merged
with that main (`targo --unverified build --release --locked`).
`census/census_compare.py`, `census/transitions.py`,
`census/newly_bound.py` and `census/size_rates.py` read the two runs'
body traces.

**First census** (`e9488c7fe`, 2026-10-02 22:00 to 02:07; bridge SHA-256
`a2c51e75…`): 1187 failed roots, 11 promoted, 0 newly failing. Of the 76
bodies it newly bound, only 11 certified. The run had 0 budget refusals,
but its host was loaded: other agents' builds at load 7 to 11, and at
times under 3000 free pages. Its dumped queries
(`x86-body-dump`) showed why so few certified. The inlined theorem of
nearly every real body contains a claim equation that substitution makes
an identity. The structural check refuses an identity, so the owner had
fallen back to the uninlined spelling. Replayed offline at low load, AY
certifies 0 of the 62 dumped uncertified queries as dumped. It certifies
14 of them inlined (`encoding/inline.py`) and 13 inlined with the
identities dropped (`encoding/drop_identities.py`). The owner now drops
those identities (`5f06edfdd`), to a fixpoint. They are true on every
input, so the theorem is unchanged in meaning (OD-72).

**Final census** (`5f06edfdd`, 2026-10-03 07:44 to 10:39; bridge SHA-256
`31899dd2…`, at a host load near 2):

| | main `cffb7e876` | slice 9 |
| --- | ---: | ---: |
| failed roots | 1198 | **1166** |
| promoted roots | | **32** (28 slice 9, 4 load) |
| newly failing roots | | **0** |
| functions bound and replayed Valid | 2198 | 2230 |
| functions bound, no independently checked proof | 551 | 595 |
| functions Valid on main and not now | | 0 |
| named mismatches | | 0 |
| bound bodies refuted | | 0 |
| budget refusals, harness errors | 0, 0 | 0, 0 |

Four of the 32 promotions are not slice 9's. They are four functions main
bound but did not certify (`fmt::num::imp::{i,u}64::format_into`,
`flt2dec::strategy::grisu::format_shortest`, and an `Error::source`
`FnOnce` shim). Their dumped theorem is byte-identical on main and on the
first census, and they certify on the final run. That is the load
sensitivity of AY's strict certification (its 3 s wall); these four are
not counted as slice-9 credit. The other 28 promoted roots are slice 9's:

- 23 with a path over 256 instructions;
- 3 with more than 16 blocks;
- 1 with more than 16 paths;
- 1 refused on main for more than 256 machine rows.

Three of these 28 are traced under their private names.

**Where main's 272 control-flow refusals went** (183 functions with more
than 16 blocks, 88 with a path over 256 instructions, 1 with more than 16
paths):

| New verdict | Functions |
| --- | ---: |
| bound, replayed Valid (certified) | 27 |
| bound, no independently checked proof | 36 |
| a loop | 100 |
| a join of paths on which different slots escaped (slice 9) | 31 |
| more than 512 machine rows (slice 9) | 26 |
| a `Switch` with two edges to one block (slice 6's CFG rule, hidden by the block bound) | 14 |
| more than 1024 LIR instructions or 128 blocks (slice 9) | 10 |
| an instruction or ABI form outside the lane | 28 |

Main also refused 13 functions for more than 256 machine rows. Slice 9
binds all of them: 1 certifies and 12 do not.

**Certification by size.** These are the 76 newly bound bodies by bound
rows; every one is a DAG or a long chain, trimmed, inlined and with its
identities dropped:

| Bound rows | Newly bound | Certified |
| --- | ---: | ---: |
| 100-149 | 1 | 0 |
| 150-199 | 4 | 3 |
| 200-255 | 8 | 1 |
| 256-383 | 42 | 16 |
| 384-511 | 21 | 8 |
| **all** | **76** | **28 (37%)** |

The 48 that do not certify are AY rejecting its own proof (strict
self-check, or a certificate with a `hole` step) or a timeout, as
measured offline. None is refuted. That is the word-level AY gap the
fixtures record, not a slice-9 refusal.

## Gates (final tree)

The census measured `5f06edfdd`, the slice-9 tree merged with main
`cffb7e876`. The branch was then merged with main `c8b07006b` (merge
`661334dfe`, 150 commits on main, among them a trust-ir pin move). That
merge was gated, not re-censused. It adds slice 9 to the x86 body
qualification matrix. Its gates, run with the stage-1 toolchain
(`~/tcg-scratch/gates_stage1.sh` with logs kept):

- `trust-cg-verify --lib -- x86_source_bound_body diag::`, with AY 0.27.0
  build 10530 and Clean: 201 passed, 1 failed, 8 ignored. The failure is
  the known flake `memory::host_qualification_replays_the_memory_body_theorems`
  (`SlotFoldedOffset` self-check-rejected in about 9 s, at host load 7-8).
  Its theorem is slice 4's and byte-identical to main's: digest-pinned, and
  bound again by the qualification matrix. Every `slice9`, `slice10` and
  matrix test passes.
- `trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus`:
  5 and 5 passed. `slice_one_to_ten_functions_promote_with_replayed_body_theorems`
  promotes the three slice-9 functions (`dag_calls`, `dag_xors`,
  `dag_stores`) with replayed theorems.
- `scripts/check_fmt.sh`: OK. `python3 scripts/check_documentation.py
  --check`: OK. `bash scripts/test_soundness_check.sh`: 89 passed.
  `scripts/check_tippy.sh` (lint) cannot run on this host: the stage-1
  `targo` has no `tippy` or `fmt` subcommand, so formatting used the
  managed package's `targo fmt`.

## Next levers

- **A join of paths on which different slots escaped:** 31 functions.
  This needs a per-slot escape condition, so that a later call reads a slot
  only on the paths that let it escape.
- **A `Switch` with two cases to one block:** 14 functions. This is slice
  6's CFG rule, which the block bound hid. The edge's test would be the
  disjunction of its cases' tests, and on the machine side the `jcc` rows
  that reach the target.
- **Loops:** 100 functions.
- **Definedness.** The DAG gives every block a 1-bit guard that holds
  exactly on the runs reaching it. A per-block definedness condition `D_B`
  (a divisor not zero, a shift amount below the width) could therefore be
  stated once as the premise `(and (or (not (= g_B #b1)) D_B) ...)`. That
  premise is the per-path definedness of the run's one path: what OD-57
  says division and the exact shift semantics need. Slice 9 does not add it.
  Its theorem still states the claims on every input.

## Reproducers (in tree)

- `census/`: `dump_core.sh` (the `core` dump), `offline_classes.py` (the
  class's shapes and slice-9 verdicts), `replay_dir.py`, `replay_join.py`
  and `replay_rates.py` (offline AY/Clean replays by size),
  `census_s9.sh` and `census_when_clear.sh` (the census), `census_compare.py`,
  `transitions.py`, `newly_bound.py`, `root_classes_s9.py`, `size_rates.py`,
  `payloads.py`.
- `probe/x86_body_probe.rs`: the probe (mode `--cf` added).
- `encoding/`: `respell.py`, `inline.py` and `drop_identities.py`, the
  query respellings replayed offline, and `pad.py`, the padding reproducer.
- `fails-before/`: `mutate.py`, `run_mutants.sh`, `qualify.sh`,
  `gate_row.sh`.
- `robustness/`: the mutation probe (plugged in by a temporary `#[path]`
  module; see Mutation robustness).
