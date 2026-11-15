# Darwin x86-64 `library/core` census — slice 13 (memory and values), 2026-10-05

Slice 13 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) admits four more
parts of the memory and value domain: a private stack address stored as
data, integer parameters and arguments on the stack, the C memory routines
behind LIR `Memcpy`/`Memmove`/`Memset`, and scalar atomic loads and stores
(ruling OD-83). This record holds the measurement that chose the scope,
where each meaning comes from, the host qualification, the controls and
their fails-before evidence, the mutation robustness probe and the census
row. Host and toolchains as in the
[slice-11 census](../2026-10-03-darwin-x86-64-census-slice11/README.md):
native stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridges built on
this host against the stage-1 `stage0-sysroot` (`targo --unverified build
--release --locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU,
proofs required (the bridge default), `x86-body-trace` and `x86-body-dump`.
The lane's qualification AY moved on this host on the same day, from AY
0.27.0 build 10530 (sha256 `9a149c35…`) to AY build 12713 (`b1b0b9de0`,
through the x86-stage1-ay12713 overlay; the
[requalification record](../2026-10-05-darwin-x86-64-ay12713-requalification/README.md),
ruling OD-85), Clean 5f09e36c on both. Slice 13 is qualified on both; its
census row is measured on build 12713, against the requalification's own
row. Nothing here is a completion claim. Payloads
are out of tree; [PAYLOADS.md](PAYLOADS.md) lists each with its SHA-256,
and this README states the numbers they carry.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-6b10` (the class measurement) | `main` `6b108b81d` | 10530 | `abf52e17…` | 1095 | 15029 s |
| `core-x86_64-darwin-O0-proof-ay12713` (baseline; the requalification's row) | `main` `6b108b81d` with the requalification (`486982bfd`) | 12713 | `dc0f68b9…` | 573 | 8342 s |
| `core-x86_64-darwin-O0-proof-slice13-ay12713` | this branch (`9ef2a6a49`) merged with the requalification (`90608b684`) | 12713 | `01fa4c3a…` | 493 | 6253 s |

**80 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted.** Every failed root of the three runs is `[TCG-PROOF-465]`, and
none recorded a resource-budget refusal. The bridges were built in this
worktree (the build-12713 one with `~/tcg-scratch/build_bridge.ay12713.sh`
against the bridge overlay, hosted by the root overlay's `trustc`,
`census/census_s13_ay12713.sh`); the build-12713 baseline is the
requalification's row on the same `main` tree. The `main-6b10` row ran
with this branch's tests and builds beside it, and the slice-13 row with
104 GiB of free disk and no other census; wall time is a trend.

## The class, measured first

On the baseline row (`main` `6b108b81d`, 1095 failed roots), the failed
roots whose named function's last body trace names a slice-13 class
(`census/roots_by_class.py`, then `census/split13.py`; payloads
`main_roots.tsv`, `classes.txt`, `classes/`). Every failed root of the run
names a distinct function, so functions = roots:

| First refusal | Functions = roots |
| --- | ---: |
| a private stack address stored as data (`uses a private stack address as a value`) | 49 |
| a DAG join of paths on which different private slots escaped (slice 9's rule) | 35 |
| more than six register parameters | 26 |
| a call passing more than six register arguments | 11 |
| an atomic access (`AtomicLoad` 13: `I8`/`I16`/`I32` 2 each, `I64` 5, `I128` 2; `AtomicStore` `I64` 1; all `Relaxed`) | 14 |
| `Memcpy` (3) or `Memset` (2) | 5 |
| a `bool` read of a private byte no `bool` store wrote | 4 |
| neighbours: an access through an address that may derive from an escaped slot (slice 7's retention rule) | 11 |
| neighbours: a `bool` argument forwarded from a `bool` parameter (slice 3's rule) | 8 |
| neighbours: a private address offset by a variable amount | 6 |
| neighbours: no observable at all (no result, call or incoming access) | 14 |

The first measurement, on the slice-11 census (`runs/census-s11`, before
slice 9 joined `main`), had 40, 0, 26, 9, 14, 5 and 3 roots in the first
seven classes; the 35 join roots appeared when slice 9's DAG bodies reached
the escape rule on `main`.

**What the bodies do** (`census/dump_class.sh` with slice 8's
[probe](../2026-10-02-darwin-x86-64-census-slice8/probe/x86_body_probe.rs)
over the slice-8 census's cleaned `core` module, for the class functions of
the slice-9 census, the newest whose module the probe could read; payloads
`dump_*.txt`):

- **A private address stored.** Every one of the 39 functions dumped
  stores the address of one private slot INTO ANOTHER private slot
  (`census/escape_shapes.py`: 39 of 39), never through an incoming
  pointer, and then passes that slot to a call: a closure environment
  capturing a local by reference, or a local slice's data pointer. These
  are the `fmt::Display` impls of the integers and `char`,
  `DisplayBuffer::write_char`, `EncodeWide::next`, the `unicode_data`
  `skip_search` closures, `binary_search_by_key` instances and their kin.
  The 35 join roots let a local's address escape (to a call) on one arm
  only, so their arms join with different escaped slots (`fmt::builders`
  closures, the `net` parsers and `Display` impls, `Formatter::pad`,
  `StrSearcher::new`, `flt2dec::decode`, `dec2flt`, `align_to`).
- **More than six register parameters**: integer parameters past RDI-R9:
  the `Formatter::debug_tuple_field{2..5}_finish` and
  `debug_struct_field{1..5}_finish`/`debug_struct_fields_finish` helpers
  (a name and pairs of fat pointers), the `flt2dec` string and Grisu
  rounding helpers, `Ipv6Addr::new` (eight `u16`s),
  `panicking::assert_failed_inner` and `Duration`'s `fmt_decimal`.
- **More than six register arguments**: their callers (seven
  `assert_failed::<T, U>` instances calling `assert_failed_inner`, the
  float formatting and `dec2flt` fast paths, `Duration`'s and
  `VaListInner`'s `Debug`, `Ipv6Addr::from`).
- **`Memcpy`/`Memset`**: struct copies and zero fills that the adapter
  states as the intrinsic.
- **Atomics**: `atomic_load::<T>` and `atomic_store::<T>`, which dispatch
  on the ordering argument through a jump table (the refusal names the
  first atomic arm's access).
- **A `bool` read of another store's byte**: a `u8` copied into a slot
  and read back as `bool`.
- Neighbours left out: the retention rule (an incoming access through an
  address that may derive from an escaped slot, which needs a points-to
  model the walk does not have), a `bool` argument forwarded from a `bool`
  parameter (slice 3's rule: the backend's own clean 32-bit `bool`
  contract is not what an LLVM caller guarantees), a private address offset
  by a variable amount (the walks resolve private bytes without the
  solver) and bodies with no observable at all (vacuous by design).

**Scope chosen, by roots and proof risk:** the stored private address
with an escape model that extends slice 7's, joins taking the union of
escaped slots (49 + 35), the incoming and outgoing stack argument areas
(26 + 11), the three C memory routines (5), atomics as their
single-threaded plain counterparts (14, all behind the jump-table dispatch
today) and the `bool` read of another store's byte (4). Left out, with the
reason:

- **Jump tables** (the atomics' dispatch): control flow, slice 12's area.
- **Read-modify-write, compare-exchange, fences and `I128` atomics**:
  their x86 forms (`lock xadd`, `lock cmpxchg`, `mfence`, `lock
  cmpxchg16b`) have meanings this walk does not model.
- **A `bool`, `I128`, float or aggregate on the stack**: no `core` root
  needs one; each is refused by name.
- **Forwarding a `B1` argument**: kept refused by the slice-3 rule.

**Measured next, offline** (slice 8's probe `--sig` over the same cleaned
module, built once with `main`'s owner and once with the slice-13 owner
before joins took the union of escaped slots; payloads `sig_main.tsv`,
`sig_wip.tsv`): the slice-13 owner binds 66 functions `main`'s does not,
binds every function `main`'s binds, and every theorem it builds holds on
the samples (no `REFUTED-AT-SAMPLE`). The census below is the measurement
of record.

## Semantics: where each meaning comes from

LIR meanings are trust-ir's (`trust_ir::interpret`, pin `0f243925`) and
`trust_cg_lower`'s documented opcodes; machine meanings are the Intel
SDM's; the System V placement is the psABI's (§3.2.3).

- **A stored private address.** An 8-byte `Store` whose value is a
  `StackAddr` (copied, cast or offset by a constant) writes the pointer's
  eight bytes. The theorem names the slot's address `slot{x}` (a free
  64-bit input) plus the offset, on both sides; the machine's `lea` of the
  same slot (the slot binding pairs slots by index) is the same term.
  Nothing is assumed about the value (alignment, distinctness from other
  slots or from incoming memory): it is only ever stored, passed or
  observed, never an address the solver resolves. A free input that ranges
  over more values than the allocator's makes the theorem stronger, never
  weaker.
- **Escape.** Where an address goes decides which memory is shared: stored
  to incoming memory or into an escaped slot, the slot escapes at once;
  into a private slot, when that slot escapes (transitively). An escaped
  slot follows slice 7: every later call reads its bytes (observed at the
  call) and redefines them (`d{site}s{slot}o{off}`), and an incoming access
  through an address that may derive from it is outside the domain. A DAG
  join takes the union of its edges' escaped slots (an over-approximation
  of the memory a callee can reach on either path, so a stronger claim).
- **Stack parameters.** psABI: an INTEGER argument with no register left
  goes on the stack, one eightbyte per argument in order, the first at
  `8(%rsp)` at entry, so `16(%rbp)` after `push %rbp; mov %rsp, %rbp`. The
  pre-RA stream reads it as `[rbp + 16 + 8k]` (the selector's
  `formal_argument_bindings`; the verify-owned placement is swept against
  it). An `I8`-`I32` parameter is the low bits of its eightbyte (the bits
  above are the caller's, never read).
- **Stack arguments.** The selector opens the area with `sub rsp, n` (`n`
  a positive multiple of 16, at most 4096), stores the `k`-th stack
  argument to `[rsp + 8k]`, calls, and closes it with `add rsp, n`. The
  callee reads its stack arguments from that area at the call; each is
  observed at its return bits, like a register argument.
- **The C memory routines.** trust-ir: `MemCopy` copies `bytes` bytes
  (overlap is undefined unless it is a move), `MemSet` writes `byte` to
  each of `bytes` bytes. The selector lowers each to a call of `memcpy`,
  `memmove` or `memset` with the operands in RDI, RSI and RDX (`memset`'s
  fill byte as an `int`). The theorem states both sides as that call (an
  uninterpreted callee of the world), so it claims only that the machine
  makes the same call with the same operands from the same state; that the
  routine's effect is the intrinsic's is trusted (the symbol binding).
- **Atomics.** trust-ir's `interpret.rs`: "with one thread every memory
  ordering collapses to sequential consistency, so an atomic access is its
  plain-memory counterpart". The selector lowers an admitted atomic load or
  store to one `mov` of its width carrying an atomic proof origin; the walk
  pairs an atomic source access only with such a row and a plain one never
  with it. The selector lowers a `SeqCst` store to a plain `mov` too, which
  is not sequentially consistent under x86-TSO (a later load may pass it),
  so a `SeqCst` store is refused by name (OD-83).
- **A `bool` read of another store's byte.** trust-ir's `Load Bool` reads
  one byte and is `byte != 0`, which the source states. The selector
  computes it from the `movzx` of that byte as `(byte + 0xff) >> 8`
  (`add`, `shr`), which the walk models row by row; the theorem proves the
  two equal, and a raw byte returned is refuted.

## Qualification

`host_qualification_replays_the_slice_thirteen_body_theorems` replays the
20 fixture shapes (stored addresses: to an out-pointer, kept across a call,
in a local passed on or read back, into an escaped slot, two slots' to two
words; stack parameters, narrow ones, stack arguments and a private
address argument; `memcpy`, `memmove`, `memset` and a copy into a local;
`Relaxed`, `Acquire` and `bool` `SeqCst` atomic loads, a `Release` store and
a store then load; a `bool` read of a `u8` byte) and 15 wrong lowerings.
On AY 0.27.0 build 10530 with Clean 5f09e36c every fixture replays
Verified (each in at most 2 s) and every wrong lowering returns a
counterexample (payload `qualification.log`): a stored address at another
offset, two slots' addresses swapped (the counterexample gives `slot0` and
`slot1` different values), a stored value kept in a register across a call
its slot escaped to (three shapes), a narrow read through a reloaded
address, swapped and widened stack eightbytes, another value stored as a
stack argument, swapped `memcpy` operands, a word copied into a local read
at another offset, an atomic load from another address, an atomic or
private `bool` byte returned raw, and an atomic store of the pointer instead
of the value. `KNOWN_UNCERTIFIED_SLICE_THIRTEEN` is empty, and the
verifier-credit test credits every bound row of every fixture Formal with
the replayed theorem. Requalified on AY build 12713 (this branch merged
with the requalification, `90608b684`, through the x86-stage1-ay12713
overlay): the same 20 Verified (each in at most 0.7 s), the same 15
counterexamples, and the verifier-credit test passes (payload
`qualification_ay12713_trial.log`); the table stays empty.

## Controls and fails-before

The solver-free library gate row `x86_source_bound_body::tests::slice13::`
(14 tests) passes, and so do the slice-7, -8 and -9 rows (75 tests in all
with slice 13), every earlier golden snapshot byte-identical. Earlier tests
that encoded the old boundary now state the new one: slice 7's `*p = &v`
is admitted and its theorem holds (returning an escaped address stays
outside); slice 3's seven-argument call is admitted (a seventh `bool`
argument stays outside by name); slice 8's register-overflow control is now
four `[u64; 2]` aggregates; slice 9's join of different escapes takes their
union, and its theorem holds; a slot address stored for a value is refuted
(the memory row, was: outside).

**Rule mutants** (`fails-before/mutate.py`, `run_mutants.sh`; one build,
`TCG_S13_MUTANT` selects the rule; payloads `mutants.txt`,
`mutants2.txt`): every mutant fails at least one control; the unmutated
build passes all 14.

| Mutant | Rule disabled | Failing (of 14) | Among them |
| --- | --- | ---: | --- |
| `store-no-escape` | an address stored to incoming memory makes its slot escape | 3 | `a_stored_address_escapes_its_slot_where_the_memory_it_went_to_is_shared` |
| `no-escape-closure` | an escaping slot takes the slots whose addresses it holds along | 4 | `different_escaped_slots_at_a_call_make_no_claim` |
| `escaped-store-no-escape` | an address stored into an escaped slot escapes | 3 | `a_stored_address_escapes_its_slot_where_the_memory_it_went_to_is_shared` |
| `address-no-offset` | a stored address's term carries its offset | 1 | `every_slice_thirteen_refutation_is_refuted_on_samples` (`AddrToOut/another-offset`) |
| `one-slot-name` | each slot's address is its own free input | 1 | `every_slice_thirteen_refutation_is_refuted_on_samples` (`TwoAddrsToOut/swapped`) |
| `partial-address-read` | the machine reading part of a stored address makes no claim | 1 | `a_partial_read_of_a_stored_address_is_outside_the_domain` |
| `escape-sets-unchecked` | at a call the machine's escaped slots are the source's | 1 | `different_escaped_slots_at_a_call_make_no_claim` |
| `stack-param-at-8` | the incoming stack area starts at `[rbp + 16]` | 6 | `the_verify_owned_stack_placement_agrees_with_the_selector` |
| `rbp-any-disp` | an RBP read is a stack parameter only at its exact displacement | 1 | `the_stack_argument_areas_admit_only_their_exact_rows` |
| `stack-arg-at-8` | the outgoing area starts at `[rsp]` | 8 | `a_private_address_stack_argument_is_checked_exactly` |
| `stack-args-unobserved` | stack arguments are observed | 2 | `every_slice_thirteen_refutation_is_refuted_on_samples` (`StackArgs/other-value`) |
| `unwritten-outgoing-ok` | an unwritten outgoing byte is an undefined read | 1 | `the_stack_argument_areas_admit_only_their_exact_rows` |
| `rsp-unbalanced` | only the matching `add rsp, n` closes the area | 1 | `the_stack_argument_areas_admit_only_their_exact_rows` |
| `rsp-open-at-return` | a return with the area open writes RSP | 1 | `the_stack_argument_areas_admit_only_their_exact_rows` |
| `memset-is-memcpy` | `Memset` calls `memset` | 6 | `the_memory_routines_are_calls_to_the_c_runtime` |
| `atomic-pairs-plain` | an atomic access pairs only with an atomic row | 1 | `atomics_pair_only_with_atomic_rows_and_a_seq_cst_store_is_refused` |
| `seqcst-store-admitted` | a `SeqCst` store is refused | 1 | `atomics_pair_only_with_atomic_rows_and_a_seq_cst_store_is_refused` |
| `join-first-escapes` | a DAG join takes the union of escaped slots | 1 of 1 (slice-9 filter) | `slice9::a_join_of_different_escapes_takes_their_union` |
| `bool-byte-refused` | (admission) a `bool` read of another store's byte is admitted | 5 | `owner_builds_for_every_slice_thirteen_shape_and_covers_every_value_row` |

The first run (payload `mutants.txt`) left two mutants alive,
`partial-address-read` and `rbp-any-disp`: their controls expected "no
claim" and got it from a later refusal (an access-trace difference, an
undefined `e_stack24`), hiding the rule. Both controls now name the
refusal they expect, and both mutants fail (payload `mutants2.txt`).
(The golden snapshot test also fails under every mutant that changes a
fixture theorem's text.)

**Mutation robustness** ([robustness/README.md](robustness/README.md)):
1111 mutants of the 24 distinct O0-O3 streams of the 20 fixtures, judged
against an independent concrete interpreter (AY 0.27.0 build 10530 and
Clean 5f09e36c). 849 are wrong by ground truth: 116 make no claim, 609 are
named mismatches and 124 are refuted by the sampler and AY; none is
credited or replays Valid. Every theorem AY refutes the sampler refutes too
(126 of 126). The 185 credited streams (24 originals, 161 mutants) are all
correct by ground truth. 77 correct mutants are not credited: 6 atomic rows
stripped of their origin (refused by OD-83's pairing rule), 1 row form
outside the lane, 68 named mismatches on bytes or registers no observable
reads (fail-closed), and 2 refuted because the theorem states every
incoming load as a fresh input (a load returning the value just stored).
Building the probe found a credit hole, fixed before landing: a return with
the outgoing argument area still open (RSP not restored) built a theorem
that held; see its README. Rerun on AY build 12713 (the same merged
tree), the table is the same cell for cell (payload
`robustness_replay_ay12713.log`).

**Optimized fixtures.** The real x86 optimizer's O1, O2 and O3 output of
every fixture: every theorem the owner builds holds on samples and none is
a mismatch (`optimized_slice_thirteen_fixtures_are_judged_without_false_mismatches`).

## End to end (`crates/trust-cg-codegen/tests/x86_source_bound_body.rs`)

The end-to-end module gains five slice-13 functions (`addr_out`,
`stack_param`, `stack_arg`, `mem_copy`, `atomic_acquire`); the
proof-required compile must promote with every one Formal, on Darwin and
Linux. With the stage-1 AY 0.27.0 build 10530
(`X86_BODY_E2E_REPLAY_IDENTITY`) all five promote with every body Formal
and an exported theorem, beside the 64 functions of slices 1 to 11, and
the module's other four tests (no replay refuses the compile by name, an
out-of-lane body keeps its sampled refusal, an uncertified body is judged
by its theorem alone, Win64 is named) pass (payload `e2e.log`). On AY
build 12713 (the merged tree, overlay toolchain) the same five tests pass
(payload `e2e_ay12713_trial.log`).

## Census delta

Of the 80 promoted roots, every one names a function the baseline refused
in a slice-13 class that is now bound and certified
(`census/census_compare.py` against the build-12713 baseline, payload
`compare/`): a private address stored 41, a join of different escapes 14,
parameters on the stack 10, arguments on the stack 9, `Memcpy`/`Memset` 5,
a `bool` read of another store's byte 1. No other verdict changed.

Where the 144 functions of the slice-13 classes went (payload
`compare/slice13_transitions.tsv`):

| Class | Functions | Bound, certified | Bound, not certified | Refused |
| --- | ---: | ---: | ---: | --- |
| a private address stored | 49 | 41 | 0 | 8: a forwarded `bool` argument 4, a join leaving different bytes where one holds an address 2, an access through an address that may derive from an escaped slot 2 |
| a join of different escapes | 35 | 14 | 7 | 14: more than 512 machine rows 10, a jump table or other machine form 2, the retention rule 2 |
| parameters on the stack | 26 | 10 | 0 | 16: more than 1024 LIR instructions 7, a stack parameter other than an integer 4, a loop 3, more than 512 machine rows 2 |
| arguments on the stack | 11 | 9 | 0 | 2: `GuardDivZero` 1, a stack argument other than an integer or private address 1 |
| `Memcpy`/`Memset` | 5 | 5 | 0 | |
| an atomic access | 14 | 0 | 0 | 14: the ordering's jump table 11, an `I128` atomic load 2, `AtomicRmw` 1 |
| a `bool` read of another store's byte | 4 | 1 | 2 | 1: a machine row outside the lane |
| **total** | **144** | **80** | **9** | **55** |

**The 9 that do not certify are AY's certification class**, replayed
offline with the requalification's simulation of the production protocol
(`replay/production_replay.py` of that record: the resident `ay
--incremental` first, 30 s, then the fresh strict solve and Clean; payload
`uncert_replay_12713.tsv`): 6 distinct texts, none satisfiable. 7 functions
(4 texts: the two `align_to` instances, three `FlattenCompat` and one
`Chain` `try_fold` closure, `Assume::but_not`) run out the resident route's
30 s deadline, the route the requalification found slower on build 12713;
`DebugStruct::field_with`'s `wide_pointer_fmt_inner` closure is a strict
self-check rejection (`incomplete proof-trusted`), and `Assume::and` a
proof AY cannot render (`incomplete proof-unrenderable`). They are the
larger bodies (156 to 437 bound rows).

## Gates

**On AY build 12713, the merged tree.** `main` `a464efe23` (the lane's
requalification) is merged at `e178c0b7f`; its non-test sources equal the
trial merge `90608b684` the census bridge was built from, and the gates
below ran on one or the other through the x86-stage1-ay12713 overlay
(`targo --unverified`, no proof claim about the build):

| Gate | Result |
| --- | --- |
| verify library on `e178c0b7f`, serially: `negative_memo::`, `slice13::`, `slice13_qualification::`, `qualification_matrix::`, `slice7::`, `slice8::`, `slice9::` and the envelope qualification | 91 passed, 1 ignored (payload `merged_verify_ay12713.log`) |
| codegen `x86_source_bound_body` end to end and `must_refuse_corpus` on `e178c0b7f` | 5 and 5 passed (payload `merged_codegen_ay12713.log`) |
| the whole verify body and envelope library on `90608b684`, serially (`gates_stage1.ay12713.sh`'s filter, `--test-threads=1`) | 243 passed, 12 failed, 10 ignored (payload `verify_body_serial_ay12713_trial.log`). The 11 `negative_memo::` failures fail the same way on the requalification's own tree before its last commit (payload `requal_tree_memo_envelope.log`); `main`'s `ba8f208b6` fixes them, and they pass on `e178c0b7f`. The twelfth, the envelope's `void_return_saves` replay, was a timeout; it passes on both reruns |
| the same library 4-wide on `90608b684` (`gates_full_stage1.ay12713.sh`), while the requalification census ran | at least 8 qualification tests failed (the helper prints the first 8; payload `gates_ay12713_trial.log`); every qualification test passes in the serial run above, and those 8 again alone (payload `qualification_serial_ay12713_trial.log`): Clean's longer checks of build 12713's proofs pass the 30 s budget only on a quiet host, as the requalification record states |
| IR, lowering and optimizer libraries; codegen library; CLI `must_refuse_corpus` (on `90608b684`) | 538, 1993 and 4226 passed (2 ignored); 4616 passed (1 ignored); 1 passed |
| every x86 test target compiled on `90608b684` (`--lib`, the 88 codegen and 10 verify targets gated to `x86_64` or named `x86`, `--keep-going`) | all compile (payload `build_x86_tests_trial.log`). The full `--tests` build of all 538 codegen targets was stopped: it needs more disk than this shared host can spare |
| `scripts/test_soundness_check.sh`, `scripts/tests/test_export_x86_qualification_matrix.py`, `bash scripts/check_fmt.sh`, `python3 scripts/check_documentation.py --check` on `e178c0b7f` | 99 passed; 10 passed (ten snapshot families); OK; OK |

**On AY build 10530, before the merge.** Run on the branch at `4eb6c6a34`,
stage-1 toolchain (`targo --unverified`, no proof claim about the build),
AY 0.27.0 build 10530 and Clean 5f09e36c (`~/tcg-scratch/gates_full_stage1.b10530.sh`;
payload `gates_b10530.log`):

| Gate | Result |
| --- | --- |
| verify library, `x86_source_bound_body` and `diag::`, with AY and Clean (every slice's qualification, slice 13's included, and the query matrix) | 236 passed, 1 failed, 10 ignored. The failure, `memory::verifier_credits_every_bound_memory_row_with_the_replayed_body_theorem`, ran while another agent's census and builds loaded the host; it passes alone together with the memory qualification, whose `SlotFoldedOffset` replay takes 10.5 s there (payload `flake_rerun.log`): the known load-sensitive memory fixture |
| codegen `x86_source_bound_body` end to end and `must_refuse_corpus` | 5 and 5 passed (the five slice-13 functions promote Formal; payload `e2e.log`) |
| IR, lowering and optimizer libraries | 538, 1993 and 4226 passed (2 ignored) |
| codegen library | 4616 passed, 1 ignored |
| CLI `must_refuse_corpus` | 1 passed |
| the library rows `slice7::`, `slice8::`, `slice9::`, `slice13::` and `qualification_matrix::` (no AY) | 76 passed |
| `scripts/test_soundness_check.sh` (the new `slice13::` row) | 99 passed |
| `scripts/tests/test_export_x86_qualification_matrix.py` | 10 passed (nine snapshot families) |
| `bash scripts/check_fmt.sh` (the managed package's `targo fmt`) | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| every workspace library and test target compiled (`build --workspace --lib --tests --keep-going`) | interrupted: the host's disk filled (`os error 28`) while it ran; to be repeated on the merged tree |
| `scripts/check_tippy.sh` | not run: as recorded by the slice-11 census, the only `tippy` on this host (managed package 6808) stops before linting every package, and the stage-1 build has no `tippy` |

## Open findings

- **No miscompile was found** in the selector's output: every fixture's
  theorem certifies, every robustness mutant AY refutes is wrong by the
  independent interpreter, and no original stream is wrong.
- **The x86 selector lowers a `SeqCst` `AtomicStore` to a plain `mov`.**
  Under x86-TSO a later load may pass that store, so it is not
  sequentially consistent (LLVM emits `xchg`). The rustc bridge never
  emits the opcode (it lowers a `SeqCst` store to `AtomicRmw Xchg`), so no
  Rust program reaches it through the bridge today; a direct trust-ir
  producer could. The lane refuses it by name (OD-83); the selector is
  unchanged here. (Fixed afterwards on main, 2026-10-05: the selector emits
  `mov; mfence` for a `SeqCst` store, with a regression test.)
- **A latent index fault in the walk's affine form**, fixed: the affine
  normal form has eight parameter slots and the constant at index 8, and
  `Affine::parameter(i)` panicked for a ninth parameter and aliased the
  constant for an eighth. No body reached it before slice 13 (at most six
  register parameters, plus pairs); a stack parameter would have.
  `parameter_affine` now gives no affine form past the eighth.
- **The probe found a credit hole before landing**: a return with the
  outgoing area open (RSP not restored); see the robustness README.
- **Atomics stay outside in `core` today**: every class root dispatches on
  its ordering through a jump table (slice 12's area).

## Reproducers (in tree)

- `census/census_s13.sh` (the census command), `census/census_compare.py`
  (promoted, newly failing, mismatches, refuted bodies, transitions),
  `census/roots_by_class.py` (the class measurement),
  `census/dump_class.sh` and `census/escape_shapes.py` (the body profile;
  the probe is slice 8's), `census/class_verdicts.py` (the offline
  verdicts), `census/payloads.py` (the [PAYLOADS.md](PAYLOADS.md) rows).
- `fails-before/`: `qualify.sh`, `mutate.py`, `run_mutants.sh`.
- `robustness/`: the mutation probe and its README.
