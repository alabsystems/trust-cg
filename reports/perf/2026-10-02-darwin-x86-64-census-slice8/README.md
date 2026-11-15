# Darwin x86-64 `library/core` census — slice 8 (aggregates in general-purpose registers), 2026-10-02

Slice 8 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`): a parameter, the
result, a direct call's argument or a direct call's one result may be a LIR
`Struct` or `Array` that System V passes in general-purpose registers. This
record holds the measurement that chose the scope, the census row, the host
qualification, the controls and their fails-before evidence, and the
mutation robustness probe. Host and toolchains as in the
[slice-7 census](../2026-10-01-darwin-x86-64-census-slice7/README.md): native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this host
against the stage-1 `stage0-sysroot` (`targo --unverified build --release
--locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs
required (the bridge default), `-Ztrust-ir-cg-args=x86-body-trace`,
`--timeout 14400`. Qualification tools: AY 0.27.0 build 10530 (`d14080122`,
sha256 `9a149c35…`) and Clean 5f09e36c (`~/clean-checker/bin/clean`, sha256
`949365b6…`). Nothing here is a completion claim. Payloads (root lists,
logs, outcome tables) are out of tree; [PAYLOADS.md](PAYLOADS.md) lists each
with its size and SHA-256, and this README states the numbers they carry.

| Row | Bridge built from | Bridge sha256 | Failed roots | Distinct reasons | Wall |
| --- | --- | --- | ---: | ---: | ---: |
| [`core-x86_64-darwin-O0-proof-90ccb1b0b`](../2026-09-27-darwin-x86-64-census/README.md) (baseline: slice 7 on `main`) | `main` `90ccb1b0b` | `331425bd…` | 1626 | 1 | 3881 s |
| `core-x86_64-darwin-O0-proof-slice8` | slice-8 branch, base `90ccb1b0b` (see Trees) | `2ab4611d…` | 1276 | 1 | 10018 s |

**350 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted, and no function that replayed `Valid` on the baseline fails to
now.** Every failed root of both runs is `[TCG-PROOF-465]`.

## What was measured

- **Trees.** The baseline is `main`'s post-push census of `90ccb1b0b`
  (`runs/main-90cc.dylib`, sha256
  `331425bdeb50b4c0ccd29f9640252e001c019d7fa17d982f8c22b7b7fbf6dcef`;
  failed-root lines sorted hash to `2b89b133…`, as `main`'s record states).
  The slice-8 bridge (`runs/s8.dylib`, sha256
  `2ab4611d19ea333fea929464ff36d7840a953f3e02c4e93d71e3352adb239558`) was
  built on this branch on top of `90ccb1b0b`, from `e6dd83f85` plus the
  working-tree edits made while it built. Its refusal text carries the
  final `BODY_OPCODES` wording. Between `e6dd83f85` and the final commit,
  the owner's only non-comment change is that diagnostic string; every
  other change is in tests, fixtures and documentation. So the census
  bridge's owner behaves as the committed one's, and every change of this
  row is the owner's (or the solver's, below).
- **Memory and host.** The census started with 1340578 free pages; no
  resource-budget refusal and no harness error occurred. The host was
  shared: other agents' AY builds and bridge matrices overlapped the run.
- **Wall time** was 10018 s against the baseline's 3881 s (single runs on
  a shared host: a trend). The new solves are 420 newly bound bodies, 79 of
  which do not certify. Each uncertified body is judged twice: once in the
  batched compile and once in its per-function fallback, where the
  negative memo answers (291 memo hits in this run). The uncertified bodies
  are also larger: newly bound uncertified bodies have a median of 144
  bound rows, against 37 for newly bound bodies that certify.

### Where the promoted roots came from

Each failed root names the first function whose proof entry is not
verified (a private copy under its `__trust_cg_private.<cgu>.<n>.` name). By
that function's class on each side (`census/promotions.py`, payload
`census-compare/promotions.txt`; the totals are `census/census_compare.py`'s,
payload `census-compare/compare.txt`):

| Named function: baseline -> slice 8 | Roots |
| --- | ---: |
| refused for a non-scalar result -> bound, replays `Valid` | 161 |
| refused for a non-scalar parameter -> bound, replays `Valid` | 138 |
| refused for a call result with no scalar type -> bound, replays `Valid` | 29 |
| refused for an inconsistent type hint (a by-value aggregate argument) -> bound, replays `Valid` | 13 |
| bound, AY strict self-check rejected (`replay=none`) -> bound, replays `Valid` | 9 |

The last row is not slice 8. All nine have only scalar parameters,
results and call results, and the same bound-row count on both runs. On
the baseline, AY's strict certificate self-check rejected each one. Among
the 2172 functions bound on both runs, these nine are the only verdict
changes, all in this direction. Two of them, `panic_display::<&str>` and a
`decode_repr` closure, are the two that `main`'s record of this baseline
lists as replaying `Valid` on the slice-7 branch census and
`none` here at load 16. They are AY's wall-clock-sensitive strict
certification, not a slice-8 effect. **Slice 8's own promotions: 341
roots.**

### Failed roots by class (`census/root_classes_s8.py`)

`main`'s `root_classes.py` rules, with the slice-8 refusals and the
more-than-six-parameters refusal matched first:

| Class of the named function | Baseline | Slice 8 |
| --- | ---: | ---: |
| bound, AY does not certify | 402 | 472 |
| non-scalar parameters (pre-slice-8 refusal) | 281 | 0 |
| non-scalar results (pre-slice-8 refusal) | 234 | 0 |
| inconsistent type hint | 27 | 0 |
| call shapes (among them a call result with no scalar type) | 76 | 16 |
| `i128` value (slice 8 refuses by name) | 0 | 79 |
| floating-point value (slice 8 refuses by name) | 0 | 38 |
| aggregate outside INTEGER: over 16 bytes (slice 8 refuses by name) | 0 | 5 |
| more than six (scalar) parameters | 22 | 22 |
| over 16 blocks / a path over 256 instructions / a loop | 168 + 78 + 47 | 183 + 88 + 61 |
| checked arithmetic | 87 | 97 |
| a machine row outside the lane | 0 | 5 |
| all other classes (slot escapes, non-scalar loads, `CallIndirect`, `CtPop`, `Bnot`, atomics, guards, shifts, division, singletons) | 204 | 210 |
| **total** | **1626** | **1276** |

### Function-level transitions

The trace classes of the 604 functions the baseline refused in the
slice-8 classes (payload `census-compare/slice8_transitions.tsv`):

| Slice-8 outcome | Functions |
| --- | ---: |
| bound, replays `Valid` | 341 |
| bound, AY does not certify (52 strict self-check rejected, 23 `unproved_steps=1`, 4 solver timeouts) | 79 |
| refused by name: an `i128` parameter or result | 79 |
| refused by name: a floating-point parameter or result | 38 |
| refused by name: an aggregate over 16 bytes (MEMORY class) | 3 |
| a later refusal of another class (control flow 39, checked arithmetic 10, `Bnot` 3, a `bool` load from a private byte 2, `CallIndirect` 2, a private address stored 2, too many machine rows 1) | 59 |
| a mixed-width `MovRR edx, v64` (a 3-byte by-value argument, `EscapeDebugExtArgs`'s three `bool`s, assembled in EDX) | 5 |

The offline prediction from the slice-7 dump (418 more bound) and the
census (420 more bound: 341 + 79) agree.

## The class, measured first

The slice-7 census's `[TCG-X86-BODY-TRACE]` lines name three refusals of a
non-scalar value: "requires B1, I8, I16, I32 or I64 (pointer) register
parameters" (606 lines), "requires B1, I8, I16, I32 or I64 results" (468)
and "has no scalar result type" (124); each function is traced once or
twice. To bucket them by the actual LIR types, the probe
(`probe/x86_body_probe.rs`, mode `--sig`) translated the slice-7 census's
own dumped `core` module (`runs/core-ir-s7`, the bridge's `dump-trust-ir`
output) with this tree's adapter and selected every function. This tree's
adapter refuses 149 of that dump's functions outright (an assertion of
unspecified panic kind, `require_assert_panic_kinds`, a refusal `main`
added after the slice-7 census); `census/clean_dump.sh` drops their bodies
and judges the other 3297. Per function, its first refusal under `main`'s
owner (`census/bucket.py`):

| First refusal (functions) | Integer aggregate <= 8 B | Integer aggregate 9-16 B | Aggregate > 16 B | `i128` | Float | Total |
|---|---:|---:|---:|---:|---:|---:|
| a non-scalar parameter | 191 | 5 | 3 | 56 | 20 | 275 |
| a non-scalar result | 197 | 0 | 0 | 14 | 12 | 223 |
| a call result with no scalar type | 58 | 0 | 0 | 4 | 0 | 62 |

- **The aggregates are integer arrays.** The commonest parameter types are
  `Array(I64, 1)` (120 functions: `Option<&T>`, `Option<NonNull<T>>` and
  their kin, which the bridge passes as a one-word aggregate),
  `Array(I32, 1)` (23), `Array(I8, 4)` (15), `Array(I8, 1)` (13),
  `Array(I16, 3)` and `Array(I32, 2)` (6 each); results `Array(I64, 1)` (67),
  `Array(I32, 1)` (46), `Array(I32, 2)` (23), `Array(I8, 1)` (16),
  `Array(I8, 5)` and `Array(I16, 2)` (13 each), `Array(I16, 4)` (8). No
  `Struct`, `Enum` or floating-point field occurs in any of the three rows.
- **"An inconsistent sidecar type hint"** (27 functions in the slice-7
  census) is the same class: a by-value aggregate argument, the adapter's
  temporary hinted with the callee's aggregate parameter type.
- **"More than six register parameters"** (13 functions) are all-scalar
  functions of 7 to 23 parameters: stack arguments, a different lane.

**Scope chosen: integer aggregates of 1 to 16 bytes**, the 451 functions
of the first two columns plus the 27 type-hint functions.
`i128` (74 functions) needs register pairs and 128-bit arithmetic, floats
(32) need SSE registers and floating-point semantics, MEMORY-class
aggregates (3) are passed on the stack and stack parameters (13) read the
incoming argument area: each is its own lane, and each is refused by name.

Offline, with the slice-8 owner as it stood when the scope was chosen (a
probe build of 2026-10-01 23:53, earlier than the committed owner, which
the census row above measures; `census/offline_transitions.py`, payloads
`sig_s7.tsv` and `sig_s8b.tsv`): it binds 2565 functions against
`main`'s 2147, 418 more (163 of the parameter class, 182 of the result
class, 50 of the call-result class, 23 of the type-hint class), and binds
none of `main`'s less. Every theorem it builds holds on 2000 samples (the
probe's own sampler, `refuting_sample`). Every in-scope function it does
not bind stops at an unrelated later refusal: 23 + 12 control flow (a
loop, more than sixteen blocks, a long path), 10 + 3 + 8 + 4 an
instruction outside the lane.

## The model

LIR carries an aggregate by its address. The selector copies an aggregate
parameter's registers into a private slot at entry, loads an argument's or
the result's eightbytes from the value's slot straight into the ABI
registers, and stores a call result's into a slot it allocates at the call
(read from the bridge's real LIR and machine streams with the probe:
`Option<&u8>::unwrap_or`, `u32::from_le_bytes`, `char::from_u32`,
`u8::checked_ilog2`). The theorem states that exactly:

- **Classification.** System V AMD64 (psABI §3.2.3): an aggregate of 1 to
  16 bytes whose every leaf is an integer field inside one eightbyte, and
  every eightbyte holds a field, is INTEGER eightbyte by eightbyte; eightbyte
  `k` travels in the low `min(8, n - 8k)` bytes of one register (the next
  argument register; RAX, then RDX, for a result). The classifier is
  verify-owned (`classify_aggregate`, over the verify-owned C layout), never
  the selector's, and it is checked against the selector's: a unit test
  (`the_verify_owned_classification_agrees_with_the_selector`) builds `fn(x:
  T) -> T { g(x) }` for 45 admitted aggregate types through the real
  adapter and selector and finds the call row's declared argument and
  result registers and widths equal to the verify-owned classification's,
  and every compile compares each call row's with it (a difference is a
  named `CallMetadata` mismatch).
- **Parameters.** The copy's byte `b` of eightbyte `k` is byte `b` of the
  `k`-th argument register's entry value; the bits above the eightbyte's
  own bytes are the caller's garbage, which nothing may read. A field read
  is an extract of the register at the layout's offset.
- **Results.** The returned address's bytes at the return, eightbyte by
  eightbyte, against exactly the low bytes of RAX and RDX a caller reads.
- **Arguments.** An aggregate argument's bytes at the call against exactly
  the low bytes of its argument registers (a callee reads no more). Its slot
  does not escape; its address where the source passes bytes is a named
  `CallStackAddress` mismatch.
- **Call results.** The callee defines each eightbyte's bytes and nothing
  above them: RAX after the call is `g_c ++ r_c`, `r_c` as wide as the
  eightbyte's bytes. The result's slot holds those bytes; once a slot
  escaped, they may be an address derived from it (slice 7's retention
  rule).
- **Padding** bytes inside an eightbyte are observed like the rest: on both
  sides they are the same bytes of the same slot or register, which is
  stronger than a caller needs and never weaker.
- **Machine forms.** The tied two-operand `shl d, imm`, `shr d, imm` and
  `or d, s` (`d = d op x`; register allocation keeps the destination as a
  def and a use), with which the selector assembles and takes apart a
  partial eightbyte, and a byte or word load into, or store from, a
  physical register's 8- or 16-bit alias (`mov al, m8`), whose bits above
  the loaded ones are a free input. Only those: the first version admitted
  every tied ALU form, and the slice-6 optimized-fixture test failed on the
  O1 `xor r, r` zeroing idiom (named an undefined read; it reads no value),
  which stays outside as before.
- **Slots.** The machine's slot table must be the source's plus each copy
  at the aggregate's size and alignment (the frame is laid out from it).
  Which machine slot holds which copy is not a soundness premise: the
  source defines every byte of a copy, and the machine every byte it walks.

## Qualification (`fails-before/qualify.sh`)

`host_qualification_replays_the_slice_eight_body_theorems`: all 22 fixture
theorems are `Verified` through the real builder (fresh replays, 131 ms to
3114 ms each), and AY refutes all 14 wrong lowerings with a counterexample
(swapped halves of a parameter, a parameter's eightbyte from the next
register, a field read at another offset, a partial eightbyte stored one
byte short, a `u8` field sign-extended, the result's eightbytes in each
other's register, a 4-byte result returned through AX, a dropped `or`, the
top byte of a partial result read one byte low, an argument's eightbytes in
each other's register, a call result's eightbytes stored at each other's
offset, a 4-byte call result used as all of RAX, a byte loaded into AL and
returned as 32 bits, a `bool` field read as its bit 0). The recorded gap
list `KNOWN_UNCERTIFIED_SLICE_EIGHT` is empty.
`verifier_credits_every_bound_slice_eight_row_with_the_replayed_body_theorem`:
every covered row of every fixture is Formal under the body theorem, and
each refutation fails every covered row. The verify crate's x86 body gate
(`x86_source_bound_body diag::`, the `gates_stage1.sh` row) passes on this
tree: 158 passed, 0 failed.

## End to end (`crates/trust-cg-codegen/tests/x86_source_bound_body.rs`)

The end-to-end module gains four slice-8 functions:

- `agg_param_field`: a `[u8; 4]` parameter whose field 2 is read.
- `agg_result_pair`: two `u32` stored into a returned `[u32; 2]`, built in
  its storage as the bridge builds it.
- `agg_call_arg`: a `[u64; 2]` parameter forwarded by value to an external
  callee.
- `agg_call_result`: an external callee's `[u32; 2]` result whose two
  fields are subtracted.

`slice_one_to_eight_functions_promote_with_replayed_body_theorems` passes
on `x86_64-apple-darwin` and `x86_64-unknown-linux-gnu`. The proof-required
compile promotes, and every slice-1 to slice-8 function has `Formal` body
credit with its exported theorem. Replay used the toolchain AY (0.27.0
build 10530, sha256 `9a149c35…`) and Clean 5f09e36c. The file's other four
tests also pass (5/5). `must_refuse_corpus` passes 2/2: every row of the
pinned corpus is refused on every admission lane. Payload:
`e2e_and_must_refuse.txt`.

## Controls and fails-before

The solver-free library gate row `x86_source_bound_body::tests::slice8::`
(18 tests; `fails-before/gate_row.sh` is the gate's exact command and
parser) passes. Before this branch the filter selected no test.

**Rule mutants** (`fails-before/mutate.py`, `run_mutants.sh`; one build,
`TCG_S8_MUTANT` selects the rule; payload `mutants.txt`): every mutant fails
at least one control, and the unmutated build passes all 18.

| Mutant | Rule disabled | Failing (of 18) | Among them |
| --- | --- | ---: | --- |
| `no-entry-bytes` | a parameter's copy holds the caller's bytes | 10 | `slice_eight_theorems_hold_on_samples`, `the_verify_owned_classification_agrees_with_the_selector` |
| `no-result-bytes` | a call result's slot holds the result's bytes | 6 | `slice_eight_theorems_hold_on_samples`, `an_access_through_a_call_result_after_an_escape_is_outside_the_domain` |
| `reversed-lanes` | eightbyte `k` is in the `k`-th register | 6 | `slice_eight_theorems_hold_on_samples`, `every_slice_eight_refutation_is_refuted_on_samples` |
| `wide-result-lanes` | a callee defines nothing above an eightbyte | 2 | `every_slice_eight_refutation_is_refuted_on_samples` (`CallResultWiden/result-register-widened`) |
| `short-return-lanes` | a returned eightbyte is observed at all its bytes | 3 | `every_slice_eight_refutation_is_refuted_on_samples` (`ResultPartial/top-byte-offset`) |
| `no-lane-metadata` | the call row's registers are compared with the classification | 1 | `a_wrong_eightbyte_declaration_is_a_named_mismatch` |
| `no-slot-table` | the machine slot table includes the copies | 1 | `a_slot_table_without_the_aggregate_copies_makes_no_claim` |
| `alias-zero-extends` | a narrow alias load leaves the bits above free | 2 | `every_slice_eight_refutation_is_refuted_on_samples` (`ParamByteWiden/al-widened`) |
| `tied-as-move` | a tied `shl`/`shr`/`or` is `d = d op x` | 5 | `slice_eight_theorems_hold_on_samples` |
| `aggregate-as-pointer` | an aggregate-typed argument is passed by value | 9 | `an_aggregate_passed_as_its_address_is_a_named_mismatch` |
| `raw-bool-bytes` | a `bool` read of a register byte is `byte != 0` | 5 | `every_slice_eight_refutation_is_refuted_on_samples` (`ParamBool/bit-zero`) |
| `no-result-taint` | a call result after an escape is escape-derived | 1 | `an_access_through_a_call_result_after_an_escape_is_outside_the_domain` |

(The golden snapshot test also fails under every mutant that changes a
theorem's text.)

**Mutation robustness** ([robustness/README.md](robustness/README.md)):
2383 mutants of the 40 distinct O0-O3 streams of the 22 fixtures (a wrong
eightbyte register, offset, width or source register, a sign/zero
extension swapped, a row dropped, a shift amount, a tied form as a move),
judged against an independent concrete interpreter with its own eightbyte
placement: 1795 are wrong, and none is credited (62 make no claim, 1014 are
named mismatches, 719 are refuted by both the sampler and AY); every
theorem AY refutes, the sampler refutes too; 271 credited streams are all
correct.

**Optimized fixtures.** The real x86 optimizer's O1, O2 and O3 output of
the 22 fixtures: every theorem the owner builds holds on samples, the rest
make no claim, and none is a mismatch
(`optimized_slice_eight_fixtures_are_judged_without_false_mismatches`).

## Cross-backend matrix (`cross-backend/s8_credited_native.py`)

A `dep` crate compiled by LLVM holds callees that take or return small
aggregates by value (`take4([u8; 4])`, `give2(u64) -> [u32; 2]`,
`give5(u64) -> [u8; 5]`, `opt_ref(Option<&u64>)`, `take6([u16; 3])`), so
every callee is an LLVM-compiled one; the `callee` crate holds fourteen
functions with aggregate parameters and results (`[u8; 4]`, `[u16; 3]`,
`[u16; 2]`, `[u32; 2]`, `[u8; 5]`, `[u64; 2]`, `Option<&u64>`) and callers of
`dep` passing or receiving them, built by LLVM or by trust-cg with proofs
required containing exactly the functions a first traced compile credits;
the bin by LLVM or trust-cg. At O0 twelve of the fourteen are credited
(`replay=Valid`; `arr3` and `res2` are bound without a certified proof), the
proof-required rlib promotes, and all four rlib x bin cells print the
oracle's (LLVM rlib + LLVM bin) 1200 lines (payload `credited_O0.txt`). At
O1, O2 and O3 six are credited (the rest make no claim: optimizer row forms
outside the lane), and the four cells agree at each level
(`credited_O123.txt`). With all fourteen compiled by trust-cg without proof
certificates (`S8_ALL=1`), the four cells print the oracle's 1400 lines at
each of O0-O3 (`all_O0123.txt`): the bridge's LIR aggregate types and the
selector's eightbytes agree with what LLVM passes and returns for every
shape.

## Reproducers (in tree)

- `census/census_s8.sh`: the census command (`postpush_census.sh`'s, on the
  built bridge); `census/census_compare.py`: promoted / newly failing lists,
  the body-trace classes and the slice-8 transitions;
  `census/promotions.py`: the promoted roots' attribution, the verdict
  changes of bodies bound on both runs and the newly bound bodies;
  `census/root_classes_s8.py`: failed roots by class on both runs;
  `census/clean_dump.sh`, `census/bucket.py`, `census/offline_transitions.py`,
  `census/sigdiff.py`, `census/probe_fn.sh`: the measurement of the class
  and the offline owner comparison; `census/payloads.py`: the identities in
  [PAYLOADS.md](PAYLOADS.md).
- `probe/x86_body_probe.rs`: the LIR / machine / verdict probe (modes
  `--sig`, `--clean`, `--tir` added for this slice).
- `fails-before/`: `qualify.sh` (the tool-gated tests on the stage-1
  toolchain), `gate_row.sh` (the gate row and its parser), `mutate.py` and
  `run_mutants.sh` (the rule mutants).
- `robustness/`: the mutation probe and its README.
- `cross-backend/s8_credited_native.py`: the LLVM-callee matrix.

## Open findings

- **No miscompile was found.** The census names no mismatch and refutes no
  bound body. The LLVM-callee matrices agree with the oracle at O0 to O3,
  both credited-only and with all fourteen functions on trust-cg. One
  candidate was investigated and is not a miscompile. The
  `IpAddr::V6` `FnOnce::call_once` shim takes `[u8; 16]` by value as one
  `Array(I8, 16)` parameter. That is the bridge's tupled `rust-call`
  convention for a shim only this crate calls, and the bridge refuses
  (`[TCG-ARG-ABI]`) when such a shim's address escapes (LIMITATIONS.md,
  `rust-call` shims). Slice 8 does not bind the shim: a 16-byte INTEGER
  aggregate would be classified, but the body stops at a 484-instruction
  path.
- **79 newly bound bodies do not certify.** On 52, AY's strict
  certificate self-check rejected its own proof. On 23, the certificate has
  one unproved step. On 4, the solver timed out. None is refuted: AY
  returned no counterexample for any of them. These bodies are larger
  than the ones that certify (median 144 bound rows against 37), and they
  are the AY class `main`'s record already tracks: the word-level `bvmul`
  gap and the strict-certification wall. Each root stays fail-closed.
- **Nine promotions are solver variance, not slice 8** (see "Where the
  promoted roots came from").
- **What slice 8 names and leaves:**
  - `i128` parameters and results: 79 functions, 79 roots. These need
    register pairs and 128-bit arithmetic.
  - floating-point parameters and results: 38 functions, 38 roots. These
    need SSE registers and FP semantics.
  - aggregates over 16 bytes (MEMORY class): 3 functions, 5 roots.
  - more than six scalar parameters: 22 roots. These need stack
    arguments.
  - A 3-byte by-value argument: 5 roots. `char::escape_debug`'s
    `EscapeDebugExtArgs`, three `bool`s, is assembled in EDX by a
    mixed-width `MovRR edx, v64` and an `or`. The lane admits no
    mixed-width register move, and refuses the row by name.
- **The largest remaining class is still AY** (472 roots name a bound body
  AY does not certify), then control flow (183 over 16 blocks, 88 long
  paths, 61 loops) and checked arithmetic (97).
