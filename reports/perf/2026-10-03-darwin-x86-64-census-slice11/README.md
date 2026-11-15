# Darwin x86-64 `library/core` census — slice 11 (register pairs and float bit patterns), 2026-10-03

Slice 11 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) admits two more
value classes: `I128`, a System V INTEGER register pair, and `F32`/`F64`,
a bit pattern in an SSE register. This record holds the measurement that
chose the scope, where each meaning comes from, the floating-point probe
behind ruling OD-73, the host qualification and its spelling experiments,
the controls and their fails-before evidence, the mutation robustness
probe and the census row. Host and toolchains as in the
[slice-10 census](../2026-10-02-darwin-x86-64-census-slice10/README.md):
native stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridges built on
this host against the stage-1 `stage0-sysroot` (`targo --unverified build
--release --locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU,
proofs required (the bridge default), `x86-body-trace` and `x86-body-dump`.
Qualification: AY 0.27.0 build 10530 (sha256 `9a149c35…`) and Clean
5f09e36c (`~/clean-checker/bin/clean`). Nothing here is a completion claim.
Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md) lists each with its
SHA-256, and this README states the numbers they carry.

| Row | Bridge built from | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-5495` (baseline) | `main` `5495c11b4` | `6b33db1e…` | 1194 | 8964 s |
| `core-x86_64-darwin-O0-proof-slice11` | this branch, `d7b2c3534` (base `5495c11b4`) | `7ec2b0d7…` | 1123 | 9627 s |

**71 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted, and no body bound on both runs changes its verdict.** Every
failed root of both runs is `[TCG-PROOF-465]`. The baseline started with
907867 free pages and the slice-11 row with 670021, and neither recorded a
resource-budget refusal. The host was shared: other agents' builds
overlapped both runs, free pages fell to about 1000 once during the
baseline, and this branch's own end-to-end test build was stopped when
they first fell below 8000; wall time is a trend. Both bridges were built
in this worktree with `~/tcg-scratch/build_bridge.sh`: the baseline from
`main` `5495c11b4`'s sources (the branch's only non-test source changes,
the owner and `smt.rs`, swapped back to `main`'s for that build), the
slice-11 one from `d7b2c3534`, whose owner is the one this record
describes; later commits change tests, the report and documentation.

## The class, measured first

On the slice-10 census (`runs/census-s10`, 1198 failed roots; `main`'s
owner since `cffb7e876`), the failed roots whose named function stops at a
slice-11 refusal (`census/split_classes.py` over slice 10's `s10_roots.tsv`):

| First refusal | Functions = roots |
| --- | ---: |
| an `i128` parameter (a register pair) | 60 |
| an `i128` result | 15 |
| a floating-point or vector parameter | 20 |
| a floating-point or vector result | 18 |
| neighbours: a non-scalar `Load`/`Uextend` (`I128` 23, `F32`/`F64` 6) | 29 |
| neighbours: an aggregate call result with an `i128` field, or a call whose callee returns `u128` | 6 |

**Profile of the bodies** (`census/dump_class.sh` with slice 8's probe over
the slice-7 census's cleaned `core` module, `census/profile.py`; payloads
`dump_*.txt`, `profile_*.txt`). Of the 56 `i128`-parameter functions in the
module, the machine rows outside slice 10's lane are only `sbb` (8
functions), `adc` (5) and one division trap; the selector computes every
other `I128` operation with rows the walk already models: compares as
`cmp`/`setcc` chains of the halves, multiplies as `mul` plus two `imul`s,
shifts by a constant through CL with `cmov`s (`neg = 64 - n; shl/shr d,
cl; cmp n, 64; cmovae`), whose one-operand `shl`/`shr`/`sar d, cl` is tied.
The LIR they run: `I128` loads and stores (27/26 functions, each two 8-byte
machine accesses), `I128` constants (27 sign-extended `Iconst`, 8
`Iconst128`), compares (28), adds and subtracts, multiplies (6), shifts by
a constant (7) and by a variable amount (1), divisions (`Udiv` 5, `Sdiv`
2: calls to `__udivti3`), `CtPop` (5, as two 64-bit counts). Of the 20
float-parameter functions, 10 only move the bits (`to_bits` four times, the
`classify` wrappers four times, `integer_decode` twice), 6 compute
(`Mul`, `Div`, `Neg` and `Abs` of `f32` and `f64`, the last two through a
constant-pool mask), and `decode` twice dispatches through a jump table. Of
the 12 float-result functions in the module, 8 only move bits (`from_bits`,
`from_u64_bits`, `biased_fp_to_float`, an `Option<f64>` residual), 2 load a
constant (`Fconst`, constant pool) and 2 convert (`Lemire::from_u64`:
`cvtsi2sd` and `addsd`).

**Floating-point arithmetic is not certifiable here** (`fp/`, replayed with
slice 7's `replay_dir.py`, payload `fp_replay.tsv`): AY's strict
certification rejects its own proof of every `QF_FP`/`QF_BVFP` query tried,
however trivial: `fp.neg (fp.neg a) = a`, `to_fp` of equal words, the same
`fp.mul` on both sides, `fp.isNaN` against its bit pattern and `a + -0 =
a` (`strict UNSAT proof validation failed: step t1 uses unsupported theory
lemma kind Generic in strict mode` or `(:reason-unknown (incomplete
proof-trusted))`), and `fp.mul` commutativity (`=`, so NaN payloads
included) runs out of 240 s. So every floating-point operation is refused
by name (ruling OD-73 in docs/decision-record.md),
and a float is admitted as the bits it is.

**Scope chosen, by roots and proof risk:** `I128` register pairs (75 roots
first refused for a parameter or result, plus the 23 `I128` loads and
extensions and the `u128` call results), with `adc`/`sbb` and the tied
shifts by CL; and float bit patterns (38 roots first refused for a
parameter or result), with the SSE moves, loads and stores. Left out, with
the reason:

- **Floating-point operations** (OD-73, above).
- **A shift of an `I128` by a variable amount** (1 function). The
  selector's register-pair lowering does not reduce the amount modulo 128:
  at 128 or more each half is shifted by its own CL mask, which is neither
  trust-ir's (undefined) nor the refinement OD-57 states. Refused by name,
  fail-closed.
- **`I128` division** (calls to `__udivti3`/`__divti3` from LIR `Udiv`/
  `Sdiv`; division stays outside with slice 10's reason).
- **Aggregates with an SSE eightbyte** (`{f64, i64}`, `[f32; 2]`; no
  census root): the selector passes them in XMM registers, and the owner
  refuses them by name, as before.

**Measured next, offline** (`census/class_verdicts.py` over the slice-11
owner's `--sig` census of the same module; payload `sig_s11.tsv`,
`class_verdicts.txt`): of the 148 functions of these classes, 91 are now
bound: `i128` parameter 42 of 60, `i128` result 11 of 15, float parameter 8
of 20, float result 6 of 18, non-scalar load/extend 18 of 29, call result 6
of 6 (11 of the 148 are absent from the module). The rest stop at a later
refusal of another class: a floating-point operation (16), more than 16
blocks (8), a division (7), a private slot's address stored (6), more than
six argument registers (5: four `i128` parameters that would go on the
stack, one call passing three `i128`s and a return buffer), an atomic load
(2), the 256-row bound (1) and the variable `i128` shift (1). Every theorem
built holds on 2000 samples (no `REFUTED-AT-SAMPLE`).

## Semantics: where each meaning comes from

LIR meanings are trust-ir's (`trust_ir::interpret`, pin `0f243925`) and
`trust_cg_lower`'s documented opcodes; machine meanings are the Intel
SDM's; the System V placement is the psABI's (§3.2.3).

- **`I128` values.** A 128-bit bit-vector. `Iconst { ty: I128, imm }` is
  `imm` sign-extended (`Opcode::Iconst128`'s documentation states that the
  single-immediate form "derives the i128 high half as that immediate's
  sign extension"), `Iconst128 { lo, hi }` is `(hi << 64) | lo`. Every
  operation is stated at 128 bits with trust-ir's meaning; a shift by a
  constant below 128 of any carrier is the shift. Every name the theorem
  defines stays 64 bits wide: a 128-bit value is defined as its two halves
  (`name_source_value`), which the library gate's sampler evaluates as
  words.
- **Placement.** An `I128` parameter, argument or result takes two
  consecutive INTEGER registers, low half first (RDI:RSI, ...; RAX:RDX); an
  `I128` result is the call's or function's only result. A float takes the
  next of XMM0-XMM7, numbered apart from the integer registers; a float
  result is XMM0 (XMM1 for a second float lane; an integer lane beside it
  stays in RAX). An `I128` with one integer register left goes on the
  stack (psABI; the selector agrees) and is outside the lane.
- **Memory.** An incoming 16-byte access is two 8-byte accesses, the low
  half at the address and the high half 8 bytes above, which is exactly
  what a non-atomic, non-volatile little-endian 16-byte access reads or
  writes (nothing runs between the two). Each half pairs with one machine
  access. Private slots are modelled byte by byte as before.
- **`adc d, a, b`** is `a + b + CF` and **`sbb d, a, b`** is `a - (b + CF)`
  at the operand width; CF is read from the flags of a row the walk models
  in the same block (`add`, `sub`, `cmp`, `test`, `imul`, `mul`); undefined
  flags are a named undefined read and unmodelled ones make no claim. The
  flags `adc`/`sbb` write are not modelled.
- **The one-operand `shl`/`shr`/`sar d, cl`** is `d = d op CL` (register
  allocation ties its operand, `first_operand_is_def_and_use`).
- **SSE moves.** `movss`/`movsd` between registers copy the low 32 or 64
  bits; register allocation treats the destination as a pure definition,
  so the bits of a `movss` destination above 32 are a free input (the
  narrow-load rule). `movd`/`movq` from an XMM register write its low 32
  (zero-extended) or 64 bits; to one, the general-purpose register's low 32
  or 64 bits zero-extended. `movss`/`movsd` loads zero-extend; stores write
  the low 4 or 8 bytes. A call may change every XMM register.
- **A float `Bitcast`** to or from the integer of its width keeps the
  bits.

## Spellings chosen by qualification

`host_qualification_replays_the_slice_eleven_body_theorems` replays 36
fixture shapes (the `I128` operations, calls, memory and aggregate field,
and the float moves, calls, loads, stores and the mixed `(u64, f64)` pair).
The first spellings left five uncertified (payloads `qualification_first.log`,
`variants*.tsv`):

| Shape | First spelling | Outcome | Chosen spelling | Outcome |
| --- | --- | --- | --- | --- |
| `u128 >> 64`, `u128 << 3` | the machine's shifts by CL as slice 10's barrel shifter of the count register | self-check rejected | a count the walk's exact constant folding knows is a shift by that constant, masked as the hardware masks CL | Verified |
| `i128 >> 100`, `i64 as i128` | `bvashr` by a constant (source and machine) | Clean rejects the `bitblast_ashr` step | every arithmetic shift by a constant spelled as the sign extension of its kept bits, both sides | Verified |
| the source's 128-bit constant shift | `bvlshr`/`bvshl` by a constant | (with the barrel shifter) self-check rejected | an extract and a concat | self-check rejected: kept `bvlshr`/`bvshl` |
| `u128::wrapping_mul` | `bvmul` at 128 bits | 30 s timeout | (none) | the recorded multiply gap (`KNOWN_UNCERTIFIED_SLICE_ELEVEN`) |

The arithmetic-shift spelling is one canonical spelling for every constant
`sar` and `Sshr` (`ShiftOp::by_constant`), so it also changes slice 1:
`AshrImm` and `AshrI8Imm`, recorded since slice 1 as Clean rejecting
`bitblast_ashr`, now certify, and their records are removed from
`KNOWN_UNCERTIFIED`. A further experiment on the census's own uncertified
`I128` bodies (`census/variants3.py`: a half of a concatenation of two
names spelled as that name) changed nothing beyond AY's own load
variance: under a control rerun of the unchanged queries 9 of 31 strict
self-check rejections certified anyway (payloads `variants3.tsv`,
`orig31.tsv`), so the canonical spelling is unchanged.

## Controls and fails-before

The solver-free library gate row `x86_source_bound_body::tests::slice11::`
(17 tests; `fails-before/gate_row.sh`) passes, and so does the whole
solver-free body suite with `smt::` (175 body tests of slices 1 to 8, 10
and 11, and 154 evaluator tests; payload `solver_free_body_suite.log`),
every earlier golden snapshot byte-identical except slice 1's two
arithmetic-shift shapes (the spelling above). Earlier tests that encoded
the old boundary now state the new one: an `i128` and an `f64` argument of
slice 3 are admitted and their theorems hold; an XMM argument register the
callee does not read is a named `CallMetadata` mismatch (was: no claim);
slice 8's classification puts an `I128` field in both INTEGER eightbytes
and refuses a vector field by name; slice 5's out-of-order result
registers stay unsupported.

**The sampler's evaluators.** Building the slice-11 controls found that the
shared SMT evaluators (the interpreter `SmtExpr::eval`, the scalar tape
`FlatProg` and the wide batch tape) truncated an `Extract` wider than 64
bits to 64 bits. An `i128` shifted right arithmetically by less than 64 is
spelled as the sign extension of such a field, so the library gate's
sampler evaluated it wrong: `shifts_by_a_constant_are_rusts` failed at
`i128 >> 1` (payload `wide_extract_before_fix.log`). Each evaluator now
keeps the field wide (`a_wide_extract_keeps_its_high_bits`, against Rust's
`i128` shift, and two new differential cases). The evaluators are test and
sampling machinery, never credit; no earlier slice states an `Extract`
wider than 64 bits.

**Rule mutants** (`fails-before/mutate.py`, `run_mutants.sh`; one build,
`TCG_S11_MUTANT` selects the rule; payload `mutants.txt`): every mutant
fails at least one control; the unmutated build passes all 17.

| Mutant | Rule disabled | Failing (of 17) | Among them |
| --- | --- | ---: | --- |
| `param-halves-swapped` | an `i128` parameter is RDI low, RSI high | 7 | `the_i128_fixtures_state_rusts_128_bit_arithmetic` |
| `result-halves-swapped` | an `i128` result is RAX low, RDX high | 7 | `slice_eleven_theorems_hold_on_samples` |
| `arg-halves-swapped` | an `i128` argument's halves, low first | 6 | `every_slice_eleven_refutation_is_refuted_on_samples` |
| `call-result-swapped` | a call's `i128` result is RAX:RDX | 6 | `slice_eleven_theorems_hold_on_samples` |
| `access-no-offset` | the high half of a 16-byte access is 8 bytes above | 4 | `slice_eleven_theorems_hold_on_samples` |
| `store-low-twice` | a 16-byte store's high half stores the high bits | 4 | `slice_eleven_theorems_hold_on_samples` |
| `iconst-zero-extended` | an `Iconst { ty: I128 }` is sign-extended | 5 | `every_slice_eleven_refutation_is_refuted_on_samples` |
| `iconst128-swapped` | `Iconst128 { lo, hi }` is `(hi << 64) \| lo` | 4 | `slice_eleven_theorems_hold_on_samples` |
| `adc-no-carry` | `adc` adds CF | 6 | `adc_and_sbb_carry_between_the_halves` |
| `sbb-adds-carry` | `sbb` subtracts CF | 6 | `adc_and_sbb_carry_between_the_halves` |
| `carry-from-anything` | CF comes from a modelled row's flags | 1 | `the_carry_an_adc_reads_is_a_modelled_rows` |
| `cl-shift-reads-zero` | a one-operand shift by CL is tied (`d = d op CL`) | 5 | `a_known_count_in_cl_is_masked_like_the_hardware` |
| `cl-constant-unmasked` | a known CL count is masked to the width | 2 | `a_known_count_in_cl_is_masked_like_the_hardware` |
| `sse-one-class` | floats are numbered apart from the integer registers | 9 | `sse_registers_follow_the_caller_saved_and_result_rules` |
| `sse-result-in-rax` | a float result lane is XMM0/XMM1 | 9 | `sse_registers_follow_the_caller_saved_and_result_rules` |
| `movss-keeps-upper` | a `movss` destination's bits above 32 are free | 2 | `every_slice_eleven_refutation_is_refuted_on_samples` (`ToBitsF64/movss-over-its-copy`) |
| `xmm-survive-calls` | a call changes every XMM register | 1 | `a_call_leaves_every_sse_register_undefined` |
| `i128-variable-shift` | a variable `i128` shift is refused | 1 | `slice_eleven_sources_outside_the_lane_are_refused_by_name` |
| `ashr-as-logical` | a constant `sar` keeps the sign | 6 | `shifts_by_a_constant_are_rusts` |
| `wide-names` | every defined name is at most 64 bits | 9 | `owner_builds_for_every_slice_eleven_shape_and_covers_every_value_row` |
| `i128-field-refused` | an aggregate's `I128` field is two eightbytes | 4 | `owner_builds_for_every_slice_eleven_shape_and_covers_every_value_row` |

(The golden snapshot test also fails under every mutant that changes a
fixture theorem's text.)

**Mutation robustness** ([robustness/README.md](robustness/README.md)):
3602 mutants of the 51 distinct O0-O3 streams, judged against an
independent concrete interpreter. 2419 are wrong by ground truth: 633 make
no claim, 773 are named mismatches and 1013 are refuted by the sampler and
AY; none is credited or replays Valid. Every theorem AY refutes the
sampler refutes too (1016 of 1016). The 450 credited streams are all
correct by ground truth. 89 correct mutants are not credited (67 named
reads of an undefined register or of bytes outside a private slot whose
value nothing observes, 3 `movss` into XMM0 refuted by the free-upper-bits
rule, 10 multiply timeouts, 4 Clean rejections, 5 partial credits).
Building the probe corrected its own ground truth twice (a `bool`
parameter's psABI bits, and a 16-byte access classified per half); see its
README.

**Optimized fixtures.** The real x86 optimizer's O1, O2 and O3 output of
every fixture: every theorem the owner builds holds on samples and none is
a mismatch (`optimized_slice_eleven_fixtures_are_judged_without_false_mismatches`).
At O1 and O2 the optimizer writes the zero constant of the `I128` shift and
negation bodies as the zero idiom `xor r, r`, a two-operand form outside
the lane, so those bodies make no claim.

## End to end (`crates/trust-cg-codegen/tests/x86_source_bound_body.rs`)

The end-to-end module gains six slice-11 functions (`wide_add`, `wide_lt`,
`wide_call`, `float_to_bits`, `float_from_bits`, `float_call`); the
proof-required compile must promote with every one Formal. The
out-of-lane control is now a `u128` shift by a variable amount (the
earlier `u128` add is in the lane), and the control for an admitted body
the replayer does not certify is a 32-bit multiply (the earlier
arithmetic shift now certifies).

## Census delta

Of the 71 promoted roots, every one names a function the baseline refused
in a slice-11 class that is now bound and certified (`census/census_compare.py`,
payload `compare/`): `i128` parameter 31, `i128` result 11, a non-scalar
`Load` 10, float parameter 8, float result 6, a non-scalar `Uextend` 3, an
`i128` call result 2. No other verdict changed. The four baseline bodies
whose uncertified queries held a `bvashr` by a constant now spell it as a
sign extension and still do not certify, for other reasons (3 strict
self-check rejections, 1 holey proof; payload `ashr4_replay.tsv`).

Where the 148 functions of the slice-11 classes went (payload
`compare/slice11_transitions.tsv`):

| Class | Functions | Bound, certified | Bound, not certified | Refused |
| --- | ---: | ---: | ---: | --- |
| `i128` parameter | 60 | 31 | 11 | 18: more than 16 blocks 6, more than six argument registers 4 (and a call passing more 1), division 5 (`Udiv` 3, `Sdiv` 2), the 256-row bound 1, a variable `i128` shift 1 |
| `i128` result | 15 | 11 | 1 | 3: an atomic load 2, more than 16 blocks 1 |
| `i128` call result | 4 | 2 | 2 | |
| `i128` aggregate field | 2 | 0 | 2 | |
| non-scalar `Load` | 22 | 10 | 4 | 8: a private slot's address stored 6, `Fconst` 2 |
| non-scalar `Uextend` | 7 | 3 | 1 | 3: `Udiv` |
| float parameter | 20 | 8 | 0 | 12: a floating-point operation 8 (`Fmul`, `Fdiv`, `Fneg`, `Fabs`, 2 each), more than 16 blocks 4 |
| float result | 18 | 6 | 0 | 12: a floating-point operation 6 (`Fconst` 4, `FcvtFromUint` 2), more than 16 blocks 4, a path over 256 instructions 2 |
| **total** | **148** | **71** | **21** | **56** |

The offline measurement above predicted 91 bound; the census binds 92.

**The 21 that do not certify are AY's certification class**, replayed
offline one at a time from the census's own dump (`census/replay_dir.py`
of the slice-7 report; payload `uncert_replay.tsv`): all 21 are strict
self-check rejections (11 `unsupported hole rule`, 10 `unverified trust
rule`); none is satisfiable. They are the larger bodies (median 81 bound
rows, against 15 for the 71 that certify): the `u128`/`i128` checked and
overflowing add and subtract, `u64::carrying_mul_add` (through `u128`),
`u128::count_ones`, `is_power_of_two` and `from_ne_bytes`, the
`NonZero<u128>`/`NonZero<i128>` parsers and `leading_zeros`, the `Debug`
formatters of `TypeId` and `FieldId` (128-bit ids) and `fmt` of `u128`.

## Gates

Run on the branch merged with `origin/main` `c8b07006b` (merge `fb1ac8618`;
the slice-11 owner unchanged by the merge but for main's lint fix),
stage-1 toolchain (`targo --unverified`, no proof claim about the build),
AY 0.27.0 build 10530 and Clean 5f09e36c. The merge renumbered this
branch's floating-point ruling OD-58 to OD-73 (main had published a
different OD-58, and slice 9 had published OD-73 and OD-72) and joined slice 11 to main's new qualification query
matrix and to the soundness gate's library rows.

| Gate | Result |
| --- | --- |
| `~/tcg-scratch/gates_stage1.sh`: verify library, `x86_source_bound_body` and `diag::` with AY and Clean (every slice's qualification, slice 11's included, and the query matrix) | 196 passed, 2 failed, 7 ignored. The two failures, `memory::host_qualification_replays_the_memory_body_theorems` (the known `SlotFoldedOffset` load flake) and `negative_memo::any_key_component_change_misses`, ran while another agent's verify suite ran on the host; both pass alone (payload `flake_rerun.log`) |
| the same: codegen `x86_source_bound_body` end to end and `must_refuse_corpus` | 5 and 5 passed; the end-to-end test replays on the stage-1 AY (`X86_BODY_E2E_REPLAY_IDENTITY`) and the six slice-11 functions promote Formal (payload `e2e.log`) |
| `fails-before/qualify.sh` on `slice11_qualification::` and slice 1's host qualification (before the merge) | 35 Verified, `MulU128` the recorded timeout, 26 of 26 refutations `CounterExample`; slice 1's `AshrImm` and `AshrI8Imm` Verified (payload `qualification_merged.log`) |
| `fails-before/gate_row.sh` (the soundness-check row `slice11::`) | 17 passed (before the merge) |
| IR, lowering and optimizer libraries (no AY variables, as `gates_full_stage1.sh`, at `-j2`) | 538, 1993 and 4226 passed (2 ignored) |
| codegen library (the same) | first run 4606 passed, 6 failed: six tests used an `i128` as their out-of-lane device (an `i128` add, identity, constant or result), which slice 11 now admits, so their modules promoted or failed on a body theorem instead of on sampled evidence (payload `codegen_lib_first.log`). They now use a variable `i128` shift, which the lane refuses by name; rerun: 4612 passed, 0 failed, 1 ignored |
| CLI `must_refuse_corpus` | 1 passed |
| `scripts/test_soundness_check.sh` (the new `slice11::` row) | 97 passed |
| `scripts/tests/test_export_x86_qualification_matrix.py` | 10 passed (its snapshot-family count moves from 7 to 8 with slice 11; it failed before) |
| `bash scripts/check_fmt.sh` (the managed package's `targo fmt`) | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `scripts/check_tippy.sh` | cannot run here: the only `tippy` on this host (managed package 6808) stops before linting every package (256 `unknown field compiler_timeout_secs`, 4 `no matching package named ay-pb`; payload `tippy.log`), and the stage-1 build has no `tippy` |

## Open findings

- **No miscompile was found.** The census names no mismatch and refutes no
  bound body; every refuted probe mutant is wrong by the independent
  interpreter, except three that differ from the source only in bits the
  owner states as a free input (a `movss` destination's bits above 32).
- **AY's certification class** keeps 21 bound class bodies uncertified
  (strict self-check rejections) and the `u128` multiply fixture (a 30 s
  timeout).
- **Floating-point arithmetic stays outside** (OD-73): 16 class functions
  stop at a floating-point operation, and an AY that certifies `QF_FP`
  proofs is what would admit them.
- **A variable `i128` shift is refused, not a miscompile.** The selector's
  register-pair lowering of an amount of 128 or more shifts each half by
  its own count mask; trust-ir is undefined there, and Rust's `<<` on
  `u128` panics or masks the amount before it reaches the shift. It is
  outside the lane because it is neither trust-ir's meaning nor OD-57's
  refinement, which a theorem must state.
- **The optimizer's zero idiom** `xor r, r` is outside the lane, so the
  `I128` shift and negation bodies make no claim at O1 and above.

## Reproducers (in tree)

- `census/census_s11.sh` (the census command), `census/census_compare.py`
  (promoted, newly failing, mismatches, refuted bodies, transitions),
  `census/split_classes.py` (the class measurement), `census/dump_class.sh`
  and `census/profile.py` (the body profile; the probe is slice 8's
  [`probe/x86_body_probe.rs`](../2026-10-02-darwin-x86-64-census-slice8/probe/x86_body_probe.rs),
  copied to `crates/trust-cg-verify/examples/` and built with the owner
  under test), `census/class_verdicts.py` (the offline verdicts),
  `census/variants*.py` and `census/copy_outcome.py` (the spelling
  experiments, replayed with slice 7's `census/replay_dir.py`),
  `census/payloads.py` (the [PAYLOADS.md](PAYLOADS.md) rows).
- `fp/`: the six floating-point queries behind OD-73.
- `fails-before/`: `qualify.sh`, `gate_row.sh`, `mutate.py`,
  `run_mutants.sh`.
- `robustness/`: the mutation probe and its README.
