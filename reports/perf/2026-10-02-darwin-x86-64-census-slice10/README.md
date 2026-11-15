# Darwin x86-64 `library/core` census — slice 10 (instruction coverage), 2026-10-02

Slice 10 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) admits six more LIR
operations with the x86-64 rows the selector lowers them to: checked
arithmetic (`CheckedUadd`/`Usub`/`Umul`/`Sadd`/`Ssub`/`Smul` of `I64`, with
the flags of `add`, `sub`, `imul` and the one-operand `mul`), `Bnot`
(`not`), `Ineg` (`neg`), `CtPop` (`popcnt`), shifts by a variable amount
(`shl`/`shr`/`sar` by CL) and `CallIndirect` (`call r64`). This record holds
the measurement that chose the scope, where each meaning comes from, the
host qualification, the controls and their fails-before evidence, the
mutation robustness probe and the census row. Host and toolchains as in
the [slice-8 census](../2026-10-02-darwin-x86-64-census-slice8/README.md):
native stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridges built on
this host against the stage-1 `stage0-sysroot` (`targo --unverified build
--release --locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU,
proofs required (the bridge default), `x86-body-trace` and `x86-body-dump`.
Qualification: AY 0.27.0 build 10530 (sha256 `9a149c35…`) and Clean
5f09e36c (`~/clean-checker/bin/clean`). Nothing here is a completion
claim. Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md) lists each with
its SHA-256, and this README states the numbers they carry.

| Row | Bridge built from | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-ac04` (baseline) | `main` `ac0481810` | `727e6e3b…` | 1272 | 6439 s |
| `core-x86_64-darwin-O0-proof-slice10` | this branch, `99c2ca5cf` (base `ac0481810`) | `a9d570c2…` | 1198 | 11134 s |

**74 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted, and no body bound on both runs changes its verdict.** Every
failed root of both runs is `[TCG-PROOF-465]`. The census started with
1035932 free pages and recorded no resource-budget refusal; the host was
shared (other agents' AY and bridge builds overlapped both runs), so wall
time is a trend. The slice-10 bridge's owner is the committed one of
`99c2ca5cf`; later commits change tests, the report and documentation.

## The class, measured first

The baseline's failed roots, by the first refusal of the function each
names (`census/classes.py`, `root_classes.py` keys; payload
`main_roots.tsv`):

| First refusal | Roots | Slice 10 |
| --- | ---: | --- |
| checked arithmetic: `CheckedUadd` 37, `Usub` 25, `Umul` 20, `Ssub` 6, `Smul` 5, `Sadd` 4 | 97 | admitted |
| `CallIndirect` | 23 | admitted |
| `Bnot` | 17 | admitted |
| `CtPop` | 15 | admitted |
| a shift by a non-constant amount (`Ishl` 8, `Ushr` 3) | 11 | admitted |
| `Ineg` | 1 | admitted |
| a private slot's address stored to memory | 34 | outside: a memory-model extension, not an instruction |
| a non-scalar `Load`/`Uextend` (`I128` 23, `F32`/`F64` 6) | 29 | outside: register pairs, SSE |
| atomics (`AtomicLoad` 11, `AtomicStore`/`AtomicRmw` 1) | 12 | outside: every one also dispatches through a jump table (`JmpR`) |
| `GuardDivZero` | 11 | outside, below |
| `Udiv` 7, `Urem` 3 | 10 | outside, below |
| no value observable | 14 | outside: nothing to state |

The dumped LIR and pre-RA streams of every in-scope function (the probe of
the [slice-8 report](../2026-10-02-darwin-x86-64-census-slice8/probe/x86_body_probe.rs)
over the slice-7 census's cleaned `core` dump; `census/split_classes.py`,
`census/lir_scan.py`, `census/cfg_scan.py`) show that each is within the
slice-6 control-flow bounds and that its only rows outside the lane are
the new ones (`Mul`, `Not`, `Popcnt`, `ShlRR`/`ShrRR`, `CallR`). The O0
selector lowers `CheckedUadd`/`Usub` to `add`/`sub; setb`, `Sadd`/`Ssub`/
`Smul` to `add`/`sub`/`imul; seto`, `Umul` to `mov rax, a; mul b; mov v,
rax; setb`, and the overflow `bool` then feeds a compare and a branch to a
panic call.

**Scope chosen, by roots over proof risk:** checked arithmetic first (97
roots; needs flag semantics), then `Bnot`/`Ineg` (one row each, no flags),
`CtPop` (one row; the narrow mask), `CallIndirect` (the slice-3 call model
plus one observed argument) and variable shifts (needs trust-ir's
undefined behaviour handled; below). Left out, with the reason:

- **Division and `GuardDivZero` (21 roots).** trust-ir's `UDiv`/`URem` is
  undefined behaviour at a zero divisor and `DIV` traps there, so a sound
  theorem must state, per path, "where the source's divisors are nonzero,
  the machine's `DIV` does not trap". That is a definedness condition in
  the path claim, which the theorem's path encoding (slice 9's area, in
  progress in parallel) does not have; `GuardDivZero` is a defined trap,
  which needs trap paths. Most of these divide by a constant, which the
  selector lowers to a magic-number `mul`, whose theorem would need AY to
  prove the reciprocal identity (bit-blasting a divider and a 128-bit
  multiplier).
- **Atomics (12 roots):** `core::sync::atomic::atomic_load` matches on the
  ordering with a jump table, which no slice admits; the atomic row itself
  would be a plain `mov` under TSO, but every such body is refused earlier.

## Semantics: where each meaning comes from

Every LIR meaning is the pinned trust-ir's (`fb477354`,
`crates/trust-ir/src/interpret.rs`):

- **Checked arithmetic** (`eval_int_overflow`): the value is
  `eval_int_binop`'s wrapping add/sub/mul; the overflow is
  `unsigned_overflow` (`sum > mask`, `lhs < rhs`, `product > mask`) or
  `signed_overflow` (the checked result outside `[min, max]`). The owner
  states it as "the mathematical result, computed at `w + 1` (sum,
  difference) or `2w` (product) bits from operands extended by their
  signedness, is not its own low `w` bits extended back"
  (`CheckedOp::overflows`); a unit test compares it with Rust's
  `overflowing_*` at both widths and every signedness on edge and random
  operands. The adapter maps exactly the 64-bit `Overflow` to these
  opcodes (`adapter.rs`, "Fast path (#474)"); narrower ones become `Iadd`/
  `Icmp`/`Bnot`/`Band` sequences (the 32-bit signed add's flag is
  `!(a ^ b) & (a ^ sum) < 0`, which is why `i8`/`i16`/`i32::overflowing_add`
  were `Bnot` roots). The owner admits checked ops of `I64` only.
- **`Not`, `Neg`, `CtPop`** (`eval_int_unop`): `!raw`, `0 - raw` and
  `count_ones` at the width. trust-ir's validator refuses `not` of a scalar
  `bool`, so a `B1` operand stays outside.
- **Shifts** (`shift_amount`): an amount at or above the width is
  undefined behaviour (an interpreter `ub` error), so trust-ir neither masks
  nor traps. In range the theorem states trust-ir's shift; out of range it
  states one refinement of the undefined behaviour, the amount reduced
  modulo the width, which is what the selector's masked lowering computes
  (`and cnt, 7` / `and cnt, 15` for a narrow count, then the hardware's
  mask of CL to 5 or 6 bits). That is sound (any value refines undefined
  behaviour) and complete for the selector, and strictly stronger than
  trust-ir: a lowering that differs only where the source is undefined (an
  unmasked narrow count) is refuted, not credited. A constant out-of-range
  amount stays outside, as before.
- **`CallIndirect`**: `args[0]` is the code pointer (`Ty::Func`, `Ptr` or a
  64-bit integer; the adapter's `CallIndirect` checks), the rest the
  arguments under the callee's signature.

The machine meanings are the Intel SDM's: `add`/`sub` set every status
flag (`sub` as `cmp`, through the shared EFLAGS model; `add` through the new
`x86_64_eflags::encode_add_eflags`, CF the carry out of the top bit);
`imul r, r` sets CF = OF to `SignExtend(truncate(TMP)) != TMP` and leaves
SF/ZF/AF/PF undefined; `mul r/m` writes EDX:EAX or RDX:RAX with the
unsigned product (each 32-bit half zero-extended), CF = OF = "the high half
is not zero", the rest undefined. Reading an undefined flag is a named
`UndefinedRead` of `rflags` (as after a call). `not`, `neg` and `popcnt`
compute at the operand width; a shift by CL reads the low byte of RCX,
masked to 5 or 6 bits. `call r64` jumps to the register's 64 bits.

**Two statements are shared by both sides**, each a definition rather than
a lowering: population count (`count_ones`) and a shift by an amount
modulo the width (`shift_modulo_width`). Unit tests compare each with
concrete arithmetic (`u64::count_ones`, Rust shifts), and the robustness
probe's interpreter computes both independently.

## Qualification (`fails-before/qualify.sh`)

`host_qualification_replays_the_slice_ten_body_theorems`: 25 fixture
shapes (six checked ops, an overflow-checked add and multiply that branch
to a panic, the 32-bit signed-add fallback, `not` of three widths, `neg`,
`count_ones` of four widths, five variable shifts, three indirect-call
shapes). 22 are `Verified` (258 ms to 14.6 s). The three 64-bit multiply
shapes are recorded gaps (`KNOWN_UNCERTIFIED_SLICE_TEN`): AY's strict
certification rejects its own proof (`step t1 uses unsupported hole
rule`, `(:reason-unknown (incomplete self-check-rejected))`). AY refutes
all 19 wrong lowerings with counterexamples (the 19th, an overflow word
compared with -1, came from the robustness probe; below).

**Spellings chosen by qualification** (`census/variants*.py`, payload
`spellings.tsv`). The first spellings left nine shapes uncertified:

| Shape | First spelling | Outcome | Chosen spelling | Outcome |
| --- | --- | --- | --- | --- |
| `count_ones` of 32 and 64 bits | a chain of full-width adds | self-check rejected | a balanced tree of adds at the count's own width | Verified |
| four variable shifts (32/64-bit, logical and arithmetic) | `bvlshr`/`bvshl`/`bvashr` by `n & (w - 1)` | an unproved step (`unproved_steps=1`), with or without the CL extract | a barrel shifter of extracts selected by the count's bits | Verified (5 of 5, offline then in the gate) |
| 64-bit multiply (3 shapes) | round-trip overflow, `bvmul` value | self-check rejected | (none found) | the value equation alone, the overflow alone, both sides as "high half != 0", and `bvumulo` are each rejected the same way |

`verifier_credits_every_bound_slice_ten_row_with_the_replayed_body_theorem`:
every covered row of every certified fixture is Formal under the body
theorem, the function is promotable and its exports bind the ABI; every
covered row of a refuted mutant fails (under the body theorem, or, for the
`neg`-as-`not` mutant, under the TV-2 provenance cross-check of the changed
row first).

## Controls and fails-before

The solver-free library gate row `x86_source_bound_body::tests::slice10::`
(17 tests; `fails-before/gate_row.sh`) passes, and the whole solver-free
body suite (slices 1 to 8 and 10, 148 tests) passes with every earlier
golden snapshot byte-identical. Three earlier tests encoded the old
boundary and now state the new one: an indirect call is admitted, a `call
r64` where the source calls a symbol is a named `CallTarget` mismatch
(was: no claim), and a variable shift is slice 10's.

**Rule mutants** (`fails-before/mutate.py`, `run_mutants.sh`; one build,
`TCG_S10_MUTANT` selects the rule; payload `mutants.txt`): every mutant
fails at least one control; the unmutated build passes all 17.

| Mutant | Rule disabled | Failing (of 17) | Among them |
| --- | --- | ---: | --- |
| `add-flags-unmodelled` | `add` defines the flags a reader uses | 6 | `owner_builds_for_every_slice_ten_shape_and_covers_every_value_row` |
| `add-carry-as-overflow` | `add`'s CF is the carry | 5 | `slice_ten_theorems_hold_on_samples` |
| `sub-borrow-inverted` | `sub`'s CF is the borrow | 5 | `slice_ten_theorems_hold_on_samples` |
| `imul-flags-defined` | `imul` leaves SF/ZF/PF undefined | 2 | `reading_a_flag_imul_or_mul_leaves_undefined_is_a_named_mismatch` |
| `mul-high-as-low` | `mul` writes the high half to RDX | 2 | `every_slice_ten_refutation_is_refuted_on_samples` |
| `mul-no-overflow` | `mul` sets CF = OF to "high half != 0" | 4 | `slice_ten_theorems_hold_on_samples` |
| `overflow-unsigned` | the overflow's signedness follows the op | 6 | `the_overflow_predicate_is_trust_irs` |
| `overflow-narrow-mul` | a product is exact at `2w` bits | 5 | `the_overflow_predicate_is_trust_irs` |
| `popcount-low-byte` | a count counts every bit (both sides) | 3 | `the_flag_models_are_the_hardwares` |
| `tied-and-as-move` | a tied `and d, imm` is `d = d & imm` | 4 | `slice_ten_theorems_hold_on_samples` |
| `callee-not-observed` | an indirect call's pointer is observed | 3 | `every_slice_ten_refutation_is_refuted_on_samples` |
| `call-kind-unpaired` | `call r64` pairs only with an indirect call | 1 | `an_indirect_call_pairs_only_with_a_register_call` |
| `narrow-checked` | checked ops of another carrier are refused | 1 | `slice_ten_sources_outside_the_lane_are_refused_by_name` |
| `shift-count-unmasked` | a shift by CL masks the count | 5 | `a_variable_shift_is_trust_irs_in_range_and_masked_beyond` |
| `source-shift-unmasked` | the source shift reduces its amount | 5 | `a_variable_shift_is_trust_irs_in_range_and_masked_beyond` |

(The golden snapshot test also fails under every mutant that changes a
theorem's text.)

**The sampler's own control.** The refutation `AddI32/overflow-word-needle`
(the robustness probe's needle, below) fails
`every_slice_ten_refutation_is_refuted_on_samples` under the sampler of
`99c2ca5cf` (no repeating patterns, no equal operands; payload
`needle_old_sampler.log`) and passes under the committed one.

**Mutation robustness** ([robustness/README.md](robustness/README.md)):
1230 mutants of the 29 distinct O0-O3 streams, judged against an
independent concrete interpreter. 1041 are wrong by ground truth: 10 make
no claim, 551 are named mismatches and 480 are refuted by the sampler and
AY; none is credited or replays Valid. Every theorem AY refutes the
sampler refutes too (484 of 484). The 81 credited streams are all correct
by ground truth. Four correct mutants are refuted, each differing from the
source only where trust-ir's shift is undefined. Building the probe found
one sampler needle (a 32-bit signed-add overflow word that is all ones only
at `a = b = 0x55555555`, which AY refuted and the sampler did not): the
library sampler now has repeating bit patterns and equal-operand samples.

**Optimized fixtures.** The real x86 optimizer's O1, O2 and O3 output of
every fixture: every theorem the owner builds holds on samples, none is a
mismatch; `MulPanics` at O1-O3 makes no claim (the optimizer tests the
carry with `bt`, a row no slice admits).

## End to end (`crates/trust-cg-codegen/tests/x86_source_bound_body.rs`)

The end-to-end module gains five slice-10 functions (`insn_overflowing_add`,
`insn_not`, `insn_count_ones`, `insn_shr`, `insn_indirect`); the
proof-required compile must promote with every one Formal; it does (see
Gates).

## Census delta

Of the 74 promoted roots, every one names a function the baseline refused
in a slice-10 class that is now bound and certified (`census/census_compare.py`,
payload `compare.txt`): checked arithmetic 39 (`Uadd` 17, `Usub` 12, `Ssub`
6, `Sadd` 4), `Bnot` 12, `CallIndirect` 8, variable shifts 7, `CtPop` 7,
`Ineg` 1. No other verdict changed.

Where the 164 functions of the slice-10 classes went (payload
`slice10_transitions.tsv`):

| Class | Functions | Bound, certified | Bound, not certified | Refused |
| --- | ---: | ---: | ---: | --- |
| checked `Uadd` | 37 | 17 | 15 | 5: more than 256 machine rows |
| checked `Usub` | 25 | 12 | 12 | 1: more than 256 machine rows |
| checked `Umul` | 20 | 0 | 19 | 1: more than 256 machine rows |
| checked `Sadd`/`Ssub` | 10 | 10 | 0 | |
| checked `Smul` | 5 | 0 | 5 | |
| `CallIndirect` | 23 | 8 | 15 | |
| `Bnot` | 17 | 12 | 5 | |
| `CtPop` | 15 | 7 | 8 | |
| variable shift | 11 | 7 | 4 | |
| `Ineg` | 1 | 1 | 0 | |
| **total** | **164** | **74** | **83** | **7** |

**The 83 that do not certify are AY's certification class**, replayed
offline one at a time from the census's own dump (`census/replay_dir.py`
of the slice-7 report; payload `uncert_replay.tsv`): 74 strict
self-check rejections (41 `unsupported hole rule`, 30 `unverified trust
rule`, 3 other), 8 proofs with an unproved step, 1 solver timeout; none is
satisfiable. All 24 multiplies are among them (the gap the fixtures
record). They are larger than the bodies that certify (median bound rows:
`Uadd` 141, `Usub` 137, `CallIndirect` 42). Respelling the source overflow
of the 42 unsigned add/sub bodies as the machine's flag (carry-out, `bvult`)
certifies one more (`format_into`), which is within AY's wall-clock
variance of its strict self-check, so the canonical spelling is unchanged.

## Gates

Run on the branch merged with `origin/main` `7d7a6035f` (the slice-10
commits unchanged), stage-1 toolchain (`targo --unverified`, no proof claim
about the build), AY 0.27.0 build 10530 and Clean 5f09e36c:

| Gate | Result |
| --- | --- |
| `~/tcg-scratch/gates_stage1.sh`: verify library, `x86_source_bound_body` and `diag::` with AY and Clean (every slice's qualification) | 178 passed, 0 failed, 6 ignored |
| the same: codegen `x86_source_bound_body` end to end (the five slice-10 functions promote) and `must_refuse_corpus` | 5 and 5 passed |
| `fails-before/qualify.sh` on `slice10_qualification::` | 22 Verified, 3 recorded multiply gaps, 19 of 19 refutations `CounterExample` |
| `fails-before/gate_row.sh` (the soundness-check row `slice10::`) | 17 passed (before the merge) |
| codegen library (no AY variables, as `gates_full_stage1.sh`) | 4581 passed, 0 failed, 1 ignored (rerun; the first run, with two other agents' builds and tests on the host and about 3000 free pages, failed `x86_verifying_jit_publishes_exactly_on_a_valid_envelope_replay` at its "the JIT must publish" assertion; that test passes alone, 118 s, and in the full rerun) |
| CLI `must_refuse_corpus` | 1 passed |
| `bash scripts/check_fmt.sh` (the managed package's `targo fmt`; the stage-1 `targo` has no `fmt`) | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `scripts/check_tippy.sh` | cannot run here: the only `tippy` on this host (managed package 6808, `tippy 0.1.98`) stops before linting on every package (`unknown field compiler_timeout_secs` in the configuration it reads, `no matching package named ay-pb`); it reports no lint diagnostic, and the stage-1 build has no `tippy` |

## Open findings

- **No miscompile was found.** The census names no mismatch and refutes
  no bound body; every refuted mutant is wrong by the independent
  interpreter or differs only where trust-ir is undefined.
- **A stronger trust-ir shift semantics is out of reach of this encoding.**
  The theorem's refinement of an out-of-range shift is stricter than
  trust-ir (four probe mutants differ only at undefined inputs and are
  refuted). A definedness condition in the path claim would remove that,
  and would also admit division; both wait for the path encoding (ruling
  OD-57 in docs/decision-record.md).
- **AY's multiply gap** keeps every 64-bit checked multiply (24 `core`
  functions) uncertified on the qualification host.

## Reproducers (in tree)

- `census/census_s10.sh` (the census command), `census/census_compare.py`
  (promoted, newly failing, mismatches, transitions), `census/classes.py`,
  `census/roots_by_fn.py`, `census/split_classes.py`, `census/lir_scan.py`,
  `census/cfg_scan.py` (the class measurement), `census/variants*.py` (the
  spelling experiments), `census/payloads.py` (the [PAYLOADS.md](PAYLOADS.md)
  rows).
- `fails-before/`: `qualify.sh`, `gate_row.sh`, `mutate.py`,
  `run_mutants.sh`.
- `robustness/`: the mutation probe and its README.
