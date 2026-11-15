# Darwin x86-64 — a 128-bit shift by a constant amount (OD-215), 2026-10-27

The x86-64 instruction selector selected every 128-bit `Ishl`/`Ushr`/`Sshr`
through its general count-in-RCX path: for `Ushr x, 64`, the high-limb
extraction of every `u128` `widening_mul`, `carrying_mul`, Display and the
adapter's 128-bit switch, 25 pre-RA rows with three `cmov`s and four shifts
by CL. AArch64 already folds a constant amount. Ruling OD-215 folds every
amount trust-ir defines (`docs/decision-record.md`); this is "Step 0" of the
division-free 128-bit checked-multiply design
(`~/tcg-scratch/i128-mulo-design/`, §7 risk 1) and a runtime change on its
own.

Host: the shared x86_64 Mac (Darwin 22.6, macOS 13.7.8). Every build and
test through `build-slot` and `scripts/trust_cargo.sh` with the overlay
`x86-stage1-ay13556` (`targo --unverified`, `nice -n 19`, `-j2`; no proof
claim about any build). Replayer pair: AY build 13556 with Clean 5f09e36c
(`QUALIFIED_AY`). Branch `feat/x86-i128-const-shift` from main `f7881289c`,
merged with origin/main `e74f215c6` (slice 23's landed head) on 2026-11-02
and re-gated there (the last section, "Merged with origin/main"). Its census (below) holds
the floor: 20 failed roots before and after.

## Soundness notes first

- **After the merge with slice 23 (2026-11-02): no new concern.** The fold
  and slice 23's pairing (OD-205) and generalization (OD-206) do not
  interact on the whole Darwin `core`: with the fold off the merged tree
  states every one of main's 4,012 probe queries byte for byte, the 30
  paired owners and their pairing records are the same with the fold on,
  and every theorem the fold changes certifies offline on AY 13556 + Clean
  5f09e36c by the census's route, as on main, with no exact refutation on
  any route (exact, parts, claims, generalizations; the merge section).
- **No new trust, no new rule.** The body theorem is unchanged: every row
  the fold emits (`mov`, `mov imm`, `shl`/`shr`/`sar r64, imm8`, `or`) is a
  row it already admits with its Intel SDM meaning, and the source is slice
  1's shift by an in-range constant. The fold only changes which admitted
  rows the selector emits.
- **Undefined amounts are untouched.** An amount of 128 or more (undefined in
  trust-ir) keeps the general CL/CMOV path byte for byte, and the body
  theorem keeps refusing an out-of-range constant by name (both pinned by
  tests). AArch64's fold reduces modulo 128 instead; the two backends agree
  on every defined amount and differ only where trust-ir owes nothing. The
  rustc bridge never emits an undefined constant amount (`raw & 127`).
- **The amount is read at the count's own type**, as the general path's zero
  extension reads it, and an `I128` `Iconst`'s high half is its sign
  extension, so a negative 128-bit immediate is an undefined amount, not a
  small one (`a_narrow_constant_count_is_read_at_its_width`,
  `a_wide_constant_count_folds_only_when_its_128_bit_value_is_defined`).
- **The opt-out reads the process environment** (`std::env`, like
  `TCG_NO_X86_JUMP_TABLE`), not `trust_cg_process_env`'s thread-local
  overrides; the installed trustc refuses every `TCG_*` variable, so through
  the bridge the fold is always on. Artifact reuse treats any present `TCG_*`
  variable as an unkeyed compiler input (fail closed).
- **Census (measured after slice 23).** The Darwin x86-64 `core` proof census
  (O0, AY build 13556 with Clean 5f09e36c) of this lane's landed head `6607d0f6b`
  has 20 failed roots, the same as slice 23's `f2a032c4d`: `census_compare.py`
  gives 0 promoted, 0 newly failing, 0 named mismatches, 0 refuted bodies, and
  the two `failed_roots.jsonl` are byte-identical (sha `c955ebdd…`). All 20 are
  OD-115's no-observable bodies. The bridge (sha `393bc99d…`, 2057 s wall) was
  built in its own detached tree with the local engineering targo.

## The case split

`k` the amount, `src = hi:lo` (64-bit halves). Rows are pre-RA, three-address
(register allocation ties each destination to its first source).

| Amount | `Ishl` | `Ushr` | `Sshr` | Rows |
| --- | --- | --- | --- | ---: |
| `k = 0` | `lo' = lo`, `hi' = hi` | same | same | 2 `mov` |
| `0 < k < 64` | `lo' = lo << k`; `hi' = (hi << k) \| (lo >> 64-k)` | `lo' = (lo >> k) \| (hi << 64-k)`; `hi' = hi >> k` | as `Ushr`, `hi' = hi >>a k` | 3 shifts + `or` |
| `k = 64` | `lo' = 0`, `hi' = lo` | `lo' = hi`, `hi' = 0` | `lo' = hi`, `hi' = hi >>a 63` | 2 |
| `64 < k < 128` | `lo' = 0`, `hi' = lo << k-64` | `lo' = hi >> k-64`, `hi' = 0` | `lo' = hi >>a k-64`, `hi' = hi >>a 63` | 2 |

Opcodes: `MovRR`, `MovRI`, `ShlRI`, `ShrRI`, `SarRI`, `OrRR`, all 64-bit. The
selector has no `shld`/`shrd`, so the funnel is two shifts and an `or`. Every
limb count is in `1..=63`, where the CPU's 6-bit count mask is the identity.

**The amount.** A count that is an `Iconst` (the selector's whole-function
pre-scan) or an `Iconst128` with a zero high half, read at its own type, and
below 128. trust-ir's shift is undefined at 128 or more
(`interpret::shift_amount`), so nothing is reduced: an undefined amount, a
`B1` count and a non-constant count keep the general path byte for byte
(unit test `undefined_or_untracked_constant_amounts_keep_the_general_path_
byte_for_byte`). The rustc bridge spells a constant 128-bit amount as
`raw & 127` at the shifted type (`emit_typed_const`), so every constant Rust
shift is in range; the adapter spells its own 128-bit amounts (rotates,
byte and bit reverses) as `Iconst128`.

## Proof coverage

**Per-instruction evidence (unchanged).** Every row the fold emits is an
opcode the x86-64 inventory already classifies as emittable with proof
(`coverage_gate.rs`, `EmittableNeedsProof` for `OrRR` and the three `*RI`
shifts; `MovRR`/`MovRI` are moves): the immediate shifts are the PROOF-5
parametric reconstruction family (`is_parametric_imm_binary_opcode`, one
free-immediate obligation per width with the `count < width` premise), `or`
the `Bor` reconstruction. Under E0.2 such a registry or reconstruction hit is
not formal credit by itself; the formal credit is the body theorem's.

**The body theorem (no change to it).** The source side is slice 1's rule
for a shift by an in-range constant of the chain (`SourceOp::Shift`,
trust-ir's `bvshl`/`bvlshr` at 128 bits, `bvashr` spelled as the sign
extension of the kept bits), already admitted for `I128` by slice 11; an
out-of-range constant stays outside by name. The machine side is the walk's
existing Intel SDM transcription: `shl`/`shr`/`sar r64, imm8` with the count
masked to 6 bits (`ShiftOp::by_constant`), `or`, `mov`, `mov imm`. The rows
are in `BODY_OPCODES`. So the fold adds no rule and no row kind, and an
`I128` constant shift the selector folds is admitted exactly where it was.

**Fixtures** (`x86_source_bound_body::tests::i128_const_shift`, real adapter
and selector output, golden `i128_const_shift_snapshots.smt2`): each shift by
0, 1, 63, 64, 65 and 127, and `(x >> 64) as u64`. Solver-free, all pass: the
streams carry exactly the case split's rows and no CL shift, compare or
`cmov`; the owner binds every value row; the theorems hold on the slice-11
pooled sampler and state Rust's shift item by item at edge halves; **every
amount 0-127 of every shift, with the fold on and with it off** (the general
path, which a constant the selector does not track still takes), is bound and
holds on 256 pooled samples; a shift by 128 stays outside by name and is not
folded.

**Replayed (AY build 13556 + Clean 5f09e36c, one test per process):** all 19
fixtures `Verified` (0.07-0.58 s each) and every covered row credited Formal
by the verifier (`verifier_credits_every_bound_i128_const_shift_row_with_the_
replayed_body_theorem`); all **51 wrong lowerings refuted with an AY
counterexample**:

| Family | Count | Mutation |
| --- | ---: | --- |
| amount off by one | 19 | the selector's own stream for `k + 1` (`k - 1` at 127) under the source for `k` |
| wrong fill | 13 | a right shift's stream for the other right shift (zero fill for sign fill, a logical high-half shift for an arithmetic one, and back; 10), a left shift's zeroed low half filled with `sar lo, 63` (64, 65, 127) |
| wrong half | 19 | the first row that reads a parameter half reads the other half |

The truncated fixture has no wrong-fill control: its one observed item is the
low limb, which no fill reaches (the mutant would be equivalent).

## Fails before

`x86_64_isel::tests::i128_ushr_by_64_is_a_move_of_halves_not_the_cl_cmov_ladder`
(trust-cg-lower): with the fold off (the selector before OD-215) `Ushr x,
64` by an `I128` count is 25 pre-RA rows, three `cmov`s, one `shl` and three
`shr` by CL, the count moved into RCX; with it on, `[MovRR lo' <- hi, MovRI
hi' <- 0]`. With the fold off the selector is the parent's, byte for byte
(every earlier golden digest reproduces with it off, below), so the folded
assertions are ones the parent fails. Pre-RA rows per shift, `I128` count
(`Ushr` asserted by the test; `Ishl` and `Sshr` counted from the general
path's code):

| Shift | general path | folded |
| --- | ---: | ---: |
| `Ishl`, `Ushr` | 25 | 2 (k = 0, k >= 64) or 4 |
| `Sshr` | 29 | 2 or 4 |

`i128_constant_shifts_compute_rusts_shift_at_every_defined_amount` runs the
emitted rows of BOTH paths through an independent concrete Intel evaluator
in the test (6-bit count mask, `cmp` flags, `cmove`/`cmovae`): every amount
0-127 x 3 shifts x 4 count types (`I128`, `I64`, `I32`, `I8`) x 24 values
(edges with both sign bits, patterns, seeded words) equals Rust's `u128`/
`i128` shift: 36,864 checks per path. Exhaustive in the amount and the
operation, sampled in the value: a test, not a proof.
`a_narrow_constant_count_is_read_at_its_width`, `a_wide_constant_count_folds_
only_when_its_128_bit_value_is_defined` and `undefined_or_untracked_constant_
amounts_keep_the_general_path_byte_for_byte` pin the amount rule.

## Native execution on this host

`e2e_x86_64_i128_const_shift` (new; registered as an x86-64 execution suite
in `scripts/full_test_matrix_hosts.py`): 19 functions (each shift by 0, 1,
63, 64, 65, 127 and `(x >> 64) as u64`), the count spelled as the rustc
bridge spells it, compiled through the AOT `Compiler` for
`x86_64-apple-darwin` at O0, O1, O2 and O3, linked with `cc` against a C
driver that compares each with C's own `unsigned __int128`/`__int128` shift
(clang's `>>` of a signed value is arithmetic) on 144 values whose halves are
12 edge words (both sign bits set and clear, all ones, 1, 2, patterns):

| Run | O0 | O1 | O2 | O3 |
| --- | --- | --- | --- | --- |
| fold (default) | 2736 checks, 0 failures | 2736, 0 | 2736, 0 | 2736, 0 |
| `TCG_NO_X86_I128_CONST_SHIFT=1` (general path) | 2736, 0 | 2736, 0 | 2736, 0 | 2736, 0 |

The decode leg (`objdump`) asserts what was exercised: with the fold, no
`cmov` and no shift by `%cl` anywhere in the object at any level; with the
opt-out, 57 `cmov`s (three per function) and 82 shifts by CL. Whole object:
935 / 751 / 751 / 751 instructions at O0-O3 folded, 1218 / 1006 / 1001 /
1010 general. Each function alone at O0 (prologue and epilogue included):

| Function | folded | general |
| --- | ---: | ---: |
| `shl`/`lshr`/`ashr` by 0 | 14 | 37 / 37 / 41 |
| by 1, by 63 | 22 | 37 / 37 / 41 |
| `shl` by 64 / `lshr` by 64 / `ashr` by 64 | 15 / 11 / 17 | 37 / 37 / 41 |
| `shl`, `lshr` by 65, 127 | 17 | 37 |
| `ashr` by 65, 127 | 18 | 41 |
| `(x >> 64) as u64` | 10 | 36 |

Evidence class: a native differential (tests), not a proof. No timing was
taken: the run-time effect is fewer instructions and no `cmov` dependency
chain, but no benchmark row is claimed.

The proof-required AOT compile of `x86_source_bound_body` (codegen e2e) now
also carries `u128_high_limb`, `u128_shr_1`, `i128_sar_65` and
`u128_shl_127`; on both `x86_64-apple-darwin` and `x86_64-unknown-linux-gnu`
every one is promoted with a Formal replayed body theorem as its export
payload (`slice_one_to_ten_functions_promote_with_replayed_body_theorems`).

## Which `core` functions change bytes

No census was run (the owner runs one after slice 23). The proxy is
`e2e_x86_64_i128_const_shift::census_proxy_lists_functions_with_a_folded_
i128_shift` (ignored; `TCG_I128_CONST_SHIFT_CENSUS_DIR`): it reads census-s22's
trust-ir dump of Darwin `core` (`~/tcg-scratch/runs/core-ir-s22`, 44 modules,
the census's own 3457 functions), lowers each module as the x86-64 Mach-O
compile lowers it (`ObjectSymbolPolicy::X86_64_MACHO_MODULE`, `Permit`), and
selects every function twice, with the fold on and off. A function whose
pre-RA rows differ is one whose bytes the fold changes; each folded shift
removes one general-path shift (three `cmov`s). Exact at selection, which is
every row the body theorem reads; register allocation and encoding follow.

**17 functions change, one folded shift each; none fails selection; all 17
certify on census-s22 today** (`replay=Valid` or stated in parts, none a
failed root), so these are the census rows to watch:

| Function (`core::`) | Pre-RA rows (general -> folded) | census-s22 |
| --- | --- | --- |
| `fmt::num::exp_u128` | 3254 -> 3233 | 15 parts |
| `num::<impl u128>::overflowing_pow` | 670 -> 647 | 3 parts |
| `num::<impl u128>::checked_pow` | 528 -> 505 | 3 parts |
| `fmt::num::<impl Binary/Octal/LowerHex/UpperHex for u128>::fmt` (4) | 346 -> 325 each | Valid (320 rows) |
| `fmt::num::div_rem_1e16` | 236 -> 215 | Valid (222 rows; OD-204's root) |
| `intrinsics::fallback::<u64 as CarryingMulAdd>::carrying_mul_add` | 205 -> 182 | Valid |
| `num::bignum::<u64 as FullOps>::full_div_rem` | 184 -> 161 | Valid |
| `num::dec2flt::lemire::full_multiplication` | 143 -> 120 | Valid |
| `intrinsics::fallback::wide_mul_u128::from_low_high` | 109 -> 86 | Valid |
| `num::nonzero::NonZero<u128>::leading_zeros` | 95 -> 72 | Valid |
| `intrinsics::fallback::wide_mul_u128::to_low_high` | 91 -> 68 | Valid |
| `num::<impl u64>::carrying_mul_add` | 77 -> 54 | Valid |
| `num::<impl u128>::is_power_of_two` | 43 -> 20 | Valid |
| `num::<impl u128>::count_ones` | 39 -> 16 | Valid |

The proxy also states each changed function's body theorem on both
selections, without a solver (`source_bound_x86_body`): **all 17 build a
theorem with the fold, as without it (0 lost)**, each with 21-23 fewer bound
rows (the bound-row counts without the fold equal census-s22's trace, 320 for
the four radix `fmt`s, 222 for `div_rem_1e16` and so on, which checks the
proxy's selection against the census's). One changes shape:
`u128::checked_pow` (477 bound rows in 3 parts) now fits one query (454 rows,
no parts); `u128::overflowing_pow` stays in 3 parts and `exp_u128` in 15.
Whether each still certifies on AY 13556 within the deadline was not
replayed here; after the merge with slice 23 it was, and all 17 certify by
the census's route (the last section).

The owner's census decides whether each still replays within the deadline:
`div_rem_1e16` (OD-204's root, 12.4 s offline on slice 22), the two `pow`s
and `checked_pow`'s move from parts to one query are the rows to watch.
Shifts whose count reaches the shift through a run-time value (a masked
variable amount) keep the general path and are not in this list; the
selector folds only a count that is an `Iconst` or `Iconst128` of the
function.

## Goldens that move

`TCG_X86_BODY_SNAPSHOT_WRITE` re-rendered every x86 body golden; two files
moved, each theorem smaller:

| Golden | Theorem | Bytes | Requalified (AY 13556 + Clean 5f09e36c) |
| --- | --- | --- | --- |
| `slice11_snapshots.smt2` | `ShrU128By64` | 707 -> 514 | Verified, 0.27 s |
| | `ShlU128By3` | 701 -> 577 | Verified, 0.49 s |
| `slice20_snapshots.smt2` | `U128RadixLoop` | 1585 -> 1585 (respelled) | Verified, 0.44 s |
| | `U128LiveAcrossCut` | 3137 -> 2384 | Verified, 3.47 s (whole and part 1) |
| | `U128CutParam` | 3710 -> 2964 | Verified, 0.12 s |

`SarI128By100` and `U128ShiftLoop` re-render byte for byte: the walk's exact
constant folding had already reduced the general path's CL/CMOV rows for
those constants to the folded rows' terms. Slice 11's two shift refutations
follow the folded rows (`ShrU128By64/low-half-moved`, in place of the CL
funnel's spill count off by one; `SarI128By100/logical`, the fill `sar 63`
made `shr 63`). Requalification, one test per process: slice 11's replay
(every fixture as recorded, `MulU128` still its recorded Timeout gap; 26
refutations refuted) and credit lanes; slice 20's replay, credit and
mis-model lanes; all pass.

**Custody.** `select` (the verify tests' driver) keeps the fold unless
`with_i128_const_shift_fold(false)`; the slice-18, slice-19 and slice-22
custody tests render history with it off, and every earlier digest they pin
(`PRE_LIMB_DIGESTS`, `PRE_CATNF_DIGESTS`, `SLICE18_DIGESTS`, the legacy
digests) still reproduces byte for byte, so the fold-off selector is the
parent's.

## Gates

On the branch's code head (`3331ee136`; every later commit touches only the
ignored census-proxy test or these records), each build and test through
`build-slot`, `--no-fail-fast` where it applies:

| Gate | Result |
| --- | --- |
| `trust-cg-lower --lib` | 2119 passed, 0 failed |
| x86 body suite (`trust-cg-verify --lib x86_source_bound_body::tests::`, all but the tool-gated qualification, credit and migration-pair lanes) | 409 passed, 0 failed, 19 ignored (the fixture printers) |
| tool-gated lanes the fold touches, one per process (on the code before the format commit; formatting only since) | `i128_const_shift_qualification` (replay, credit), `slice11_qualification` (replay, credit), `slice20_qualification` (replay, credit, mis-models): all pass |
| codegen `--test x86_source_bound_body` (AY 13556 + Clean 5f09e36c found, not skipped) | 5 passed, 0 failed; the four new constant-shift functions promoted Formal on both triples |
| codegen `--test must_refuse_corpus` | 5 passed, 0 failed |
| codegen e2e touching 128-bit values: `e2e_x86_64_i128_const_shift`, `e2e_x86_64_i128_div`, `e2e_x86_64_differential`, `e2e_x86_64_triple_oracle`, `e2e_x86_64_checked_arith`, `e2e_x86_64_internal_multi_result` | `i128_const_shift` 2 passed (1 ignored: the census proxy); `i128_div` 4; `differential` 17; `triple_oracle` 9; `checked_arith` 6; `internal_multi_result` 11 passed, 1 failed (below) |
| `check_fmt.sh` (managed 6808 targo) | OK |
| `check_documentation.py --check` | OK |
| `full_test_matrix_hosts.py --check` | OK (the new suite registered as x86-64 execution; its census proxy and the new fixture printer registered as ignored) |

**Failing before and after, unrelated (the same verdicts with
`TCG_NO_X86_I128_CONST_SHIFT=1`, which selects the parent's rows):**
`e2e_x86_64_internal_multi_result::jit_internal_linkage_multi_results_
execute_exactly` (the JIT's proof promotion refuses `produce_int3`, which has
no shift: `MovRR` has statistical evidence only, this host's portable
certificate set being disabled, `drat-trim` hash `beb09303…` not in
`manifest.v1`); `e2e_x86_64_i128_stack_abi::sysv_stack_i128_crosses_c_abi_
in_both_directions` (trust-ir validation, `TargetInfoRequired`, before any
lowering; recorded as pre-existing in the decision record); all 7 tests of
`e2e_x86_64_mixed_width_shift` (trust-ir validation, `BinOpTypeMismatch` on a
mixed-width shift's operands, before any lowering).

## Merged with origin/main `e74f215c6` (2026-11-02)

Branch head `bd2bbd3b9` merged with origin/main `e74f215c6`: slice 23
(OD-205 arithmetic congruence pairing, OD-206 generalization over
arithmetic leaves, with the pairing record every consumer re-derives),
OD-210/211, OD-216 to OD-219, the unnamed-module path fix (OD-210
amended), OD-223 (Clean's own checker deadline, negative memo v6) and the
trust-ir pin move to `f4683868` (AY `7ed2ea1da`). Merge commit
`23565718e`. main's AY manifest carries `[trust] backstop`, which the
`x86-stage1-ay13556` overlay's targo refuses, so every build here uses the
`x86-stage1-ay13556-t011` overlay's targo (the same stage-1 trustc
`d7f143f3b`; `~/tcg-scratch/trust-t011/README.md`), `targo --unverified`,
`nice -n 19`, `-j2`, through `build-slot`. Replayer pair: that overlay's
`bin/ay` (AY 13556, sha256 `55d348f4…`) and `bin/clean` (Clean 5f09e36c,
`949365b6…`), byte-identical to the `x86-stage1-ay13556` overlay's. The
scripts are in [`merge/`](merge/), the payloads in
[PAYLOADS.md](PAYLOADS.md).

### Conflicts

Four files, all textual; no golden conflicted (each lane moved other
files):

| File | Resolution |
| --- | --- |
| `x86_source_bound_body_tests.rs` | both module groups kept: slice 23's (`slice23`, `slice23_qualification`), then OD-215's (`i128_const_shift`, its qualification twin) |
| `scripts/full_test_matrix_hosts.py` | both lanes' fixture printers in `IGNORED_TESTS` |
| `CHANGELOG.md` | both entries; OD-215's first (it lands after slice 23) |
| `docs/decision-record.md` | OD-205 and OD-206, then OD-215, after OD-204 |

The auto-merged custody tests compose: slices 18, 19 and 22 render history
with the fold off (this lane) and, where slice 23 needs it, without the
pairing (main). **OD numbers:** no number is duplicated by the merge
(OD-203 to OD-206, OD-210, OD-211 and OD-215 to OD-223 one heading each);
the duplicate headings OD-58, OD-145, OD-146 and OD-155 are on main and on
the merge base alike, not this lane's.

### Goldens

Every x86 body golden was re-rendered from the merged code
(`TCG_X86_BODY_SNAPSHOT_WRITE=1`, `merge/golden_write.sh`): **all 20 files
re-render byte for byte as merged**, every pinned digest unchanged. So no
theorem moved at the merge, and each golden equals one parent's bytes:

| Golden | against main | against this branch |
| --- | --- | --- |
| `slice11_snapshots.smt2` (`ShrU128By64`, `ShlU128By3`) | the fold's move | equal |
| `slice20_snapshots.smt2` (`U128RadixLoop`, `U128LiveAcrossCut`, `U128CutParam`) | the fold's move | equal |
| `i128_const_shift_snapshots.smt2` | new (this lane) | equal |
| `snapshots.smt2` (`Mul`, `MulU32`), `slice10_snapshots.smt2` (`ShrU64`, `SarI32`), `slice14_snapshots.smt2` (`DivOnOnePath`) | equal | slice 23's move |
| `slice23_snapshots.smt2` | equal | new (slice 23) |
| the other 13 | equal | equal |

**Review against main** (`merge/review_m1.py`, on slice 23's `review23.py`,
the slice-18 design's `smtq.py` evaluator and z3 4.15.4): the 5 theorems the
fold moved, each against main's version: 256 seeded inputs over the union of
free inputs, **0 claim mismatches, no false claim on either side, every
source-side name equal**; z3: **the new theorem Valid (unsat), the old one
Valid, the two claims equivalent (unsat), 5 of 5**. Slice 23's own review
(every name both theorems define equal) passes 4 of 5; on
`U128LiveAcrossCut` it differs only at the machine names `m7`, `m9`, `m10`,
which name other rows once the ladder's rows are gone (main's `m7` is the
ladder's `cmov` select, the merged `m7` the constant 1): a selector change
renumbers the machine side, so its review is the claims and the replay, not
the names. The new theorems replay Verified in their lanes (below).

**Review against this branch** (slice 23's `review23.py` unchanged): the 5
theorems slice 23 moved, **0 mismatches, 5 of 5 unsat**, which reproduces
slice 23's own review (§5 of its report).

### Slice 23 and the fold on the whole core

Slice 23's pairing keys are `shl`/`shr`/`sar r, cl` at 32 and 64 bits
paired with a source shift of the same key; the general path's CL rows
serve a 128-bit source shift (no 32- or 64-bit key), and the fold's rows
are immediate shifts, which are no key. So neither side of the fold can
pair, and the measurement confirms it.

Slice 23's whole-core probe (`probe/run_probe_all.sh`, with the review's
pairing re-derivation, `merge/x86_body_probe.pairing.diff`) built from the
merged tree (`merge/build_probe.sh`) over `runs/core-ir-s23` (3,457
functions; 4,012 query files on main, which slice 23's report counts as
4,013 with the index, and 4,010 with the fold, `checked_pow`'s 3 parts being
one query), compared function by function with the probe of
main without the fold (`s23-fix/all/w5`, slice 23's final head
`33cb58a2b`, whose code is main's; `merge/cmp_probe.py`):

| Run | functions whose selection changes (cf.tsv) | whose theorem bytes change | paired owners (records re-derive / refused) |
| --- | ---: | ---: | --- |
| merged, fold off (`TCG_NO_X86_I128_CONST_SHIFT=1`) | 0 (`cf.tsv` identical) | 0 (`diff -r` of every query empty) | 30 / 0, identical to main's |
| merged, fold on | **17**, exactly the census proxy's 17 | **11**, all among the 17 | 30 / 0, identical to main's |

- The 17 are the census proxy's list, each with 21-23 fewer bound rows.
  None is a paired owner; the 30 paired owners and their records (stem,
  paired rows) are identical with the fold on, off and on main: **no
  pairing appears or disappears**.
- 11 theorems change bytes; 6 keep them byte for byte (`NonZero<u128>::
  leading_zeros`, `u128::is_power_of_two`, `lemire::full_multiplication`,
  `wide_mul_u128::to_low_high` and `from_low_high`, the `u64`
  `CarryingMulAdd` fallback): the walk's exact constant folding had already
  reduced their ladder to the folded rows' terms, as for `SarI128By100`.
  No other function's theorem moves.
- **`u64::overflowing_pow` does not change.** The fold changes
  `u128::overflowing_pow` (`cgu.0.1738`, `numo15overflowing_pow`), not
  slice 23's promoted root `u64::overflowing_pow` (`cgu.0.1709`,
  `numy15overflowing_pow`), whose 21 queries (theorem, generalization,
  claims and their generalizations) are byte for byte slice 23's final
  stage (`s23-run/stage_p4/q`), with the fold on and off. The other two
  slice-23 roots (`align_offset::<u8>`, `wide_mul_u128::scalar_mul`) do not
  change either. All three were replayed anyway (below).

### The replays

The probe with slice 22's claim split and slice 23's generalization writer
(`probe/run_probe.sh`, `S22_CLAIMS=1 S23_GENERAL=1`) over the 17 and the
three slice-23 roots, with the fold (`stage/m1`) and without it
(`stage/m1off`, = main); every query replayed one-shot on the pair above
(`ay -smt2 Q --strict-proofs --proof P --proof-format alethe`, then `clean
cert verify-external`), AY 30 s, Clean 180 s (OD-223's deadline), one
solver at a time (`merge/measure_m1.py`, `merge/replay_all_m1.py`, each
function one `build-slot` hold), 1-minute load 3.6-5.5.

**Every route the census uses, merged tree** (351 queries: each unit exact,
whole or part; its generalization; each claim exact and generalized; a
paired theorem's arbiter): 337 certify; the other 14 are a timeout,
`memout`, AY's self-rejection or a satisfiable generalization (no verdict,
OD-200), **never an exact refutation**. Among the 17 fold functions 271 of
276 certify; the 5 others are `u128::overflowing_pow`'s exact parts 2 and
3 (AY `memout`, as on main) and the fallback `carrying_mul_add`'s exact
claims 1-3 (timeouts on main's unchanged bytes; their generalizations
certify).

**`u128::overflowing_pow`** (602 bound rows, 3 parts, 26 queries) certifies
wherever a route covers it, as on main: the claims route covers all three
parts, the generalization route parts 2 and 3 (part 1 has no arithmetic node
to generalize), the exact route part 1 only. Part 1 exact 0.12 s; parts 2
and 3 exact AY `memout` at 13.2 and 12.4 s (main: 12.8 and 12.1 s, the same
outcome), their generalizations certify in **1.64 and 2.11 s** (main 1.70
and 2.16 s); every claim of every part certifies exact (19 claims, max 11.1
s, part 2 claim 7; part 3 claim 9 10.6 s), and those two claims'
generalizations certify in 0.76 and 0.85 s. Production route: part 1 exact,
parts 2 and 3 generalized, as on main. **`u64::overflowing_pow`** (unchanged
bytes): exact AY self-rejection (3.7 s), generalization **0.86 s** (slice
23: 0.76 s), claim 8 timeout exact and 0.17 s generalized, claims 9, 14 and
15 exact 5.9, 10.5 and 3.1 s: slice 23's record.

The production route (unit exact; then its generalization; then claim by
claim, OD-197 and OD-206) on each function, merged and main (AY s; a part
list is per part):

| Function (`core::`) | bound rows (main -> merged) | theorem (main -> merged) | route, merged | route, main |
| --- | --- | --- | --- | --- |
| `fmt::num::exp_u128` | 2980 -> 2959 | 15 parts, 50,205 -> 51,355 bytes | 15 parts exact, max 3.59 s (part 4) | 15 parts exact, max 3.54 s |
| `u128::overflowing_pow` | 625 -> 602 | 3 parts, 11,525 -> 11,521 bytes | part 1 exact 0.12; parts 2, 3 generalized 1.64, 2.11 | 0.12; generalized 1.70, 2.16 |
| `u128::checked_pow` | 477 -> 454 | 3 parts -> **one query** (14,379 -> 13,398 bytes) | whole exact 2.20 | parts exact 0.13, 0.70, 0.70 |
| `Binary`/`Octal`/`LowerHex`/`UpperHex` `fmt` for `u128` | 320 -> 299 each | respelled, same length | whole exact 0.64-0.65 | 0.65-0.75 |
| `fmt::num::div_rem_1e16` (OD-204's root) | 222 -> 201 | respelled, 4,543 bytes | whole exact 14.34 | 14.36 |
| `u64::carrying_mul_add` | 75 -> 52 | respelled, 1,032 bytes | whole exact 5.02 | 5.05 |
| `u128::count_ones` | 37 -> 14 | 16,341 -> 14,948 bytes | whole exact 5.54 | 10.90 |
| `bignum::<u64 as FullOps>::full_div_rem` | 171 -> 148 | respelled, 1,292 bytes | whole exact 0.23 | 0.23 |
| `<u64 as CarryingMulAdd>::carrying_mul_add` (fallback) | 193 -> 170 | byte for byte | whole exact 12.94 | 12.94 |
| `NonZero<u128>::leading_zeros` | 91 -> 68 | byte for byte | whole exact 1.54 | 1.54 |
| `lemire::full_multiplication` | 135 -> 112 | byte for byte | whole exact 0.38 | 0.38 |
| `wide_mul_u128::from_low_high` | 103 -> 80 | byte for byte | whole exact 0.12 | 0.12 |
| `wide_mul_u128::to_low_high` | 87 -> 64 | byte for byte | whole exact 0.07 | 0.07 |
| `u128::is_power_of_two` | 41 -> 18 | byte for byte | whole exact 0.28 | 0.28 |
| `u64::overflowing_pow` (slice 23 root) | 309 | byte for byte | generalized 0.86 | 0.86 |
| `ptr::align_offset::<u8>` (slice 23 root) | 136 | byte for byte | whole exact (paired) 4.37, Clean 7.92 | the same |
| `wide_mul_u128::scalar_mul` (slice 23 root) | 323 | byte for byte | generalized 4.54 | 4.54 |

**All 20 close on the production route, merged and main** (20 of 20 each,
`merge/replay` tables in PAYLOADS); no root opens, none needs a route it did
not need on main. Main's own census of slice 23's head (`census-s23-f2a0`)
has every one of the 20 `Valid`. Evidence class: offline replays of the
real builder's bytes on the qualification pair, the census's route; the
owner's census of the landed head is the measurement of record.

### Gates on the merged tree

On the merge's code (`23565718e`; the later commits touch only this
report, its `merge/` scripts, PAYLOADS.md and the decision record), through
`merge/chain_gates.sh`: each build and test through `build-slot`,
`--no-fail-fast` where it applies, the tool-gated lanes one test per process
on the pair above (`merge/qualify.sh`).

| Gate | Result |
| --- | --- |
| the solver-free x86 body suite (`x86_source_bound_body::tests::`, all but the tool-gated qualification, credit and migration-pair lanes) | **469 passed, 0 failed, 21 ignored** (the fixture printers; main: 461 and 20, this lane before the merge: 409 and 19) |
| the fold's lanes: replay, credit | pass: 19 fixtures `Verified` (0.09-0.54 s), 51 wrong lowerings refuted with AY counterexamples (0.08-0.09 s); every covered row credited |
| slice 11 (replay, credit), whose golden the fold moved | pass: `ShrU128By64` 0.32 s, `ShlU128By3` 0.63 s, `SarI128By100` 0.09 s, `MulU128` its recorded `Timeout` gap; 26 refutations refuted |
| slice 20 (replay, mis-models, credit), whose golden the fold moved | pass: `U128RadixLoop` 0.49 s, `U128LiveAcrossCut` 3.7 s (whole and part 1), `U128CutParam` 0.14 s |
| slice 23 (body theorems, generalizations, wrong lowerings, credit) | pass: 9 fixtures `Verified` and its 4 recorded gaps (`SremPaired`, `U64OverflowingPowLeaf`, `ScalarMulLeaf`, `U8CarryingMulAdd`) as recorded; 3 generalizations certify, u8 `carrying_mul_add`'s satisfiable (no verdict); 11 wrong lowerings refuted |
| slices 1 (the canonical credit lane), 10 and 14 (credit), whose goldens slice 23 moved (not moved again) | pass |
| `trust-cg-lower --lib` | **2119 passed, 0 failed** |
| codegen `--test x86_source_bound_body --test must_refuse_corpus --test e2e_x86_64_i128_const_shift --test e2e_x86_64_i128_div --test e2e_x86_64_differential --test e2e_x86_64_triple_oracle --test e2e_x86_64_internal_multi_result` | **all pass**: 11, 5, 2 (1 ignored: the census proxy), 4, 17, 9 and 13 passed, 0 failed. `x86_source_bound_body` re-run with `--nocapture`: replays on the overlay's AY 13556 (`toolchain-pinned-ay`), not skipped. `internal_multi_result`'s JIT failure recorded above is gone (main's OD-219) |
| the census proxy (ignored; `TCG_I128_CONST_SHIFT_CENSUS_DIR=runs/core-ir-s23`) on the merged code | the same 17 functions as on census-s22's dump, 0 theorems lost, 0 selection refusals |
| `TRUST_TARGO=<6808 targo> scripts/check_fmt.sh` | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK (from PATH and with `TRUST_TARGO` naming the 6808 targo) |
