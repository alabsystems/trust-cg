# Darwin x86-64 — the division-free 128-bit checked multiply (OD-224), 2026-11-02

The adapter computed the flag of a 128-bit checked multiply (`Inst::Overflow
{ MulOverflow, U128 | I128 }`) by dividing the low product by an operand. On
x86-64 that division is a call of `__udivti3` / `__divti3`, and 11 roots of
the Darwin `core` proof census certified only through ruling OD-202's routine
contract for it. Ruling OD-224 (`docs/decision-record.md`) replaces the flag
on x86-64 with LLVM's `ExpandIntRes_XMULO(UMULO)` limb check, following the
design in `~/tcg-scratch/i128-mulo-design/README.md`, with two departures
that the real bytes forced (section 3). AArch64 keeps the division form byte
for byte.

Host: the shared x86_64 Mac (Darwin 22.6, macOS 13.7.8). Every build and
test ran through `build-slot` and `scripts/trust_cargo.sh` with the overlay
`x86-stage1-ay13556-t011` (`targo --unverified`, `nice -n 19`, `-j2`). No
build carries a proof claim. Replayer pair: AY build 13556 with Clean
5f09e36c (the t011 overlay's `bin/{ay,clean}`), one test per process.
Branch `feat/x86-i128-mulo-divfree` from origin/main `e74f215c6`, merged with
origin/main `6607d0f6b` (OD-215's constant-shift fold) on 2026-11-03.
**Census:** the Darwin x86-64 `core` proof census (O0, AY build 13556 with Clean
5f09e36c) of `682862195` (the lane's code head; `d41e2c62b` adds only the z3
lemmas) has 20 failed roots, the same as `6607d0f6b`'s: `census_compare.py`
gives 0 promoted, 0 newly failing, 0 named mismatches, 0 refuted bodies, and the
two `failed_roots.jsonl` are byte-identical (sha `c955ebdd…`); all 20 are
OD-115's no-observable bodies, so the 11 changed functions still certify on the
census itself (bridge sha `f4b4305b…`, 1720 s wall, the local engineering targo).
Before the census, the measurement on real bytes was slice 23's whole-core probe
plus the census's replay route, offline (section 5). Payload paths below (`logs/`, `all/`, `stage/`, `replay/`,
`icount/`, `exp/`, `qual_*/`) are under `~/tcg-scratch/mulo-run/`;
[PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.

## Soundness notes first

- **No new trust.** The limb check is exact, and every operation in it is a
  LIR op that the x86-64 body theorem already admits with its exact
  semantics. The 11 roots' theorems no longer contain a call, so their credit
  no longer rests on OD-202's routine contract. AArch64 keeps the division
  form, and OD-202 still covers it.
- **One body-theorem change, an identity.** A `mul` row now reads its CF and
  OF from the name it defines for the product's upper half, not from the
  product term. The name is defined as that term, so the two are equal.
  OD-205's pairing re-spells that name as the source's widening product, so
  the flag now follows the re-spelling. Checked on the whole `core` dump:
  in the division form, the tree with this change states every one of main's
  4,012 probe queries byte for byte.
  - The pre-slice-18 legacy spelling does not inline the name, and its
    custody test showed that. History is now rendered with the term, under the
    test-only `with_mul_flag_of_the_term`.
- **A seam that production never sets.**
  `trust_cg_lower::with_x86_i128_mulo_division_form` brings back the division
  form on x86-64, on its own thread, for the length of one closure.
  - Uses: golden custody, the fails-before controls, and the A/B probe
    (`MULO_DIVISION_FORM=1`, a probe-local toggle that is never committed).
  - Both forms are exact, so neither setting weakens a check.
- **Credit moves from exact replays to OD-206 generalizations.** For a
  full-operand limb check, AY 13556 computes UNSAT on the exact theorem and
  then rejects its own proof in its strict certification. This is the class
  of slice 23's `U64OverflowingPowLeaf`.
  - Generalization: every arithmetic node becomes a fresh input. That
    replay certifies, and it is a strengthening, so its credit is sound.
  - Affected: 6 of the 11 changed functions now close by generalization where
    main closed them exactly. No exact query on any route was refuted.
- **L04-P10 (the adapter step) stays statistical.** No sampled check is
  called a proof (section 4.4).
- **Two typos in the design README** (its own tables are correct).
  - §3.4 lists the no-zero-guard counterexample as `a = 2^71, b = 0`. That
    pair is no counterexample; the replayed z3 model in
    `z3_mutants_w128.jsonl` is `a = 2^127`.
  - It lists the `CheckedSmul` swap's counterexample as `2^71 - 1`. That pair
    is no counterexample either; the replayed one is `2^127 - 1`.
  - The tests use the replayed values.

## 1. Target selection

`translate_overflow` already knows its ISA: `guard_carrier_arch`, which
`guard_carrier_arch_for_target` sets from the compile target on every
production translation path (AOT, JIT, census, bridge). The division-free
forms are chosen when it is `X86_64` and the seam is off.

- **Default.** The default is `AArch64`, so a caller that names no target
  keeps the division form.
- **RISC-V** keeps the division form too; its selector refuses every I128 op.
- **Pinned.** `adapter_i128_mulo_tests::both_expansions_are_pinned_op_for_op`
  pins AArch64's expansion op for op, as it was before this change.
- **Value.** `the_expansion_is_chosen_per_target` checks that the value is the
  same `Imul a, b` on every target.

## 2. The expansions

The value is `r = Imul a, b` on every target, the first instruction as
before. `x = x1:x0` means 64-bit limbs; `hi` and `lo` take a 128-bit
product's halves.

| Form | Flag | LIR instructions |
| --- | --- | ---: |
| u128, design's op list exactly | `hi(a1*b0) != 0 \| hi(a0*b1) != 0 \| r1 <u lo(a1*b0) + lo(a0*b1) \| (a1 != 0 & b1 != 0)`; the cross products are `I64` `CheckedUmul`s; the carry is read off `r`'s high limb | 21 |
| u128 by a constant `C` (new) | `x >u floor((2^128 - 1) / C)`; for `C = 0` the limit is `2^128 - 1`; the division happens at translation time | 3 |
| i128 (new spelling) | `core(\|a\|, \|b\|, hi(\|a\|*\|b\| mod 2^128)) \| (((r1 >>a 63) ^ mn) != 0 & r != 0)`; the magnitudes are `I64` mask arithmetic under `ma = a1 >>a 63`, `mb = b1 >>a 63`, `mn = ma ^ mb` | 58 |

Magnitude of `x` under its mask `m` (`push_magnitude_limbs`): low limb
`(x0 ^ m) - m`, high limb `(x1 ^ m) - m - (((x0 | (0 - x0)) >> 63) & m)`. The
same high-limb formula gives `pu1` from `r` and `mn`
(`push_masked_negation_high`).

## 3. Why the design changed, measured on real bytes

First run (the design's expansion, plus the CF fix of the soundness notes):
the census route closed 9 of the 11 changed functions (`stage/new_p2`).

1. **`i128::checked_mul`: not certified.**
   - Exact replay timed out, its generalization was satisfiable, and so were
     its claims.
   - The source has two paths and is stated path by path. OD-205 never pairs
     such a source.
   - The design builds the magnitudes as a select of a 128-bit negation, and
     the two sides spell that differently. The source writes
     `extract(bvsub 0 (concat a1 a0))` with a `B1` select condition. The
     machine writes `sub`/`sbb` and a `setcc` byte with unknown upper bits.
   - So the theorem kept two multipliers over operands spelled apart.
   - The straight-line `i128::overflowing_mul` did certify, through pairing.
   - **Fix:** build the magnitudes as `I64` mask arithmetic. Each operation
     selects to the one row of the same operation, so both sides spell the
     core's `mul` operands alike without pairing.
   - On the second run one spelling still differed: the selector's `neg` row
     is `bvneg`, while the source's `Ineg` is `bvsub 0 x`. So `0 - x0` became
     an `Isub` from zero.
2. **`div_rem_1e16`: not certified.**
   - Its exact theorem timed out, it has no generalization, and its claim 3
     timed out.
   - A product by a constant is no arithmetic node for OD-206, so it has no
     generalization.
   - Claim 3 certifies offline in 69-80 s (`exp/exp1.out`: AY 69.0 s, and
     79.7 s with the machine's commuted add swapped back). The census allows
     30 s.
   - Commuting the add is not the cause.
   - **Fix:** the constant form, the compare with the constant's limit. The
     theorem then certifies whole in 11.4 s.

With both fixes the census route closes all 11 (`stage/new`, section 5).

## 4. Evidence, by class

### 4.1 Exhaustive (scaled analogs only)

`crates/trust-cg-lower/src/adapter_i128_mulo_tests.rs` translates real
trust-ir for each target. It runs the adapter's actual output on a small LIR
interpreter that knows only these expansions' opcodes; any other opcode makes
it panic by name.

- **Scaling.** `I128` becomes `W` bits and `I64` becomes `W/2`. The constants
  64 and 63 become `W/2` and `W/2 - 1`. 128-bit constants scale limb by limb,
  and only 0, 1, all ones and the sign bit; any other refuses
  (`an_unscalable_constant_is_refused`).
- **`W = 8`, 4-bit limbs.** All 65,536 pairs, for both signs, both targets and
  both forms: 0 mismatches.
- **`W = 16`, 8-bit limbs.** All 2^32 pairs of each division-free form, 0
  mismatches: unsigned in 1,368.6 s, signed in 3,800.5 s, on two threads of a
  debug build. Run by
  `the_division_free_expansions_are_exact_on_every_pair_at_sixteen_bits`,
  which is `#[ignore]`d for its cost (`logs/sweep16.log`).
- **Batched evaluator check.** The `W = 16` run uses a batched evaluator. It
  equals the per-pair one on every pair at `W = 8` and on a spread of `W = 16`
  rows.

This is evidence for these widths only. It says nothing about the 128-bit
circuit.

**Mutants.** The design's mutants are applied to the adapter's output. At
`W = 8` each one is refuted, with exactly the mismatch count the design's
independent Python model measured:

| Mutants | Mismatch counts at `W = 8` |
| --- | --- |
| unsigned | 208, 3521, 2324, 2324, 284, 1312, 1292 |
| `t = m1 \| m2` | 0 (equivalent, as the design found) |
| signed | 256, 2246, 30815, 713, 184, 1669 |
| each dispatch swap | 2233 |

At 128 bits each mutant fails at the design's replayed counterexample.

The constant form's identity is checked on every `(x, C)` at 8 bits. Its
adapter output is checked at 128 bits against native `checked_mul` for 55
constants and about 2,000 operands, with `C` on either side.

### 4.2 Statistical at 128 bits

- **Adapter tests.** Both targets' expansions agree with Rust's native
  `checked_mul` on every pair of a 42-value edge set (both signs) and on
  200,000 random operands of every bit length.
- **L04-P10.** Its machine sides agree with native on 20,000 random pairs.

### 4.3 Formal per theorem (AY 13556 with Clean 5f09e36c)

**Fixtures.** 5 OD-224 fixtures and slice 22's 5 checked-multiply shapes, from
the real adapter and selector:

- **Credit route.** Every full-operand limb check certifies by its OD-206
  generalization, 0.2-2.8 s. Its exact theorem gets
  `incomplete self-check-rejected`, which is recorded in
  `KNOWN_UNCERTIFIED_*` with the measured outputs. The production verifier
  credits every covered row, `verifier_credits_every_bound_slice_twenty_two_row_...`.
- **Exact certificates.** `U128CheckedMulSmall` (0.1 s) and the constant form
  (0.5 s) certify exactly.

**Wrong lowerings.** 6, each one edit of the real stream, are refuted with AY
counterexamples:

- the carry dropped;
- the carry compared signed;
- the both-high test dropped;
- a cross-product test dropped;
- `shr` for the sign mask's `sar` (signed/unsigned swapped);
- the constant's limit off by one.

Every other gate of slice 22's and slice 23's lanes is unchanged.

**Codegen lane.** `tests/x86_source_bound_body.rs` promotes the full
`u128::checked_mul` and `i128::overflowing_mul` flags with replayed body
theorems, `I128_MULO`.

### 4.4 The adapter step: L04-P10, statistical

`checked_mul_i128_proofs.rs` adds three x86-64 forms: the limb check, the
magnitudes route, and the constant-limit compare.

- **AArch64's forms stay.** AArch64's two division-identity forms remain,
  because AArch64 still emits them. Restating them as the x86-64 form would
  relabel AArch64's evidence.
- **Controls.** 19 new controls: the design's 13 non-equivalent mutants, the
  2 dispatch swaps, and 4 limit-compare controls.
  - Each is refuted at its directed witness.
  - Where the sampler reaches one, the sampler refutes it too. Which ones it
    reaches was measured and is pinned in `SAMPLING_VISIBLE_LC`.
- **Formal attempt on the repository's own route:**
  - Each obligation, whole: AY times out at 10 s, `L04_P10_FORMAL`.
  - Structured, `L04_P10_STRUCTURED`, on AY plus Clean:

| Lemma | AY + Clean outcome |
| --- | --- |
| Unsigned core lemma, limb products as free inputs under their facts (zero iff a factor is; at most `(2^64-1)^2`) | Verified, 3.1-8.9 s |
| Signed sign reduction, product free | Verified, 0.3-1.4 s |
| Zero-product fact of a 64x64 product | Verified, 70-153 s |
| 64x64 product bound | Timeout, 60 s |
| `Imul` high limb as its limb chain | Timeout, 60 s |

So the flag obligations reduce formally to two multiplier lemmas that AY does
not decide. **L04-P10's class stays STATISTICAL.**

### 4.5 Tests (native)

`crates/trust-cg-codegen/tests/e2e_x86_64_i128_checked_mul.rs` runs
`overflowing_mul`, `checked_mul` and `saturating_mul` of `u128` and `i128`.
They are spelled in trust-ir as rustc lowers them, compiled by trust-cg for
x86-64 at O0-O3, linked and executed.

- **Oracle.** C's `__builtin_mul_overflow` on every pair of 19 unsigned and 20
  signed edge values: 0, 1, -1, MIN, MAX, 2^64, 2^64 - 1, and products just
  under and just over 2^128 and 2^127.
- **Result.** 761 pairs per level, every line equal, at every level. Equal
  with and without the fold (`TCG_NO_X86_I128_CONST_SHIFT=1`).
- **No routine.** Every object calls no 128-bit multiply or division routine:
  no `__udivti3`, `__divti3`, `__umodti3`, `__modti3` or `__muloti4` in
  `nm -u`.

### 4.6 Fails before

- **Fixtures.** The same trust-ir in the division form, through the seam,
  selects `call __udivti3` / `__divti3` on x86-64. The limb form calls nothing
  (`the_division_form_called_the_routine_and_the_limb_check_does_not`, over
  the 5 OD-224 and 5 slice-22 shapes).
- **Native.** The codegen object in the division form has `___udivti3` and
  `___divti3` undefined, links, and computes the same answers
  (`x86_64_the_division_form_called_the_routines_and_the_limb_check_does_not`).
- **Main's census objects** (census-s23-f2a0): 14 call a 128-bit division
  routine. 11 of them are these checked multiplies; the other 3 are
  `full_div_rem`, `exp_u128` and `int_log10::u128_impl`
  (`logs/main_f2a0_ti3_callers.txt`).

### 4.7 Solver-backed: the two departures at full width (z3 only)

**Class: SOLVER-BACKED.** These proofs use z3 4.15.4 in Python and nothing
else.

- **Not replayed.** No AY or Clean replay, no registration, no credit.
- **Hand-composed.** The lemmas are composed by the argument below, not by a
  checker.
- **Undecided stays undecided.** A query z3 does not decide is recorded as
  undecided.
- **Source.** `proofs/od224_z3.py` imports the design's `lir_model.py` and
  `z3_proofs.py` (`design/`).
- **Run.** `nice -n 19` under `ulimit -t 900`, 122.4 s of CPU in all, of which
  119.6 s is the one undecided attempt (`z3/od224_z3.json`).

**The constant form, `x >u limit(C)` with `limit(C) =
u128::MAX.checked_div(C).unwrap_or(u128::MAX)`.** The adapter admits every
canonical trust-ir constant (`mulo_u128_constant`), so every `C` in
`[0, 2^128)` is in scope:

| Lemma | 128 bits | 64 bits |
| --- | --- | --- |
| K0: `C = 0`. `checked_div` returns `None`, so no division is done; the limit is `MAX`; the flag `x >u MAX` is false for every `x`, and so is the exact condition (`x * 0 = 0`). | proved, 0.001 s | proved |
| K1: `C = 1`. The limit is `MAX / 1 = MAX`; the flag is false, which is exact. | proved, 0.001 s | proved |
| K2: `C >= 2`. `x >u L` iff `x * C > MAX`, where `L` is given by its floor bounds `L*C <= MAX < (L+1)*C`. | proved, 0.004 s | proved, 0.64 s |
| K3: `C >= 2`. The same, with `L = MAX div C` (z3's integer division). | proved, 0.005 s | proved |
| K4: `MAX div C` satisfies the floor bounds, so K2 and K3 state one limit. | proved | proved |

The 64-bit row is for completeness only: this path never sees 64 bits. A
64-bit checked multiply is `CheckedUmul`. Only the I128 branch of
`translate_overflow` reaches `mulo_u128_constant`.

What the lemmas do not cover, and how that is covered instead:

- the Rust computation of the limit at translation time, and its split into
  `Iconst128 { lo, hi }`;
- the `Icmp ugt` of the other operand against it, whichever side the constant
  is on.

These are tested, not proved: `a_constant_operand_is_compared_with_its_limit`
(55 constants, `C = 0` and `C = 1` among them, both sides), the 8-bit
exhaustive check here (all 65,536 `(x, C)`, 0 mismatches), and the native
test.

**The signed mask spelling (58 instructions), at 128 bits, lemma by lemma.**
`x = x1:x0` are 64-bit limbs. `m = x1 >>a 63`. `r = a * b mod 2^128`.

| Lemma | Statement | z3 |
| --- | --- | --- |
| S1 | `((x1 ^ m) - m - (((x0 \| (0 - x0)) >> 63) & m)) : ((x0 ^ m) - m) == (x <s 0 ? -x : x)` for every `x` | proved, 0.22 s |
| S1-MIN | the magnitude of `MIN` is `2^127` | proved |
| S1b | `x <s 0 ? -x : x`, read unsigned, is `\|x\|` for every signed `x` and at most `2^127` | proved |
| S2a | `ma`, `mb` are all ones iff negative, else 0; `mn = ma ^ mb` is all ones iff the signs differ | proved |
| S2b | `push_masked_negation_high(r, mn)` is the high limb of `neg ? -r : r` | proved, 0.03 s |
| S3 (4 sign cases) | `a * b = neg ? -N : N` with `N = \|a\| * \|b\|`, and `neg ? -r : r = N mod 2^128` | proved ×4 |
| S4 | the unsigned core: `core(x, y, hi(x*y mod 2^128))` iff `x * y >= 2^128` (integer encoding; the shipped op list is the design's) | proved, 0.69 s |
| S5 | `((r1 >>a 63) ^ mn) != 0` iff `(r <s 0) xor neg`; `(r0 \| r1) != 0` iff `r != 0` | proved |
| S6 | `N` free in `[0, 2^254]`: `(N >= 2^128) \| (r != 0 & (r >=u 2^127) != neg)` iff `neg ? -N : N` is outside `[-2^127, 2^127)` | proved |
| S7 (attempt) | the whole shipped signed flag = trust-ir's, one bit-vector query | **undecided** (120 s) |

The composition, by hand:

1. By S1, S1b and S2a the core's inputs are the limbs of `|a|` and `|b|`.
2. By S2b and S3, `pu1` is the high limb of `N mod 2^128`. So by S4 the core
   yields `N >= 2^128`.
3. By S3, the trust-ir product is `neg ? -N : N`, and `r` is it mod `2^128`.
4. By S5, the sign check is `r != 0 & (r <s 0) != neg`.
5. So by S6 the flag is exactly trust-ir's.

S1-S6 also hold at 64 bits, run for completeness.

**Controls.** Each control is one deliberate defect and must make its query
SAT. All 9 do:

- the limit compared with `>=`;
- the limit plus one;
- `C = 0` without its `MAX`;
- the magnitude without the borrow;
- the sign mask by a logical shift;
- `pu1` without the borrow;
- the sign check's xor as an or;
- the core without its carry;
- the composition without its `r != 0` guard.

The floor bounds of K2 are also satisfiable, so K2 is not vacuous.

**Concrete cross-check.** The script's Python copy of the 58 instructions
(`conc_shipped_smulo`, in the adapter's order) equals trust-ir's flag:

- on every pair at 8 bits (65,536 pairs, 0 mismatches);
- on every pair of a 24-value 128-bit battery (576 pairs, 0 mismatches).

## 5. Real bytes: slice 23's whole-core probe and the census route

**The probe.** The probe (`lane/build_probe.sh`) was built from the lane's
final code and run over every function of a `core` trust-ir dump
(`run_probe_all.sh`), once in each form.

| Comparison | Result |
| --- | --- |
| Division form vs main (`i128sh-m1/all/m1`, main `6607d0f6b` with the fold) | byte for byte, all queries and every `cf.tsv` row |
| Division-free vs division form | 11 functions' theorems change; nothing else |

The 11 changed functions:

- `checked_mul` and `overflowing_mul` of `u128` and `i128`;
- `u128::overflowing_pow`;
- both `from_ascii_radix`;
- `div_rem_1e16`, `full_multiplication`, `wide_mul_u128::scalar_mul` and
  `<u64 as CarryingMulAdd>::carrying_mul_add`.

These are exactly the design's 11 OD-202 roots. Pairing records: 35
re-derive, against 30 in the division form; none is refused.

**Census route** (`lane/measure_mulo.py`, the production route: each unit
exact, then its OD-206 generalization, then claim by claim). Offline,
AY 13556 plus Clean 5f09e36c, 30 s AY and 180 s Clean, one solver at a time.
**All 11 certify in both forms.** AY and Clean seconds are what the route
spent (`route_cost.txt`):

| Function | Main (division form) | OD-224 | AY s main → OD-224 |
| --- | --- | --- | ---: |
| `carrying_mul_add` (u64) | whole, exact | whole, exact | 9.0 → 6.0 |
| `div_rem_1e16` | whole, exact | whole, exact (the constant form) | 13.6 → 11.4 |
| `u128::from_ascii_radix` | 9 parts exact | 7 exact, parts 6 and 8 generalized | 5.4 → 6.4 |
| `i128::from_ascii_radix` | 9 parts exact | 7 exact, parts 6 and 8 generalized | 5.5 → 6.7 |
| `i128::checked_mul` | exact | generalized | 1.0 → 2.2 |
| `i128::overflowing_mul` | exact | generalized | 0.8 → 2.2 |
| `u128::checked_mul` | exact | generalized | 0.7 → 5.5 |
| `u128::overflowing_pow` | 3 parts (2 generalized) | 4 parts (2 generalized) | 27.6 → 11.6 |
| `u128::overflowing_mul` | exact | generalized | 0.6 → 1.2 |
| `wide_mul_u128::scalar_mul` | generalized | generalized | 34.1 → 24.8 |
| `full_multiplication` | exact | exact | 0.3 → 2.1 |

**Every route.** Each unit exact and generalized, each OD-197 claim exact and
generalized, and each arbiter (`chain_replay.txt`), over 262 queries:

- 215 certified;
- 44 with no verdict;
- 3 timeouts;
- no exact query refuted, and no generalization satisfiable.

**Fresh dump.** A fresh `core` dump from this branch's bridge: see section 7.

## 6. Instruction counts (static, decoded by Xcode's `objdump`)

Decoded from the native test's module (`lane/count_insns.py` over
`icount/objs_{fold,nofold}`). Each row is one whole function: the multiply,
its flag, and the store or the select that `overflowing_mul`, `checked_mul`
and `saturating_mul` add.

The division form's count excludes its callee: `__udivti3` / `__divti3` from
compiler-rt, at least one `div` plus fix-up. The fold (OD-215) does not change
the division form, which has no constant shift.

| Function | Division form, + 1 call | Limb, fold | Limb, no fold |
| --- | ---: | ---: | ---: |
| `u128 overflowing_mul` O0 / O1-O3 | 111 / 89 | 99 / 78 | 167 / 193-203 |
| `u128 checked_mul` O0 / O1-O3 | 131 / 114 | 123 / 105 | 183 / 169-223 |
| `u128 saturating_mul` O0 / O1-O3 | 139 / 131-140 | 143 / 115-124 | 181-208 |
| `i128 overflowing_mul` O0 / O1-O3 | 139 / 158 | 226 / 162 | 231-278 |
| `i128 checked_mul` O0 / O1-O3 | 162 / 124 | 186 / 192 | 225-301 |
| `i128 saturating_mul` O0 / O1-O3 | 159 / 139-143 | 218 / 183-187 | 255-296 |

Multiplies: the limb form has 5 (the value's 3 plus two `CheckedUmul`), the
division form 3. The fold removes 33-125 instructions from every limb form:
the CL/CMOV shift ladders of 3 high-limb extractions (u128) or of 5 to 7
(i128).

No timing was measured: these are static counts, not a runtime claim.

## 7. Fresh dump from this branch's bridge

The release bridge was built from the lane at `8b6435da6`
(`~/tcg-scratch/build_bridge.t011.sh`, 1 h 42 min including the queue for the
slot). Its dylib's sha256 begins `af313e1a`.

- **Dump.** A fresh `core` trust-ir dump with it (`lane/dump_core_ir.sh`, on the
  t011 root overlay's trustc): 88 files.
- **Same trust-ir.** The 44 `.trust_irbin` modules are byte for byte
  census-s23's (`runs/core-ir-s23`). The 44 JSON sidecars differ only by a
  `"link_unit_definitions": []` field that main added since.
- **Same theorems.** Slice 23's whole-core probe over the fresh dump states
  every query and every `cf.tsv` row byte for byte as over `core-ir-s23`, in
  both forms (`logs/chain_bridge.txt`).
- **So** the census-route replays of section 5 are this bridge's bytes.

## 8. Gates

On the lane merged with origin/main `6d4143878` (head `07c38c1a3`; that merge
brought the trust-ir pin move to `6d2e3811`), each `--no-fail-fast`, one test
per process for the tool-gated lanes (`logs/chain_gates.txt`):

| Gate | Result |
| --- | --- |
| `trust-cg-lower --lib` | 2129 passed, 0 failed, 1 ignored (the 16-bit sweep, run separately) |
| x86 body suite (`x86_source_bound_body::tests::`, solver-free) | 473 passed, 0 failed, 22 ignored |
| L04-P10 (`checked_mul_i128_proofs::tests::`, solver-free) | 11 passed |
| Tool-gated lanes on AY 13556 + Clean 5f09e36c | 9 of 9 exit 0: OD-224's three (the theorems and generalizations, the refutations, slice 22's generalizations); slice 22's four (replays, refutations, verifier credit, OD-210's credit); L04-P10's formal attempt and structured attempt |
| `proof_gate_strict` (`checked_mul_i128_corpus_addition_is_exact_live_and_nondegenerate`, the `AUDITED` list) | passed |
| `coverage_gate_tests` (`umulh_row_requires_the_i128_checked_mul_family_credit`) | passed |
| pipeline `backend_expansion_nounwind_callees` | passed (AArch64's table, unchanged) |
| codegen `x86_source_bound_body`, `must_refuse_corpus`, `e2e_x86_64_i128_div`, `e2e_x86_64_checked_arith`, `e2e_x86_64_differential`, `e2e_x86_64_triple_oracle`, `e2e_x86_64_i128_checked_mul` | 11, 5, 4, 6, 17, 9, 2 passed; 0 failed |
| `check_fmt.sh` (6808 targo) | OK |
| `check_documentation.py --check` | OK |
| `full_test_matrix_hosts.py --check` | OK |

The census-route measurement (sections 5 and 7) and the qualification
outcomes quoted in section 4 were taken on the lane before that merge
(`8b6435da6`, base `6607d0f6b`). The merge changes no line of the lane's
code. On the merged code, the whole-core probe over the fresh dump states:

- **Division form:** main's queries byte for byte.
- **Division-free form:** every query and every `cf.tsv` row byte for byte as
  the measured lane's (`p4_new`). So the census-route replays apply to the
  merged head's bytes unchanged.

Probe built from `07c38c1a3` (`logs/chain_probe_p5.txt`).

## Reproduce

- `lane/` holds the lane's scripts as run:
  - builds and jobs: `run.sh`, `job.sh`, `waitjob.sh`, `runbin.sh`,
    `jobbin.sh`;
  - the probe and staging: `build_probe.sh`, `chain_probe.sh`,
    `cmp_probe.py`, `run_stage.sh`;
  - the replays: `measure_mulo.py`, `replay_all.py`, `chain_replay.sh`,
    `route_cost.py`, `table_mulo.py`, plus the census route's `probe_run.py`,
    copied from slice 23's `scripts/`;
  - the offline diagnostics: `exp.py`;
  - the fresh dump: `chain_bridge.sh`, `dump_core_ir.sh`;
  - the gates: `qualify.sh` and `chain_gates.sh`;
  - the counts and payloads: `count_insns.py`, `payloads_mulo.py`.
- `proofs/od224_z3.py` holds the z3 lemmas of section 4.7. Run it with
  `ulimit -t 900; nice -n 19 python3 proofs/od224_z3.py 120 128 64`; it
  prints one JSON object.
- `design/` holds the design's Python model and its sweeps and z3 proofs,
  verbatim from `~/tcg-scratch/i128-mulo-design/`.
- The probe's source is `~/tcg-scratch/mulo-run/probe/x86_body_probe.rs`, never
  committed. It is OD-215's copy plus the `MULO_DIVISION_FORM` toggle.
