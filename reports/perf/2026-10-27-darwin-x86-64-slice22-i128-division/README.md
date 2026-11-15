# Darwin x86-64 `library/core` — slice 22 (the `i128` division class), 2026-10-27

Slice 22 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs` and
`x86_source_bound_body/normal.rs`) targets 14 failed roots of census-s21
(36 failed roots on AY build 13556 with Clean 5f09e36c): 13 `i128`
division roots and the `int_log10::u128_impl` guard root, as designed and
measured in `~/tcg-scratch/s22-design/` (README §1-§6). In 11 of the 14 the
division is the adapter's 128-bit multiply-overflow check (`(a * b) / (a ==
0 ? 1 : a) != b`), so the class travels with the 128-bit product.

| Ruling | Stage | Rule | Design |
| --- | --- | --- | --- |
| OD-202 | 22a | an `I128` division is the call of its runtime routine (`__udivti3`, `__divti3`, `__umodti3`, `__modti3`); the `I128` divide-by-zero guard is slice 14's at 128 bits | §3, §5.1 (the s20 design's 20a) |
| OD-203 | 22b | a 128-bit product is spelled by its 64-bit limbs (`limb`, `addhi0`, `acmul`), and a guarded claim whose guard's double negation was folded keeps its skeleton (`guard`, a measured departure) | §2, §5.2 |
| OD-204 | 22c | a normal form of bit moves (`catnf`) | §2.3, §5.3 (optional; kept) |

Host: the shared x86_64 Mac (4 cores, Darwin 22.6, macOS 13.7.8 22H730,
i7-7920HQ), 1-minute load 1.7-5 during the measurements (each record keeps
its own); every build through `scripts/trust_cargo.sh` with the local
overlay `x86-stage1-ay13556` (`targo --unverified`, `nice -n 19`, `-j2`; no
proof claim about any build). Replayer pair: AY 0.27.0 build 13556 with Clean
5f09e36c (`QUALIFIED_AY`, the overlay's `bin/ay` and `bin/clean`). Branch
`feat/x86-body-slice22` (worktree `~/tcg-scratch/wt-s22`) from main
`3e760392e` (slices 1-21), merged with origin/main `20649afe9` (the trust-ir
pin `73c5a310`; the whole-core probe on either side of the merge states
every function's theorem byte for byte alike). Payloads are out of tree;
[PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.

**Census:**

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-20649afe9-ay13556` (baseline) | `main` `20649afe9` | 13556 | `e12c1dc5…` | 36 | 1510 s |
| `core-x86_64-darwin-O0-proof-slice22-ay13556` | this branch, `b596e62fe` (slice 22 on `20649afe9`) | 13556 | `5673600b…` | **23** | 2257 s |

**13 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
9 refused at an `I128` `Udiv`, 3 at an `Sdiv` and 1 at the `I128`
divide-by-zero guard now replay Valid, as the real builder's bytes predicted
(13 of the 14 targets; `scalar_mul` stays open). Both rows were built by
`census13556.sh`, each bridge in its own tree, with no resource-budget
refusal.

## Soundness notes first

- **New trust (OD-202), stated in the ruling and LIMITATIONS:** that the
  routine the link binds to `__udivti3`/`__divti3`/`__umodti3`/`__modti3`
  (for a Rust program the sysroot's `compiler_builtins`; for a C link the
  platform's compiler-rt, libSystem's here, an OS-version-dependent binding;
  or the program's own External definition — narrowed by OD-210 to a
  definition outside the module under proof, see §8) returns trust-ir's
  128-bit `udiv`/`sdiv`/`urem`/`srem` on trust-ir's defined domain (and,
  OD-211, §8: writes no memory the caller observes, has no effect on the
  world, returns). This is
  **tested, never proved**: §2's native differential (15.6 M checks per
  binding, 0 mismatches, a wrong routine caught) is statistical evidence.
  The argument and result placement, the symbol per opcode and the guard
  are checked by the theorem, not trusted.
- **Two "references" are not independent, flagged:** trust-ir's interpreter
  computes `u128 /`, which compiles to the very `__udivti3` under test, and
  `e2e_x86_64_i128_div` links the same routine on both sides (it is lowering
  evidence only). The selector's `TRUST ASSUMPTION` comment and the e2e
  test's header said otherwise and now say so.
- **Off the defined domain** the two bindings differ (`compiler_builtins`
  makes a zero divisor `unreachable()`, compiler-rt traps; both wrap `MIN /
  -1` to `MIN`, `native/offdomain.c`). Nothing is owed there; the call model
  states no result value, so the off-domain behaviour never enters a theorem
  (`I128SdivMinNegOne` builds and holds), and the adapter's eleven checks
  never reach it.
- **OD-203 and OD-204 add no trust** (identities on every input), but they
  change bytes outside the class. The whole-core replay is the guard: every
  census-certified function whose theorem bytes change still certifies (§3,
  §4). The `guard` step departs from the design's pipeline: the design's
  Python prototype applied no structural check, and on the real bytes
  `checked_mul`'s two theorems failed it (§3).
- **Found on the way, not fixed:** the AY proof step Clean's Carcara
  rejects (`equiv_simplify` of `(= (not false) false)`), written up as an AY
  issue note:
  `reports/2026-10-27-ay-equiv-simplify-negated-constant/`.

## In short

- **Real bytes** (§1): a FRESH `core` dump from census-s21's bridge
  (`s21.dylib`, 87407a8d…), replayed one-shot on the qualification pair at
  the lane's 30 s deadline with OD-197's claim-by-claim route: **22a closes
  5 of the 14 roots, 22b 12, 22c 13** (the design: 5, 12, 13). `scalar_mul`
  stays open (AY bit-blasts a multiplier the claim needs only as an atom,
  the design's §4.3).
- **Whole core** (§3, §4): OD-202 changes no other function; OD-203 and
  OD-204 change 142 census-certified functions' theorems (33 and 112), every
  one still certifying (one, `u128` `__fmt_inner`, claim by claim before and
  after).
- **Goldens:** OD-202 moves none; OD-203 moves 2 theorems (slice 11's
  `MulU128` back to slice 18's spelling by slice 9's rule, slice 14's
  `SremChecked32` now canonically spelled by `guard`); OD-204 moves 30
  theorems and parts of slices 1, 5, 8, 11, 15 and 20. Every one reviewed by
  a 256-input sweep and z3 (unsat), and the spelling without each stage's
  groups re-renders every golden before it byte for byte.
- **Controls:** 17 slice-22 fixtures over real adapter and selector output,
  12 wrong lowerings refuted (7 of the division class, 5 wrong 128-bit
  multiplies), 2 named mismatches, exhaustive sweeps of every new group;
  **16 rule mutants, each failing a control**.
- **Qualification** (§5): every slice's lanes, one test per process on AY
  13556 + Clean (49 runs), pass; the recorded gaps keep their outcomes and
  one joins (slice 22's `U128MulConst`, a 128-bit difference over a product,
  88.8 s at a 300 s budget).

## 1. The 14 roots on the real builder's bytes

**The dump.** `census/dump_core_ir.sh` (slice 18's script on the AY 13556
overlay; it runs AY, as the slice-20 design measured, so it ran alone) over
`runs/s21.dylib` (sha256 `87407a8d…`, the census-s21 bridge, built from
`401db9e46`: main's bridge, the merge `3e760392e` adds only a test fix):
`runs/core-ir-s22`, 88 files, main module sha256 `d5c9163d…` (census-s20's
dump the design read: `99228581…`). All 14 names are in it.

**The probe.** `probe/x86_body_probe.rs` is slice 21's probe with one
addition, an OD-197 claim writer (`S22_CLAIMS=1`: every replayed unit's
`replay_claims` split, one query per claim); its `S20_DIV128` rewrite is
never set (the owner states the division itself). Built from the branch at
each stage (`probe/build_probe.sh`, never committed) and run over the dump
restricted to the 14 names (`probe/run_probe.sh`). `census/measure.py`
replays each unit (the theorem, or each part) one-shot (`ay -smt2 Q
--strict-proofs --proof P --proof-format alethe`, then `clean cert
verify-external`, 30 s each, the bridge's command lines), a unit without a
verdict claim by claim, serially, stopping at the first claim that does not
certify (the production route); a root closes when every unit is certified
whole or credited claim by claim. Replays are cached by the sha256 of the
bytes, so bytes a stage leaves unchanged reuse the earlier measurement.

**22a's bytes against the design's.** 50 of the 51 queries are byte for
byte the design's `queries/today` (its probe rewrite and guard lift on
census-s20's dump), once the production owner, like the probe, states a
source with an `I128` division but no other stop path by path (a division
that is a call stops nothing; the first build stated these 8 queries over
the DAG). The 51st, `int_log10::u128_impl`, is smaller (3,898 against 4,270
bytes): its guards divide by `10^32`, a constant with a high half,
which the production guard rule knows never fire (the design's §6 asked
for it).

| root | 22a (OD-202) | 22b without `guard` | 22b (OD-203) | 22c (OD-204) |
| --- | --- | --- | --- | --- |
| `<u64 as CarryingMulAdd>::carrying_mul_add` | certified, 9.0 s | = | = | = |
| `lemire::full_multiplication` | 0.34 s | = | = | = |
| `<u64 as FullOps>::full_div_rem` | 0.23 s | = | = | 0.24 s |
| `fmt::num::exp_u128` (15 parts) | 15/15, max 3.9 s | = | = | 15/15, max 3.6 s |
| `int_log10::u128_impl` | 0.92 s | = | = | = |
| `u128::checked_mul` | timeout (claim 1/2) | timeout | **0.71 s** | 0.71 s |
| `i128::checked_mul` | timeout (claim 1/2) | timeout | **1.04 s** | 1.02 s |
| `u128::overflowing_mul` | timeout (claim 1/5) | **0.55 s** | 0.55 s | 0.61 s |
| `i128::overflowing_mul` | timeout (claim 1/5) | **0.82 s** | 0.82 s | 0.82 s |
| `u128::from_ascii_radix` (11 parts) | 9/11 (parts 8, 10) | **11/11, max 1.5 s** | = | 9 parts, max 1.1 s |
| `i128::from_ascii_radix` (11 parts) | 9/11 (parts 8, 10) | **11/11, max 1.6 s** | = | 9 parts, max 1.6 s |
| `u128::overflowing_pow` (4 parts) | 2/4 (parts 2, 3) | **parts 2, 3 claim by claim** (8 and 9 claims, max 9.6 and 9.9 s) | = | 3 parts (one emptied), parts 2, 3 claim by claim |
| `fmt::num::div_rem_1e16` | timeout | timeout | timeout (claim 2/4) | **12.4 s** |
| `wide_mul_u128::scalar_mul` | timeout | timeout | timeout | timeout (claim 1/4) |
| **roots closed** | **5** | **10** | **12** | **13** |

`div_rem_1e16`'s 22b bytes also give no answer at a 300 s budget
(`census/offline300.py`, 300.1 s). The design's numbers per stage were 5,
12 (its `limbacm2`) and 13 (its `v22`); 22b reaches 12 only with the
`guard` step (§3).

## 2. OD-202: an `I128` division is the call of its runtime routine

**Claim.** An `I128` LIR `Udiv`/`Sdiv`/`Urem`/`Srem` is a direct,
interposable call of `__udivti3`/`__divti3`/`__umodti3`/`__modti3`
(`i128_division_routine`) under the slices 3/7/13 call model: the two
`I128` operands are the call's arguments (RDI:RSI, RDX:RCX), observed
against the machine's argument registers; the result is the call's `I128`
result (RAX:RDX), a free input both sides share; the escaped slots are read
and left as at any call. No division and no undefined stop is stated (the
call is total). The machine's `call` row is checked like every call's:
symbol and binding, declared argument and result registers. Slice 17's
byte liveness reads every escaping slot at such a division
(`split::i128_divisions`, a type analysis of the LIR whose errors only
refuse), and the division does not make a several-path source a DAG. An
`I128` `GuardDivZero` is slice 14's guard at 128 bits against the selector's
`or d, lo, hi; TrapDivZeroExact d`; a nonzero 128-bit constant's (one with
a high half included, read from its own definition) never fires. The claim
is OD-84's: for every value the routine returns, the machine's observables
equal the source run's in which the division returns it; with the
contract, that is refinement on trust-ir's defined domain.

**The contract's evidence (statistical).** `native/run_diff.sh` builds
`native/diff_ti3.c` twice: bound to libSystem's routines (`cc` alone;
`nm`: `___udivti3` (from libSystem)) and to the Trust sysroot's
`compiler_builtins` (rlib `libcompiler_builtins-491c939a746515db.rlib`,
sha256 `48acf5c9b1e6e5ae…`, its objects linked first; `nm`: "non-external
(was a private external)"), against an independent reference: bit-serial
restoring division on two 64-bit halves (no 128-bit division, so no call of
a routine under test). Inputs: every pair of a 74-value edge set, 20,000
random pairs in each of the 13 × 13 classes of dividend and divisor bit
length, and `q d + r` with `r` at 0, 1 and `d - 1`. **15,621,296 checks per
binding, 0 mismatches** (1,040,608 undefined inputs skipped); the
`-DMUTANT` build (the quotient's low bit flipped for a divisor with a high
half) reports 1,431,186 mismatches. Off the domain both bindings wrap `MIN
/ -1` to `MIN` (`native/offdomain.c`). The library test
`slice22::the_i128_division_routines_match_an_independent_reference` runs
the same differential (200 pairs per class by default;
`TCG_I128_DIVISION_DIFFERENTIAL_PER_CLASS` raises it) against the routines
its own Rust test binary binds, with its own wrong-routine control.

| Control | Kind |
| --- | --- |
| `U128Div`, `U128Rem`, `I128Div` (both of rustc's checks), `I128Rem`, `U128DivRem` (`full_div_rem`: two calls), `U128DivConst` (`n / 10^16`), `U128CheckedMulSmall` (the adapter's check of a widening product), `I128GuardConst` (a constant with a high half: no stop), `I128GuardVar` (`or d, lo, hi; TrapDivZeroExact d`), `I128SdivMinNegOne` (no check: `MIN / -1` and zero reach the call) | fixtures, every one certified (0.1-0.6 s) |
| `EscapedSlotAcrossDivision` (a local escaped to a call, the division after a cut) | fixture, certified; stated in parts at every block too (the liveness control) |
| the dividend's halves swapped; dividend and divisor swapped; the result halves swapped; the high half stale; `full_div_rem`'s second divisor wrong; the constant divisor's high half in its low half's place; the guard's `or` of the low half with itself | refuted on samples, AY counterexamples |
| `__udivti3` where the source divides signed | named `CallTarget` mismatch |
| the dividend's high half read from RSI after the call | named `UndefinedRead` mismatch |
| an `I128` division in slice 14's neighbour control | now admitted |

| Mutant | Fails |
| --- | --- |
| `div-no-call-event` | 8 controls (the fixtures, the refutations, the golden) |
| `div-args-unobserved` | `every_slice_twenty_two_refutation_is_refuted`, the golden, the custody |
| `div-symbol-unchecked` | `a_wrong_routine_or_a_clobbered_register_is_a_named_mismatch` |
| `guard128-low-half-only` | 4 (the `or`-with-itself refutation holds; `I128GuardVar` refuted) |
| `guard128-wide-constant-stops` | `the_i128_guard_is_slice_fourteens_guard_at_128_bits`, the golden |
| `liveness-division-no-call` | `owner_builds_every_slice_twenty_two_shape` (`EscapedSlotAcrossDivision` in parts refuses), added for this mutant: on the first run it failed no control |
| `i128-division-stops` | the golden and the custody |

## 3. OD-203: the 128-bit product by its 64-bit limbs

**Claim.** Four groups in `normal.rs` (`Terms::rule_v22`, after the "v18"
groups, before the slice-19 groups), each an identity on every input:
`limb` (a 128-bit product of operands not both extensions of at most 64-bit
terms, or constants below `2^64`, is `zext(xL)*zext(yL) + concat(xH*yL +
xL*yH, 0_64)`; limbs and partial-product operands built with one "v18" step,
so constants come out folded and the rule cannot oscillate); `addhi0`;
`acmul` (a 64-bit sum with a product leaf, addends sorted by a STRUCTURAL
key, a 128-bit FNV-1a over operator, payload, width and operands' keys, and
nested right; scoped as the design measured); and `guard`.

**The `guard` step (the departure, measured).** With the three design
groups the real bytes close 10 roots, not the design's 12: `checked_mul`'s
`u128` and `i128` theorems keep their raw `(bvmul (concat …) (concat …))`.
A spelling trace (a local patch, `probe/`'s build of it is in PAYLOADS)
showed why: their canonical spelling FAILS the structural check ("path claim
`(or (= r1 #b0) …)` is not `(or (not C) X)`") and the theorem keeps slice
18's spelling, which the prototype never checked. `look` normalizes the
claims it rewrites as one term, folding a guard's `(not (not L))` to `L`.
`guard` reads an item `(or L X)`, `L` no negation, back as `(or (not (not L))
X)` (exact). Only theorems that failed the check before can change, and the
whole core bears it out: a second trace build (22b without `guard`, the
check traced in theorems and parts, `probe/trace2.patch` in PAYLOADS)
reproduces the 32 other functions the step changes byte for byte and shows
every one failing the check (theorem or part) before. With it: 12 roots
(`checked_mul` 0.71 and 1.04 s).

**Whole core.** `probe/run_probe_all.sh` over every function of the dump on
each stage, `census/allcmp.py` and `census/regress.py` (functions whose
theorem bytes change, with their census-s21 body-trace outcome):

| step | functions whose theorems change | census-certified among them | still certify |
| --- | ---: | ---: | ---: |
| main (s21's probe) → 22a | 14 (newly built: the 14 roots; no other byte moves) | 0 | — |
| 22a → 22b without `guard` | 8 (7 class roots, `u64::carrying_mul_add`) | 1 | 1 (5.2 s; addends reordered) |
| 22b without → with `guard` | 34 (2 class roots, 32 others) | 32 | 32, all whole (max 3.1 s) |
| 22a → 22b | 42 | 33 | 33 |

**Goldens.** Slice 11's `MulU128` (its one claim becomes an identity,
so by slice 9's rule it keeps slice 18's spelling; still the recorded gap,
§5) and slice 14's `SremChecked32` (`guard`: now canonically spelled). Both
reviewed by `review/review22.py` (a symmetric version of slice 19's
review: 256-input sweep of the union of free inputs, equal claim values and
equal shared definitions; z3 4.15.4 on both theorems with their defined
names renamed apart, asserting the claims or a shared name differ): 0
mismatches, unsat. `the_canonical_spelling_without_the_limb_groups_
reproduces_every_earlier_golden` re-renders every golden of main without
the groups byte for byte.

**Exactness.** `limb` and `addhi0`: `limb/limb_exhaustive.c`, every operand
pair at limbs of 1 to 8 bits (4.3 G pairs at 8; ALL EXACT); z3 5.1.0 in
integer arithmetic at 128 bits, the whole identity and its five lemmas
(`limb/*.smt2`, unsat), the identity with one cross product omitted `sat`.
The library sweep is exhaustive at limbs of 1 to 4 bits.

| Control | Kind |
| --- | --- |
| `every_limb_group_is_exact_exhaustively_at_small_widths` | `limb` 104 instances (93 K inputs), `limb` + `addhi0` 8 (140 K), `addhi0` 30 (10 K, with nonzero-low near misses swept for value), `acmul` 13 (17 K) |
| `the_limb_groups_leave_what_they_do_not_rewrite` | widening products (zero, sign, constant, a 32-bit zero extension), a 64-bit product, a nonzero low addend, an extract below the top bit, a sum without a product leaf, a 128-bit sum |
| `the_product_sum_order_is_independent_of_creation_order` | four permutations of a sum, alone and after a table created their leaves in reverse order: one spelling |
| `a_folded_guard_keeps_its_skeleton` | `guard`'s shape and value; without it the folded item stays |
| `a_wrong_multiply_stays_refuted_and_the_correct_one_keeps_slice_eighteens_spelling` | five wrong lowerings of `MulU128` (a cross product omitted, `aH*bH`, the low product's wrong operand, the cross products' operands swapped, `dst_lo` from RDX) refuted on samples and by AY |
| `the_widening_product_theorems_keep_their_spelling` | `U64CarryingMulAdd` and slice 10's checked multiplies, byte for byte with and without the groups |
| `U128CheckedMul`, `I128OverflowingMul`, `U128MulZextOperand` (`from_ascii_radix`'s product by a widened radix), `U128MulAcrossCut` (also in parts at every block), `U64CarryingMulAdd` | fixtures, certified (0.9-5.4 s) |
| `U128MulConst` (`n - q * 10^16`) | fixture; a recorded gap (§5) |

| Mutant | Fails |
| --- | --- |
| `limb-one-cross` | 5 (the exhaustive sweep, the wrong-multiply control, the fixtures) |
| `limb-widening` | 5 (the near misses, the widening guard, ...) |
| `addhi0-any-low` | `the_limb_groups_leave_what_they_do_not_rewrite` |
| `acmul-unscoped` | 4 (the near misses, the widening guard, the golden, the custody) |
| `acmul-creation-order` | `the_product_sum_order_is_independent_of_creation_order`, the golden, the custody |
| `guard-fold-off` | `a_folded_guard_keeps_its_skeleton`, the custody |

## 4. OD-204: a normal form of bit moves (`catnf`)

**Claim.** One group of bit moves (`Terms::bit_move_normal`): an extract
across a concatenation's halves is the concatenation of the two extracts;
an extract across a zero extension's boundary is a zero extension;
concatenations nest right; adjacent extracts of one term at a chain's head
merge; the `bvor` of a zero extension of `x` and a right-nested chain ending
in `0_|x|` is the chain with `x` in place of its zeros. Each an identity on
every input; the design's measurement and this replay decide whether it is
kept.

**Kept.** It closes `div_rem_1e16` (12.4 s; 11.9-12.0 s in three repeats),
by the design's mechanism (§2.3): the source's and the machine's spellings
of the quotient's bits (its `s28`/`m48`, `s29`/`m45`) become one
concatenation of the same input bytes, value numbering merges them, and the
product claim drops (its query shrinks from 6,741 to 4,543 bytes). Whole core (`m` = the merged tree
without `catnf`, which states every function as 22b's did):

| step | functions whose theorems change | census-certified | still certify |
| --- | ---: | ---: | ---: |
| 22b → 22c | 123 (11 class roots) | 112 | **112**: 111 whole; `u128` `__fmt_inner` claim by claim |
| 22a → 22c (both groups) | 153 (11 class roots) | 142 | **142** |

`u128` `__fmt_inner`'s part 7 times out whole on 22b's bytes and on
22c's, and is credited claim by claim on both (8 claims, max 0.6 s): its
route does not move. No census-certified function is lost, so 22c is kept.

**Goldens.** 21 shapes, 30 theorems and parts: slice 1's `ShlU8Imm`,
`LshrU8Imm`; slice 5's five `PairCallBool*`; slice 8's `ResultPair`,
`ResultPartial`; slice 11's `ShlU128By3`, `ParamArrayU128`; slice 15's
`ThreeBytes`; slice 20's `U128ShiftLoop`, `U128RadixLoop`,
`U128LiveAcrossCut`, `U128CutParam`, the three masked shifts and both
`CallBool*` shapes (parts included). Every one reviewed (sweep 0
mismatches, z3 unsat); without `CATNF` every golden of 22b re-renders byte
for byte.

| Control | Kind |
| --- | --- |
| `the_bit_move_normal_form_is_exact_exhaustively` | extract across a concatenation (every split to 4 bits, 100 instances), across a zero extension (100), nesting (4), merges (34), the `bvor` chains (27); near misses (a nonzero tail, extracts not adjacent) |

| Mutant | Fails |
| --- | --- |
| `catnf-halves-swapped` | the exhaustive sweep, the custody |
| `catnf-or-any-tail` | the exhaustive sweep |
| `catnf-merge-any` | the exhaustive sweep |

## 5. Qualification

Every tool-gated x86 body test, one per process (`census/qualify.sh` over
`census/qual_list.txt`: every slice's replay, refutation and credit lanes,
slice 9's spellings, the canonical migration pair and the envelope's two
lanes, 48 tests; then `census/qualify_ignored.sh`, the explicit
deadline-bound lane at its 300 s budget), on AY 13556 + Clean 5f09e36c from
the overlay (`TCG_X86_BODY_QUALIFY_AY`, `TCG_EXTERNAL_CLEAN_CHECKER`),
`nice -n 19`, each test's replayed queries kept
(`TCG_X86_BODY_QUALIFY_DUMP`), at 1-minute load 1.6-2.6, on the final code
(22c, merged): **all 49 pass**.

- **The recorded gaps keep their outcomes**: slice 1's `MulI16` (Timeout),
  slice 9's `LongChain` (AY rejects its own proof), slice 11's `MulU128`
  (Timeout; its spelling is slice 18's again, OD-203, the 300 s record
  already measured that spelling), slice 14's `UdivConst` and `UremConst32`
  (Timeout), slice 16's three `LongChain` parts (Timeout). One joins:
  slice 22's `U128MulConst` (Timeout; `census/offline300.py`: `unsat` after
  88.8 s at a 300 s budget, Clean 1.5 s), recorded in
  `KNOWN_UNCERTIFIED_SLICE_TWENTY_TWO`. None leaves.
- **Every moved golden certifies** where it did: `SremChecked32` 0.7 s,
  `ShlU128By3` 0.5 s, `ParamArrayU128` 0.1 s, slice 20's
  `U128LiveAcrossCut` and `U128CutParam` production theorems 3.2 and 0.1 s,
  slice 5's, 8's, 15's and slice 1's moved theorems in their lanes. Slice
  20's three variable `I128` shifts (deadline-bound on this host) certify
  in 18.8, 19.5 and 25.6 s in the lane and in 19.3, 19.5 and 25.9 s in the
  explicit 300 s lane (before OD-204: 28.4-37.5 s offline); they stay
  deadline-bound entries.
- **Slice 22's lanes:** 17 of the 18 fixture theorems certify (0.1-5.4 s;
  `U64CarryingMulAdd` 5.4 s), `U128MulConst` is the gap above, the cut
  fixtures' parts certify; all 12 wrong lowerings (7 of OD-202, the five
  wrong multiplies) are refuted with AY counterexamples; every covered row
  of every certified shape is credited Formal, and no wrong lowering's row
  is credited.
- **Every wrong lowering of every slice** stays refuted with a
  counterexample (each refutation lane asserts it).

The four slowest certified class queries, replayed three more times each
(`data/repeats_c.jsonl`, load 1.6-2.1): `carrying_mul_add` 8.3-8.6 s (9.0 s
in the stage run), `div_rem_1e16` 11.9-12.0 s (12.4 s), `overflowing_pow`
part 2's claim 7 9.3-9.4 s and part 3's claim 9 9.1 s (9.6 and 9.9 s): at
least 17 s inside the deadline.

## 6. Gates

| Gate | Result |
| --- | --- |
| the solver-free x86 body suite (`x86_source_bound_body::tests::`, every library test but the tool-gated lanes) | 401 passed, 0 failed, 18 ignored on the final code (`logs/gate_c5.log`); 393 at 22a, 400 at 22b |
| `trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus` | 5 passed and 5 passed; the body lane replayed on AY 13556 (`X86_BODY_E2E_REPLAY_IDENTITY`, no skip) and its four slice-22 bodies (`u128_div_checked`, `i128_rem_checked`, `u128_div_guarded`, `u64_widening_mul_overflows`) promote on both triples |
| `trust-cg-codegen --test e2e_x86_64_i128_div` (native) | 4 passed |
| `trust-cg-lower --lib` | 2113 passed |
| `scripts/check_fmt.sh` (the 6808 package's `targo fmt`) | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK (the slice-22 printer is in `IGNORED_TESTS`) |

The lint gate (`scripts/check_tippy.sh`) is not run on this host: the
managed 6808 package's `targo-tippy` cannot resolve the workspace and
refuses a mixed package (unchanged since slice 19).

## 7. Reproducers (this directory)

| File | What |
| --- | --- |
| `native/diff_ti3.c`, `native/offdomain.c`, `native/run_diff.sh` | OD-202's native differential of both bindings, and the off-domain probe |
| `limb/limb_exhaustive.c`, `limb/*.smt2` | `limb` and `addhi0` exhaustively at limbs of 1 to 8 bits; the z3 integer lemmas and the wrong identity |
| `probe/x86_body_probe.rs`, `probe/build_probe.sh`, `probe/run_probe.sh`, `probe/run_probe_all.sh` | the local probe (never committed) and its runs over the 14 roots and the whole core |
| `census/dump_core_ir.sh` | the fresh `core` dump from the census-s21 bridge |
| `census/measure.py`, `census/detail.py`, `census/probe_run.py` | the replay of a probe run's units and claims (the production route) and its per-root table; `probe_run.py` is the design's runner |
| `census/allcmp.py`, `census/regress.py` | the whole-core comparison and regression sets |
| `census/offline300.py` | the 300 s offline replays of the gaps |
| `census/qualify.sh`, `census/qualify_ignored.sh`, `census/qual_list.txt` | one tool-gated test per process on the qualification pair |
| `census/build_test.sh` | the test build, copying the binary the build names |
| `review/review22.py`, `review/golden_write.sh` | the golden review and the golden rewrite with digest pinning |
| `fails-before/mutate.py`, `fails-before/run_mutants.sh` | the 16 rule mutants and their run |
| `review-fixes/mutate_review.py`, `review-fixes/run_review_mutants.sh` | §8's six mutants and their run |

## 8. The hostile review: OD-210, OD-211 and three controls

A hostile review of the landed slice (sweep and notes in
`~/tcg-scratch/s22-review/`, its `sweep.py` an exhaustive re-derivation of
every rewrite) found no false credit from the rewrites themselves, and
found the following. Fixed on branch `fix/x86-body-s22-hardening`.

### 8.1 Soundness: the module under proof could define the trusted routine (OD-210)

OD-202 trusts whatever routine the link binds to `__udivti3`, `__divti3`,
`__umodti3` or `__modti3`, and nothing checked whether the module under
proof defines one. The object's own definition is what its call binds to
(ahead of the sysroot's weak `compiler_builtins` copy), so:

- a crate with `#[unsafe(no_mangle)] extern "C" fn __udivti3(a: u128, b:
  u128) -> u128 { 0 }` had every `u128 /` body credited Formal, although
  every division returns 0;
- a `__udivti3` whose own body divides at `I128` (a call of itself) was
  credited too: its theorem assumed the contract of the body under proof.

**Where the module is seen.** The verifier saw one function: its LIR, its
pre-RA stream and its ABI. The module is seen by the compiler: the AOT
certificate lane (`compile_x86_64`) and the host JIT
(`compile_replayed_lir_module_to_jit`) both hold the lowered trust-ir module
they compile. They now name its definitions to the verifier
(`X86ModuleDefinitions::of_trust_ir_module`: every function with a body,
whatever its linkage, and every global, by link-time symbol, keeping the
four routine names), through `verify_for_certificates` and
`verify_with_request_and_abi`.

**The check.** Admission records the routine of every `I128` division it
states as a call (`SourceSites::routines`, the owner's `trusted_routines`);
`source_bound_x86_body_in_module` refuses with a typed reason,
`X86BodyUnsupported::TrustedRoutine`: `TheFunction` (the function under
proof is the routine, whatever module is named), `TheModule` (the module
defines it), `Unnamed` (the caller named no module: the three-argument
`source_bound_x86_body` and every entry point without a module). Unsupported
is no theorem, no credit and no claim about the lowering.

**Verifier input.** The definitions can change a verdict, so `x86_input`
(the report's receipt and the exports' binding) and the JIT cache key
(`x86_verifier_input_digest`) bind one line for a function with a division
opcode whose routine the module defines (or, no module named, any division
opcode). Every other function's digest is the one it had: the existing
digest pins and caches are untouched.

**What stays trusted.** A definition elsewhere in the link still binds and
is trusted, as slice 13 trusts `memcpy`: another crate, the sysroot's
`compiler_builtins`, the platform's compiler-rt, and in the JIT the host's
symbol map (consulted before the module's own functions). **The module is
the compile unit:** the bridge compiles a crate in codegen units, and a
definition in a sibling unit binds unseen, so the review's crate is refused
only where its `__udivti3` shares the division's unit (always with `-C
codegen-units=1`). LIMITATIONS says so. *(Superseded the same day by OD-216:
"always with one codegen unit" did not hold, since the bridge's
per-function fallback compiled `div` alone after OD-210 refused it in the
merged module; the bridge now names the whole crate's definitions. See the
[OD-216 report](../2026-10-27-darwin-x86-64-od216-link-unit-routines/README.md).)*

**Fails before.** The review's module as fixtures (`slice22::routine_module`:
`div` with rustc's zero check beside `__udivti3` returning 0, or a
`__udivti3` dividing through itself, or a declared one) and in the codegen
integration test (`routine_module`, `div_by_own_routine` beside the
module's `__udivti3`). "Before" is the env-gated mutant
`od210-routine-trusted` of `review-fixes/mutate_review.py`, which restores
slice 22 as landed (no definition read); the builder itself is unchanged.

| Check | Before (mutant) | After |
| --- | --- | --- |
| `slice22::a_routine_the_module_defines_is_never_trusted` | FAILED: "a theorem trusting [\"__udivti3\"] was built" | ok: `TheModule`, and `Unnamed` with no module; a declared routine keeps its theorem |
| `slice22::the_routine_never_divides_through_itself` | FAILED (and under `od210-circular-trusted`: `TheModule` where `TheFunction` is owed) | ok: `TheFunction` whatever module is named |
| `slice22_qualification::verifier_credits_no_row_whose_routine_the_module_defines` (AY 13556 + Clean 5f09e36c, one test per process) | FAILED: `div`'s theorem replays Valid and **25 of 25 covered rows are credited Formal** | ok: the same theorem replays Valid, **0 of 25** rows credited, nothing exported (circular `__udivti3`: 0 of 12; its module's `div`: 0 of 25); the declared routine's `div` keeps every row Formal |
| codegen `a_division_by_the_modules_own_routine_never_promotes` (the proof-required AOT compile, AY 13556) | FAILED: the module **promoted**, `div_by_own_routine` credited Formal by its body theorem | ok: the compile is refused naming `div_by_own_routine`; the declared routine's module promotes |
| codegen `x86_body_trace_names_a_routine_the_module_defines` (solver-free) | FAILED: the trace shows `div_by_own_routine`'s theorem built (`bound rows=14`) | ok: the trace names the `TrustedRoutine` refusal (OD-210) |

Records (out of tree, bound in [PAYLOADS.md](PAYLOADS.md)):
`s22h-run/records/qualification_od210.txt`, `codegen_od210.txt`,
`mutants_verify.txt`.

### 8.2 Wording: the routine's ABI trust is not the call model's (OD-211)

OD-202 called the routine contract's "ABI half (callee-saved registers
preserved, no memory the caller observes written, a return)" "the call
model's existing assumption for every call". Only its callee-saved half is:
the call model (slices 3, 7, 13, 15) lets a callee rewrite the escaped
slots' bytes, incoming memory and the world, and says nothing of a callee
that never returns. Linking the call to trust-ir's pure division therefore
additionally trusts that the routine writes no memory the caller observes,
has no effect on the world, and returns. OD-211 states it; OD-202 keeps its
words with an "Amended" line; the module documentation's slice-22
paragraph, its **Trusted** list, the division arm's comment and LIMITATIONS
say so. No theorem changes, and no test covers it (the differential
observes results only).

### 8.3 Controls for three checks whose mutants survived

Each control is a test of its own in `slice22`, with a mutant in
`review-fixes/mutate_review.py` that the review said would survive the
slice's controls; each fails exactly its control (records
`s22h-run/records/mutants_verify.txt` and `guard_controls.txt`, bound in
PAYLOADS.md):

| Check (code) | Mutant | Control | Mutant's failure |
| --- | --- | --- | --- |
| `catnf` merge's same-term test (`normal.rs`, `self.arg(c, 0) == self.arg(a, 0)`) | `catnf-merge-two-terms`: the test deleted | `catnf_moves_only_bits_of_one_term_and_of_zero_extensions`: `(concat t[h:m] (concat u[m-1:l] r))` for every split of 2- to 4-bit `t`, `u`, exactly evaluated on every input | `(concat ((_ extract 1 1) t) (concat ((_ extract 0 0) u) r)) -> (concat t r)` |
| the extract rule's restriction to zero extension | `catnf-extract-sext`: a sign extension too | the same test: `extract[h:l](sext_k y)` across the boundary, `y` of 1 to 3 bits, `k` 1 to 3 | `((_ extract 1 0) ((_ sign_extend 2) y)) -> ((_ zero_extend 1) y)` (slice 22's golden reproduction fails too: the mutant respells existing theorems) |
| the `bvor` rule's restriction to zero extension | `catnf-or-sext`: a sign extension too | the same test: `(bvor (sext x) (concat c 0_|x|))`, either order | `(bvor ((_ sign_extend 1) x) (concat c (_ bv0 1))) -> (concat c x)` |
| the `I128` guard's zero-constant test (`lo \| hi != 0`) | `guard128-zero-never-fires`: the test dropped | `an_i128_guard_of_zero_with_its_trap_dropped_is_refuted`: `I128GuardConst` with the divisor `Iconst128 { 0, 0 }`, its `TrapDivZeroExact` removed | "a wrong lowering's theorem holds on samples" (after: refuted on samples; the selector's lowering holds and the guard is a stop) |

Each near miss runs under `catnf` alone (no other rule reaches the term
first), the test's groups and the canonical ones. The high-half-only
fixture, `an_i128_guard_of_a_high_half_only_never_fires` (`Iconst128 { 0,
1 }`, `2^64`): no stop, the lowering holds, and a carrier `or d, lo, lo`
(it traps on every run) is refuted on samples. All six mutants and the
fixed code were run from one env-gated build; the fixed code passes all 23
`slice22::` tests.

### 8.4 Gates

On the final code merged with origin/main `dd130156b`, built once
(`targo --unverified` from the `x86-stage1-ay13556` overlay, `nice -n 19`,
`-j2`, through `build-slot`), tool-gated lanes on AY 13556 + Clean
5f09e36c, one test per process:

| Gate | Result |
| --- | --- |
| the solver-free x86 body suite (`x86_source_bound_body::tests::`, every library test but the tool-gated lanes) | 407 passed, 0 failed, 18 ignored (877 s); `slice22::` 23 passed |
| `slice22_qualification::verifier_credits_no_row_whose_routine_the_module_defines` | ok |
| `slice22_qualification::verifier_credits_every_bound_slice_twenty_two_row_with_the_replayed_body_theorem` | ok: every covered row of every certified slice-22 shape still Formal through the module-naming verifier (48 s) |
| `trust-cg-codegen --test x86_source_bound_body` | 7 passed with the replay tools (the four slice-22 bodies still promote on both triples through the AOT lane that now names the module) |
| `trust-cg-codegen --lib`, the x86 certificate, JIT and envelope tests whose call sites changed | 56 passed, 0 failed, 1 ignored (`compiler::tests::x86*`, the refusal-layer, decode-backing and x86 envelope JIT test modules, the JIT request cache); with the replay tools' `TCG_*` variables set, `x86_64_windows_coff_stale_cache_entry_misses_before_unwind_guard` fails at "test compiler should build a cache context" (those variables disable artifact reuse) and passes without them |
| `function_request::tests` | 8 passed; the two AArch64 request tests fail on this host before any x86 code runs: an overlay-built trust-cg refuses the test's stand-in checker (`overlay.json names the Clean with sha256 949365b6…`), environmental |
| `scripts/check_fmt.sh` (the 6808 package's `targo fmt`) | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK |

Slice 22's own qualification (`host_qualification_replays_…`,
`host_qualification_refutes_…`) was not re-run: no theorem changes (the
slice's golden test, `slice_twenty_two_smt2_is_canonical_per_shape`, pins
every fixture's theorem text and passes).

`folded_guard`'s `!= Op::Not` and `width != 0` tests, which the review
called dead code, are left as they are: not shown dead here.

