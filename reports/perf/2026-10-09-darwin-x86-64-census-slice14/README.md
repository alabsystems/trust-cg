# Darwin x86-64 `library/core` — slice 14 (definedness and dispatch), 2026-10-09

Slice 14 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) admits four refusal
classes of the Darwin `core` proof census: division and remainder, the
divide-by-zero guard, a `Switch` several of whose cases share a target, and
the selector's jump tables. Rulings OD-178..OD-181 in
`docs/decision-record.md`. Host: the
x86_64 Mac of the slice-12 record (4 cores, 16 GB, shared with a census
pipeline and an AY agent), the `x86-stage1-ay12713` overlay (`targo
--unverified`: no proof claim about any build), qualification pair AY 0.27.0
build 12713 with Clean 5f09e36c. Nothing here is a completion claim.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-a902ea9ef-ay12713` (baseline) | `main` `a902ea9ef` | 12713 | `2c1ef38f…` | 377 | 7455 s |
| `core-x86_64-darwin-O0-proof-slice14-ay12713` | this branch, `ffdfb2b23` (slice 14 on `a902ea9ef`) | 12713 | `6a297a16…` | **342** | 4690 s |

**35 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
17 functions refused at the machine-table rule now replay Valid (jump
tables), 8 at `Udiv`, 6 at `GuardDivZero` and 2 at `Urem`; 2 more were
bound on both sides and certify here. Both rows were built by
`census12713.sh` (each bridge in its own tree; an earlier pair of rows was
discarded because both bridges were built into a shared target directory
and the baseline ran a stale dylib), one after the other, with no
resource-budget refusal.

In short: 28 fixtures, 26 certified (the two divisions by a constant other
than a power of two are recorded solver gaps), 24 wrong lowerings refuted,
22 rule mutants each caught; of the 71 class functions, 44 now build a
theorem and 35 of those certify offline. One selector change, a hardening
(the 32-bit jump-table selector is zero-extended), with no miscompile
observed natively.

## The classes, measured first

Census `runs/census-s15-cf98` (the slice-15 bridge, 466 failed roots) traces
71 functions first refused by the four classes (`census/classes.py` over
`stderr.log`'s `[TCG-X86-BODY-TRACE]` lines; each function is named by at
least one of the failed roots):

| Class | Refusal | Functions |
| --- | --- | ---: |
| division | `instruction N (Udiv/Urem/Sdiv) is outside Iconst, Copy, …` | 22 (`Udiv` 15, `Urem` 4, `Sdiv` 3) |
| guards | `instruction N (GuardDivZero { obligation: None }) is outside …` | 13 |
| shared switch targets | `block Block(N) ends in a Switch with two edges to one block` | 15 |
| machine tables | `machine function is outside the body domain: constant pool, jump tables, EH, guard obligations or an outgoing call area` | 21 |

The probe (`probe/x86_body_probe.rs`, mode `--dump` added here) read each of
the 71 from the slice-9 dump of `core`'s trust-ir (`runs/core-ir-s9`) and ran
the slice-12 owner (this branch's base) over it: all 71 reproduce their
census refusal. **The machine-table refusal, split by cause:** all 21
functions have exactly one jump table and nothing else (no EH tables, no
guard obligations, no outgoing call area, no constant-pool row): 11
`atomic_load::<T>` (a dispatch on the ordering, cases 0..4), 2
`flt2dec::decoder::decode::<f32/f64>` (on the float's class) and 8
`Display`/`Debug`/`as_str`/`source` methods of error enums (on the
discriminant).

Their size bounds what admitting the class can promote (OD-72's 512
machine rows): every division and guard function is under it (45 to 433
rows), 19 of the 21 machine-table functions are (104 to 458; two are 548
and 552), but 14 of the 15 shared-switch functions are not: the 12
`from_ascii_radix::<T>` (1054 to 1404 rows; their shared target is the
`+`/`-` sign test, `43 | 45`) and the 2 `dec2flt::slow::parse_long_mantissa`
(`0 | 1`). The fifteenth, `char::escape_default`, switches over six sparse
cases (three to one block), which the selector lowers as a search tree
whose synthetic blocks break the block correspondence (a refusal slice 14
does not touch). So the shared-switch rule promotes no `core` root by
itself; it is admitted, tested and refuted like the others, and the size
bound and the search tree are the next levers there.

## Semantics: where each meaning comes from

**Division** (pinned trust-ir `cf33f748`, the `Cargo.lock` rev after
merging `main` `49b93b2ee`, in the cargo git checkout
`trust-ir-4d018c57bcd84dec/cf33f74`): `crates/trust-ir/src/interpret.rs`,
`eval_int_binop`, lines 9606-9639 (the same text as at the earlier pin
`8dfdd235`, lines 9564-9596, where this slice began).

| Operation | Value where defined | Undefined behaviour |
| --- | --- | --- |
| `UDiv` | `lhs.raw / rhs.raw` | `rhs == 0` (`"unsigned division by zero"`) |
| `URem` | `lhs.raw % rhs.raw` | `rhs == 0` (`"unsigned remainder by zero"`) |
| `SDiv` | `(lhs_signed / rhs_signed) as u128`, masked (Rust `i128` `/`: truncating) | `rhs == 0` (`"signed division by zero"`); `lhs == MIN && rhs == -1` (`signed_div_overflows`, lines 10264-10267: `"signed division overflow"`) |
| `SRem` | `(lhs_signed % rhs_signed) as u128`, masked (the remainder with the dividend's sign) | `rhs == 0`; `MIN % -1` too (`"signed remainder overflow"`) |

So a zero divisor is undefined behaviour, never a trap, and so is `MIN / -1`
and `MIN % -1` (unlike Rust's `wrapping_rem`; the selector's comment calling
trust-ir's `SDiv`/`SRem` total is stale, and its `cmov` fixup computes a
value there that refines the undefined behaviour). The fsym UB map
(`crates/trust-cg-verify/src/fsym_ub_map.rs`, the six `eval_int_binop`
division sites, re-derived from the pinned source by `tests/fsym_ub_map.rs`)
lists the same six conditions. trust-ir's `behaviour_refines`
(`lean/trust_ir-semantics/TrustIr/Proofs/TransformCorrectness.lean`): "a
source with UB at some fuel constrains nothing". The adapter maps `BinOp`
`UDiv`/`SDiv`/`URem`/`SRem` to LIR `Udiv`/`Sdiv`/`Urem`/`Srem` unchanged
(`adapter.rs`, the `BinOp` arm); the owner states trust-ir's meaning of them
(`division`, `division_undefined`), and
`the_division_meanings_are_trust_irs` checks both against the pinned
interpreter at 8, 16, 32 and 64 bits on 144 operand pairs each (every value
the interpreter returns equals the stated one, and the stated undefinedness
holds exactly where the interpreter reports undefined behaviour).

**`GuardDivZero`** is no trust-ir instruction: the adapter emits it before a
trust-ir division whose node carries `ProofAnnotation::DivNonZero`
(`integer_div_or_rem_has_nonzero_proof`), with `obligation` the node's
`ProofRef` if any; outside the adapter's own tests no obligation is
synthesized (`node_obligation_id_or_test_model`), so the census's guards are
all `obligation: None`. Its LIR meaning (`trust-cg-lower/src/instructions.rs`,
"an exact guard/check instruction"; `action_equiv.rs`'s interpreter: "trap
when the divisor is zero") is a trap exactly when its divisor is zero. The
x86 selector lowers it to the `TrapDivZeroExact [divisor]` carrier
(`select_guard_div_zero`); an unbound carrier is never deleted, and the
pipeline expands it after the body theorem's subject (the optimized pre-RA
stream) to `test d, d; je trap; ...; trap: ud2`
(`expand_x86_div_zero_check_carriers`, whose `je` its guard-carrier canary
binds). The division after a guard is therefore never undefined at zero,
and the trap is a defined, observable outcome.

**x86** (Intel SDM DIV/IDIV/CWD-CDQ-CQO/XOR): `div src` divides the unsigned
double-width EDX:EAX or RDX:RAX by `src` (32 or 64 bits), quotient to
EAX/RAX, remainder to EDX/RDX (a 32-bit write zero-extending); `idiv` the
signed dividend, truncating, the remainder with the dividend's sign; #DE when
`src` is zero or the quotient does not fit the width; CF, OF, SF, ZF, AF and
PF undefined afterwards. `cqo` sets RDX to the sign of RAX, `cdq` EDX to the
sign of EAX; `xor r, r` is zero. `the_machine_division_is_intels` sweeps the
owner's `machine_division`, in its double-width form and in the simplified
forms for a high half that is zero or the low half's sign, against a direct
computation of Intel's definition (10 x 10 operands x 5 high halves x both
widths and signednesses).

**Jump tables** (`emit_x86_jump_table`): the selector copies the selector
into a 64-bit register (a narrower one is first zero-extended by
`normalize_condition_operand`; a 32-bit one was copied with a 64-bit `mov`,
now with the zero-extending `mov r32, r32`: a hardening of the pre-RA
stream, below), forms
`n = sel - min`, `cmp n, range; ja default; jmp dispatch`, and
the dispatch block `lea b, [rip + table]; mov e, [b + n*8]; add e, b; jmp e`;
the table (`X86JumpTableData`: `min_val` and the dense `targets`, a hole the
default) is emitted by the codegen (`pipeline.rs`, the `jt_fixups` loop) into
the function's own `.text` right after its body, 8-byte aligned, entry `i`
the 8-byte signed delta `offset(targets[i]) - table_base`, and the `lea`'s
`disp32` is patched to the table's base.

## The theorem

The owner's module documentation ("Definedness and dispatch (slice 14)") is
the full statement; rulings OD-178..OD-181 give the choices and why.

**Stops.** Each source program (a path, or a DAG block's fragment) records
its STOPS in execution order (`SourceStop`): a `GuardDivZero` (a defined
trap when its divisor is zero) and each division (undefined at a zero
divisor, and signed at the minimum by -1). From them the builder states,
before every event of the world trace and at the program's end, the 1-bit
source stop term `s` (`UnitStops`): 0 at a path's start, at a DAG's first
block and at a loop header (a region instance); a DAG block starts with its
one predecessor's end term, or at a join the incoming edges' end terms
joined by their guards (so a division on an untaken path adds nothing); each
stop in order ORs in its condition. The machine walk keeps two bits
(`MachineState::stopped`, `trapped`): `stopped` ORs in every `div`/`idiv`'s
#DE condition and every `TrapDivZeroExact` carrier's firing, `trapped`
records a carrier that fires before any other stop. The walk goes on past a
stop (its later rows then state what a run that does not stop computes),
and every claim keeps it honest:

- each observed item at event `k` (a call's arguments, an access's address
  and value) and each returned value (`k` the end) is claimed under the
  condition that the source has not stopped there, `(or (not (= s_k #b0))
  (= src mach))` (`running`, `under`, `items_under`; a block's guard joins
  the condition, as before: `(or (not (and (= g #b1) (= s_k #b0))) ...)`);
- each DAG edge's machine literals and cut-point relation are under the
  block's end term the same way;
- LIVENESS: before each event and at the end, `(= t_k #b0)` under the same
  condition, `t_k` the machine's `stopped` bit there: a #DE or a carrier
  where the source has not stopped is refuted;
- GUARDS: for each guard firing at event position `k`, `(= T_k #b1)` under
  `(and (= s_before #b0) fire)`, `T_k` the machine's `trapped` bit: where the
  source traps, the machine's first stop before its next event is a carrier
  (a #DE in its place, a dropped carrier, a carrier on another register or
  after the event, is refuted).

Every claim keeps the structural form `(or (not C) X)` the theorem's check
admits (`check_definitional`), and a constant-zero stop term adds no
condition, so a body without a stop states exactly what it did before.

A several-path source with a stop is stated over its DAG (`per_path`); a
one-path chain states its items, waived, and its stop claims in one
conjunction. Every edge of a machine block, and every route of an edge,
must stop alike (else no claim), so the block's stop claims hold for each.

**Soundness**, along one source run on one input (and region instance by
region instance, as slice 12 argues): let `p` be the first point the source
stops, if any. Before `p` every stop term is 0, so every item and liveness
claim there holds unconditionally: the machine has performed the same events
with equal values and has not stopped. If `p` is a guard firing, its claim
makes the machine's first stop before the next event a carrier, after
liveness kept it running through the events before: the machine traps with
the same trace. If `p` is an undefined division, the source run is
undefined there (trust-ir constrains nothing of it); the machine matched it
up to its last event before `p`. If the source never stops, every claim
holds at the end: the machine returns (or ends) as the source does, having
never stopped. The DAG's guards select the source path exactly (slice 9),
so the join of the stop terms is the stop term of the path taken.

**Division values.** The source's `Udiv`/`Urem`/`Sdiv`/`Srem` are `bvudiv`,
`bvurem`, `bvsdiv` and SMT-LIB's `bvsrem` (spelled through `bvurem` of the
magnitudes, as the standard defines it); the machine's `div`/`idiv` state
the same terms when its dividend's high half is the selector's zero or sign
(the definitions of the names RDX holds), and the double-width division
otherwise, with #DE exactly when the divisor is zero or the quotient does
not fit (its remainder spelled `dividend - quotient * divisor` at double
width, which is `bvurem`/`bvsrem` for every divisor and which the library
gate's native evaluator computes at 128 bits).

Two exact spellings make a correct lowering's theorem solvable. AY build
12713 ran out of memory (`unknown`, `memout`, 72 s) on the canonical
theorem of `u64` `a / b` (`UdivUnchecked`), whose source and machine sides
each define a 64-bit division over distinct but equal names, and proved
the same query with every definition inlined (the two divisions then one
term) in 0.1 s. So a canonical machine division's value is defined as
`(ite C S X)` (`pair_divisions`): `X` its own definition, `S` the value of
the source division its row is stamped with, `C` that the machine's
dividend and divisor equal the source's operands (at a narrower source
width, the operands extended as the division is signed or not, and the
narrow source division defined). Where `C` holds, `S` is the same
`division` of equal operands at the same width (or the extension of a
defined narrow division, which is the wide division of the extended
operands), so the restatement equals `X` on every input: it names no new
value and claims nothing. With it, `UdivUnchecked` replays and certifies
in 0.5 s. And a signed division states its divisor's unit cases first
(`bvsdiv` by 1 is the dividend and by -1 its `bvneg`, `bvsrem` by either
is 0, as SMT-LIB defines them): the selector's overflow fixup divides by 1
where the source divides by -1, and the solver then compares `bvneg`
terms, not a division circuit by -1 (with the pairing alone, `SdivChecked`
was a strict self-check rejection after 105 s). Third, an unsigned
division by a constant power of two is stated as its shift or mask
(`power_of_two_division`), and the selector's one-operand `mul` by a
constant power of two (its magic-number division by one) as the shifts it
is (`power_of_two_product`); `the_power_of_two_spellings_are_exact` sweeps
both against `division` and Intel's `mul`. A division by any other
constant is the magic-number product, which stays a gap.

A division by a constant
other than 0 (signed, other than -1) is defined for every dividend and adds
no stop; nor does a guard of a nonzero constant. A chain whose claims under
its stop terms number fewer than two is refused by name, as a DAG's is.

**Shared switch targets** are one source edge per distinct target
(`switch_targets`): its test is the disjunction of its cases' (and the
default's) tests (`BranchTest::Cases`); its machine literal the disjunction
of every route of the compare chain to the target block (`block_routes`,
`walk_routes`), each route's `jcc`s before its own not taken.

**Jump tables.** `dispatch_blocks` recognizes the selector's dispatch block
(`lea b, [rip + table]; mov e, [b + n*8]; add e, b; jmp e`, its recorded
successors the table's distinct targets, each table used by exactly one);
it lowers no LIR block of its own (`Correspondence::dispatch`: it is part of
the block whose final `jmp` reaches it). The walk tracks the table address,
the entry at index `n` and the target address (`TableValue`), never their
bits; the indirect `jmp`'s literal on a route to block `S` is the
disjunction of `n == i` over the table's indices `i` of `S`, read from the
pre-RA table itself. A route to the default is the bound check's `ja` taken,
or (a hole) the dispatch at one of the default's indices.

## Fixtures, controls and wrong lowerings

**Fixtures** (`x86_source_bound_body_slice14_tests.rs`, `DefinedShape`, 26
shapes, real adapter and selector output): division (`u64` `/` checked, `u32`
`%` checked, `i64` `/` checked, `i32` `%` checked, `u64` `/` unchecked, `u8`
`/`, `i16` `/`, `u64`/`i64` `/` with a third argument in RDX, `/ 10` and `%
1000` by the magic multiply, a division before and after a call, a division
on one path of two), the guard (`DivNonZero` annotated `u64` `/` and `i32`
`%`, the bridge's checked-then-guarded shape, a guard before a call), shared
switch targets (`43 | 45`, a case sharing the default, three cases to one
block, cases reaching one join with different arguments through copy blocks)
and jump tables (dense, shared targets, a hole the default shares, a table
indexed from 10).

**Wrong lowerings** (`slice_fourteen_refutations`, each must build a theorem
that is refuted; the qualification test asks AY for each counterexample): a
missing `cqo`, `cdq` where `cqo` is needed, a missing `xor edx, edx`, the
remainder for the quotient, the quotient for the remainder, `div` for
`idiv`, `idiv` for `div`, the dividend taken from another register, a narrow divisor not zero-extended, the magic
multiplier off by one, a dropped guard, the guard on the dividend, a guard
moved after the call, a trap on the path that divides nothing, the division
hoisted above its branch, an extra division by zero, a shared case compared
with another value, a shared case sent to the default, two cases' arguments
swapped, two jump-table entries swapped, the bound check one short, the
table's first case not subtracted, a 32-bit selector copied with a 64-bit
`mov` (the selector's former form), a hole's entry sent to a case.

## Qualification on AY build 12713 and Clean 5f09e36c

`slice14_qualification` through `fails-before/qualify.sh` (the overlay's
`ay` and `clean`, one test thread; payload `qualification_run4.log`):

| Shape | AY | ms | Shape | AY | ms |
| --- | --- | ---: | --- | --- | ---: |
| `UdivChecked` | Verified | 1137 | `DivThenCall` | Verified | 690 |
| `UremChecked32` | Verified | 5420 | `CallThenDiv` | Verified | 758 |
| `SdivChecked` | Verified | 8060 | `DivOnOnePath` | Verified | 2777 |
| `SremChecked32` | Verified | 7062 | `GuardedUdiv` | Verified | 3559 |
| `UdivUnchecked` | Verified | 638 | `GuardedSrem32` | Verified | 3456 |
| `UdivNarrow` | Verified | 2698 | `GuardedChecked` | Verified | 1018 |
| `SdivNarrow16` | Verified | 3758 | `GuardThenCall` | Verified | 6506 |
| `UdivThree` | Verified | 860 | `SharedCases` | Verified | 537 |
| `SdivThree` | Verified | 6347 | `SharedDefault` | Verified | 400 |
| `UdivConst` | **Timeout** (gap) | 30017 | `SharedThree` | Verified | 1124 |
| `UremConst32` | **Timeout** (gap) | 30014 | `CaseArgs` | Verified | 579 |
| `UdivPow2` | Verified | 684 | `JumpTable` | Verified | 759 |
| `UremPow2_32` | Verified | 1035 | `JumpTableShared` | Verified | 844 |
| | | | `JumpTableHoles` | Verified | 857 |
| | | | `JumpTableOffset` | Verified | 1241 |

26 of 28 certify (each Verified is AY `unsat` with a strict Alethe proof
that Clean accepts). The two gaps divide by a constant, which the selector
lowers to the magic-number multiply; AY gives `unknown` (timeout) offline
after 300 s on each too (payloads `UdivConst.300.out`,
`UremConst32.300.out`): showing the 128-bit product's high half, shifted,
equal to `bvudiv`/`bvurem` by the constant is past this solver. They are
recorded in `KNOWN_UNCERTIFIED_SLICE_FOURTEEN` (`PENDING(solver-capacity)`)
and earn no credit. Several shapes take 4 to 8 s of the 30 s budget, so
their credit, like slice 9's `StoreJoin`, depends on the host's load.

Every one of the 24 wrong lowerings is refuted by AY with a counterexample.
`verifier_credits_every_bound_slice_fourteen_row_with_the_replayed_body_theorem`
passes: for each certified shape every row the owner binds is Formal body
credit, the function's opcode inventory is promotable and its exports bind
the ABI; for the gaps the rows stay `NeedsReplay` with no export; for each
wrong lowering every covered row fails.

Before the division pairing (`pair_divisions`) and the signed unit-divisor
spelling, all 18 division and guard shapes timed out at 30 s (payload
`qualification_run1.log`); the switch and table shapes certified then as
now.

## Fails before: each rule disabled alone

`fails-before/mutate.py` guards each slice-14 rule of the owner behind
`TCG_S14_MUTANT=<name>` and `mutate_selector.py` the selector's 32-bit
copy; one build runs every mutant over the `slice14::` filter
(`run_mutants.sh`; payload `mutants.txt`, each run's log beside it). The
unmutated run passes all 13 tests. Every mutant fails at least one; the
table names the tests other than the golden digest (which every mutant
that changes a theorem's bytes also fails):

| Mutant (the rule disabled) | Tests failed besides the golden |
| --- | --- |
| `no-undefined-stop` (an undefined division adds no stop) | owner fixtures, O1-O3, the per-path premise, the guard |
| `no-constant-fold` (a division by a nonzero constant adds a stop too) | none: the fold only simplifies (the theorems still hold); the golden fails |
| `path-insensitive-stop` (every unit waived by every unit's stop) | the refutations (a trap on the path that divides nothing is no longer refuted) |
| `no-join-stop` (a join starts running) | owner fixtures, O1-O3, the per-path premise |
| `no-guard-claim` (a firing guard asks nothing) | the refutations (a dropped guard is no longer refuted), the guard |
| `fault-traps` (a #DE counts as the guard's trap) | the refutations (a dropped guard), the guard |
| `no-liveness` (the machine may stop where the source runs) | owner fixtures (a one-path chain keeps one claim and is refused), the refutations, determinism |
| `no-division-fault` (`div` never faults) | owner fixtures (as `no-liveness`: no machine stop is left to claim), the refutations, determinism |
| `canonical-always` (every dividend taken as extended) | the refutations (a missing `cqo`, a missing RDX zeroing), the Intel sweep |
| `cqo-zero` (`cqo`/`cdq` define RDX as 0) | owner fixtures, O1-O3 |
| `div-swapped` (quotient and remainder swapped) | the refutations, owner fixtures, O1-O3 |
| `xor-reads` (no zeroing idiom) | the refutations, owner fixtures, O1-O3, determinism, the guard |
| `refuse-shared-targets` (the old refusal) | the shared-target test, the refutations, owner fixtures, determinism |
| `first-case-only` (a shared edge tests its first case) | the refutations (a shared case sent to the default) |
| `first-route-only` (a shared edge's literal is one route's) | owner fixtures, O1-O3 |
| `table-any-index` (a table reaches a target at any index) | the refutations (two entries swapped) |
| `table-index-shift` (the index read one too high) | owner fixtures, O1-O3 |
| `dispatch-unrecognized` (no dispatch block) | the refutations, owner fixtures, the machine shapes, determinism |
| `pair-always` (a division restated as the source's even where the operands differ) | the refutations (the dividend from another register) |
| `pow2-division-shift` (a division by 2^k spelled as a shift by k + 1) | the spelling sweep, owner fixtures (`UdivPow2` refuted), O1-O3 |
| `pow2-product-shift` (a `mul` by 2^j's high half shifted one bit short) | the spelling sweep, owner fixtures (`UdivPow2` refuted), O1-O3 |
| `selector-64-bit-copy` (the selector's former 64-bit copy) | owner fixtures (`JumpTableHoles`, `JumpTableOffset` refuted), O1-O3, the refutations |

## The selector's 32-bit jump-table selector

The theorem refuted the selector's dispatch of a `u32`/`i32` selector: a
64-bit `mov` of the selector's `Gpr32` vreg into the 64-bit bound check
and index, whose bits above 31 the instruction-selection stream does not
define (slice 15's mixed-width rule). The selector now copies it with the
zero-extending `mov r32, r32` (`emit_x86_jump_table`, ruling OD-181); a
narrower selector was already zero-extended, a 64-bit one is unchanged.
This hardens the stream the theorem judges; it fixes no observed
miscompile. `tests/e2e_x86_64_jump_table_selector_width.rs` runs both
forms natively: for a `u32` argument with RDI's high half set and for
`match x as u32` on a `u64` with high bits set, the former form also
returns the right value in every case (`S14_FORMER_U32_DISPATCH
wrong_with_stray_bits=[]`, `TRUNC_FORMER_U32_DISPATCH
wrong_with_high_bits=[]`; payload `native_full.log`): downstream stages
leave those bits clear in both contexts. Only the current form is
asserted.

## Gates

After merging `main` `49b93b2ee` (slice 12 landed; trust-ir `cf33f748`), at
`a6ea60400`, through the x86-stage1-ay12713 overlay (`targo --unverified`,
no proof claim about the build), AY build 12713 and Clean 5f09e36c,
niced, `-j2`; payloads in `scratch14/payloads2/` (the pre-merge runs, with
the same results, are in `scratch14/payloads/`):

| Gate | Result |
| --- | --- |
| the slice-14 golden after the merge | unchanged: SHA-256 `6f1e3a64…` (payload `golden.log`) |
| verify library `x86_source_bound_body` without the replays (`--skip _qualification`): every slice's fixtures, goldens, controls and the matrix | 250 passed, 1 ignored (payload `lib_body.log`); every other slice's golden digest unchanged |
| `x86_source_bound_body::tests::slice14_qualification::` with AY and Clean | 2 passed, 1 ignored: 26 of 28 certify, the 2 recorded gaps, 24 of 24 refutations (payload `qualification.log`) |
| the 22 rule mutants over `slice14::` | each fails, the unmutated run passes (payload `mutants.txt`) |
| lowering library (the selector change and its unit test) | 2038 passed (payload `libs_lower.log`) |
| codegen `e2e_x86_64_jump_table_selector_width` (native) | 2 passed (payload `native_full.log`) |
| codegen `x86_source_bound_body` end to end and `must_refuse_corpus`, with the overlay pair | 5 passed; 5 passed (payload `codegen_e2e.log`) |
| CLI `must_refuse_corpus` | 1 passed (payload `cli_must_refuse.log`) |
| codegen library | 4731 passed, 2 failed, 1 ignored (payload `libs_codegen.log`). Both failures are `main`'s at `49b93b2ee`, not this branch's: `compiler::tests::x86_trap_only_body_certifies_and_argument_shims_are_judged_by_their_body_theorem` (trust-ir admission: "global 'shim_msg_local': const type mismatch: expected i64, got bytes[8]") and `wasm::lower::tests::refuses_an_out_of_range_bool_constant` ("const type mismatch: expected bool, got int"); the branch leaves both test files and `Cargo.lock` byte-identical to `49b93b2ee` |
| every workspace library and test target type-checked (`check --workspace --lib --tests --keep-going`) | only the three known kernel-JIT fixture refusals (`e2e_defeq_cache`, `e2e_lazy_delta`, `e2e_phase_completion`: "kernel JIT fixtures require exact Rust 1.95.0, Rust 1.97.1, or the certified Trust compiler"; payload `check_workspace.log`) |
| `scripts/test_soundness_check.sh` (the new `slice14::` row) | 102 passed (payload `test_soundness_check.log`) |
| `bash scripts/check_fmt.sh`, `python3 scripts/check_documentation.py --check` | OK; OK |
| `scripts/check_tippy.sh` | not run: the lint tool is unavailable on this host (the managed package's `tippy` stops before linting every package, and the stage-1 build has none) |

Not run: the other slices' AY qualification tests (their queries are byte
for byte unchanged, the goldens above), a robustness (mutation) probe
over many streams, and a census of a slice-14 bridge (slice 12 has
landed; the census runs before this branch lands).

## The 71 class functions under the slice-14 owner

The probe (`--dump`, the AOT selection of each function from
`runs/core-ir-s9`, then the owner; `census/dump_classes.py` groups the
verdicts) over the 71, with the slice-12 owner first (all 71 refused in
their class) and then this branch's:

| Class | Functions | Theorem built | Still refused |
| --- | ---: | ---: | --- |
| `GuardDivZero` | 13 | 12 | 1: the guard of an `i128` divisor |
| `Sdiv` | 3 | 1 | 2: an `i128` division (the selector's runtime-library call) |
| `Udiv` | 15 | 8 | 7: an `i128` division |
| `Urem` | 4 | 4 | 0 |
| jump tables | 21 | 19 | 2: over the 512-row cap (548, 552 rows) |
| shared `Switch` targets | 15 | 0 | 10 over the 512-row cap; 2 an `i128` loop-carried value (`parse_long_mantissa`); 2 over the source instruction cap; 1 the search tree's synthetic blocks (`escape_default`) |

None of the 44 theorems is refuted on the sampler's structured inputs.
Replayed offline on AY build 12713 and Clean (`census/replay_dir.py`, one
worker, each query's own 30 s deadline; payload `probe_replay_final.tsv`),
35 certify: all 19 jump-table functions, the 8 `Udiv` ones, 2 of the 4
`Urem` and 6 of the 12 guard functions: the 5 `offset_from_unsigned` by
a power-of-two `size_of::<T>()` (1, 2, 4, 16, 16 bytes) and
`as_chunks_unchecked::<_, 4>`; 5 of these certify through the power-of-two
spelling and timed out before it. The 9 others
fall in known solver-capacity classes, every division in them paired
(`pair_divisions`): 4 divide by a constant other than a power of two
through the magic-number multiply (the 2 `int_log10`, `Duration`'s
`Debug`, `offset_from_unsigned` of the 24-byte `fmt::Part`; `unknown`,
timeout), the class of the two recorded fixture gaps; 3 carry 64-bit
multiplies, slice 10's `MulU64` class (`rotate_left`, `align_offset`,
`flt2dec`'s `cached_power`; timeout); and the 2 `align_to_offsets`, also
with multiplies, end in AY's strict self-check rejection after 0.3 s (no
proof for Clean, no credit).
Several "guard" functions guard a division by a constant (`size_of::<T>()`
in `offset_from_unsigned`): such a guard never fires and adds no stop, and
the selector's magic multiply has no `div`. The theorems' AY replay is
below.

## Open findings and soundness notes

- The two divisions by a constant other than a power of two are recorded
  gaps: the selector's magic-number multiply is stated exactly and the
  qualified AY cannot certify it. A census of a slice-14 bridge will show
  the same class in `core` (`int_log10`, `Duration`'s `Debug`, a 24-byte
  `offset_from_unsigned`).
- The division pairing and the unit-divisor and power-of-two spellings
  change no meaning: each is an identity (the pairing's by construction,
  the others swept by unit tests), and every refutation stays refuted with
  an AY counterexample. Their only purpose is the solver's reach.
- The stop premise keeps the claims before an undefined division, which is
  stronger than trust-ir's `behaviour_refines` (an undefined run
  constrains nothing): a lowering that moves an event past a division that
  is undefined would be refuted though trust-ir allows it. Fail-closed.
- A guard's carrier is checked at the stream before the pipeline expands
  it; the expansion itself (`test d, d; je -> ud2` at the register's
  width) is the guard-carrier canary's, not this theorem's.
- The jump table's bytes are trusted to be the codegen's emission of the
  pre-RA table (`jt_fixups`); the theorem reads the targets from that
  table.
- Several certified shapes use 4 to 8 s of the 30 s budget; on a loaded
  host their credit can fall back to a replay gap (never to a wrong
  verdict).

