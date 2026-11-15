# Darwin x86-64 `library/core` — slice 21 (floating point as paired events, and the three atomics), 2026-10-26

Slice 21 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) admits the twelve
census roots that stop at a floating-point operation or at one of the three
remaining atomics, as designed and measured in `~/tcg-scratch/s21-design/`
(README §1-§7, `data/tables.md`): nine floating-point roots (`<f32/f64 as
Mul/Div>` x4, `GeneralFormat::already_rounded_value_should_use_exponential`
x2, `Lemire::from_u64` x2, `pow2_to_pow10`) and three atomics
(`atomic_load::<i128>`, `atomic_load::<u128>`, `atomic_store::<*const
OsFunctions>`).

| Ruling | Rule | Design |
| --- | --- | --- |
| OD-198 | rounding operations are paired IEEE 754 events (supersedes OD-73 for them); compares exact | §5.1, OD-TBD-a |
| OD-199 | LIR `FcvtToInt { dst_ty: I64 }` means the saturating conversion | §3.1, OD-TBD-b |
| OD-200 | an FP-abstract theorem's satisfying model is no counterexample | §5.1 "Verdicts", OD-TBD-c |
| OD-201 | the `I128` atomic load and the atomic exchange, single-threaded (extends OD-83) | §4, §5.2, OD-TBD-d |

Host: the shared x86_64 Mac (4 cores, Darwin 22.6, i7-7920HQ), 1-minute load
1.7-3.3 during the measurements; every build through `scripts/trust_cargo.sh`
with the local overlay `x86-stage1-ay13556` (`targo --unverified`, `nice -n
19`, `-j2`; no proof claim about any build). Replayer pair: AY 0.27.0 build
13556 with Clean 5f09e36c (`QUALIFIED_AY`, the overlay's `bin/ay` and
`bin/clean`). Branch `feat/x86-body-slice21` (worktree `~/tcg-scratch/wt-s21`)
from origin/main `c4885af82` (slices 1-20 and the canonical spelling,
OD-187..189 and OD-195..197); origin/main did not move during the lane.
Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md) binds each by size and
SHA-256.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-c4885af82-ay13556` (baseline) | `main` `c4885af82` | 13556 | `fc5b5349…` | 48 | 1108 s |
| `core-x86_64-darwin-O0-proof-slice21-ay13556` | this branch, `401db9e46` (slice 21 on `c4885af82`) | 13556 | `87407a8d…` | **36** | 1515 s |

**12 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
the 12 targets: `Fmul` 2, `Fdiv` 2, `Fcmp` 2, `FcvtFromUint` 2, `FcvtFromInt` 1
(`pow2_to_pow10`), the two `i128` atomic loads and the `AtomicRmw` exchange.
Both rows were built by `census13556.sh`, each bridge in its own tree, with
no resource-budget refusal.

## Soundness notes first

- **New trust, all stated in the rulings and LIMITATIONS:** the Intel SDM
  transcription of the SSE rounding rows, `ucomisd`'s flags and
  `cvttsd2si`'s indefinite (T1); MXCSR's default control state `0x1F80`
  whenever a body runs (T3: code that changes MXCSR voids every FP theorem);
  trust-ir's meaning of the admitted FP operations (T2); the frame's save
  and restore of RBX around a body with the `cmpxchg16b` pseudo (T4); the
  writability of the 16 bytes an `I128` atomic load reads (T5); the
  single-threaded meaning of the two pseudo rows (T6).
- **T5 is an across-levels argument, flagged.** trust-ir has no read-only
  memory at all (its interpreter reads no rule from a `Global`'s `mutable`
  flag), so a trust-ir `AtomicLoad I128` of read-only memory is defined
  there while the machine faults. The admission rests on Rust's rule that
  such a load is undefined behaviour (cited below), i.e. on the program's
  producer being Rust. The lane's plain incoming stores already rested,
  unstated, on the same writability (a store to an immutable global, which
  the backend emits read-only, faults where trust-ir's interpreter writes);
  LIMITATIONS now says so. A trust-ir rule making a write or an `I128`
  atomic load of read-only memory undefined would remove both.
- **Found on the way, not fixed (outside the slice):** none beyond the
  design's §7 (the bridge's raw `fptosi`, which `5d732f441` already fixed).
- **OD-200's flag is the owner's, not the query's.** A theorem whose
  spelling drops every FP leaf (a result both sides name alike, as in the
  swapped-`divsd` control) still claims its pairings' operands equal, a
  sufficient condition stronger than refinement: its refutation (AY's
  model `+0 / 2^-1074` against `2^-1074 / +0`) is no counterexample by
  itself. The first implementation keyed OD-200 on FP-leaf input names and
  the library gate caught it; the rule now keys on the owner
  (`SourceBoundX86Body::is_fp_abstract`: any source rounding event or
  machine rounding row).

## In short

- **Every earlier golden theorem is unchanged** (the solver-free body
  suite: every slice's digest-pinned golden passes byte for byte). The
  slice-21 golden is new: 35 fixtures, 0 `=>`.
- **The 12 roots** (§4): through the real builder (this branch's owner over
  the census-s20 bridge's `core` dump), all 12 build a theorem, and all 12
  certify offline on the qualification pair at the 30 s deadline, AY 0.1-0.8
  s each, every certificate `unproved_steps=0 trust_free=yes` and Clean
  `verification: PASSED`.
- **Qualification** (§3): all three slice-21 lanes pass, one test per
  process: 35 of 35 fixture theorems and the 5 theorems and parts of the
  loop and cut-point fixtures certify (0.1-1.2 s); the five pure
  bit-vector controls are AY counterexamples; the four FP-abstract controls
  are satisfiable (AY models of their negations) and leave every covered row
  uncredited, none failed by the theorem; every covered row of every fixture
  is credited Formal by the production verifier.
- **Controls** (§1): 16 wrong lowerings as unit fixtures; **fails-before**:
  16 rule mutants, each failing a control (the unmutated run passes 9 of 9).
- **21b decision** (§2): the `I128` loads are **admitted**, with T4 (the
  RBX restore cannot be checked by the walk) and T5 (Rust's cited UB)
  stated in OD-201; the exchange is admitted.

## 1. The rules: claim, checked, trusted, controls, fails-before

The library gate is `x86_source_bound_body::tests::slice21::` (solver-free;
it runs in the full x86 body suite). The tool-gated lanes are
`slice21_qualification::`. Mutants: `fails-before/mutate.py` guards each rule
behind `TCG_S21_MUTANT=<name>`; one test build serves all of them, and
`fails-before/run_mutants.sh` runs the slice-21 library tests and the OD-200
classification control once per mutant.

### OD-198: rounding operations as paired events (21a)

**Claim.** LIR `Fadd`, `Fsub`, `Fmul`, `Fdiv` of two `F32`/`F64` patterns,
`FcvtFromInt`/`FcvtFromUint` of an `I64` to an `F32`/`F64`, and the
in-range value of `FcvtToInt` of an `F64` to an `I64` are EVENTS of the
world trace (`SourceFloat`, `SourceEvent::Float`). The machine row of the
same operator key (`FloatKey`: operation, format, rounding direction;
`machine_float_key`: `addsd`..`divss`, `cvtsi2sd`/`cvtsi2ss r64`, `cvttsd2si`,
`cvtsd2si`) pairs with the source's next event when its TV-1 stamp names the
event's LIR instruction. Paired, the theorem observes the row's operands
against the event's (items, as a call's arguments; an `FcvtFromUint`'s
operand's bit 63 against `#b0` as one more item), and both sides read the
result as the event's FP leaf `fe{k}`. A rounding row no event pairs (the
u64 sequence's `cvtsi2sd(h)` and `addsd`) gets an FP leaf of its own
(`fu{k}`/`fw{k}`); a source event no row pairs refuses (the trace ends
short). `Fcmp` (all 14 LIR conditions) and `ucomisd`/`ucomiss`'s ZF, PF, CF
(OF, SF cleared) are exact over the bits (`FloatRelation`, with
`fp_bv_lowering::Masks`' `nan`/`key`/`ordered`). No implication is spelled
`=>`. Narrower conversions, `Fsqrt`, `Fma`, `Fmin`/`Fmax`, rounding,
`FPExt`/`FPTrunc`, `FcvtToUint` and an `F32` source of `FcvtToInt` are refused
by name. The theorem claims refinement: for every value of the leaves the
machine's observables equal the source's; instantiated with x86's own
results it is a source run trust-ir permits. No NaN payload is ever claimed.

**Checked** (by the replayed proof): every pairing's operand patterns, every
compare, flag read, saturation and selection, the claimed top bit. **By the
walk** (only choose): keys, stamps, order. **Trusted:** T1, T2, T3.

| Control | Kind |
| --- | --- |
| 35 fixtures: `Fmul`/`Fdiv` x `f32`/`f64` (the roots' shapes, `Fmul`'s unread third parameter included), `Fadd`, `Fsub`, `(a*b)/(a+b)` (three events), the 12 trust-ir compares at `f64` and `une`/`olt`/`oge` at `f32`, the two `already_rounded_value_should_use_exponential` shapes (a load, a call to `abs`, three compares over a DAG with a join), `pow2_to_pow10`, `f64 as i64`, `i64 as f64`/`f32`, the two `Lemire::from_u64` shapes, the five atomics | every one holds on samples and certifies (0.1-1.2 s) |
| `the_float_compare_and_conversion_meanings_are_trust_irs`: every trust-ir `FCmp` at `f32` and `f64` (its LIR condition read from the real adapter's output) against `FloatRelation::holds`, on 15 x 15 and 23 x 23 patterns (zeros of both signs, subnormals, normals, the bounds, infinities, quiet and signalling NaNs) | equal to the pinned interpreter |
| `the_sse_compare_and_truncation_rows_are_the_hosts`: `ucomisd`/`ucomiss` (15 x 15 and 6 x 5 patterns) and `cvttsd2si` run on this CPU against the stated flags and indefinite; `stmxcsr` | equal; MXCSR's control bits `0x1f80` |
| `fmul64/mulss` (format), `fmul64/divsd` (operation), `fmul64/stamped-elsewhere` (the row's stamp names another instruction) | refused by name: the event has no partner |
| `fdiv64/swapped` | uncredited (OD-200): AY's model `e_xmm0 = +0`, `e_xmm1 = 2^-1074` |
| `une64/no-setp`, `olt64/no-setnp`, `oge64/seta` | AY counterexamples (a NaN; a NaN; equal zeros) |
| `u2f64/signed-only` (`u64 as f64` as the signed `cvtsi2sd` alone) | uncredited (OD-200): AY's model `e_rdi = 2^64 - 1` |
| `U64ToF64` variant (the selector's correct unbounded round-to-odd halving) | stated; satisfiable (its pairing claims bit 63 clear): an incompleteness, never a refutation |
| `region_fixtures`: an `fmul` inside a loop (an `f64` loop-carried value, slice 12's regions) and an `fmul`, a call and an `fdiv` across a block boundary, each as the production owner states it and cut at every block (slice 16's parts) | stated, holding on samples; on the pair all 5 theorems and parts certify (0.07-0.16 s) |

| Mutant | Fails |
| --- | --- |
| `key-no-format` (every SSE arithmetic row keyed binary64) | `fmul64/mulss` certifies; `FmulF32` refused |
| `key-no-operation` | `fmul64/divsd` certifies |
| `key-no-rounding` | `pow2/cvtsd2si` certifies |
| `no-operand-claims` | `fdiv64/swapped` holds |
| `uint-no-top-bit` | `u2f64/signed-only` holds |
| `stamp-ignored` | `fmul64/stamped-elsewhere` builds a theorem |
| `ucomis-pf-zero` | the compare fixtures are refuted; the host-hardware check fails |
| `fcmp-olt-as-ult` | `olt64/no-setnp` holds; `Fcmp64(OLt)` refuted; the interpreter check fails |
| `cvtt-saturating` (out of range saturating, not the indefinite) | `f64toi64/cmova` holds |

### OD-199: the saturating conversion

**Claim.** LIR `FcvtToInt { dst_ty: I64 }` of an `F64` is NaN to 0, `>=
2^63` to `i64::MAX`, `< -2^63` to `i64::MIN`, else the truncation event's
leaf (`saturating_f64_to_i64`): exactly trust-ir `FPToSISat` (the bridge's
since `5d732f441`) and a refinement of `FPToSI`, which the adapter maps to
the same opcode. `cvttsd2si` is the leaf where the value fits
(`f64_fits_i64`) and `0x8000_0000_0000_0000` elsewhere; the selector's
`ucomisd`/`cmovae MAX`, `cmovb MIN`, `cmovp 0` are walked exactly. **Trusted
in addition:** nothing.

| Control | Kind |
| --- | --- |
| `F64ToI64` (a free `f64`: NaN reaches it), `Pow2ToPow10` | certified |
| the interpreter check: `FPToSISat` equal on every pattern; `FPToSI` equal wherever defined, undefined exactly where `f64_fits_i64` fails | passes |
| `f64toi64/no-cmovp` (NaN reaches `MIN`), `f64toi64/cmova` (misses `2^63`) | uncredited (OD-200); AY's models are the real failing inputs (`e_xmm0` all ones; `0x43e0_0000_0000_0000`) |

| Mutant | Fails |
| --- | --- |
| `saturation-dropped` (`fptosi`'s event alone) | `Pow2ToPow10` refuted |

### OD-200: an abstract theorem's satisfying model

**Claim.** `x86_body_row_result(obligation, verdict, fp_abstract)`: an
`Invalid` verdict of an FP-abstract theorem leaves every covered row
`Unverified` with `X86_BODY_FP_ABSTRACT_SAT` (uncredited, never failed);
`x86_body_replay_trace` prints `Unknown (FP abstraction: a satisfying model is
no counterexample)`. A `Valid` verdict credits; a pure bit-vector theorem
keeps its refutations. No concrete replay of a model is run, so no
FP-abstract theorem is ever reported refuted (fail-closed: a real
miscompile such as `u2f64/signed-only` is uncredited and the proof-required
compile refused, not named). **Trusted in addition:** nothing.

| Control | Kind |
| --- | --- |
| `an_fp_abstract_refutation_is_uncredited_and_never_reported_refuted` | the mapping both ways |
| the qualification credit lane over the four abstract controls | every covered row uncredited, none failed by the theorem |

| Mutant | Fails |
| --- | --- |
| `fp-abstract-never` | the controls lane (`fdiv64/swapped`), `owner_builds_...`, the variants |

### OD-201: the `I128` atomic load and the exchange (21b)

**Claim.** An `I128` `AtomicLoad` (any load ordering, a non-private address)
is its two 8-byte halves (`AtomicPseudo::Cmpxchg16b`), paired only with one
`AtomicLoadCmpxchg16b [m]` row: RAX the low half, RDX the high, RCX and RBX
zero, memory unchanged. `AtomicRmw { op: Xchg }` of an `I32`/`I64` (any
ordering, a non-private, non-derived address) is an incoming load of the old
bytes and a store of the operand at one address (`AtomicPseudo::Exchange`),
paired only with the `AtomicRmwCasLoop [dst, src, [m], 5]` row: `dst` and
RAX the old bytes, R10 the operand (32-bit forms zero-extend). Each pseudo is
one row of two events; a pseudo-lowered access never pairs with a `mov`, nor
a pseudo with any other access. **Trusted:** T4, T5, T6 (§2).

| Control | Kind |
| --- | --- |
| `AtomicLoadU128`, `AtomicLoadI128Twice` (Relaxed and Acquire, xored), `AtomicXchgU64`, `AtomicXchgU32` (AcqRel), `AtomicStoreSeqCst` (the exchange's result unused) | certified |
| `xchg64/returns-new` (`mov dst, src` after the pseudo), `ld128/halves-swapped` | AY counterexamples |
| `ld128/plain-atomic-movs`, `ld128/pseudo-for-plain-load`, `xchg64/plain-store` | refused by name |
| `only_the_cmpxchg16b_pseudo_may_write_rbx` (any other RBX write) | `PreservedWrite` mismatch |
| variants: an `I128` atomic store, `atomic_add` | refused by name |

| Mutant | Fails |
| --- | --- |
| `cmpxchg16b-halves-swapped` | `ld128/halves-swapped` holds; `AtomicLoadU128` refuted |
| `rbx-refused` | the `I128` fixtures and the RBX control |
| `cas-result-from-r10` | `AtomicXchgU64` refuted |
| `pseudo-pairs-plain` | `ld128/plain-atomic-movs` builds a theorem |
| `pseudo-any-access` | `ld128/pseudo-for-plain-load` builds a theorem |

The table rows are the mutant run's (`fails-before/run_mutants.sh` on one
mutated build of `a2ebd562b`; the unmutated run 9 of 9).

## 2. The 21b decision: the `I128` loads are admitted

- **RBX (T4): judged not checkable here, trusted.** The walk's subject is
  the pre-RA stream; the prologue's save of RBX and the epilogue's restore
  are emitted after register allocation
  (`x86_merge_fixed_callee_saved_gpr_defs` adds every fixed callee-saved
  definition, the pseudo's implicit RBX def among them, to the save set),
  so their rows are not in the stream the walk could verify. The theorem
  already rests on the same frame for every callee-saved register the
  allocator assigns (module docs: "the frame ... covered only by the
  TV-4/TV-5/ENC-3 validators"), and TV-5 leaves callee-saved restores out of
  scope. The walk records only the pseudo's RBX write as the frame-restored
  clobber; any other RBX write stays `PreservedWrite`. Evidence (testing,
  never credit): `e2e_x86_64_atomics`' `test_x86_64_atomic_load_u128_cmpxchg16b`
  calls the compiled `u128` atomic load from an assembly `rbx_probe` holding
  a sentinel in RBX at O0, O2 and O3 (§5).
- **Writable memory (T5): a cited Rust UB, trusted.** The pseudo writes the
  16 bytes back and faults on a read-only page where a plain load reads
  (the design's hardware probe). Rust: "In general, *all* atomic accesses on
  read-only memory are undefined behavior ... even a `load` can fault on
  read-only memory", with "sufficiently small" Relaxed loads excepted, 8
  bytes on `x86_64` (`library/core/src/sync/atomic.rs`, "Atomic accesses to
  read-only memory", lines 160-192 of the Trust toolchain source at
  `~/trust` `d7f143f3be`, the commit the overlay's trustc reports). trust-ir is silent (see the
  soundness notes). A misaligned `I128` atomic is trust-ir's own undefined
  behaviour (natural alignment 16).
- **The exchange** needs neither: R10 and RAX are caller-saved, and its
  store is part of trust-ir's `AtomicRMW` meaning too, so it rests on no
  writability beyond the one every plain incoming store already does.

## 3. Qualification

`census/qualify.sh` ran each lane in a process of its own on the overlay pair
(`TCG_X86_BODY_QUALIFY_AY` and `TCG_EXTERNAL_CLEAN_CHECKER` its `bin/ay` and
`bin/clean`), at 1-minute loads 1.97-3.44 (payloads `qual1/` to
`qual4/`):

| Run | Code | Outcome |
| --- | --- | --- |
| 1 | `a2ebd562b`'s owner, before the credit lane's control check was relaxed | the replay lane and the controls lane pass; the credit lane credits every fixture row and stops at `u2f64/signed-only`, whose `cvtsi2sd` TV-2 fails (it carries the digest of the signed conversion it was selected from) |
| 2 | the credit lane counts only the theorem's verdicts on a control | passes |
| 3 | the final owner (`a2ebd562b`) | all three lanes pass |
| 4 | the replay lane also replays the region fixtures' 5 theorems and parts | all three lanes pass |

Fixture replay times (run 1, ms): `FmulF64` 95, `FmulF32` 224, `FdivF64` 69,
`FmaChainF64` 91, the `f64` compares 147-1196, the `f32` compares 154-730,
`ShouldUseExponential64`/`32` 856/474, `Pow2ToPow10` 504, `F64ToI64` 489,
`I64ToF64`/`F32` 68/83, `U64ToF64Bounded`/`F32` 220/197, the atomics 73-188
(`FdivF32`, `FaddF64` and `FsubF32` are byte-identical theorems to earlier
ones, answered by the session memo). `KNOWN_UNCERTIFIED_SLICE_TWENTY_ONE` is
empty.

## 4. The 12 roots

`probe/x86_body_probe.rs` is slice 20's probe with an `FP-ABSTRACT` mark,
built from this branch as an example; `probe/run_probe.sh` runs its `--cf`
mode over the census-s20 bridge's `core` dump (`runs/core-ir-s20`, the
design's), restricted to `s21-design/data/names12.txt`. That dump predates
`5d732f441`, so `pow2_to_pow10`'s trust-ir conversion is `FPToSI` there and
`FPToSISat` on main; both are LIR `FcvtToInt { dst_ty: I64 }`, so the LIR, the
machine rows and the theorem are the same (OD-199). `census/replay_roots.sh`
replayed each root's one query on the pair at the 30 s deadline
(`census/replay_one.py`: strict Alethe one-shot, then Clean):

| Root | Bound rows | FP-abstract | AY wall | Proof | Clean |
| --- | ---: | :---: | ---: | ---: | --- |
| `<f64 as Mul>::mul` (cgu.0.2671) | 5 | yes | 0.1 s | 6 KB | PASSED |
| `<f32 as Mul>::mul` (2670) | 5 | yes | 0.2 s | 135 KB | PASSED |
| `<f64 as Div>::div` (2676) | 4 | yes | 0.1 s | 5 KB | PASSED |
| `<f32 as Div>::div` (2675) | 4 | yes | 0.2 s | 135 KB | PASSED |
| `GeneralFormat<f64>::already_rounded_value_should_use_exponential` | 34 | no | 0.8 s | 1.4 MB | PASSED |
| `GeneralFormat<f32>::...` | 34 | no | 0.4 s | 0.9 MB | PASSED |
| `Lemire<f64>::from_u64` (3104) | 58 | yes | 0.1 s | 0.5 MB | PASSED |
| `Lemire<f32>::from_u64` (2368) | 58 | yes | 0.1 s | 0.4 MB | PASSED |
| `pow2_to_pow10` | 17 | yes | 0.3 s | 0.8 MB | PASSED |
| `atomic_load::<i128>` | 211 | no | 0.4 s | 2.0 MB | PASSED |
| `atomic_load::<u128>` | 211 | no | 0.4 s | 2.0 MB | PASSED |
| `atomic_store::<*const OsFunctions>` | 198 | no | 0.3 s | 0.1 MB | PASSED |

**12 of 12 build and certify.** The probe's own sampler printed
`REFUTED-AT-SAMPLE 18446744073709551615` for the two `atomic_load::<i128>`
roots: that value is the sampler's "cannot evaluate" mark (a 128-bit
definition, the `I128` join of the three ordering arms, which its `u64`
evaluator cannot hold), not a refutation; AY proves both. The census itself
(`~/tcg-scratch/census13556.sh`) is the coordinator's.

## 5. Gates

| Gate | Result |
| --- | --- |
| the solver-free x86 body suite (`x86_source_bound_body::tests::`, every library test but the tool-gated lanes) | 384 passed, 0 failed, 17 ignored on the final code (`logs/gate3.log`); 383 on the final owner before the region fixtures' test (`gate2.log`); the run before the golden's digest was pinned: 382 passed, the digest assertion the 1 failure (`gate1.log`) |
| `trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus` (the body lane gains eight slice-21 functions: an `f64` product, an `f32` quotient, `une`, `f64 as i64`, `i64 as f64`, `pow2_to_pow10`, the exchange, the `u128` atomic load) | 5 passed and 5 passed; the body lane replayed on AY 13556 (`codegen1.identity.log`) and promoted every listed function, the eight slice-21 ones among them, Formal on both triples |
| `trust-cg-codegen --test e2e_x86_64_atomics` (native; the RBX probe) | 10 passed, 1 failed: `test_x86_64_atomic_cmpxchg`, whose fixture builds `cmpxchg` with one result where the pinned trust-ir requires two (`InstrResultArityMismatch` at trust-ir validation, `stage: Received`, before any lowering: not this slice's); the RBX probe (`test_x86_64_atomic_load_u128_cmpxchg16b`, O0/O2/O3) and `test_x86_64_atomic_rmw_xchg` pass |
| `trust-cg-lower --lib` | 2113 passed |
| `scripts/check_fmt.sh` (the 6808 package's `targo fmt`) | OK |
| `python3 scripts/check_documentation.py --check` | OK |
| `python3 scripts/full_test_matrix_hosts.py --check` | OK (the slice-21 printer is in `IGNORED_TESTS`) |
| `scripts/check_tippy.sh` (not in the lane's gate list) | not run: the overlay's targo has no `tippy`, and the 6808 package's cannot resolve the workspace (`ay-pb`, `compiler_timeout_secs`; `tippy.log`) |

## 6. Reproducers (this directory)

| File | What |
| --- | --- |
| `fails-before/mutate.py`, `fails-before/run_mutants.sh` | the 16 rule mutants and their run |
| `census/qualify.sh` | one tool-gated test per process on the qualification pair |
| `probe/x86_body_probe.rs`, `probe/run_probe.sh` | the probe (place it in `crates/trust-cg-verify/examples/`) and its run over the 12 roots |
| `census/replay_roots.sh`, `census/replay_one.py` | the 12 roots' offline replay |
| `census/payloads.py` | the PAYLOADS.md table |
