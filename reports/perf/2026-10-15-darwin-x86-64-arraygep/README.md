# Darwin x86-64 `library/core` — `ArrayGep` in the x86-64 body theorem (OD-185, OD-186), 2026-10-15

Main's census of the Darwin x86-64 `core` proof lane rose from slice 14's 342
failed roots to 813 at main `2854ce3e3` (`~/tcg-scratch/runs/census-s14`,
`~/tcg-scratch/runs/census-main-2854ce`). This record holds the cause, the
rulings that admit it (OD-185 and OD-186 in
`docs/decision-record.md`), their
soundness argument, controls, fails-before evidence, host qualification and
the measured outcome. Owner:
`crates/trust-cg-verify/src/x86_source_bound_body.rs`; fixtures and controls
in `x86_source_bound_body_arraygep_tests.rs` (solver-free gate
`x86_source_bound_body::tests::arraygep::`) and
`x86_source_bound_body_arraygep_qualification_tests.rs` (tool-gated). Branch
`fix/x86-body-arraygep`, from slice 16 (`feat/x86-body-slice16-size`,
`946b2fd77`). Host: the shared 4-core x86_64 Mac; builds through
`scripts/trust_cargo.sh` with the `x86-stage1-ay12713` overlay's `targo
--unverified` (no proof claim about any build), `nice -n 19`, `-j2`,
`CARGO_INCREMENTAL=0`; AY 0.27.0 build 12713 with Clean 5f09e36c (the pair
`QUALIFIED_AY` pins).

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-cb390e657-ay12713` (baseline) | `main` `cb390e657` | 12713 | `e0f2f9a8…` | 743 | 4426 s |
| `core-x86_64-darwin-O0-proof-arraygep-ay12713` | this branch, `d12c627fb` (OD-185/186 on `cb390e657`) | 12713 | `8de8c7b8…` | **235** | 7255 s |

**508 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
394 functions main refused at `ArrayGep`, 112 at an inconsistent type hint
(OD-186) and 2 at a machine row of the selector's `ArrayGep` lowering now
replay Valid. Both rows were built by `census12713.sh`, each
bridge in its own tree, one after the other, with no resource-budget refusal.

## 1. The cause

`newly_failing.py` lists the functions census-s14's body trace credits
(`replay=Valid`) and main's does not: **476**, one per newly failing root.
Main's refusal of them:

| main `2854ce3e3` refusal | functions |
| --- | ---: |
| `ArrayGep { elem_ty: I64 }` outside the body domain | 198 |
| `ArrayGep { elem_ty: I32 }` | 89 |
| `ArrayGep { elem_ty: I8 }` | 41 |
| `ArrayGep { elem_ty: I16 }` | 24 |
| `ArrayGep { elem_ty: I128 }` | 2 |
| `inconsistent type hint for Value(N)` | 109 |
| other (9 AY timeouts or their negative memo, 3 past 512 rows, 1 machine row) | 13 |

**Which side refused:** the SOURCE side. `admit_blocks` had no arm for LIR
`ArrayGep`; the machine side already modelled `LeaSib` over two registers
exactly (`base + index*scale + disp`, 64-bit, wrapping), and the earlier
observation that "the x86 body lane refuses" `extract_element`'s `LeaSib` was
the source refusal. What the machine side lacked is the selector's rows for
an `ArrayGep` of a PRIVATE slot (a scaled `lea` of a frame register, an
`imul` of a constant index).

With `ArrayGep` admitted, the probe on a fresh dump of main's bridge
(`~/tcg-scratch/runs/core-ir-2854ce`) showed **344 of the 476 stopping at one
second class**, the "type hint" class, including 237 of the 354 `ArrayGep`
functions: a `StackAddr` whose sidecar type is a small array (`[u64; 1]` 182,
`[u32; 1]` 59, `[u32; 2]` 25, `[u8; 1]` 20, ...), filled by `Memmove` and
returned (227) or passed by value (117). It is the adapter's by-value copy
of an aggregate `Load` (`adapter.rs` `translate_load`); on the older dump of
main `a902ea9ef`'s bridge (`core-ir-s16`) the same functions return the
source slot directly. Slice 8 admits that meaning for a `Copy` of a slot
address so typed and states the rule for a slot address in general (the
hint check's comment), but only a `Copy` reached it. OD-186 admits it.

## 2. What is admitted, and why it is exact

**OD-185.** `ArrayGep { elem_ty }(base, index)` is `base + index *
size(elem_ty)` at 64 bits, wrapping.

- `size` is the element's natural-C size under the verify-owned `layout`
  (`array_element_stride`; the same layout `StructGep` uses), compared with
  the selector's `Type::bytes` by `the_verify_owned_stride_is_the_selectors_element_size`
  over scalars, padded structs, nested arrays and their combinations. That
  is the opcode's one meaning: LIR documents `base + index * sizeof(elem_ty)`
  with an `I64` index (`trust-cg-lower/src/instructions.rs`,
  `Opcode::ArrayGep`); the opcode carries a repr-less LIR type and the
  adapter emits it only where the natural-C stride is the authority, writing
  any other stride out as `Iadd(base, Imul(index, stride))`
  (`adapter.rs` `emit_array_element_ptr` with `explicit_element_stride`);
  and the selector resolves it only as `elem_ty.bytes()`
  (`x86_64_isel.rs` `select_array_gep`).
- The index is the `I64` value itself. The adapter extends a narrower
  trust-ir index before the opcode with an explicit `Uextend` (unsigned
  type) or `Sextend` (signed) (`map_gep_index`,
  `extend_index_to_i64_if_needed`), which the lane already models exactly
  (the selector's `MovRR32` and `Movsx`); the selector scales the index
  register as it is. An index of another LIR type is refused by name, as are
  an element type outside the layout model (an enum) and a zero-sized one.
- Over an incoming pointer, a symbol, a call result or an address derived
  from an escaped slot (OD-114) the element address is the value
  `SourceOp::ArrayElement`, spelled `bvadd b (bvmul i s)` (`bvadd b i` at
  size 1) by `array_element_address`, the one function that also spells the
  machine's `LeaSib`; loads and stores through it are incoming or derived
  accesses exactly as before.
- Over a private slot it is admitted only at an `I64` index that is a
  constant `k` of the chain: the slot address offset by `k * size`, the
  exact integer product and sum, overflow refused (the walks place private
  bytes by slot and offset; the 64-bit wrapping address equals that offset
  whenever it fits). Any other index keeps the refusal `offsets a private
  stack address by a non-constant amount (defined by ...)`, its text and
  class unchanged (slice 17's domain; `non_constant_offset` now serves both
  `Iadd` and `ArrayGep`, naming what defines the index).
- Machine side, the selector's rows (`select_array_gep`): `lea d, [b +
  i*s]` for sizes 1, 2, 4, 8; `lea d, [b + i*(s-1)]; add d, d, i` for 3, 5,
  9; `imul t, i, s; add d, b, t` otherwise. Added: a `LeaSib` whose base
  holds a private address and whose index the walk knows as a 64-bit
  constant is that address offset by `k*scale + disp` (overflow refused; any
  other index reads the address as bits: no claim); a 64-bit `ImulRRI` of a
  known constant is a constant; a `LeaSib` at a constant index has the
  exact affine value `base + k*scale + disp`. The source states an affine
  value for an element address only at a constant index or at size 1, so
  the solver-free refusal names a differing address only where both sides
  are exact.

**OD-186.** A `StackAddr` the LIR types as a by-value aggregate is that
aggregate (its bytes when returned or passed by value), as slice 8's `Copy`
of a slot address so typed already was: the selector defines a
`StackAddr`'s value at its hinted type (`select_stack_addr`, as
`select_move_reg` does for the call-argument `Copy`), so its System V
classifier passes the bytes and an aggregate return loads them. An element
or field address hinted as an aggregate stays refused: `select_struct_gep`
and `select_array_gep` define the result at `I64` whatever its hint, so the
machine passes it as a pointer. (The selector refuses a load or store
through an address typed as an aggregate, `require_memory_address_type`, so
such a source has no machine to judge.) Slice 7's control
`other_uses_of_an_escaped_address_stay_outside_the_domain` pinned the
refusal of a slot address hinted `[i64; 2]` and passed to a call (it named
27 `core` functions, rustc's small `Copy` aggregates passed by value); it
now checks that a hint that fits the slot passes the bytes
(`CallArg::Aggregate`, never an escaping address) and that a larger one is
refused by name (`passes an aggregate that extends past its slot`).

Every earlier slice's golden digest is unchanged (the whole x86 body gate,
goldens and the qualification matrix included, passes on the branch).

## 3. Fixtures and controls

Eighteen fixtures over real selector output (`ARRAY_GEP`): two-index loads
of `u64`/`u32`/`u16`/`u8` (scales 8, 4, 2, 1), a 3-byte element (`lea; add`),
a 12-byte element (`imul; add`), a store, `u32` and `i32` indices, a returned
address, constant indices, three private-slot shapes (`[u64; 4]`, `[[u8; 3];
4]`, `[[u32; 3]; 4]` at constant indices), a derived base, and the three
OD-186 shapes (a loaded `[u64; 2]` returned, a loaded `[u32; 2]` passed by
value, an element of a loaded `[u64; 2]`). Each builds a theorem that holds
on samples, covers every value row, and is in the golden snapshot
(`arraygep_snapshots.smt2`, digest pinned) and the qualification matrix's
`arraygep` family.

Wrong lowerings (`arraygep_refutations`), each refuted on samples and, on
the qualification host, with an AY counterexample (§5):

| control | what it does wrong |
| --- | --- |
| `LoadU64/wrong-element-size` | the first index scaled by 4 for an 8-byte element |
| `LoadStride3/wrong-element-size` | the 3-byte stride's `add` of the index dropped |
| `LoadStride12/wrong-element-size` | the 12-byte stride multiplied by 8 |
| `LoadU64/wrong-base` | the element address based at the index register |
| `IndexU32/missing-extension` | the `u32` index's zero extension dropped (the parameter's whole register) |
| `IndexI32/wrong-extension` | the `i32` index zero-extended instead of sign-extended |
| `LoadU64/off-by-one-element` | one element further |
| `Address/off-by-one-element` | the returned address one element further |
| `LoadU64/wrong-element-loaded` | the load through `p.gep[i]`, not `p.gep[i, j]` |
| `StoreU64/wrong-element-stored` | the store through `p.gep[i]` |
| `FrameU64/wrong-element-size` | a private element written at the half-scaled offset |
| `FrameU64/wrong-element-loaded` | private element 2 loaded where the source loads 1 |
| `FrameStride12/wrong-element-size` | a private 12-byte element at stride 8 |
| `Derived/wrong-element-loaded` | the derived load through `q.gep[i]` |
| `LoadedReturned/swapped-eightbytes` | (OD-186) the copy's eightbytes returned the other way round |
| `LoadedElement/wrong-element-loaded` | (OD-186) element 0 of the copy loaded |
| `LoadedPassed/short-copy` | (OD-186) the by-value copy made 4 bytes short |

Typed mismatches without a solver (`a_known_wrong_element_address_is_a_typed_mismatch`):
a constant index scaled by 4 and a size-1 element based at the index are
`MemoryAddress`. Named refusals: a private slot at a variable index (the
slice-17 text), an `I32` index, an enum and a zero-sized element, an offset
past `i64`, a private address as the index, a scaled `lea` of a frame
address at an unknown index, and an element address hinted as an aggregate.
The real optimizer at O1-O3 names no mismatch on any fixture.

## 4. Fails-before

`fails-before/mutate.py` guards each rule behind `TCG_AGEP_MUTANT=<name>` in
the working tree (one test build serves every mutant; the file is restored
with `git checkout` afterwards and never committed);
`fails-before/run_mutants.sh` runs the `arraygep` gate per mutant. On
`165816579` the unmutated build passes all 15 tests (one ignored diagnostic)
and every one of the 16 mutants fails at least one:

| mutant | rule disabled or weakened | failing tests |
| --- | --- | ---: |
| `source-refused` | the source value rule | 7 |
| `source-unscaled` | the stride dropped from the source address | 4 |
| `source-unindexed` | the index dropped from the source address | 4 |
| `source-affine-off` | the source's affine value | 1 (the typed mismatch) |
| `any-index-width` | the `I64` index rule | 1 (the named refusal) |
| `frame-refused` | a private base at a constant index | 11 |
| `frame-unscaled` | the private offset unscaled | 6 |
| `frame-wrapping` | the private offset's overflow refusal | 1 |
| `frame-variable-zero` | the slice-17 refusal (a variable index as offset 0) | 1 |
| `layout-unchecked` | the layout model and zero-size refusals | 2 |
| `machine-frame-off` | the machine's private scaled `lea` | 6 |
| `machine-frame-unscaled` | its scale | 4 |
| `machine-imul-fold-off` | the 64-bit `imul` constant fold | 5 |
| `machine-affine-off` | the scaled `lea`'s affine value | 1 (the typed mismatch) |
| `stackaddr-hint-off` | (OD-186) the `StackAddr` hint rule | 6 |
| `gep-hint-aggregate` | (OD-186) the hint taken on an element address too | 1 |

## 5. Host qualification

`qualify.sh`, one test per process, AY 0.27.0 build 12713 with Clean
5f09e36c through the `x86-stage1-ay12713` overlay, on the merged branch
(`7af6a5e35`, origin/main `84055afb5` merged):

- `host_qualification_replays_the_arraygep_body_theorems`: **all 18
  fixtures `Verified`** (88 ms to 1.0 s each) and **all 17 wrong lowerings
  refuted with an AY counterexample** (log `~/tcg-scratch/agep/qual2.log`,
  queries `~/tcg-scratch/agep/qdump2/`). `KNOWN_UNCERTIFIED_ARRAY_GEP` is
  empty.
- `verifier_credits_every_bound_arraygep_row_with_the_replayed_body_theorem`:
  every covered row of every fixture is Formal under the replayed theorem,
  each function is promotable with one export per bound row, and every
  refuted body fails all its covered rows.

The first run (on `165816579`) spelled every source element address as
`b + i*s`: `LoadStride3` timed out at 30 s (the machine's `lea [b + i*2];
add i` against `b + i*3`). `728cd47a2` spells strides 3, 5 and 9 as the
selector's own `(b + i*(s-1)) + i` (exact in `Z/2^64`; the element-address
sweep checks it), and it then certifies in 1 s. No query of the 476 has such
a stride.

## 6. Measured outcome on the 476

The probe (`probe/x86_body_probe.rs`, the slice-17 design's probe with local
additions: a names-only mode, a progress line per function, a skip list,
the definition and hint of an inconsistent type hint, and at most 10
samples for a theorem of more than 2000 definitions, whose evaluator
searches a list) selected every function of the fresh dump as the AOT
compiler does and ran the owner at `165816579` (before the merge of main;
`--cf`, 200 samples per theorem; payload `~/tcg-scratch/agep/cf5.tsv`):

- **all 476 build a theorem**, every one holding on its samples (354
  `ArrayGep`, 109 type-hint, 13 other);
- over the whole dump (3457 functions) against census-s16's trace
  (`compare_full.py`): the 2633 functions census-s16 credits all build a
  theorem; 409 of the 412 `ArrayGep` refusals and all 118 type-hint
  refusals build one (the other 3 stop at a slot two paths leave different,
  a cut point a path enters with a different slot, and a machine block
  correspondence); no named mismatch, no theorem refuted on samples.

Offline, every built theorem of the 476 (the statement as the probe dumps
it, `~/tcg-scratch/agep/smt2-5/`) replayed on AY build 12713 with Clean
within the live 30 s budget (`census/replay_dir.py`, two workers, beside a
`-j2` build): **469 `VERIFIED`, 7 `TIMEOUT`**. Of the seven, three are past
512 machine rows (the census states and replays them in parts, slice 16,
which this replay does not), two timed out in main's census as well (AY
TIMEOUT), and two are bodies of 284 and 368 rows (credited at those sizes
by census-s14).

Building is not credit: a census row (the owner's live replay on AY build
12713) decides how many roots return.

## Gates

On the branch with origin/main merged (`8fc4e3470` and the per-host
qualification view after it):

- `trust-cg-verify --lib x86_source_bound_body::tests::` (skipping the
  negative memo, host-qualification, verifier-credit and canonical-migration
  tests, as the landing train does): 281 passed, 0 failed; every slice's
  golden digest and the qualification matrix (its new `arraygep` family
  included) unchanged.
- the two `arraygep_qualification` tests on the qualification pair: pass
  (§5).
- `trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus`:
  5 and 5 passed (built at `7af6a5e35`; no non-test source changed since).
- `check_fmt.sh` OK, `check_documentation.py --check` OK.
- `targo tippy` cannot run on this host (the overlay's `targo` has no
  `tippy`; the package's `targo` refuses the pinned ay manifest's
  `compiler_timeout_secs`), as slice 16 recorded; it was not run.

## Reproduce

- `census/newly_failing.py census-s14 census-main-2854ce newly.tsv`: the
  476.
- the probe: place `probe/x86_body_probe.rs` in
  `crates/trust-cg-verify/examples/` and build it with
  `scripts/trust_cargo.sh build -p trust-cg-verify --example
  x86_body_probe`; run `--cf <dump> cf.tsv <smt2 dir> <names>` with
  `AGEP_SAMPLES=200 RAYON_NUM_THREADS=1`; `census/measure.py cf.tsv
  newly.tsv`, `census/compare_full.py cf.tsv census-s16/stderr.log`. The
  dump is `reports/perf/2026-10-14-darwin-x86-64-slice16-parts/census/dump_core_ir.sh`'s
  procedure over main `2854ce3e3`'s bridge.
- `census/replay_dir.py <smt2 dir> out.tsv 2`: offline AY 12713 + Clean
  replay, 30 s each.
- `qualify.sh <test binary> <log> <test>`: one tool-gated test per process.
- `fails-before/`: the mutants.
