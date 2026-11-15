# The scale-1 SIB fold (2026-09-29): a stride multiply the SIB could do for free, and the upstream regression it recovers

An upstream change moved the bridge to lower an element address as an explicit
stride multiply feeding a scale-1 SIB. The x86 SIB fold had no anchor for that
shape, so the multiply survived into every heap-indexing hot loop. This adds the
missing anchor. On a resolvable `h1_vec_push_sum` the fold is worth **0.892x with
P(ON<OFF) = 1.000**, and it recovers a measured **1.12x regression** the upstream
change had introduced.

## The shape, and why the existing fold could not see it

`sib_addr_fold_run_on_block_with_maps` anchors on a formed
`LeaSib d,[base+index*scale+disp]`, or on an `imul`/`shl` followed by an `AddRR`
that materialises `base + index*scale`. The new dialect emits NEITHER:

```text
  imul  %rcx, $8, %rax          ; ImulRRI — the stride multiply
  mov   (%rdx,%rax,1), %rcx     ; MovRMSib, scale == 1 — the SIB does the add
```

No `LeaSib`, no `AddRR`, so no anchor: the multiply stayed. The fold supplies the
missing anchor and rewrites it to what the SIB can do for free:

```text
  mov   (%rdx,%rcx,8), %rax
```

## Why the rewrite is an exact equality, not an approximation

`imul` with 64-bit operands yields the low 64 bits — `index * k` modulo 2^64 — and
SIB address computation is also modulo 2^64. So `(index * k) * 1` and `index * k`
are the SAME value for EVERY input, including the wrapping ones. That is why this
arm needs no range or non-overflow side condition, which is the usual obstacle to
folding arithmetic into an addressing mode.

Side conditions, any failure leaving the code alone: the SIB scale is exactly 1 and
its index is a VReg; that index is globally single-def with its def in the same
block before the memory op, read by `sib_scale_def` as a power-of-two
`ImulRRI`/`ShlRI` with scale in {2,4,8}; the def carries no `proof_origin` and
default flags; the multiplied SOURCE is not redefined between the def and the
memory op; and the index has exactly one use with the multiply's RFLAGS dead there,
so deleting it is invisible.

## The regression it recovers, bracketed

`main`'s `imul`/SIB-scale-8 counts across four bridge dylibs built from this
worktree, plus the runtime of the same 10x-scaled `h1` (pinned, interleaved):

| bridge | imul | SIB scale-8 | scaled h1 | vs LLVM |
| --- | ---: | ---: | ---: | ---: |
| before the merge | 3 | 2 | 226.60ms | 2.629x |
| after merge `afe987c69` | 4 | 1 | 254.39ms | **2.951x** |
| with this fold | 3 | 2 | **226.83ms** | **2.628x** |

The regression is attributed to the merge, not to anything local: with the ENTIRE
bounds-check-elimination pass disabled the post-merge bridge still shows
`imul=4`/`sib8=1` and 254.8ms. The only non-merge commit touching the changed files
(`wide_projection.rs`, `value_layout.rs`, `pointer_coercions.rs`) is
`d0d0e4caf fix(bridge): advance Linux AArch64 core and runtime lowering` — an
AArch64 fix in target-independent bridge files, which introduces an explicit
`TrustIrBinOp::Mul` for element stride. It was NOT bisected to that commit, so it
is named as the candidate, not the cause.

## Measurement

Isolated by `-Ztrust-ir-cg-args=no-x86-sib-scale1-fold`, one bridge, both arms,
15 INTERLEAVED samples on one pinned core:

| | min | median |
| --- | ---: | ---: |
| trust-cg, fold OFF | 254.18ms | 255.15ms |
| trust-cg, fold ON | **226.83ms** | **233.76ms** |
| ON / OFF | **0.8924x** | 0.9161x |

`P(a random ON sample < a random OFF sample) = 1.000` over all 225 pairs. Every ON
sample beat every OFF sample, so this is not a noise artefact of the kind that
produced a false 0.953x elsewhere in this round.

## Whole corpus, and the honest limit of the claim

All 18 beat-llvm programs, both arms, `no-proof-certs`:

| | fold OFF | fold ON |
| --- | ---: | ---: |
| coverage | 18/18 MATCH, 0 MISMATCH | 18/18 MATCH, 0 MISMATCH |
| runtime geomean vs LLVM -O3 | 0.903x | **0.880x** |
| heap category | 1.390x | **1.237x** |
| h1_vec_push_sum | 2.756x | 2.562x |
| h2_vec_grow | 1.096x | 0.805x |
| h3_box_leak | 1.190x | 1.075x |
| worst program | 2.756x | 2.562x |
| **resolvable-rows-only geomean** | **0.791x** | **0.792x** |

Correctness is intact in both arms: 18/18 MATCH, zero MISMATCH, on a pass that
rewrites address computation.

THE LIMIT, stated plainly: every corpus row the fold improves (h1 24ms, h2 15ms,
h3 38ms) is BELOW the harness's own 50ms resolvability floor, so the contract's
resolvable-rows headline does not move (0.791x -> 0.792x, noise). The 0.892x with
P=1.000 above is real but comes from a SCALED diagnostic copy, not a corpus row.
The defensible statement is: the fold improves the intent-to-treat geomean
0.903x -> 0.880x and the heap category 1.390x -> 1.237x, and is worth 0.892x on a
resolvable version of the program it was aimed at.

## Tests

Eight, in `x86_peephole.rs`: two positives (`ImulRRI` and the `ShlRI` spelling),
one displacement-preservation check, and five refutations — a SIB scale that is not
1, a non-power-of-two stride (a 24-byte element), the multiplied source redefined
between def and use, live multiply flags, and a multiply used more than once.
Vacuity-checked: all three positives FAIL with the fold disabled.

## Addendum: the multi-use generalization, and a noise calibration that matters more

The fold initially declined an index with more than one use. `p4_matmul`'s inner
statement is `c[i*N+j] = c[i*N+j].wrapping_add(..)`, whose index feeds BOTH a load
and a store, so that looked like the obvious next case — and unlike the heap family
`p4` is above the 50ms resolvability floor, which would have made a win countable.

The generalization is implemented and tested: all appearances of the pre-scaled
index must be scale-1 SIB indices, every use must be in this block, and the
source-not-redefined scan now runs to the LAST rewritten use. Three new refutations
pin the shapes that must still decline — the index also being the STORED value
(`mov [base+v*1], v`), the index used as a SIB BASE (where the SIB does not scale
it), and a use escaping the block.

**It fires on nothing in the corpus.** `p4_matmul` and `b1_mispredict` compile
BYTE-IDENTICALLY with and without the whole fold (`imul` counts 209/209 and 167/167,
identical sha256), so neither exercises it. The generalization is a correct widening
with no measured effect, and it is not credited with one.

### The calibration

Chasing that non-effect produced something more useful. A full-corpus A/B of the
fold, `--n-run 5 --n-compile 1`, reported:

| | fold ON | fold OFF |
| --- | ---: | ---: |
| runtime geomean vs LLVM -O3 | 0.909x | 0.893x |
| resolvable-rows-only | 0.791x | 0.788x |
| b1_mispredict | 1.174x | 1.105x |
| p4_matmul | 1.095x | 1.105x |

Every one of those differences is NOISE, and provably so: the `b1` and `p4` binaries
in the two arms are byte-identical. So at contract-default `--n-run 5` the harness
swings `b1_mispredict` by **6%** and the whole-corpus geomean by **1.6 points**
between runs of THE SAME MACHINE CODE. An earlier round of this A/B happened to
order the arms the other way (0.880x ON vs 0.903x OFF), which is the same fact seen
twice.

Consequences, and they apply to every performance claim in this repository:

* A corpus geomean difference of a point or two, from single runs, is not evidence.
* `b1_mispredict` in particular needs many more samples than 5 before a few percent
  means anything — which also retires any reading of it against the ~1.15x it has
  hovered at all round.
* The way to measure one change is what was done for h1 above: ONE bridge, the
  change's own lever, many INTERLEAVED samples, and a rank statistic. That gave
  `P(ON<OFF) = 1.000`, which no amount of corpus-level noise can manufacture.

Re-verified on the current backend after a further `origin/main` merge: fold OFF
254.33ms, ON 226.79ms, **0.8917x**, `P(ON<OFF) = 1.000`, h1 2.958x -> 2.638x. The
win is stable across three bridge builds.

## Addendum 2: three dialect mismatches in the vectorizer, and where h1 now stands

With `trace-vectorize-bail` reachable, h1's non-vectorization stopped being a mystery
and became a queue of named conditions. Three were genuine mismatches between the
dialect the recognizers were written against (raw post-ISel) and the dialect that
exists after the cleanup cluster, each fixed with an identity argument:

1. **The header test's spelling.** Recognizers match the frontend's materialized
   boolean (`CmpRR ; Setcc(B) ; [Movzx/MovRR/AndRI]* ; CmpRI w,0 ; Jcc(NE|E) ; Jmp`).
   The peephole FUSES that into `CmpRR ; Jcc(B|AE) ; Jmp`, which no recognizer
   matched — the `header chase_below_branch` bail at the late position. The two
   compute the same predicate (`B` IS `l <u r`; `AE` is its negation, so the targets
   swap), so `chase_below_branch_either` returns the same tuple for both. Scoped to
   the reg-arg tier.
2. **A RELOADED length is still invariant.** `is_reg_loop_invariant` requires the
   register to be undefined in the loop. A `Vec` keeps its length in its header, so
   `while k < v.len()` reloads it every iteration and the check can never pass —
   which is exactly why a reduction over a `Vec` was refused where the same
   reduction over a `&[T]` (length in a register) was accepted.
   `is_reg_invariant_or_invariant_reload` also accepts a plain non-volatile load from
   a loop-invariant address when the loop body writes NO memory. That no-write
   condition is the existing `invariant_load_addr` soundness precondition, which the
   file documented as "the caller enforces this"; it is now actually checked, by
   `loop_body_writes_no_memory` (stores AND calls AND volatile accesses).
3. **The increment's spelling.** `is_iv_plus_one` accepted only
   `AddRR [v, iv, <MovRI 1>]`; const-fold turns the same increment into
   `AddRI [v, iv, Imm(1)]`. And the zero-entry check used `const_of`, which requires
   the vreg's OWN def to be the `MovRI` — true for the raw one-link init, false after
   copy-propagation leaves `iv <- MovRR a <- MovRR b <- MovRI 0`.
   `const_of_through_copies` follows `MovRR` (never `MovRR32`, which truncates).

WHERE h1 STANDS, stated exactly: its inner sum loop now passes EVERY
bail-printing condition in the reg-arg i64 sum-reduction tier, and is still declined
by a later condition that has no `bail!` site. `main` contains no `paddq`. **h1 is
not vectorized**, and the 1.979x vectorization factor is not recovered.

Risk check, because two of the three fixes touch helpers (`iv_enters_as_zero`,
`is_iv_plus_one`) that EVERY recognizer calls, so a wider match could fire somewhere
new on the default path: whole corpus 18/18 MATCH, 0 MISMATCH, resolvable-rows
geomean 0.793x against 0.791x/0.792x before — unchanged within the noise band
calibrated above.

## Addendum 3: two more mismatches cleared, and the blocker that remains

Iterating with the bail trace cleared two further conditions in the reg-arg i64
sum-reduction tier:

4. **The element GUARD's spelling.** The bounds-check guard block was chased with
   `chase_below_branch` while the header used `chase_below_branch_either`, so the
   guard was refused in exactly the fused form the header now accepts. Same fix.
5. **A false CROSS-LENGTH report.** The guard's bound and the header's trip bound
   were compared by vreg identity. An owning container RELOADS its length, so those
   are two reads of one `Vec` header field and the comparison reported a
   cross-length mismatch that is not real. `same_value_or_same_reload` accepts two
   plain non-volatile loads of the same width from the same canonical address when
   the loop body writes no memory — the vectorizer analogue of the bounds-check
   pass's reloaded-length arm, with the no-write condition checked, not assumed.

A DUPLICATED CHECK was also removed. Step 1b of the recognizer re-stated
`iv_enters_as_zero` inline but with `const_of` where the helper uses
`const_of_through_copies`, making the duplicate STRICTER than step 1a's `is_counter`
(which calls the helper). A loop could therefore clear 1a and be refused at 1b for
the same property, silently, because that rejection had no `bail!`. It now calls the
one helper.

### The blocker, named

h1's inner sum loop now clears every condition in the tier up to the load
classifier, where it is refused because the element read is
`MovRMSib [ptr + idx*8]` and the classifier accepts only the non-SIB `MovRM`:

```rust
if op != X86Opcode::MovRM {
    bail!("load {:?} is not the non-SIB MovRM spelling", op);
}
```

The `MovRMSib` form carries exactly the information `heap_elem_base` extracts from
the `AddRR(ptr, iv*8)` form — arguably more directly — so this is a shape gap, not a
legality one. Two routes forward, neither taken here:

* Teach the element-load classifier the SIB spelling. Contained, but it feeds the
  plan's base/index extraction in the most safety-critical pass in the backend.
* Run the vectorizer after SROA instead. At the EARLY position h1's only bail is
  `len_reg not loop-invariant`, and the cause is the slice-temp `(ptr, len)` stores
  that SROA removes — so with SROA first the loop would arrive in the recognizer's
  NATIVE dialect and need none of these spelling fixes. That is a pass-order change
  against an explicit design comment, so it needs its own measurement.

**h1 is still not vectorized.** Five spelling mismatches are fixed and the sixth is
named. Corpus after all of them: 18/18 MATCH, 0 MISMATCH, resolvable-rows geomean
0.792x — unchanged within the calibrated noise band.

## Addendum 4: all three pass positions fail on ONE root cause, and upstream had already named it

A third vectorizer position was added and measured: `vectorize-post-sroa`, immediately
after SROA and before LICM. The reasoning was that h1's early-position bail
(`len_reg not loop-invariant`) is caused by the slice fat-pointer living in memory,
which SROA promotes — so the loop would arrive in the recognizers' NATIVE dialect and
need none of the spelling fixes above.

**It gives the identical bail.** SROA cannot promote the slot in question: the length
is read from the `Vec`'s OWN stack slot, and that slot's address escapes to the
allocator in the push loop, so SROA correctly refuses it. `v.len()` is a genuine
reload at every position.

So all three positions fail for one reason:

| position | bail |
| --- | --- |
| early (default) | `len_reg not loop-invariant` |
| `vectorize-post-sroa` | `len_reg not loop-invariant` |
| `vectorize-late` | cleared, then `load is not the non-SIB MovRM spelling` |

### Upstream had already refuted the obvious fix, with a reason I had missed

An `origin/main` merge replaced my `is_reg_invariant_or_invariant_reload` with
upstream's strict check, which carries:

> A header-local reload is not enough: the new VP0 reads len before the original
> header, so admitting that shape also requires a proven-safe dominating
> rematerialization in the plan.

That is correct and it is the objection my change did not answer. The vectorized plan
reads the trip bound in a NEW preheader, BEFORE the original header, so a value the
scalar program only loads INSIDE the loop cannot just be relabelled invariant and used
there — that executes a load the scalar program might never execute.

(My change also reached `origin/main` in a state that DID NOT COMPILE, because the
merge dropped a helper definition while keeping its call and I pushed without
rebuilding the merge result. Fixed in the following commit. A merge is a new tree and
needs its own build.)

One observation for whoever takes this further, offered as an observation and not as a
change: the obligation looks dischargeable. h1's header IS the loop's first block, so
its `len` load executes on every entry to the loop, including the zero-trip case.
A load placed in a preheader that dominates the header is therefore on a path the
scalar program already takes. But discharging it means EMITTING that load into VP0 —
work in the plan emitter, in the most safety-critical pass in the backend, on exactly
the question where upstream has already corrected me once. It is not being done
unilaterally here.

**Net for the vectorization lever:** not recovered. The 1.979x remains. What the
session produced instead is a diagnosis that names every blocking condition, a
reachable bail trace to re-derive it, two extra pass positions to test against, and
five spelling mismatches fixed so the tier is no longer refusing loops for how they
are written.
