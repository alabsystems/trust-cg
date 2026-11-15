# h1's vectorization: three dialect gates cleared, still not vectorized, next gate named

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · Reference: in-tree LLVM 22.1.2

## Why h1 is the target

Re-measured with `tsmeasure` (150 interleaved rounds, `taskset -c 2`, min, with
byte-identical control arms), `h1_vec_push_sum` is **1.887x LLVM -O3** — the
suite's largest gap by a wide margin:

| arm | min ms | vs LLVM |
|---|---|---|
| llvm | 9.446 | 1.0000 |
| llvm2 | 9.453 | 1.0007 |
| trust-cg | 17.881 | **1.8930** |
| trust-cg (2) | 17.844 | 1.8891 |

This **corrects two recorded figures**: `x86-h1-reaches-parity` records 1.0037 on an
UNCHANGED program source (`h1_vec_push_sum.rs` last touched in `2442cc803`), and h4 was
recorded at 1.0341 but measures **1.195x**. The suite harness's own `--n-run` ratios are
unreliable in BOTH directions for sub-40ms programs: it reported h2 at 0.976 where a
proper measurement gives **1.111x**, and h3 at 1.070 where h3 is genuinely at parity
(0.9905).

## The entire gap is vectorization

```text
  LLVM   main 104 insns, 4 paddq + 2 movdqu       (SIMD, 2 u64/iteration)
  cg     main 222 insns, ZERO SIMD
  cg's innermost loop is 5 instructions and ALREADY OPTIMAL as scalar code:
      mov (%rdx,%rcx,8),%rax ; add %rax,%r14 ; lea 0x1(%rcx),%rcx
      cmp %rbx,%rcx ; jb
```

The earlier BCE/pointer-reload work landed — the scalar loop went from 12 instructions
to LLVM's 5. **There is nothing left to win in h1's scalar loop.** What is missing is
SIMD, and `trace-vectorize-bail` says every tier declines.

## Three gates cleared, each a SPELLING gap rather than a legality one

The vectorizer's recognizers encode the raw post-ISel dialect, and h1's loop reaches
them in a different but equivalent spelling at every step.

1. **SIB element address.** The tier accepted only `AddRR t, ptr, iv*8` + `MovRM [t]`,
   and bailed `load MovRMSib is not the non-SIB MovRM spelling`. After the peephole's
   address fold the element read is `MovRMSib [ptr + idx*s]`, which the tier's own source
   says carries "exactly the information `heap_elem_base` reads out of the `AddRR` form".
   `heap_elem_base` now decodes it, requiring `disp == 0`, `Gpr64` base and index, and
   `scale * provenance_factor == 8` EXACTLY — the product, so both the raw-counter
   (`scale = 8`) and pre-scaled (`scale = 1`) spellings are accepted and no non-unit
   stride is.
2. **`ImulRRI` / `ShlRI` provenance.** `prov` modelled `MovRR, MovRI, Lea, LeaSib,
   ImulRR, AddRR` but neither immediate-form scaling. At the tier's position h1's index
   is `ImulRRI [idx, iv, 8]` feeding `MovRMSib [ptr + idx*1]` — the scale lives in the
   multiply because the SIB scale-1 fold runs later — so the index resolved to `Unknown`
   and the address classified as neither element nor invariant. Both arms use CHECKED
   arithmetic and degrade to `Unknown` on overflow, since a wrapped stride would assert
   an element stride the loop does not have. `ShlRI` refuses shift amounts >= 63.
3. **The flag-neutral `Lea` counter.** `in_body_def_is_unit_increment` and
   `is_iv_plus_one` accepted `MovRR`/`AddRI` but not `Lea iv, [iv + 1]`, which is what
   the peephole emits when the increment's flags are dead — and is literally what h1's
   emitted loop contains. Both now accept it, with the base required to canonicalize to
   `iv`, `disp == 1` exactly, and the non-SIB `MemAddr` form only (`LeaSib` carries an
   index and computes something else).

## h1 still does not vectorize, and the next gate is named

Each cleared gate revealed the next. At the late vectorizer position the remaining
declines are:

* **heap tier** (the one whose doc describes `while k < v.len()` over a `Vec`):
  `L4940: step guard` — `is_counter` still refuses h1's counter for a condition OTHER
  than the increment spelling just added. That is the next thing to read.
* **reg-arg tier**: `iv Gpr32 not gpr64 counter` (it is looking at the outer `p < passes`
  loop, which is `u32`).
* **saxpy-Q**: `header is not the recognized iv <u bound idiom`.
* At the EARLY positions, still `CROSS-LENGTH: MovMR in Block(11) writes memory` — the
  own-length proof's "no store anywhere in the body" condition, which only the late
  position clears.

## ROOT CAUSE, found after the three gates: the loop is BOTTOM-tested on `iv + 1`

The three gates above were dialect. The gate they exposed is structural, and it explains
why h1 has resisted every previous attempt. Block 17 at the late position, from
`trace-peephole-entry`:

```text
    MovRMSib v196, [v203 + idx]     ; v[k]
    AddRR    v197, v150, v196       ; acc += elem
    AddRI    v200, v148, 1          ; k' = k + 1
    MovRR    v148, v200             ; k <- k'
    CmpRR    v200, v155             ; tests k+1 <u len   <-- the INCREMENTED value
    Jcc B, Block(17)
```

The compare's lhs is `v200 = k + 1`, not the counter `v148`. The tier therefore takes
`iv = v200`, which has **zero** definitions outside the loop, while `iv_enters_as_zero`
requires exactly one, in the preheader, assigning 0 — hence `L4940: step guard`.
saxpy-Q's `header is not the recognized iv <u bound idiom` is the same root cause.
**Every recognizer assumes a TOP-tested `iv <u bound` header with `iv` entering as 0;
h1's loop is a bottom-tested do-while testing `iv + 1`.**

⚑ The comment justifying the late position states it runs "BEFORE `X86LoopRotate` so the
recognizers still see the frontend's TOP-TESTED shape". The loop is already bottom-tested
there, so that premise does not hold and the position does not deliver what it claims.

### What a correct fix must establish

The iteration set is unchanged — the body runs for `k = 0..len-1`, because the loop
continues while `k+1 <u len` — so resolving `iv` through the unit increment to `v148`
preserves the trip count and is the right register for the element addresses.

But the shape is **do-while**: the test follows the body, so `while k < v.len()` compiles
to a zero-trip GUARD plus a do-while. The packed-footprint argument deliberately elides
the per-access bounds-check diamonds inside `[0, vN)`, and that rests on the guard. A
recognizer that accepted the bottom-tested form without PROVING the zero-trip guard
dominates would elide bounds checks on a loop that can run with `len == 0` — a
miscompile, and precisely the class the earlier reviewed revert warned about. That is
legality work, not dialect work, and it is not attempted here.

## Measured cost: zero, and this must not be read as a win

| check | result |
|---|---|
| 18-program differential, default config | **20 MATCH-lines** |
| `library/core` at O3, lowering lane | **0 failed roots / 1284 objects / 0 refusals** |
| `trust-cg-opt` | 4014 pass / 0 fail |
| SIMD counts, 7 SIMD-relevant programs, default vs `vectorize-late` | **identical** |
| those programs' binaries, default vs `vectorize-late` | **byte-identical** |

So all three widenings are **INERT on today's corpus**. They are prerequisites in the
same sense as [the trip-bound rematerialization](../2026-09-29-x86-vec-bound-remat/),
which also landed with no performance claim and the next blocker located. Keeping them is
justified because each is a sound dialect fact the recognizers were missing, every one is
required before the tier can reach its legality checks at all, and the suite proves they
admit no shape the address and counter recognizers have not proven. Claiming anything
more would be unsupported: by this repo's own rule, byte-identical means the lever did
nothing yet.
