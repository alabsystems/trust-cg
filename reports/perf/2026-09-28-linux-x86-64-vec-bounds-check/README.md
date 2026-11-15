# The Vec own-length bounds check on x86-64 (2026-09-28): the check is now removed, and that is NOT what h1 costs

`h1_vec_push_sum` is the largest per-program gap in the whole corpus — 2.6x vs
LLVM-through-rustc. Earlier today I recorded its cause as "an un-eliminated bounds
check on `Vec` indexing, plus the vectorization that check blocks". The first half
of that is **withdrawn here**: the check is now eliminated, the hot loop is 25%
shorter, and the runtime did not move. This report has the measurement that says so
and the decomposition that replaces it.

## The capability gap that was real

`X86BoundsCheckElimination` removes an own-length bounds check when a dominating
identical compare proves its trap edge dead. It required both compares to
canonicalize, through value-preserving copies, to the SAME vreg.

* A `&[T]` passes `len` in a register. One vreg, so the pass fired.
* A `Vec`/`String` keeps `len` in its header, so `while k < v.len() { .. v[k] .. }`
  RELOADS it. The guard and the check compare two textually distinct load results
  with different roots, every case declined, and the check survived.

So the pass worked on slices and not on the commonest owning-container loop in
Rust. That is now case 4: two load-defined vregs denote the same value when they
read the same frame bytes and nothing between them may have written those bytes.
Both halves are proved statically (a byte range in one named stack slot; a
one-path scan that fails on a call, an unresolvable address, or any overlapping
store) or the case is declined. The pass is memory-safety-critical — a
wrongly-removed check is a silent out-of-bounds — so there is no optimistic arm.

## WITHDRAWN: "it fires exactly where it was aimed"

An earlier revision of this report claimed the arm fired on h1 — `main` 181 -> 164
instructions, inner loop 12 -> 9 per iteration. **That is withdrawn. The arm does
not fire on h1 at all.** Two compounding mistakes produced it, both worth naming
because either alone would have been enough.

**1. The A/B could not isolate the arm.** It compared `-Ztrust-ir-cg-args=no-x86-bce`
against the default — i.e. the WHOLE pass off against the whole pass on. Cases 1-3
predate this work, so any difference that A/B shows is the pass's, not the new arm's.
There is now a lever that isolates it, `-Ztrust-ir-cg-args=no-x86-bce-reload`, which
disables case 4 and leaves the rest of the pass running. With it, h1 compiles
**byte-identically** (both `d690da2c9c5dc9cf…`): the arm contributes nothing here.

**2. The two arms came from different backends.** The 181/164 pair was measured on a
bridge dylib built BEFORE an `origin/main` merge that landed 26 files and ~5400
insertions across the compiler crates. On the current backend, `main` is 181
instructions with BCE on and 181 with BCE off. A cross-build pair is not an A/B, and
this one silently attributed an upstream change to a local one.

### Why the arm cannot fire on h1 — the real reason, from the pass's own trace

`-Ztrust-ir-cg-args=trace-vectorize-dump` prints the loop after the cleanup cluster.
h1's inner sum loop reaches the check as:

```text
  Block(8)  guard: MovRR v93, v89 ; MovRM v95, [v94+0] ; CmpRR v93, v95 ; Jcc B
  Block(9)  check: MovRR v100, v89 ; MovRM v107, [v106+0] ; CmpRR v100, v107 ; Jcc AE -> trap
```

Both compares read a COPY of the loop IV (`v93`, `v100`) rather than the IV `v89`
itself, and each copy is defined in its own block BEFORE its own compare. Case 3
admits exactly one shape — guard uses the root DIRECTLY, check uses a copy captured
inside the covered window — so `same_value_operand` declines on the LEFT operand and
`continue`s. **The length is never reached**, so no improvement to the length
reasoning can matter for h1. The reloaded-length arm was aimed at the right program
and the wrong operand.

(The chained-`Lea` resolution added alongside this — a field address is
`lea a,[StackSlot(s)+0]` then `lea b,[a+16]`, and a one-link resolver saw `b` as
opaque — is a genuine fix to the length side, with its own vacuity-checked test. It
simply is not h1's blocker.)

### What the arm is, stated without credit it has not earned

A capability with 12 tests (3 positives, 9 refutations), vacuity-checked in both
directions: every positive fails with the arm disabled, and the first draft of the
test builder spliced the "intervening" instructions AFTER the check load, which made
four refutations pass vacuously — they caught it by failing in the UNSAFE direction.
`Vec`/`String` own-length loops are now reachable by the pass where before they were
structurally excluded.

**It has no demonstrated effect on any measured program.** That is the honest state.

## What h1's 2.6x actually decomposes into

Same scaled program, same core, 13 interleaved samples, RE-MEASURED on the current
backend after the merge above (it reproduces: 1.979x / 1.334x against the earlier
1.977x / 1.333x, so this decomposition is not affected by the cross-build problem —
all three builds here come from one bridge and one rustc). `-Cno-vectorize-loops
-Cno-vectorize-slp` is confirmed effective by disassembly: the `paddq`/`xmm` count
in `main` drops from 4/present to **0**.

| build | min | vs LLVM -O3 |
| --- | ---: | ---: |
| LLVM -O3 | 85.90ms | 1.000x |
| LLVM -O3, vectorizer OFF | 169.97ms | 1.979x |
| trust-cg | 226.72ms | 2.639x |

So the gap is two independent factors, and now each has a number:

* **1.979x is vectorization.** LLVM's `main` contains four `paddq` on `xmm` — two
  `u64` per instruction across four accumulators. trust-cg emits a scalar loop.
* **1.334x is ordinary scalar codegen quality** (226.72 / 169.97), entirely
  independent of vectorization: trust-cg's scalar loop is a third slower than
  LLVM's scalar loop.

The bounds check appears in neither. That is the withdrawal.

## A hypothesis about the 1.333x that is REFUTED, recorded so it is not retried

If the scalar loop were bound by the serial `acc = acc + v[k]` dependency chain,
splitting the reduction across four accumulators would break it. `h1_4acc-diagnostic.rs`
does exactly that in the source (same total work, same checksum — all four builds
exit 80).

| build | min | vs its own 1-accumulator form |
| --- | ---: | ---: |
| trust-cg, 4 accumulators | 254.06ms | **1.121x SLOWER** |
| LLVM -O3, 4 accumulators | 85.98ms | 0.998x (unchanged) |

So the loop is not accumulator-dependency-bound, and hand-splitting the reduction
makes trust-cg worse, not better. LLVM is unmoved because its own vectorizer
already normalises both forms.

Nor is it simple instruction count in the hot loop: removing 25% of the loop's
instructions (above) moved nothing.

WHAT I COULD NOT MEASURE, and so do not claim: which microarchitectural resource
does bound it. Hardware counters are unavailable on this host —
`/proc/sys/kernel/perf_event_paranoid` is 4, and raising it is a system-wide
security setting, not something to change for a benchmark. Any statement here about
issue width or port pressure would be inference, not measurement, so there is none.

## What this is worth

* The capability is real but UNDEMONSTRATED: `Vec`/`String` own-length loops are now
  reachable by the pass, where the same-vreg requirement structurally excluded them.
  Twelve tests, vacuity-checked. No measured program is improved by it yet, and h1 —
  the program it was written for — is declined on the left operand instead.
* The pass is now A/B-able through the bridge at all. Its kill switch was
  `TCG_NO_X86_BCE`, and `trustc` refuses every `TCG_*` variable before the backend
  loads, so the only A/B was to build the bridge twice. `pipeline.rs` had a SECOND
  copy of the env read; it now delegates to the pass's gate, because a second copy
  would ignore the knob and make this very A/B read as "no difference" while both
  arms ran the pass.
* For h1 the ranked levers are numbered: vectorizing a pointer-based reduction
  (1.979x) then the residual scalar gap (1.334x). Neither is the bounds check.
* The next concrete step for h1's check, if anyone wants it, is the LEFT operand:
  admit a guard-side copy defined before the guard compare by extending the
  redefinition scan BACK to that copy's definition, instead of starting it at the
  compare. That is a real soundness argument to make, not a relaxation to wave
  through.

Retained: `h1_4acc-diagnostic.rs`. The scaled copy is `passes` 300 -> 3000 applied
to `benchmarks/beat-llvm/progs/h1_vec_push_sum.rs`; both are DIAGNOSTIC programs,
not corpus rows, and no ledger row is claimed from any number here.
