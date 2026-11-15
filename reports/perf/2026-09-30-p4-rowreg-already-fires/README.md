# p4's recorded gap is WRONG: the MAC-register-blocking tier already fires by default

Established 2026-09-30 by adding acceptance tracing to the vectorizer's tier chain and
then int3-patching every loop in `p4_matmul`'s `main` to see which ones execute.

## 1. `rowreg` accepts p4's k loop in the DEFAULT build

Every tier in the `else if` chain now reports ACCEPTANCE, not only declines — because a
loop accepted by an early tier produces no bail from any later one, which made
"no bail from `rowreg`" and "`rowreg` accepted" indistinguishable. With that in place:

```
p4, base build:          run31/p4main/hdr=Block(14): tier=saxpyq-rowreg
p4, +x86-loop-simplify:  run31/p4main/hdr=Block(14): tier=saxpyq-rowreg
rowreg acceptances:      p4 1x,  h1 0x,  v1 0x,  p7 0x
```

`recognize_saxpyq_rowreg_loop` — the tier that "holds the (k-stationary) c row in `N/2`
XMM accumulators across the whole k-loop, eliding the per-(k,j) c store/reload" — **was
already firing on p4 before any of today's work.** The preheader insertion was not needed
for it; the `"k loop has no preheader"` bail came from a LATER vectorizer run, on the CFG
the early run had already transformed.

## 2. The register blocking is in the EXECUTED code

Every backward branch in `main`, with its loop measured and its liveness proven by
patching the head byte to `int3` and observing SIGTRAP:

| loop head | insns | xmm | memrefs | pmuludq | live? |
| --- | ---: | ---: | ---: | ---: | --- |
| `0x209ad` | 31 | 0 | 6 | 0 | LIVE (scalar) |
| `0x20ab7` | 334 | 137 | 105 | 12 | LIVE (outer) |
| `0x20b0f` | 273 | 137 | 87 | 12 | LIVE (outer) |
| **`0x20ba8`** | **102** | **48** | **23** | **0** | **LIVE — the hot inner loop** |
| `0x20dda` | 119 | 65 | 30 | 12 | **DEAD** |
| `0x20e63` | 65 | 60 | 11 | 12 | **DEAD** |
| `0x20f8e` | 18 | 0 | 7 | 0 | **DEAD** |

And immediately after the live loop's backedge:

```
20d72: jb     20ba8              <- the live inner loop's backedge
20d78: movdqu %xmm2,(%r8)        <- TWELVE accumulators written out
20d7d: movdqu %xmm3,0x10(%r8)
 ...
20dc2: movdqu %xmm13,0xb0(%r8)
20dcb: jmp    2100a              <- skips the dead region
20dd0: cmp $0x18,%rbx ; jae 2100a
20e2b: cmp $0x229,%rcx           <- 553 = N*N - N + 1, the rowreg row guard
```

The live loop keeps **twelve** XMM accumulators (`xmm2`..`xmm13`) live across it and spills
them once on exit. That IS MAC register blocking, in the code that runs. The dead region is
the parallel fallback `rowreg` keeps as its check-fail target, dead because the check
PASSES.

## 3. What this refutes

* **`[[x86-p4-two-named-capabilities]]`'s "c re-loaded and re-stored every k iteration ...
  MAC register blocking, which this repo HAS for AArch64 and lacks for x86"** — wrong on
  both halves. x86 has it, it fires on p4, and the executed loop does not reload c per k
  iteration; it holds twelve accumulators in registers.
* **The whole premise of today's preheader work for p4.** The blocker it removed was real
  (`find_preheader` genuinely refuses a multi-entry header) but it was not what stood
  between p4 and this tier, because the tier was already succeeding.
* **Any p4 instruction-count analysis that did not prove its loop live.** Three of p4's
  seven loops are dead, two of them carrying all twelve `pmuludq`. An analysis of the
  packed-multiply route that landed on `0x20e63` or `0x20dda` measured code that never
  executes — and `[[x86-p4-packed-multiply]]`'s "the innermost VECTOR loop spends 20 of its
  45 instructions on a round trip to scalar" needs re-checking against `0x20ba8`
  specifically, which is 102 instructions, not 45.

## 4. What p4's gap therefore is NOT, and where to look next

Not the preheader, not the absence of register blocking, and not the `c` reload. The live
hot loop is `0x20ba8`: 102 instructions, 48 XMM ops, 23 memory refs, **zero `pmuludq`** —
so it multiplies through the scalar `imul` + `movq` route while a packed-`pmuludq` loop
sits dead in the same binary.

The open question is now sharp and cheap to ask: **why does the live loop use scalar
multiplies when a packed loop was emitted?** Either they are the two arms of
`no-x86-saxpyq-scalar-mul` (recorded as 0.88% faster packed, which would make the default
choice wrong) or they are different tiers' outputs and only one is reachable. Either way
the next step is a measurement on `0x20ba8`, not a new capability — and every earlier
number attributed to p4's inner loop must be re-taken with liveness proven first.

---

# 5. The answer to "why scalar multiplies": the rowreg applier never got the packed default

p4's live hot loop (`0x20ba8`, 102 instructions) is opcode-exactly:

| count | op |
| ---: | --- |
| 24 | `imul` — SCALAR 64-bit multiplies |
| 24 | `movq` — GPR<->XMM round trips |
| 12 | `punpcklqdq` |
| 12 | `paddq` |
| 25 | `mov` |

`saxpyq_scalar_mul_enabled()` defaults to FALSE, and its own doc says "The route was
DEFAULT ON until 2026-09-29; the PACKED PMULUDQ compose is now the default".
`apply_saxpyq_plan(func, plan, scalar_mul)` takes that flag and branches on it in four
places. **`apply_saxpyq_rowreg_plan(func, plan)` takes no such parameter and contains ZERO
references to `scalar_mul`** — it emits `ImulRR` + `MovqToXmm` + `Punpcklqdq`
unconditionally (around `x86_vectorize.rs:7828-7856`).

So when packed became the default, the sibling applier was updated and this one was not,
and the existing test `saxpyq_default_route_is_the_packed_pmuludq_compose` covers only the
sibling. **p4's executed loop takes the route a measurement had already rejected**
(63.76 -> 63.20 ms, packed 0.88% faster).

## The fix and its honest ceiling

`emit_i64_packed_mul` already exists, is proof-covered, and carries the mod-2^64 argument.
Wiring it in needs a packed load of the `b` pair, an `aik` broadcast hoisted out of the
unrolled group, then the compose plus one `Paddq`. Per lane pair that is **8 instructions
-> 10**: it trades two scalar `imul` and two GPR<->XMM round trips for three `pmuludq`, two
`psrlq`, one `psllq` and two `paddq`. Not an instruction-count win — the 0.88% came from
removing the round trips.

**Ceiling roughly 0.9% on a program that needs 8.2%**, and the 0.88% was measured on the
INNER tier's loop rather than this one, so it must be re-measured here. Recorded rather
than implemented: it is a genuine defect worth fixing, but it does not bring p4 to parity,
and a proof-sensitive rewrite of a product-emission path deserves its own verified change
rather than being appended to this one.

---

# 6. The packed route was BUILT for this tier and is 16.8% SLOWER — reverted

Section 5 called the rowreg applier's unconditional scalar-IMUL emission a defect, since
the sibling `apply_saxpyq_plan` takes a `scalar_mul` parameter and branches on it in four
places while this applier referenced the flag nowhere. It was wired up and measured.

| `p4_matmul` | vs LLVM -O3 |
| --- | ---: |
| scalar IMUL (this tier's default) | **1.0827** |
| packed PMULUDQ compose | **1.2649 / 1.2641** |

**16.8% slower**, against a 0.0008 floor. The implementation is CORRECT — the 18-program
differential is 20 MATCH-lines, `library/core` is 0 failed roots, and p4's `main` went
`imul=36 pmuludq=12` -> `imul=0 pmuludq=48`, so the route fully swapped. It is simply much
worse here.

**Why, and it is not instruction count.** Per lane pair the packed route is 10
instructions against 8, and its compose is a six-deep DEPENDENT chain
(`pmuludq -> psrlq -> pmuludq -> paddq -> psllq -> paddq`) where the two scalar `imul`s are
independent. This tier unrolls TWELVE accumulator groups, so ILP is abundant and latency
decides. The inner tier, where packed measured 0.88% faster, does not have that unrolling.

**A default measured on one tier's loop does not transfer to another's.** That is the
lesson, and it is the same shape as the instruction-budget error earlier today: a number is
only meaningful at the position it was taken.

## What was kept

The default is REVERTED — the default build is byte-identical to before the experiment
(18 of 18), p4 back to `imul=36 pmuludq=12`, differential 20 MATCH-lines. What stays:

* the row tier now has its OWN EXPLICIT default with the measurement recorded at the
  decision site, instead of a scalar route that merely looked like an oversight;
* the product route is threaded as a PARAMETER like the sibling's, not read from a global
  inside the applier, so both arms are selectable without process state;
* both arms are TESTED — the three golden-output tests back on the scalar shape plus a new
  one pinning the packed arm through a per-instance builder. Making a hardcoded path
  conditional and covering only its default arm is how a knob rots, and this change
  created exactly that risk;
* the test helper no longer identifies the row body by `MovdquRM == 0`, a signature that
  held only while the product route was scalar.
