# b1_mispredict 1.0959 -> 1.0260: the demanded-bits capability existed and was AArch64-only

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · `perf_event_paranoid=4`
(no hardware counters) · Reference: in-tree LLVM 22.1.2 (`-C opt-level=3`)

## Result

`b1_mispredict`, the suite's worst program, measured with its own tracked knob
(`-Ztrust-ir-cg-args=x86-xorshift-demanded-bits`), 120 interleaved rounds,
`taskset -c 2`, `min` statistic, **both arms carried twice as byte-identical
copies** to expose the floor:

| arm | min ms | med ms | vs LLVM |
|---|---|---|---|
| llvm | 189.907 | 190.925 | 1.0000 |
| off (default) | 208.113 | 209.152 | 1.0959 |
| off2 | 208.233 | 209.238 | 1.0965 |
| **on** | **194.839** | 195.688 | **1.0260** |
| on2 | 194.628 | 195.785 | 1.0249 |

Floors 0.0006 (off/off2) and 0.0011 (on/on2); the 0.070 effect is ~60x the
larger floor. `on` and `on2` are byte-identical; `off` and `on` differ, so the
lever is isolated and did act. All three arms exit 44 — same answer.

## The identity, and why it is a LATENCY win

Shifting left by `k` cannot change bits below `k`, so

```text
    y = x ^ (x << k)   =>   y[i] == x[i]  for all i < k
```

b1's loop is `s ^= s<<13; s ^= s>>7; s ^= s<<17`, and the branch choosing its
two arms tests `s & 1` — bit 0 of the FINAL value. This backend computed that
predicate from `s3`; LLVM computes it from `s2`, one dependent operation
earlier, and `s3 = s2 ^ (s2 << 17)` so bits 0..16 agree.

The loop went **38 -> 37 instructions**. This is deliberately not an
instruction-count claim: the extra xor is free on an out-of-order core, but the
branch cannot resolve until its input does, and b1's cost is wrong-path work
executed in a mispredicted shadow. Both of b1's consumers fired:

```text
  BtRI  op0 now reads v24 instead of v30   (demands bit 0  < 17)
  AndRI op1 now reads v24 instead of v95   (demands bits <= 2 < 17)
```

## The capability existed. It was AArch64-only.

`crates/trust-cg-opt/src/xorshift_demanded_bits.rs` implements this exact
identity and is registered **only** in the AArch64 pipeline, where it is
default-ON and credited "-9ms of b1's 29ms gap", independently reproduced at
-11ms, with its module doc stating "It is latency, not instruction count."
`x86_loop_top.rs` carried a comment naming the capability as missing on x86.
This is the same shape as the AArch64-only GVN and the AArch64-only scheduler.

## Why a direct port would have fired on NOTHING

Three differences, each fatal, and none of them visible without dumping the real
pre-RA stream (`-Ztrust-ir-cg-args=trace-peephole-entry`):

1. **Different IR universe.** x86 passes implement `X86MachinePass` over
   `X86ISelFunction`; the AArch64 pass takes `MachFunction`.
2. **No shift-fused xor.** AArch64's producer is ONE instruction,
   `EorRRLsl dst, a, a, #k`, recognized by "both source registers are equal".
   x86's producer is the PAIR `ShlRI t, x, k` + `XorRR y, x, t`.
3. **x86 ISel vregs are not SSA, and the operands do not match syntactically.**
   b1's measured stream:

   ```text
     MovRR v25, v24
     ShlRI v28, v25, 17        <- shifts v25
     XorRR v29, v24, v28       <- xors  v24   (NOT v25)
     MovRR v30, v29
     BtRI  v30, 0              <- reads v30   (NOT v29)
   ```

   A recognizer requiring `ShlRI`'s source to equal `XorRR`'s other operand
   matches nothing, and a consumer scan keyed on the xor's `dst` matches
   nothing. Both sides are resolved through `MovRR` copy chains.

An analysis agent mis-cited the x86 shapes three ways (naming `emit_shift_imm`
where the shift goes through `select_shift`; presenting 3-operand `AndRI` as an
ISel-output shape when ISel emits `AndRR` and the immediate form only appears
after the peephole's fold). Dumping the stream settled all of it.

## Correctness

A pure in-place OPERAND SUBSTITUTION: no instruction created, deleted, merged or
moved; no flag behaviour changes; every accepted slot is a USE. Two independent
fail-closed conditions:

* **The bit range.** `hi < k`, every demanded bit strictly below the shift.
  Reading a bit at or above `k` from `x` is a WRONG VALUE, so this inequality is
  the whole value argument. An unrecognized consumer yields `None` and is left
  alone.
* **Single-def-ness, which SSA gave the AArch64 twin for free.** Every vreg on a
  resolved copy chain, and `x` itself, must have exactly ONE function-wide
  definition. `x`'s single def is an operand-producer of `y`'s def, and `y`'s
  def dominates the consumer (else the given program is already invalid), so
  every path reaching the consumer has passed `x`'s def and `x` still holds the
  value the identity was proven about. Without this a loop-carried merge vreg
  could be redefined in between and the substitution would read the NEXT
  iteration's seed.

Idempotent, which matters because at O3 the pass manager runs `run_to_fixpoint`:
it only rewrites a use toward a strictly earlier def, and the rewritten operand
names `x`, which is not a producer `dst` of the same chain.

Only `ShlRI` producers. A right shift preserves the HIGH bits, which no accepted
consumer demands.

## Gates

* 13 unit tests, 11 of them negative: bit at `k`, bit above `k`, mask reaching
  `k`, right-shift producer, two-source xor carrying a shift, zero shift,
  multi-def `x`, multi-def copy on the chain, the 2-operand `AndRI` RMW form
  (whose operand 0 is both def and use — rewriting it would change the value
  WRITTEN), the commuted operand order, and idempotence.
* `trust-cg-opt` 3943 pass / 0 fail; pipeline schedule pins 6/6 (registration is
  gated on the knob, so the default schedule is unchanged).
* The certificates-ON compile of b1 fails `[TCG-MIR-UNSUPPORTED]` **with the pass
  off as well** — pre-existing, in the Trust-verification lane, not caused by
  the rewrite.
