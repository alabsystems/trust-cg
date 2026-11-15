# p4_matmul: the loop this campaign has been analysing is DEAD, and the real gap is XMM register copies

Host AMD Ryzen 9 9900X3D, Linux, `-Copt-level=3`, one dylib.

## The refutation

Every earlier p4 analysis in this campaign — recorded as "3 bounds checks + 2
invariant recomputations = 8 of 26 hot-loop insns; needs affine BCE" — described
the loop at `0x20fcf`:

```
20fcf: lea    0x0(%r13,%rdi,1),%rcx     ; i*N + j
20fe0: cmp    $0x240,%rcx ; jae <panic>  ; bounds check 1
20fed: mov    -0x3628(%rbp,%rcx,8),%rsi  ; c[i*N+j]
20ff5: imul   $0x18,%r8,%rdx             ; k*N  -- invariant in the j loop
...
21020: lea    (%r12,%rdi,1),%rcx        ; i*N + j AGAIN, different register
21024: cmp    $0x240,%rcx ; jae <panic>  ; bounds check 3, duplicate of 1
```

**That loop is never entered.** It is the scalar REMAINDER loop of a vectorized `j`
loop whose stride is 8 (`add $0x8,%rdi`). `N = 24`, so the vector loop runs exactly
3 iterations and exits with `rdi == 24`; the guard at `0x20fc0`
(`cmp $0x18,%rdi ; jb 20fcf`) is then never taken.

Proved rather than argued: patching the loop's first byte to `int3` and running the
binary gives the **same exit code 111 and no signal**.

```
file offset of 0x20fcf: 0x1ffcf   original bytes: 49 8d 4c 3d 00
orig     exit=111 signal=no
trapped  exit=111 signal=no
```

So p4 is vectorized, its real hot loop contains **no bounds checks at all**, and
"p4 needs affine BCE" is refuted. Three of the five hot-loop defects previously
attributed to p4 (two duplicate bounds checks, the duplicated `i*N` address, the
invariant `imul $0x18`) are defects of dead code.

## The real hot loop, and the one difference that survives

Real inner loop, tcg `0x20ea8..0x20fb9`; LLVM `0x209f0..0x20cca`. Both emulate the
64x64 multiply the same way (SSE2 has no `pmullq`), so the comparison is clean.
tcg strides 8 elements per iteration, LLVM strides a whole 24-element row
(`add $0xc0,%rsi`), so normalise per element:

| opcode | tcg (65 insns / 8 elem) | LLVM (141 insns / 24 elem) | per-element delta |
| --- | ---: | ---: | ---: |
| `pmuludq` | 1.50 | 1.50 | 0 |
| `paddq` | 1.50 | 1.50 | 0 |
| `movdqu` | 1.50 | 1.50 | 0 |
| `psrlq` | 0.50 | 0.54 | 0 |
| `psllq` | 0.50 | 0.50 | 0 |
| **`movdqa`** | **2.00** | **1.08** | **+0.92** |
| `lea` | 0.25 | 0 | +0.25 |
| loop overhead | 0.375 | 0.125 | +0.25 |
| **total** | **8.1** | **5.9** | **+2.2** |

Every arithmetic and memory opcode matches exactly. The whole difference is
**register copies** (`movdqa`, +0.92/element, about 7 extra per iteration) plus a
3x smaller unroll.

`pmuludq` is two-address (`dst *= src`), so a copy is needed to preserve a live
operand. tcg copies the loop-INVARIANT operands (`%xmm4` = `aik` lo, `%xmm5` = hi)
on every use and copies `b` again to build `b >> 32`:

```
movdqa %xmm4,%xmm3 ; pmuludq %xmm1,%xmm3      <- copies the invariant
movdqa %xmm1,%xmm0 ; psrlq $0x20,%xmm0        <- copies b to shift it
movdqa %xmm4,%xmm2 ; pmuludq %xmm0,%xmm2      <- copies the invariant again
movdqa %xmm5,%xmm0 ; pmuludq %xmm1,%xmm0      <- and again
```

4 copies per 2 elements. The minimum for this dependence pattern is 2 — tie the
destination to the operand that DIES (the freshly loaded `b`), and shift `b` in
place at its last use — which is exactly LLVM's 1.08/element.

## Status of the implied fix

The pass that would do this, `crates/trust-cg-opt/src/x86_two_addr_expand.rs`,
already has a commuted-tie arm behind the tracked knob `x86-twoaddr-commute`
(default off). **Measured: it fires on nothing.** Byte-identical binaries with and
without the knob for `p4_matmul`, `b1_mispredict`, `p1_xorshift`, `p2_collatz` and
`h4_vec_dropper` — consistent with its own doc, which notes it needs a candidate
whose LHS dies "and this never does". It is also GPR-only
(`is_commutative_gpr_two_address` admits `AddRR`/`AndRR`/`OrRR`/`XorRR`/`ImulRR`),
whereas every copy above is XMM.

So closing p4 needs the commuted tie extended to the XMM two-address ops, which is
not attempted here. **Do not assume it is worth the full 8.3%**: `movdqa` reg-reg
is renamer-eliminated on Zen, so the 7 saved instructions cost dispatch slots
rather than execution ports, and the unroll factor is a separate contributor. The
NOP refutation in `2026-09-29-jcc-align-is-a-trade/` is the cautionary case — 19
bytes of NOPs in this same program's dead loop measured as exactly zero.

## Reproduce

```sh
DRV=trust/build/host/stage2/bin/trustc
DYLIB=$PWD/target-bridge/release/librustc_codegen_trust_cg.so
C="-Ztrust-verify=off --edition=2021 --crate-type bin -Cpanic=abort -Copt-level=3"
$DRV -Zcodegen-backend=$DYLIB -Ztrust-ir-cg-args=no-proof-certs $C \
     -o /tmp/p4.tcg benchmarks/beat-llvm/progs/p4_matmul.rs
$DRV $C -o /tmp/p4.llvm benchmarks/beat-llvm/progs/p4_matmul.rs
objdump -d --no-show-raw-insn /tmp/p4.tcg    # inner loop 0x20ea8..0x20fb9
objdump -d --no-show-raw-insn /tmp/p4.llvm   # inner loop 0x209f0..0x20cca
```

The deadness check: copy the binary, set the byte at file offset `0x1ffcf` to
`0xCC`, run it, and confirm exit 111 with no signal.

## What extending the commuted tie to XMM actually requires

Read before starting: the change is not "add `Pmuludq` to a list". Today the pass
cannot touch an XMM candidate at all, because `copy_opcode_for_class` returns `None`
for every non-GPR class and its doc says "the expansion is then skipped (a perf
no-op)". Three coordinated pieces:

1. **`copy_opcode_for_class`** must map the XMM class to the class-exact copy
   opcode. The existing arms are chosen so the inserted copy "normalizes to
   `PSEUDO_COPY` (the form the coalescer folds)" — so the XMM arm has to name the
   opcode the `x86_isel_copy_like_vregs` combos recognise, not merely a working
   `Movdqa`. If the coalescer does not fold it, the pass ADDS a copy instead of
   removing one.
2. **A candidate filter** beside `is_expandable_gpr_two_address` for the XMM
   two-address value producers (`Pmuludq`, `Paddq`, `Pand`, `Por`, `Pxor`, …),
   and a commutative subset beside `is_commutative_gpr_two_address`. `Psubq`,
   `Psllq` and `Psrlq` are not commutative and must stay out.
3. **The deadness proof must be re-read for XMM.** Both proofs the pass relies on
   — single-read, and the block-local kill — are stated over `read_counts` and
   `lhs_dead_after`. The class-blind rule applies: a kill test that compares whole
   `VReg`s rather than `.id` will mis-handle a narrower view of the same register,
   which is the defect class already recorded for the vectorizer's width views.

Expected value, stated in advance so it can be falsified: p4's dependence pattern
allows **2** copies per 2 elements against the 4 it emits, but the commuted tie alone
recovers only about ONE of those two — the last use of `b`, where `b` finally dies.
Reaching LLVM's 1.08/element also needs `b >> 32` computed at `b`'s last use so the
shift happens in place, which is a scheduling change, not a tie change. So predict
roughly `movdqa` 2.00 -> 1.50/element, about 4 instructions of 65, and expect LESS
than that in time because `movdqa` reg-reg retires through the renamer on Zen.
If the measured gain is near the full 8.3%, the model above is wrong and should be
re-derived rather than believed.

## REFUTED by direct measurement: the XMM commuted tie cannot pay

The section above names "extending the commuted tie to the XMM two-address ops" as p4's
lever and asks to be falsified if the measured gain is near the full 8.3%. It is
falsified in the other direction: the gain is **zero**.

Rather than build the three-part change and measure it afterwards, the question was
isolated first. `movdqa_cost_bench.c` (in this directory) runs p4's exact SSE2 64x64
multiply-accumulate unit — 3 `pmuludq`, `psrlq`, `psllq`, 3 `paddq`, a `movdqu` load/store
pair, and `b` reloaded every iteration as the real loop does — in two variants that differ
ONLY in register copies:

* **A**, what trust-cg emits: **4** `movdqa` per unit; it copies the loop-INVARIANT `aik`
  lo/hi on every use and copies `b` again to build `b >> 32`.
* **B**, what LLVM emits: **2** `movdqa` per unit; each product ties to the dying `b`, and
  `b` is shifted IN PLACE at its last use.

Both print the same result, so they are semantically equivalent; B − A isolates exactly
2 `movdqa`, which is p4's own per-unit difference (~1.75). 200M units, 30 interleaved
rounds on `taskset -c 2`, minimum statistic, each arm carried twice:

| arm | min ms | vs A |
| --- | ---: | ---: |
| A — 4 `movdqa` | 409.43 | 1.0000 |
| A duplicate | 409.35 | 0.9998 |
| B — 2 `movdqa` | 409.64 | 1.0005 |
| B duplicate | 409.48 | 1.0001 |

The noise floor is 0.0002 and B sits inside it, marginally on the SLOW side. The loop is
bound by the `pmuludq`/`paddq` dependency chain and the load/store, not by dispatch slots
for renamer-eliminated moves. **So the XMM commuted tie is worth nothing here and should
not be built.** This also explains why the GPR arm measured neutral once it was reachable
(`2026-09-29-twoaddr-expand-unreachable/`): same mechanism, same answer.

### Where that leaves p4's 8%

With `movdqa` free, and every arithmetic and memory opcode already matching EXACTLY per
element, the per-element accounting no longer explains the gap — and the remaining
candidate, loop overhead, fails the same argument: `add`/`cmp`/`jb` are scalar ops that
issue alongside 12 `pmuludq` on a 6-wide core, so they should hide as completely as the
copies do.

The difference the innermost-loop comparison MISSES is structural. LLVM strides a whole
24-element ROW per iteration (`add $0xc0,%rsi`), i.e. its innermost loop IS the `k` loop
with `j` fully unrolled; trust-cg has TWO loop levels there, a `k` loop containing a
3-iteration `j` loop. So the honest next question for p4 is not a peephole at all — it is
whether the vectorizer can fully unroll a constant-trip inner loop and collapse a level,
which is a vectorizer design change and is NOT attempted here. Anyone picking this up
should re-derive the cost from the LOOP NEST (the `i`/`k` bodies execute 11.5M times for
this input), not from the innermost body alone.

## The loop-nest hypothesis is ALSO refuted: collapsing a level is worth 0.13%

The section above hands p4 on to "whether the vectorizer can fully unroll a constant-trip
inner loop and collapse a level". That was measured before anyone could act on it, by the
same method. `loop_nest_cost_bench.c` (in this directory) runs IDENTICAL SSE work — 12
multiply-accumulate units per `k`, over 24 `k` — in two structures:

* **A**, what trust-cg emits: a `k` loop containing a 3-iteration `j` loop of 4 units, with
  indexed addressing off the `j` counter.
* **B**, what LLVM emits: a `k` loop whose body is 12 units fully unrolled at fixed
  displacements, with no inner loop at all.

600k reps (288 units each), 30 interleaved rounds, `taskset -c 2`, minimum, arms duplicated:

| arm | min ms | vs A |
| --- | ---: | ---: |
| A — inner `j` loop | 78.86 | 1.0000 |
| A duplicate | 78.87 | 1.0001 |
| B — fully unrolled | 78.77 | 0.9988 |
| B duplicate | 78.75 | 0.9985 |

The floor is 0.0001, so B's 0.12-0.15% is REAL — and it is 1/60th of p4's 8.0%. **Full
unroll does not explain p4's gap and is not worth a vectorizer change on its own.**

## p4: every component hypothesis is now measured, and none of them is the 8%

| hypothesis | status | measured worth |
| --- | --- | ---: |
| 3 bounds checks + 2 invariant recomputations | the loop was DEAD (int3-proved) | 0 |
| 19 bytes of in-loop alignment NOPs | measured | 0 |
| `movdqa` 2.00/element vs LLVM's 1.08 | microbenchmark | 0 (0.0005, inside floor) |
| inner `j` loop vs full unroll | microbenchmark | 0.13% |
| arithmetic / memory opcode mix | identical per element | 0 by construction |

So the gap is **not in the innermost loop**, and this is where the trail honestly ends for
now rather than being handed on as another named lever. What has NOT been isolated: the
enclosing nest. For this input the `k` body executes about 11.5M times and the `i` body
480k times, and neither was ever compared against LLVM's — the whole campaign compared
innermost bodies. A next attempt should start by attributing p4's 0.063s across the
three loop levels, which on this host means instrumenting the program rather than reading
disassembly, since `perf_event_paranoid=4` denies hardware counters.

**Method note, earned twice here.** Both levers were specified in detail from static
disassembly analysis, and both were worth nothing. Each took ~15 minutes to refute with a
20-line microbenchmark that isolated exactly the claimed mechanism, against
multi-hour changes to register allocation and the vectorizer. On this core, isolate the
mechanism before implementing it.
