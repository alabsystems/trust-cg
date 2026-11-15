# What the x86 vectorizer is actually worth (2026-09-29), and a p4 diagnosis I withdraw

Two results. The first is a measurement that was not previously possible; the second is a
correction to a claim of mine from earlier today.

## 1. The vectorizer had no reachable lever, and it is worth 3.2x to 54x

`X86Vectorize` is the largest single optimization in this backend. Its only switch was the
`TCG_NO_VECTORIZE` environment variable, and `trustc` refuses every `TCG_*` variable before
the backend loads — so its NET per-program effect had never been measured through the real
compiler. Its presence was inferred from vector opcodes in the output, which is not the
same thing.

Adds `-Ztrust-ir-cg-args=no-x86-vectorize` (whole pass) and
`-Ztrust-ir-cg-args=no-x86-vec-regarg` (the reg-arg/saxpy-q reduction tier alone). One
bridge, exit codes agreed three ways first, 11 interleaved samples per arm on one pinned
core, `min` reported:

| program | vectorizer ON | OFF | OFF/ON | reg-arg tier OFF |
| --- | ---: | ---: | ---: | ---: |
| v2_memfill | 2.89ms | 157.60ms | **54.443x** | 1.006x |
| v3_popcount | 12.52ms | 320.66ms | **25.608x** | 1.002x |
| v1_saxpy | 48.79ms | 299.19ms | **6.133x** | 1.000x |
| p7_sieve | 22.87ms | 77.60ms | **3.393x** | 0.998x |
| p4_matmul | 63.84ms | 206.31ms | **3.232x** | 0.997x |

So the vectorizer pays for itself many times over on every program that reaches it, and
this is now a measured fact rather than an inference. The reg-arg tier specifically makes
no measurable difference on any of them, which also tells us p4_matmul does NOT go through
that tier despite its inner loop using the `PADDQ`-accumulate shape that tier emits.

## 2. WITHDRAWN: "p4_matmul's hot loop wastes 8 of 26 instructions"

Earlier today I reported that p4's innermost loop spends three instructions on
un-eliminated bounds checks (`cmp $0x240` — `N*N` = 576) and two on loop-invariant
recomputations, and I called an earlier diagnosis of mine ("needs i64 multiply
vectorization") too coarse. **That correction was itself wrong, and the original reading
was closer to right.**

The error: I selected "the innermost loop" from the disassembly by SMALLEST BACKWARD-BRANCH
SPAN. Span does not determine nesting. p4's `main` has seven backward branches, and the
26-instruction one I analysed is a REMAINDER loop, not the hot path.

The real hot loop is `0x20c14..0x20de4`: **103 instructions for 24 elements — 4.29 per
element — with ZERO bounds checks**, already vectorized:

```text
  mov (%rdi),%rdx ; mov (%rbx),%rax ; mov 0x8(%rbx),%rcx
  imul %rdx,%rax  ; imul %rdx,%rcx           ; two pipelined scalar i64 multiplies
  movq %rax,%xmm0 ; movq %rcx,%xmm1 ; punpcklqdq %xmm1,%xmm0
  paddq %xmm0,%xmm2                          ; packed accumulate
```

The pre-RA dump confirms the shape: row bases are hoisted out of the `j` loop
(`LeaSib v298/v299` in the loop's preheader) and the per-element bounds checks are
strength-reduced to per-ROW checks against **553** = `N*N - N + 1`. The backend already
does the two things I claimed it was missing.

The scalar-multiply-plus-pack sequence is also deliberate and documented in
`x86_vectorize.rs`: "two pipelined scalar IMULs beat the 3xPMULUDQ + 2-shift + 2-add lo64
compose", which is LLVM's own SSE2 strategy for 64-bit lane products. I hypothesised that
vectorizing the ACCUMULATION was counter-productive — six instructions per two elements
against four for plain scalar adds. The table above refutes that too: turning the
vectorizer off costs p4 **3.232x**.

## What this leaves for p4

Its 1.029x against clang and 1.243x against gcc is what remains AFTER a 3.2x vectorization
win, on a loop that is already unrolled 24-wide, check-free, and packing its accumulation.
gcc (51.32ms) also beats clang (61.97ms) here, so the bar is gcc, and the difference is
scheduling or blocking quality rather than a missing transform. That is a much narrower and
less promising target than "three redundant bounds checks", and saying so is the point of
this note.

**Method note for the next person:** do not pick a loop out of a disassembly by branch
span. Enumerate every backward branch, establish nesting by containment, and cross-check
against the pre-RA dump (`-Ztrust-ir-cg-args=vectorize-late -Ztrust-ir-cg-args=trace-vectorize-dump`).
Both mistakes above came from skipping that.
