# Post-RA spill-reload elision, and the 14.8% landmine it stepped on: the loop aligner's live-seam refusal (2026-09-29)

Two changes that only make sense together.

* **Post-RA redundant spill-reload elision.** The register allocator's spill
  replay emits each instruction's reloads immediately in front of it with no
  memory of the previous instruction's, so consecutive uses of one spilled vreg
  each reload the same slot into the same scratch. `h4_vec_dropper`'s vector loop
  carried three such reloads in twelve instructions.
* **The loop-head aligner now pads a LIVE fall-through seam.** It refused to,
  and that refusal turned the first change into a **14.8% regression on
  `h3_box_leak`** — a program that had reached parity hours earlier.

Combined, against the previous default, over the 18-program runtime corpus:

| program | old | new | verdict |
| --- | ---: | ---: | --- |
| `h1_vec_push_sum` | 1.0023 / 1.0036 | **0.9800 / 0.9788** | **2.3% faster; now BEATS LLVM -O3** |
| `h4_vec_dropper` | 1.0494 / 1.0487 | 1.0334 / 1.0454 | 0.5–1.5% faster |
| `h2_vec_grow` | 1.0013 / 1.0012 | 1.0013 / 1.0010 | neutral (already at parity) |
| `h3_box_leak` | 0.9875 / 0.9883 | 0.9884 / 0.9859 | neutral |
| `p4_matmul` | 1.0816 / 1.0805 | 1.0809 / 1.0808 | neutral |
| `p7_sieve` | 0.7416 / 0.7420 | 0.7422 / 0.7400 | neutral |
| `v1_saxpy` | 0.6505 / 0.6504 | 0.6502 / 0.6505 | neutral |
| the other 11 | — | — | BYTE-IDENTICAL |

Each arm is carried TWICE as byte-identical copies so it has its own noise floor;
`taskset -c 2`, interleaved rounds, minimum of each. Execution differential 18/18
MATCH. Nothing got slower.

## Part 1: the transform

```text
  mov R10, [slot]      ; the spiller's reload for instruction A
  <A>                  ; touches neither R10 nor the slot
  mov R10, [slot]      ; the spiller's reload for instruction B   -> DELETED
```

plus the store-to-reload form, where a spill store's source register still holds
the value and the reload becomes a register copy. Measured on `h4_vec_dropper`'s
vector loop:

```
  OFF (12 instructions, 3 slot accesses)       ON (10 instructions, 1 slot access)
    mov -0x70(%rbp),%r10   ; reload              mov -0x70(%rbp),%r10   ; reload
    lea (%rcx,%r10,8),%rax                       lea (%rcx,%r10,8),%rax
    movdqu (%rax),%xmm0                          movdqu (%rax),%xmm0
    paddq %xmm0,%xmm2                            paddq %xmm0,%xmm2
    movdqu 0x10(%rax),%xmm0                      movdqu 0x10(%rax),%xmm0
    paddq %xmm0,%xmm1                            paddq %xmm0,%xmm1
    mov -0x70(%rbp),%r10   ; reload  DELETED     add $0x4,%r10
    add $0x4,%r10                                mov %r10,-0x70(%rbp)   ; store
    mov %r10,-0x70(%rbp)   ; store               cmp %rdx,%r10
    mov -0x70(%rbp),%r10   ; reload  DELETED     jb  ...
    cmp %rdx,%r10
    jb  ...
```

The remaining reload at the loop head is redundant too — the previous iteration's
store put the value in the same register — but this pass is BLOCK-LOCAL, and that
reuse crosses the back edge. Recorded as the obvious next increment.

Soundness rests on the pass's own conditions, because TV-5 does not police this:
its documented v1 misses include spill-slot and memory dataflow, the same caveat
`x86_try_rename_coalesce_copy` carries. An entry says "slot `s`'s contents are
also in register `holder`, covering `bytes` bytes" and dies on: any instruction
clobbering the holder's 64-bit root (via the same `x86_inst_clobbers_gpr64_root`
the `MovRR` coalescer uses, which resolves vregs through the allocation and
accounts for implicit defs); any store to `s`; a call or return; any OTHER memory
write; a proof-carrying, pseudo, atomic or fence instruction; and every block
boundary. A deletion additionally requires the holder to be the reload's
destination at the IDENTICAL width spelling, so x86's implicit zero-extension of a
32-bit destination is already in place.

One rule is there purely to fail closed: **an instruction with a def operand this
pass cannot resolve to a physical register clears the whole map.**
`resolve_operand` answers `None` for a vreg missing from the allocation, and an
unresolved def is indistinguishable from a def of a holder — so an incomplete
allocation must not read as "clobbers nothing". A test pins it by removing one
entry from the allocation and checking that the same function stops firing.

## Part 2: the 14.8% landmine

With the transform on and the aligner unchanged, `h3_box_leak` went from 0.9893x
to **1.1460x** LLVM -O3. Its hot INNER loop was byte-for-byte identical in both
arms; the pass had only removed two reloads from an OUTER-loop preamble that runs
20 times. What changed was the inner loop's ADDRESS.

The aligner's own trace (`-Ztrust-ir-cg-args=trace-x86-loop-align`, a knob this
work had to add — see Part 3) named it in one line:

```
[loop-align] `..h3_box_leak4main`: heads=2 already=0 padded=0 (+0 bytes) miss=0
  | declines: nested_head=0 pad_too_big=0 body_too_big=1 already_contained=0 live_seam=1
```

h3's 37-byte inner loop sat 35 bytes into a 64-byte fetch line, so it straddled;
the aligner recognised it, and refused because the seam before it is a LIVE
fall-through. A four-arm build settles it beyond argument:

| arm | min | vs LLVM -O3 |
| --- | ---: | ---: |
| reload-elide OFF, seam-pad 0 (previous default) | 23.179 ms | 0.9893 |
| reload-elide OFF, seam-pad 63 | 23.253 ms | 0.9924 |
| reload-elide ON, seam-pad 0 | 26.851 ms | **1.1460** |
| **reload-elide ON, seam-pad 63** | **23.101 ms** | **0.9859** |

Allowing the pad recovers the whole 14.8% and then produces the fastest arm of
the four. With the transform OFF the knob changes h3's binary not at all, so it
is a containment repair that fires exactly when needed, not a blanket speed-up.

### Why the refusal was reasonable, and why it expired

The refusal was imported from the AArch64 aligner's only measured failure mode
(huffbench: 3.0e9 retired pad NOPs inside a hot enclosing loop, for an alignment
worth 0), justified on the ground that 41 of 45 innermost heads on this corpus sit
behind a non-elided `jmp`, so refusing "costs nothing today". That was true of the
code as it then stood, and it stopped being true the moment an unrelated pass
changed one function's instruction count. **This is the second measured-OFF
default this week whose justification expired rather than being wrong** — the
first was LICM's pointer-base arm, and the pattern is now recorded twice.

### The new policy comes with an argument, not just a measurement

Write `h` for the loop head's offset and `len` for its body length. G5 admits only
`len <= 64`; G6 pads only a body that STRADDLES where it stands, i.e.
`h mod 64 + len > 64`; and the pad is `64 - (h mod 64)`. Subtracting:

> **the pad is strictly SHORTER than the loop body, always.**

A straddling loop cannot need a pad as long as itself. The pad retires once per
ENTRY to the loop and the body once per ITERATION, so the worst case is under one
extra iteration's worth of fetch per entry against one saved line crossing per
iteration — it pays from roughly the second iteration. The huffbench case is
excluded by G6, not by the seam gate: "alignment worth 0" means that loop was
never a containment repair at all. A `debug_assert` in the pass now states the
invariant at the decision point.

`-Ztrust-ir-cg-args=x86-loop-align-seam-pad=0` restores the refusal, and the unit
test asserts BOTH directions through it.

## Part 3: the aligner had no A/B surface under `trustc` at all

All four of the aligner's levers, and its decision log, were reachable only
through `TCG_*` environment variables — which `trustc` refuses before the backend
loads. So under the Trust driver a pass that inserts NOPs into hot loops, whose
four defaults were all chosen on AArch64 evidence, could not be measured either
way. That is the eighth instrument this campaign has found in that state.

Now tracked: `no-x86-loop-head-align`, `x86-loop-align-seam-pad=<bytes>`,
`x86-loop-align-max-body=<bytes>`, `x86-loop-align-max-skip=<bytes>`,
`trace-x86-loop-align`. Every measurement above exists because of them.

## What is NOT claimed

`h1_vec_push_sum`'s 2.3% is reproducible (two builds, two byte-identical copies
each, 0.12% floor) but it is **not attributed to either transform**: h1's vector
loop body is instruction-identical between the arms, and both arms' bodies are
contained in one fetch line, so the gain is a layout effect whose mechanism this
report did not isolate. It is recorded as a measured fact about the new default,
not as a transform's earnings.

More generally: this session measured a **14.8% swing produced by code layout
alone** on a program whose hot loop did not change. Every remaining gap on this
corpus — `b1_mispredict` 1.12x, `p4_matmul` 1.08x, `h4_vec_dropper` 1.03x,
`p2_collatz` 1.02x — is smaller than that swing. Until an instruction-count change
can be measured without its layout shadow, "matches LLVM" on a sub-30 ms program
is a statement about one binary, not a property of the backend. Carrying both arms
twice, as every table here does, is the minimum that makes such a reading
falsifiable.

## Verification

18/18 execution MATCH on the default build; the verification-ON Trust corpus test;
Lean-through-Clean 5/5; TY 9/9; `trust-cg-opt` green; `trust-cg-codegen` green
apart from the two pre-existing AArch64-host failures. Six new tests for the
reload pass (the transform, a clobber, a call, an unrecognised store, the
fail-closed unresolvable def, and the block boundary) and the aligner's seam test
rewritten to assert both directions.

Also fixes a pre-existing `needless_return` that made `scripts/check_clippy.sh`
RED on `main` in `crates/trust-cg-verify/tests/x86_sse_lane_gate.rs`; the gate is
green again.
