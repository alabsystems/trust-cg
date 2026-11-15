# x86 has NO instruction scheduler — and building one would buy about 1% (2026-09-29)

## The structural gap is real

`crates/trust-cg-opt/src/scheduler.rs` is **6708 lines**: list scheduling over a dependency
DAG with critical-path priorities, a per-port latency model, and two tiers the pipeline selects
by level —

> * **O1**: `InstructionScheduler` (fast, ILP-focused).
> * **O2/O3**: `PressureAwareScheduler`

— and its module doc opens `//! Pre-register-allocation instruction scheduling for AArch64.`
It operates on `MachBlock`/`MachInst` with an Apple M-series (Firestorm) latency table.

**The x86 pipeline contains no scheduling pass at all.** `grep` over
`crates/trust-cg-codegen/src/x86_64/pipeline.rs` finds no scheduler, and no x86 pass reorders
instructions for ILP — the x86 passes rewrite, fold, eliminate and lay out blocks, but never
permute a block for the pipeline. So x86 emits in ISel order, as modified by the peephole and
layout passes.

That is a large, nameable asymmetry, and it was the obvious candidate for `p4_matmul`, whose
remaining gap I had characterised as "scheduling/blocking quality vs gcc, on a loop already
unrolled 24-wide and check-free".

## So I measured the prize before building anything

An x86 scheduler cannot recover more than scheduling is WORTH on these programs. That is
directly measurable on the references, which have schedulers I can switch off:

* gcc: `-fno-schedule-insns -fno-schedule-insns2`
* clang/LLVM: `-mllvm -enable-misched=false -mllvm -enable-post-misched=false`

Falsifiability first — the flags must actually do something. Each arm's `main` has the SAME
instruction count with a DIFFERENT order, which is exactly what a scheduler does:

| program | gcc vs no-sched | clang vs no-sched | `main` insns (gcc / clang) |
| --- | --- | --- | ---: |
| p4_matmul | binaries differ | binaries differ | 148 / 141, unchanged both arms |
| b1_mispredict | binaries differ | **byte-identical** | 77 / 80, unchanged both arms |
| p2_collatz | binaries differ | binaries differ | 36 / 41, unchanged both arms |

### What scheduling is worth to the references

| program | gcc scheduler | clang scheduler |
| --- | ---: | ---: |
| p4_matmul | **1.28%** | **0.00%** |
| b1_mispredict | **0.11%** | 0.00% (identical binary) |
| p2_collatz | **0.00%** | **0.57%** |

**At most 1.3%.** Against gaps of 9.3%, 15.2% and 1.9% versus LLVM, an x86 instruction
scheduler cannot close any of them. The missing scheduler is NOT why these programs are slow,
and porting 6708 lines of AArch64 list scheduling — plus an x86 latency model for this host's
AMD core, which `perf_event_paranoid=4` makes unmeasurable here anyway — would be a large
investment for about one percent.

**This refutes my own hypothesis for p4.** I had named scheduling quality as p4's remaining
cause. It is not.

## Method, and a noise control that earns the numbers

`taskset -c 2`, INTERLEAVED samples (every arm measured once per round, 15 rounds, 3 warm-up
rounds), reported as `min` plus the rank statistic `P(arm < base)`. Equal-ISA references
(`-march=x86-64` / `-march=x86_64`, never `-march=native`). C ports from
`benchmarks/beat-llvm/progs_c/`, exit-code checked against every arm before timing.

Critically, each batch carries **`tcg2`, a byte-identical copy of the `tcg` binary**, as an
in-batch noise control:

| program | tcg | tcg2 | apart |
| --- | ---: | ---: | ---: |
| p4_matmul | 1.0929 | 1.0921 | 0.08% |
| b1_mispredict | 1.1518 | 1.1512 | 0.05% |
| p2_collatz | 1.0191 | 1.0189 | 0.02% |

So at this sample count the floor is **~0.1%**, which is what licenses reading a 1.28% gcc
scheduler effect as real and a 0.00% one as absent.

A caution recorded against my own first batch: there, clang and clang_nosched on b1 were
BYTE-IDENTICAL yet measured 1.8% apart — `min`-of-15 caught a bad slot. The in-batch identical
control is what exposes that, and it belongs in every batch. Without it I would have written up
"clang's scheduler is worth 1.8% on b1" from two copies of the same program.

## The per-program picture this re-frames

| program | vs **LLVM** (Rust, same language) | vs **clang** (C) | vs **gcc** (C) |
| --- | ---: | ---: | ---: |
| p4_matmul | 1.0929x | 1.0261x | 1.2378x |
| b1_mispredict | 1.1518x | 1.1954x | 1.1172x |
| p2_collatz | 1.0191x | 1.0185x | **0.7273x** (trust-cg WINS by 27%) |

Two things this makes plain that the single "vs gcc" number hid:

* **p4's big number is a gcc fact, not a trust-cg fact.** gcc is **1.133x faster than LLVM**
  on p4 (51.48 vs 58.30 ms). trust-cg is 1.026x clang and 1.093x LLVM there. So whatever wins
  p4 for gcc, LLVM does not do it either — the 1.24x is mostly the gcc/LLVM gap, not the
  LLVM/trust-cg gap.
* **gcc is not a uniform ceiling.** On p2 gcc is **1.40x SLOWER than LLVM** and trust-cg beats
  it by 27%. "Match gcc" and "match LLVM and clang" are different targets on different programs.

`b1` is the one program slower than every reference, and its gap survives at 1.15x LLVM /
1.20x clang — far above the 0.1% floor. Note also that LLVM-on-Rust is itself 3.8% slower than
clang-on-C on b1 (190.56 vs 183.62), so part of the "vs clang" figure is language overhead
rather than backend quality; 1.1518x LLVM is the fair backend comparison.

## Status of the clause

Still NOT met. Against LLVM and clang, four programs remain short: h1 2.488x, b1 1.152x,
p4 1.093x, p2 1.019x. What this report removes is a wrong explanation and a large piece of
speculative work — the absent x86 scheduler is worth about 1%, so the causes of all four gaps
lie elsewhere.
