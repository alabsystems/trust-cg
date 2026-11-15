# A frontend-free LLVM bar: both backends on IDENTICAL LLVM IR

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · in-tree LLVM 22.1.2
(`opt`, `llc`) · `trust-cg-ws2-import` built `--features driver`

## Why this method exists

Every "vs LLVM" figure in this repo compares **rustc+LLVM against rustc+trust-cg on Rust
source**. That is valid for the Rust lane and unavailable for the others: Clean's
fixtures are `.tir` modules from Lean and TY compiles TLA+ bytecode, and clang has no
frontend for either. So "performance at least matching LLVM and clang" could not be
stated for those lanes at all — not because it was unmeasured, but because the
comparison as framed did not exist.

`crates/trust-cg-llvm-import` is an **LLVM IR -> trust-ir** importer ("for external
correctness corpora", 20 e2e tests, a `trust-cg-ws2-import` CLI). It makes a different
comparison possible:

```text
  fixture.ll --opt -O3--> o3.ll --llc -O3----------------------> LLVM backend
                                └--ws2-import->trust-ir--trust-cg -O3--> trust-cg backend
```

Both backends consume the SAME optimized LLVM IR, so the frontend drops out and what
remains is codegen. It also bypasses MIR, so it is unaffected by the `panic=abort`
bounds-check refusal that currently blocks ten Rust programs.

## Result: trust-cg emits 1.90x-3.47x LLVM's instruction count

| fixture | IR lines (O0 -> O3) | llc -O3 | trust-cg -O3 | ratio | LLVM SIMD | cg SIMD |
|---|---|---:|---:|---:|---:|---:|
| ary3_init_offset | 245 -> 491 | 397 | 1377 | **3.47** | 31 | 40 |
| intmm_main_loop | 330 -> 265 | 150 | 414 | **2.76** | 0 | 0 |
| intmm_initmatrix | 177 -> 135 | 77 | 206 | **2.68** | 0 | 0 |
| revertBits | 245 -> 248 | 252 | 479 | **1.90** | 0 | 0 |

Without the `opt -O3` step (both backends on raw clang -O0 IR) the ratios are 2.45, 2.76
and 2.68 on the three that import, so the gap is not an artifact of unoptimized input.

## ⚑ TWO CORRECTIONS, the second of which replaces the first

**Correction 1 was WRONG.** I recorded that the importer "does not support phi nodes",
inferred from a refusal on a transcription of p2_collatz's loop. That inference was
false and I tested it instead of trusting it: a diamond phi, a loop-carried phi, a
conditional branch with phis on BOTH targets, a nested loop with loop-carried phis, and a
two-block cycle with phis in both blocks all import today.

**Correction 2, the real cause: the importer required the entry block to be literally
named `entry`.** Proved in both directions — renaming the rejected function's first block
`start:` to `entry:` imports it (62 instructions), and renaming a WORKING function's
`entry:` to `start:` reproduces the identical error. Two cases were handled before (a
block named `entry`, and an UNLABELLED first block via `implicit_entry_block_label`); a
first block with any other explicit label fell through both, leaving the interned `entry`
block empty, and the function was rejected with

```text
  block in @f has no terminator (phi or fallthrough not supported)
```

which names neither the cause nor the block and blames phis that are fine. That message
is what produced correction 1.

**This mattered well beyond hand-written IR: rustc names its first block `start`**, so
every rustc-emitted function hit it. FIXED here, with
`tests/entry_block_any_label.rs` pinning `entry`, `start`, and arbitrary labels in both
directions; the importer's other 19 targets are unaffected (58 passed, and the one
failure — `apple_objects_...` in `symbol_linkage_elf` — is a macOS test failing on a
Linux host both with and without the change).

## And with the kernel importing, a RUNTIME number that invalidates this lane as a proxy

The collatz kernel now imports, so the comparison can be run with timing and with output
agreement checked (both binaries exit 88):

| IR into both backends | llc -O3 insns | trust-cg insns | llvm ms | trust-cg ms | ratio |
|---|---:|---:|---:|---:|---:|
| as written | 43 | 123 | 164.3 | 422.8 | **2.574** |
| after `opt -O3` | 61 | 162 | 163.2 | 424.1 | **2.599** |

60 interleaved rounds, both arms doubled (floors 0.0022 and 0.0012).

**The same algorithm through the MIR path is 1.011x LLVM.** So the import path is 2.5x
slower than the MIR path on identical source logic, and the gap is not the backend's
codegen in general — it is the trust-ir the IMPORTER produces, which this backend's passes
evidently recognize far less well than the trust-ir the MIR lowering produces. This repo
has a name for that: recognizers keyed to one spelling declining an equivalent one.

**Consequence for the method:** this lane measures the importer, not the backend, so it
is NOT a usable LLVM bar for the Clean or TY lanes. Proposing it as one (as the earlier
version of this report did) was wrong. Closing the gap would take making the importer's
trust-ir resemble the MIR lowering's, which is a much larger job than the two parser
fixes below.

## What this does and does NOT establish

**Does:** the lane exists and runs, and on the selected importable IR fixtures the import path
trails LLVM by 1.9x-3.5x instructions. `ary3_init_offset` is notable: trust-cg emits MORE SIMD (40 against
31) and still 3.47x the instructions, so the gap there is not a missing vectorizer.

**Does not:**

* **The four-fixture table above is static instruction count.** Those small
  correctness fixtures have no driver or workload and were not timed. The separate
  collatz comparison above records runtime for its own workload. Instruction count has been a
  misleading proxy in this repo before — see
  `reports/perf/2026-09-30-loop-top-refuted/`, where a change that reduced taken branches
  exactly as intended was 4.7% slower, and
  `../2026-10-01-x86-xorshift-demanded-bits/`, where a 38 -> 37 instruction change was
  worth 6.4% because the mechanism was latency. A 2-3x static ratio is a strong signal,
  but it is a signal.
* **It is not the production Rust path.** Rust reaches trust-cg through MIR -> trust-ir,
  and on that path the eight currently-compilable programs are at geomean **0.9517x LLVM
  runtime**. The import path produces different trust-ir shapes, and this repo's history
  is full of recognizers that accept one spelling and decline an equivalent one
  (`../2026-10-01-h1-vectorizer-dialect-gates/` cleared three such gates in one commit).
  The most likely reading of a 2-3x gap on imported IR is dialect coverage, not a
  2-3x-worse backend.
* **It is not one of the goal's four lanes.** The input here is C-through-clang. The
  method is what transfers to Clean and TY, not this corpus.

## Remaining coverage gaps and qualification limits

* **Imported shape coverage remains limited.** The earlier blanket no-phi diagnosis
  was withdrawn above: supported diamond and loop phis import. The entry-label fix
  removes the diagnosed refusal; it does not establish acceptance of arbitrary LLVM
  SSA IR or equivalence of this lane to the MIR, Clean, or TY production paths.

* **Cannot consume rustc-emitted LLVM IR.** All five Rust corpus
  programs refuse with `unsupported: aggregate / vector type <{ [24 x i8], ptr, ptr, ptr }>`
  — a Rust runtime shape (panic `Location`/fmt). So the obvious move, feeding the existing
  beat-llvm corpus's own IR to both backends, does not work today. Supporting that
  aggregate would turn the whole 18-program corpus into a frontend-free comparison,
  including the ten programs the bridge currently refuses.
* `ary3_reverse_accum` refuses with `codegen: AOT direct module-function binding`, and
  `ary3_init_clang_o0` fails in `opt` before either backend sees it.

## Next step for the Clean and TY lanes

Representative Clean and TY loop shapes and instruction mixes transcribed into `.ll`
can help investigate importer coverage. The collatz comparison above shows that this
lane currently needs further qualification before it can supply a performance bar for
those production paths. A trust-ir -> LLVM IR emitter could instead let their actual
modules be compiled both ways; no such emitter exists (the only LLVM crate here imports).
