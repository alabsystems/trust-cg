# NEON LD1/ST1 post-index live writebacks through `neon_butterfly` (X-OPCODES-P11) — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This is the qualifying run for the new required Linux floor target
[`neon_butterfly_writeback_execution`](../../../crates/trust-cg-codegen/tests/neon_butterfly_writeback_execution.rs).
It addresses the boundary that
[`neon_ld1_st1_post_execution`](../2026-09-23-linux-neon-ld1-st1-post/README.md)
left open for ledger gap X-OPCODES-P11. That target executes NEON LD1/ST1
post-index words, but every writeback in it is dead, so the base-register
update was never observed.

The run is on clean source `59ef39126879ac8ea8ea5685a071e3b9dfebd790` (tree
`f8331198559687455dbe49c03cc4e3b397a9ef09`). `git status --porcelain
--untracked-files=all` was empty before and after, and HEAD did not move.
The host is the Linux AArch64 GNU machine (NVIDIA Grace, kernel
`6.17.0-1026-nvidia`), with Ubuntu gcc 13.3.0 as `cc`, rustc and cargo
1.97.1, GNU binutils 2.42 and LLVM 18.1.3 `llvm-objdump`.
`records/results.json` (`host`) holds the identities and the CPU feature
line. The AY solver and Clean checker were pinned first on `PATH`. Every
command passed:

- `neon_butterfly_writeback_execution` with the Linux floor's arguments
  (`--nocapture --test-threads=1`), once with the record directory and once
  without:
  `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 23.33s`
  and
  `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 30.66s`.
  The floor's own `classify_result` judges the plain transcript `pass`, with
  no skip line. `check_linux_aarch64.py` lists 148 targets, including this
  one, and `check_darwin_aarch64.py` has 194 rows (1,332 minimum passes),
  including this one with minimum 4.
- The sibling target `neon_ld1_st1_post_execution`, whose header comment now
  points here:
  `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 20.51s`,
  also judged `pass` by `classify_result`.
- `trust-cg-codegen --lib` (the whole library suite):
  `test result: ok. 4089 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 8.99s`.
  The ignored test is the existing explicit real-tool
  `raw_machir_request_cache_real_exhaustive_campaign`.
- `cargo check -p trust-cg-codegen`, with and without `--features verify`.
- `scripts/check_fmt.sh`.
- The three gate-script suites: `Ran 94 tests`, `OK (skipped=1)`. The
  skipped test is host-conditional, as in earlier runs.
- `native_test_host_matrix.py --check`, `check_documentation.py --check` and
  `generate_diagnostics_inventory.py --check`.

X-OPCODES-P11 stays **PARTIAL**. A separate audit decides closure.

## Why `neon_butterfly`

`neon_fmap`'s remainder loop recomputes every stream pointer with MADD, so a
mutant that changes only an LD1/ST1 writeback passes the oracle there. The
one scheduled emitter whose writeback is live is `neon_butterfly`, which
`trust-cg-opt/src/pipeline.rs` schedules at O2, Os and O3. At base
`dbfc88b79`, `apply_candidate` (`neon_butterfly.rs` lines 1190–1263) forms one
pointer per stream in the vector preheader. It advances each pointer only
through `LD1 {Vt.4S}, [Xn], #16` for the read streams `z[i]` and `z[i+m]`,
and through `ST1 {Vt.4S}, [Xn], #16` for the output streams `w[i+k]` and
`w[i+kb]`.

The target builds three trust-ir kernels in the exact shape that
`RecognizedButterfly::recognize` admits. The matcher was read, not guessed.
All three use strict `llvm.fma.f32`:

- `bfly_nested_e0` uses the Oscar `Fft` address recipe (a second MADD for
  `z[i+m]`, `w[i+k]` and `w[i+kb]` inside the loop), with twiddle offset 0;
- `bfly_nested_e8` is the same with offset 8, so the pass forms the twiddle
  range start with an ADD;
- `bfly_hoisted_e8` forms `z + m*8`, `w + k*8` and `w + kb*8` before the
  loop, with offset 8.

`Compiler` compiles them at O0–O3. The pass fires on all three at O2 and O3,
for ELF and Mach-O. O0 and O1 schedule no NEON pass. Os is not reachable
through `Compiler`, whose `OptLevel` stops at O3.

## What the run shows

- **Decode.** Every word of the final object's code section is classified
  twice, by trust-cg-lift and by the test's own bit mask
  (`word & 0xbfbff000 == 0x0c9f7000`), and the two must agree. The test
  reads the ELF and Mach-O symbol tables itself. At O2 and O3 each kernel
  holds exactly two LD1 and two ST1 post-index `.4S` words on four distinct
  base registers: 6 LD1 and 6 ST1 per object. LLVM objdump (both
  containers) and GNU objdump (ELF) give the same per-function counts on
  every retained object (`results.json` `objects`). The O0, O1 and
  no-`neon_butterfly` objects have none. The native O2 and O3 objects are
  byte-identical to the explicit `aarch64-unknown-linux-gnu` objects
  (`72372238…` and `f8276cba…`, 2,712 bytes each).
- **Liveness, decoded stream.** `records/liveness/*.tsv` lists, for each of
  the 12 LD1/ST1 words per object (both containers, O2 and O3), its base
  register, the word that reads it next and the backward branch on that
  path. In every case the reader is the same LD1/ST1 on the next iteration,
  reached through the loop's `b.lt`. No word between the writeback and that
  read defines the register. The walk models the general-register effect of
  every word family in these functions and refuses any other. The same
  walk reports both writebacks of a `neon_fmap` remainder loop compiled in
  the test dead (`records/objects/fmap-control-*.o.gz`).
- **Liveness, external listing.** The qualify harness repeats the check on
  the LLVM and GNU objdump text of every O2/O3 object
  (`butterfly_loops` in `results.json`). In each kernel, one conditional
  branch targets the first LD1 (the loop top). The 13-word loop body
  mentions each of the four base registers only as the base of its own
  post-index LD1/ST1. For example, `native-O2.o` `bfly_nested_e0` has its
  loop at `0x160`–`0x190` on `x4`, `x2`, `x1` and `x0`.
- **Execution.** Each level's host ELF object (`records/objects/native-*.o.gz`)
  is linked with `cc` against the C oracle in `records/oracle/driver.c.gz`.
  The oracle performs each scalar operation with one inline-asm A64
  instruction in the loop's operand order. gcc at `-O0` compiles
  `F(e+4) * ndi` as `fmul s0, ndi, ei` and passes `fmaf`'s multiplicands
  swapped, which changes which NaN propagates once FNEG has produced a NaN
  of the opposite sign. A first draft that used C operators and `fmaf`
  failed at O0 for that reason. After every call the oracle compares the
  whole six-region buffer bit for bit. That covers every output element, the
  guards and every input the call must not write.

  Each kernel gets 9,633 calls per level: 3 value patterns (finite normals,
  IEEE specials with the default NaN, raw bits with one signalling NaN)
  × 19 placements × (3 starts × 54 trip counts + 7 magnitude pairs).
  - The trip counts run from −2 to 40, plus 63–65, 127–129, 255–257, 300
    and 301. A count of 1 or less is the do-while's single iteration.
  - The magnitude pairs are `(-2, 5)`, `(-2^40, -2^40+5)`,
    `(2^31-8, 2^31-1)`, `(2^31-7, 2^31-1)`, `(2^31-1, 2^31+4)`,
    `(2^31, 2^31+3)` and `(2^40, 2^40+5)`.
  - Placements 0–11 pass the seven-pair check. They include disjoint
    streams in both address orders; ranges that touch (B after A, A after
    B, A after S1 and B before S2); `m` of 1, 0 and −1, so the reads
    overlap; and the twiddle touching A, touching B, inside S1 or
    straddling two elements.
  - Placements 12–18 overlap a store range with a read range (including
    the in-place FFT), with the other store range, or with the twiddle
    (inside A, or over B's last word).

  The driver predicts each call's path from the byte ranges, independently
  of the object. Per kernel it expects 4,161 scalar-path calls, 216 one-pair
  calls and 5,256 calls with two or more pairs, with 148,104 vector pairs and
  2,844 odd scalar tails. The counts are identical for every kernel and
  level. All 28,899 calls per level match at O0, O1, O2 and O3, and at O2
  compiled with `TRUST_CG_DISABLE_PASSES=neon_butterfly`.
- **Mutation.** At O2 and O3, 48 objects are made from the executed object,
  each with one LD1/ST1 word changed, and each is run for its own kernel
  (`records/mutation/mutants-O*.tsv`). All 96 exited 1 with an oracle
  `MISMATCH` line for that kernel, and none mismatched in a scalar-path
  call. On finite inputs, all 1,752 multi-pair calls failed for every
  mutant. There are two classes:
  - 24 per level change only the writeback. One rewrites the word to
    `[Xn]`. The other uses register post-index `[Xn], Xs`, where a
    must-dataflow over the decoded stream proves Xs holds 8 at every entry
    to the loop: x15 for `bfly_nested_e0` and `bfly_hoisted_e8`, x19 for
    `bfly_nested_e8`. That is the pass's own 8-byte twiddle-range length,
    so each pointer advances 8 bytes instead of 16. These failed in 5,251
    to 5,256 of the 5,256 multi-pair calls and in none of the 216 one-pair
    calls, where the last iteration's writeback is dead. The other
    target's literal `[Xn], X1` is not a stride here: x1 is the ST1 base of
    the `w[i+k]` stream in every object.
  - 24 per level change the transfer: narrowed to 64 bits (Q=0, which also
    makes the implied post-index 8) or replaced by NOP. These also failed
    in 188 to 216 of the 216 one-pair calls.

## Negative controls

- The decode gate refuses the scalar-only O0 and O1 objects, and O2
  compiled with `TRUST_CG_DISABLE_PASSES=neon_butterfly`, on both
  containers. The O2 objects without the pass are retained.
- For each container, each of the 12 LD1/ST1 words is replaced one at a
  time by the narrowed, NOP, no-writeback or wrong-stride form. The gate
  refuses all 48 mutants and names the kernel.
- With each kernel's backward branch replaced by NOP, the census still
  accepts the object. The liveness gate refuses it, and the walk reports
  all four writebacks dead (12 per container).
- The liveness walk reports the `neon_fmap` remainder writebacks dead.
- The 96 executed mutants above. The writeback-only half is the
  discriminating control: in `neon_ld1_st1_post_execution` the same class
  passes the oracle, and here every one fails it.

## Records

- `records/results.json` holds:
  - the source and host identities;
  - each command, with its exit status, duration and `test result:` lines;
  - both floor classifications and the Linux and Darwin floor rows;
  - for every retained object, its SHA-256, the per-function LD1/ST1
    counts from each external disassembler and the external loop check;
  - the mutant summaries.
- `records/logs/*.log.gz`: the complete output of each command.
- `records/objects/*.o.gz` are the objects the test compiled, stored
  gzip-compressed because the repository ignores `*.o`:
  - `native-*` were linked and executed;
  - `aarch64-*-O*`, `*-O2-without-neon_butterfly` and `fmap-control-*`
    were checked at object level.
- `records/liveness/*.tsv`: the decoded-stream liveness report per
  container and level.
- `records/oracle/driver.c.gz`: the C oracle as compiled.
- `records/mutation/mutants-O2.tsv` and `records/mutation/mutants-O3.tsv`
  (not `mutants/`, which the repository ignores): every mutant's kernel,
  word, base register, original and mutated word, exit status, decode-gate
  verdict and mismatch count per path class, and the first `MISMATCH` line.
- `records/disasm/*.txt.gz` and `records/symbols/*.txt.gz`: LLVM and GNU
  objdump listings and GNU `readelf -sW` symbol tables.
- `harnesses/`: the qualify and archive scripts that produced this
  directory. `source/`: the tested test file.
- Recorded paths under `/tmp/claude-1000/…` are the original capture
  locations on the host. They are not themselves evidence.

## Boundary

This is object and execution evidence on one host for the named shapes and
inputs. It is not a proof of `neon_butterfly`, of its runtime alias check or
of the LD1/ST1 encoder. The path each call took was predicted from the byte
ranges and confirmed only indirectly: mutants of vector-body words never
changed a scalar-path call's result.

- The kernels are one f32 butterfly shape with strict `llvm.fma.f32` and
  twiddle offsets 0 and 8. The matcher also admits offsets up to 4,088, but
  an exploratory O2 compile with offset 4,088 did not vectorize: the
  `+4092` address of the second field was hoisted out of the loop instead
  of folded into its load, so the two twiddle loads no longer share a base.
  Clang's `llvm.fmuladd` form, which Oscar uses, is not run.
- Os schedules the pass but is not reachable through `Compiler`.
- The oracle checks agreement with the host's scalar instructions, not IEEE
  conformance.
- The Darwin floor row (minimum 4) has not run on a macOS host. Its Mach-O
  objects were checked here at object level only (decode, liveness and the
  external LLVM listing).
- The `neon_iota_fill` LD1/ST1 uses and the emitters that cannot run in the
  default pipelines (`vectorize.rs`, contains4, `neon_map`/`neon_stencil`
  trailing ST1, `neon_condstore`) have no native control.
