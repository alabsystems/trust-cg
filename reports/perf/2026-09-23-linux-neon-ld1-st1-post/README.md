# NEON LD1/ST1 post-index execution on Linux (X-OPCODES-P11) — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This is the qualifying run for the new required Linux floor target
[`neon_ld1_st1_post_execution`](../../../crates/trust-cg-codegen/tests/neon_ld1_st1_post_execution.rs).
It addresses the last open family of ledger gap X-OPCODES-P11: NEON LD1/ST1
post-index (`NeonLd1Post`/`NeonSt1Post`). The gap had credited these forms
to `neon_array_execution`, but that target never runs them.

The run is on clean source `4eafcaccf5f1236efd0dd7c306d1629b60af764d` (tree
`ea9fae04ac1c4b00e4ba946c927e26d466d9e6df`). It replaces the first run of
this archive, on `99245c009`, after the review found an undisclosed
evidence boundary: the post-index writeback is never observed (see
**Boundary**). The test now enforces that boundary, and this run re-records
everything. The compiled objects are byte-identical to the first run's. `git status --porcelain
--untracked-files=all` was empty before and after, and HEAD did not move.
The host is the Linux AArch64 GNU machine (NVIDIA Grace, kernel
`6.17.0-1026-nvidia`), with Ubuntu gcc 13.3.0 as `cc`, rustc and cargo
1.97.1, GNU binutils 2.42 and LLVM 18.1.3 `llvm-objdump`.
`records/results.json` (`host`) holds the identities and the CPU feature
line. The AY solver and Clean checker were pinned first on `PATH`. Every
command passed:

- `neon_ld1_st1_post_execution` with the Linux floor's arguments
  (`--nocapture --test-threads=1`), once with the record directory and once
  without:
  `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 16.41s`
  and
  `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 15.83s`.
  The floor's own `classify_result` judges the plain transcript `pass`, with
  no skip line. `check_linux_aarch64.py` now lists 146 targets, including
  this one.
- `trust-cg-codegen --lib` (the whole library suite):
  `test result: ok. 4069 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 4.73s`.
  The ignored test is the existing explicit real-tool
  `raw_machir_request_cache_real_exhaustive_campaign`.
- `cargo check -p trust-cg-codegen`, with and without `--features verify`.
- `scripts/check_fmt.sh`.
- The three gate-script suites: `Ran 94 tests`, `OK (skipped=1)`. The
  skipped test is the host-conditional
  `test_real_runner_refuses_a_ceiling_it_cannot_enforce`, which runs only on
  hosts without `/proc` supervision.
- `native_test_host_matrix.py --check`, `check_documentation.py --check` and
  `generate_diagnostics_inventory.py --check`.

X-OPCODES-P11 stays **PARTIAL**. A separate audit decides closure.

## Which emitters can run

At base `ba9e57cd7`, most LD1/ST1 emitters cannot run in the default
pipelines:

- The `vectorize.rs` i32 induction-store ST1 is quarantined by the literal
  `I32_INDUCTION_STORE_REWRITE_AUTHORITY_AVAILABLE = false` as a known
  miscompile.
- The contains4 LD1 needs `TRUST_CG_ENABLE_CONTAINS4_SCANNER_MEMORY_REWRITE`.
- `neon_map` and `neon_stencil` emit their trailing ST1 only when `UNROLL`
  is odd, and it is 4.
- `neon_condstore` is unscheduled.

`neon_fmap` runs in the O2, Os and O3 pipelines. After its `UNROLL`x`vf`
LDP/STP Q main loop, it runs a one-vector remainder loop. Each input stream
there is `LD1 {Vt.4S|.2D}, [Xn], #16`, and the result is
`ST1 {Vt.4S|.2D}, [Xn], #16`. The scalar loop takes the last `< vf` lanes.
`records/disasm/native-O2.llvm-objdump.txt.gz` shows this for each kernel.
O0 and O1 schedule no NEON pass.

## What the run shows

The target builds ten trust-ir map loops and compiles them with `Compiler`
at O0–O3. At O2 and O3, `neon_fmap` vectorizes eight of them:

- `y[i] = a*y[i]`, in place, as a guarded do-while and as a header-tested
  i32 `for`, f32 and f64;
- `y[i] = a*x[i] + y[i]` and `y[i] = (x[i] - b[i]) / a` as rotated
  do-whiles, f32 and f64, behind the pass's runtime range-disjointness
  check.

`ld1st1_for_axpy_f32` (two arrays) and `ld1st1_for_diff_f64` (three
arrays) stay scalar at every level and serve as controls: `neon_fmap`
versions multi-array maps only on the rotated exit, and the kernels carry
no noalias authority.

- **Decode.** Every word of the final object's code section is classified
  twice, by trust-cg-lift and by the test's own bit mask
  (`word & 0xbfbff000 == 0x0c9f7000`). The two must agree. The test reads
  the ELF and Mach-O symbol tables itself. Each LD1/ST1 post-index word must
  lie in a named kernel and carry that kernel's `.4S` or `.2D` arrangement,
  and the per-kernel counts must be exact. At O2 and O3 the counts are 12
  LD1 and 8 ST1 in 8 of the 10 kernels, for both containers. The ELF object
  has 714 code words and the Mach-O object 697.

  Two external disassemblers give the same per-kernel counts on every
  retained object (`results.json` `objects`): LLVM objdump for both
  containers and GNU objdump for ELF. The rotated two- and three-array
  kernels have 2 LD1 and 1 ST1 each, the in-place kernels 1 and 1, and the
  O0, O1 and no-`neon_fmap` objects none.

  The native O2 object is byte-identical to the explicit
  `aarch64-unknown-linux-gnu` O2 object (`eab864c9…`, 4,624 bytes), and the
  native O3 object to the explicit O3 object (`1ac5620d…`). The O3 object
  differs from the O2 object and carries the same forms.
- **Execution.** Each level's host ELF object (`records/objects/native-O*.o.gz`)
  is linked with `cc` against the C oracle in `records/oracle/driver.c.gz`.
  The oracle is compiled with `-O0 -ffp-contract=off` and runs the same
  loops with the same operand order. At each of O0–O3 it makes 38,376
  calls. After each call it compares the whole three-region buffer
  (40,525,056 elements per level) with the reference bit for bit. That
  covers every output lane, the guard elements and the inputs the call must
  not write.

  The inputs vary in these ways:
  - counts from −3 to 70 plus 97, 127–129, 255–257 and 300;
  - start offsets of 0, 1 and 3 elements;
  - three value patterns: finite normals, IEEE specials with the default
    NaN, and raw bit patterns with one signalling NaN;
  - for the two- and three-array kernels, eight pointer layouts: layouts 0
    and 1 are disjoint for every kernel, in both address orders; layouts 5
    and 6 are also disjoint for axpy, which never reads `b`; the rest
    overlap a read stream, including loop-carried reads. Which path the
    runtime range check chose per layout was not observed.

  Split by the vectorizer's documented partition, the layout 0–1 calls of
  the vectorized kernels give each level 391,824 main-loop lanes, 35,532
  remainder lanes and 8,316 scalar-tail lanes. This split is computed from
  `n`, not measured, and is a lower bound for axpy (layouts 5–6).
- **Mutation.** At O2 and O3, 140 objects are made from the executed
  object, each with one word changed. 100 change what the oracle can see:
  - each of the 20 LD1/ST1 words narrowed to 64 bits (Q=0);
  - each of the 20 LD1/ST1 words replaced by `NOP`;
  - each of the 60 vector FADD/FSUB/FMUL/FDIV swapped for another FP
    operation.

  Each is linked and run for its own kernel. All 200 exited 1 with an
  oracle `MISMATCH` line for that kernel (`records/mutation/*.tsv`). Several
  are caught where only the remainder loop can run. For example, the
  narrowed LD1 of `ld1st1_rot_scale_f32` fails at `n=4`, element 2, with
  `got=00000000`: the upper lanes a Q=0 load zeroes. The unmutated object
  passes the same per-kernel runs with the exact per-kernel summary line.

  The other 40 per level change only the base-register update: each
  LD1/ST1 word rewritten to the no-writeback form `[Xn]` and to the
  register post-index form `[Xn], X1`. The test requires all 80 to **pass**
  the oracle with the exact per-kernel summary line, and requires the
  decode gate to refuse each one. Both held (TSV columns `decode_gate` and
  `oracle_expected`; `results.json` `mutants`
  `writeback_only_passing_oracle_and_refused` = 40 per level). This is the
  boundary described below, enforced rather than assumed.

## Negative controls

- The decode gate refuses the scalar-only O0 and O1 objects, and O2
  compiled with `TRUST_CG_DISABLE_PASSES=neon_fmap`, on both containers.
  The O2 objects without `neon_fmap` are retained.
- For each container, each of the 20 LD1/ST1 words is replaced one at a
  time by a narrowed, `NOP`, no-writeback or register post-index form. The
  gate refuses all 80 mutants and names the kernel.
- The 200 executed observable mutants above. The FP swaps leave every
  LD1/ST1 word in place, and the test requires the decode gate to accept
  them; only the oracle catches them. The LD1/ST1 mutants are also refused
  by the decode gate.
- The 80 executed writeback-only mutants are **not** caught by the oracle,
  by design and by assertion: the oracle cannot see the post-index base
  update, so for that property the decode gate is the only control.

## Records

- `records/results.json` holds:
  - the source and host identities;
  - each command, with its exit status, duration and `test result:` lines;
  - the floor classification;
  - for every retained object, its SHA-256 and the per-kernel LD1/ST1
    counts from each external disassembler;
  - the mutant summaries, including the decode-gate verdicts and the
    writeback-only class.
- `records/logs/*.log.gz`: the complete output of each command.
- `records/objects/*.o.gz` are the objects the test compiled, stored
  gzip-compressed because the repository ignores `*.o`:
  - `native-O*` were linked and executed;
  - `aarch64-*-O*` and `*-O2-without-neon_fmap` were checked at object
    level.
- `records/oracle/driver.c.gz`: the C oracle as compiled.
- `records/mutation/mutants-O2.tsv` and `records/mutation/mutants-O3.tsv`
  (the directory is not called `mutants/` because the repository ignores
  that name):
  every mutant's kernel, word index, original and mutated word, exit status,
  first output line, decode-gate verdict and oracle expectation (`mismatch`
  or `pass`).
- `records/disasm/*.txt.gz` and `records/symbols/*.txt.gz`: LLVM and GNU
  objdump listings and GNU `readelf -sW` symbol tables.
- `harnesses/`: the qualify and archive scripts that produced this
  directory (the qualify script's schema is v2: it summarizes the two new
  TSV columns). `source/`: the tested test file.
- Recorded paths under `/tmp/claude-1000/…` are the original capture
  locations on the host. They are not themselves evidence.

## Boundary

This is object and execution evidence on one host for the named shapes and
inputs. It is not a proof of `neon_fmap`, of its runtime alias check, or of
the LD1/ST1 encoder. The runtime check's choice of vector or scalar path for
each layout was not observed; only the results were compared.

The executed LD1/ST1 words observe the transfer (address, width, arrangement
and data), not the post-index base-register update. By construction,
`neon_fmap`'s remainder loop (`emit_fmap_remainder`) recomputes every stream
pointer and the store pointer with MADD on each step, so the `#16`
writeback of all 20 executed words is dead: in the objects the base
register is redefined (by the next `add` or `sxtw`) before any read. The
oracle therefore cannot distinguish the post-index form from `[Xn]` or
`[Xn], X1`; the writeback-only mutants above show that for these objects
and inputs, and the test fails if that ever changes. The post-index addressing form is
pinned only by the decode gate.

The only scheduled emitter whose LD1/ST1 writeback is live is
`neon_butterfly` (O2, Os and O3; it walks its pointers `p1`/`p2`/`pa`/`pb`,
`neon_butterfly.rs` around lines 1212–1262). It has no native control. LD1/ST1
post-index writeback semantics therefore remain unexecuted for
X-OPCODES-P11.

The `neon_butterfly` and `neon_iota_fill` LD1/ST1 uses, and the
unreachable emitters listed above, have no native control. The Darwin floor
row (minimum 4) has not run on a macOS host. Its Mach-O objects were checked
here at object level only.
