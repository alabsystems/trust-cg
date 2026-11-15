# Emitted-code size versus LLVM -O3 on Darwin arm64: 1.147x -> 0.951x (L14-P10, S3/S4)

> **Payloads out of tree** (durable evidence policy, docs/linux-aarch64-completion.md):
> this record keeps its Markdown and reproducer sources. Its JSON data and the
> harness's JSON records were removed after commit `d4e3a331a`, the last that
> contains them; recover one with `git show d4e3a331a:<path>`. SHA-256 at removal:
>
> | file | sha256 |
> |---|---|
> | `data/attrib.json` | `3c42a6e565e2b778bb98110fc01d71cdb451e7aa6ac702d2d60c4ac50171af8d` |
> | `data/runtime-ab.json` | `5b636504bcba562e0dec4a393ec0e8ab27d905c130fccf4f36211a845f86acd6` |
> | `data/compile-ab.json` | `fb0685a300cd1be316dfc91efbd25fc69e71721ea1aca549871f403aa80b83ae` |
> | `after/b30d99c81778-20261001T002319Z.json` | `a93b07033db15c00651065adffebda9ae3081c5b4a5a0a1961114b084bb8425d` |
> | `after/raw_samples.json` | `09fa59abaac6b89f2e7107982e7af75c24afa5a91ec5f067abb00c2ad8d3858d` |
> | `after/outcomes.json` | `76ee684978b5dd26849e121baf6e40ce76f9ab2f63bf0fdded7467dd1b9d7229` |
> | `after/inventory.json` | `5de7e7cb8551411285feb969b12aa7bf6b638b435afea6e9f60ab4a37579014e` |
> | `before/b30d99c81778-dirty-20261001T002948Z.json` | `17f0f0cfca05a34a4b692351729ef2a2e63c757a9937fc815995b6f509d08915` |
> | `before/raw_samples.json` | `17e844b29d4ba4e5b9ecda0f30db439179b586c2d25be47f5680f79edbb3f9e7` |
> | `before/outcomes.json` | `76ee684978b5dd26849e121baf6e40ce76f9ab2f63bf0fdded7467dd1b9d7229` |
> | `before/inventory.json` | `6d8b2d89fdbad2f39ba0fdcd61c148950854180d7d86c00cf5aade9e28dc6b07` |

Host: Apple M4 Max (`Mac16,5`, 12 performance and 4 efficiency cores), macOS 26.6,
the shared development machine. Driver: Trust package 9192 (`trustc` `321aaeda7`,
explicit unverified frontend lane `-Ztrust-verify=off`). Backends: `before` is the
rustc bridge built from `main` `c84d39e93` (sha256 `d1cccbb7ea76…`), `after` the
bridge built from this branch after its merge of that `main` (sha256 `ff40e7351fd9…`;
later commits on the branch change tests, gates and documentation only). Every bridge
compile here uses `-Ztrust-ir-cg-args=no-proof-certs`, the diagnostic lane, because
the production lane compiles none of the corpus on this host (`[TCG-PROOF-465]`,
ledger `L07-P2`). Every number is a measurement on one host, not a proof, and no
ledger row was appended.

**The host was loaded** (1-minute load 10 to 45 from other agents throughout). Byte
counts and instructions retired do not move with load; wall-clock times are listed
with the load average and are not claimed as results.

## Summary

| | before (`main` `c84d39e93`) | after (this branch) |
|---|---:|---:|
| emitted-code size, geomean over the 18 programs, x LLVM `-O3` | **1.1474** | **0.9514** |
| worst / best program | 2.000 (`b1_mispredict`) / 0.125 (`p7_sieve`) | 1.602 (`p4_matmul`) / 0.112 (`p7_sieve`) |
| programs at or below LLVM `-O3` | 5 of 18 | 6 of 18 |
| emitted bytes, sum over the corpus | 14,920 | 12,484 (-16.3%) |
| runtime geomean x LLVM `-O3` (median of 11, interleaved, load 10.7-19.5) | 0.9599 | 0.9578 |
| program instructions retired, after / before, geomean | | 0.99996 |
| compile instructions retired, after / before, geomean (median of 3, load 43-46) | | 0.99951 |
| compiler peak RSS, after / before, geomean | | 0.999 |
| exit codes | 18/18 equal LLVM's | 18/18 equal LLVM's |

Gate S3 (emitted-code geomean at most 1.10x LLVM `-O3`) and S4 (at most 1.00x) of
`benchmarks/beat-llvm/contract/gates.json` version 3 are met in this diagnostic lane;
they stay unmet as evidence until the production lane compiles the corpus.

## 1. Where the excess was (attribution at `c84d39e93`)

`commands/size_attrib.py` compiles each program as `run.py` does, links once with the
linker map, attributes every live atom of the compile's own objects to its function
(the definition of `benchmarks/beat-llvm/emitted_size.py`, which the tool imports),
disassembles each function from the linked image and classifies every instruction
(frame, spill, move, const, nop, check, call, branch, vector, other). Its output for
both lanes is `data/attrib.json`.

By function, summed over the 18 programs (bytes; `+align` is the after backend with
the loop-head alignment opt-in, so the column between isolates the other changes):

| function | before | after, +align | after | LLVM `-O3` |
|---|---:|---:|---:|---:|
| user `main` | 6,220 | 6,008 | 5,540 | 14,228 |
| `std::rt::lang_start` + its closure vtable (48 B rodata) | 2,232 | 2,232 | 2,232 | inlined into `_main` (vtable 48 B, `l_anon`) |
| `done` (the corpus's `exit` wrapper) | 1,168 | 1,168 | 1,080 | 864 |
| `_main` entry wrapper | 1,080 | 648 | 648 | 1,152 |
| `lang_start` closure `call_once` | 936 | 720 | 720 | inlined |
| `__trustcg_array_fill_*` helper (6 programs) | 836 | 836 | 680 | none (inline stores or libSystem `memset`) |
| closure vtable shim | 792 | 216 | 216 | 504 |
| `lang_start` closure body | 648 | 576 | 576 | 504 |
| `FnOnce::call_once<fn()>` | 576 | 360 | 360 | inlined |
| allocator shims | 360 | 360 | 360 | 360 |
| `__rust_begin_short_backtrace` | 72 | 72 | 72 | 360 |
| LLVM-only `RawVec` growth paths (h1-h4), m2 helpers, literals | 0 | 0 | 0 | 1,128 |
| **total** | **14,920** | **13,196** | **12,484** | **20,132** |

The user `main` functions were already smaller than LLVM's in aggregate (`p7_sieve`
alone: LLVM unrolls its sieve to 8,992 bytes). The excess was a FIXED per-program
cost of the runtime entry chain, 164 bytes per program (304 against LLVM's 140 with
`lang_start` inlined into `_main`) and 16 more in `done`, plus loop-head alignment
padding (194 pad NOPs inside functions over the corpus; the gaps ld64 leaves in
front of 32-byte-placed functions are not counted), plus the
`__trustcg_array_fill_*` helper in six programs.
On the 400-byte programs (`m1`, `m2`, `p2`, `p5`, `p8`) the fixed cost alone was
40-45% of LLVM's size.

Instruction classes, summed over the corpus (`data/attrib.json`):

| lane | instructions | frame | spill | move | const | nop | check | call | branch | vector | other |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| LLVM `-O3` | 4,813 | 456 | 301 | 82 | 443 | 0 | 0 | 339 | 163 | 74 | 2,955 |
| before | 3,514 | 601 | 67 | 452 | 389 | 194 | 45 | 387 | 191 | 38 | 1,150 |
| after | 2,905 | 419 | 67 | 431 | 393 | 0 | 45 | 351 | 186 | 36 | 977 |

(LLVM's "other" is dominated by `p7_sieve`'s unrolled sieve.) Constant
materialization was not an excess: MOVZ/MOVK chains appear where LLVM also uses them,
and neither lane uses literal pools on this corpus. Loads and stores off `sp`/`x29`
(spills, reloads and stack arrays together) were fewer than LLVM's. Jump tables and overflow/bounds check sequences do not differ on this corpus
(each of the 45 `check` instructions is a `brk #1` directly after a call to a `-> !`
function, `done`, `exit` or a panic entry, which LLVM omits; see "What remains").

## 2. The changes and what each one buys

Bytes are sums over the 18 programs, attributed from the per-function table above (the
loop-alignment share is measured directly with the opt-in knob).

1. **Loop-head alignment is opt-in** (`470b27971`, `8e0b27622`): the 32-byte
   innermost-loop-head NOP padding and the 32-byte placement of loop-bearing functions
   no longer run by default. 712 bytes (39.6 per program, up to 88 on `p4_matmul`);
   the after geomean is 1.0052 with the opt-in and 0.9514 without it. Opt-in: the
   tracked bridge knob `a64-loop-head-align`, or `TCG_LOOP_HEAD_ALIGN=1` for direct
   embeddings, which proof-grade routes refuse like every other ambient late-layout
   control. The pass is unchanged, so the opt-in re-emits the previous layout.
2. **Tail call of a narrowed result** (`7a5166b30`): `_main` returns
   `lang_start(...) as i32`; the caller of an `i32` function reads only `W0`, so the
   `bl; mov w0, w0; ret` and its frame record become one `b`. 432 bytes (24 per
   program).
3. **SROA promotes register-passed aggregate argument slots and retires dead slots;
   TCO ignores a deleted slot root** (`3c962d9f7`): the closure vtable shim
   (44 -> 12 bytes, now a tail branch) and the closure `call_once` (52 -> 40) no
   longer round-trip their argument through a stack slot. 792 bytes. One user `main`
   (`h2_vec_grow`) also loses its now-empty stack adjustment. Neither admission
   applies to a slot a source-level debug variable names (every fixed scalar
   `alloca` the adapter describes, with or without `-g`), and such a slot is never
   retired: the first full Darwin floor run of this branch failed
   `aarch64_elf_dwarf` (4 tests) and `o3_debug_lldb_line_200loc` (1 test) because
   retiring the promoted `acc` alloca turned a local those debugger tests read at
   its frame slot into an optimized-out one. That frame-slot description was
   already stale after promotion (LIMITATIONS.md: gdb reads `acc` as 0 at O1-O3);
   the restriction (`sroa::debug_variable_home_slots`) keeps the documented
   behavior and changes no corpus byte: the per-function attribution of all 18
   programs is identical with and without it.
4. **An indirect-call target that dies at its `BLR` may use a caller-saved register**
   (`5a8ac997f`): `FnOnce::call_once<fn()>` was `mov x19, x0; blr x19` with an
   x19/x20 save pair; it is now `blr x0` inside a bare frame record (32 -> 20 bytes).
   216 bytes.
5. **Constant-folded extensions** (`7333b345d`): `uxtb`/`sxtb` of a known constant
   (`mov w0, #0; uxtb w0, w0` in the `lang_start` closure; the fill byte of an array
   initializer in `p7`, `v1`, `v2`, `v3`) fold to the constant. 72 bytes in the
   closure plus one instruction per affected `main`.
6. **A bitwise-chain vector drain skips a provably empty scalar tail** (`64421ab08`):
   `b1_mispredict`'s `[u64; 16]` sum ran a second vector loop and a scalar remainder
   that can never execute (16 is a multiple of the 8-lane block); `main` goes
   512 -> 332 bytes before the padding change, 300 after it.
7. **A W write defines its whole X register** in the incoming-argument span scan
   (`7d9156bdb`): a 32-bit outgoing argument no longer reserves its X register from
   entry; no byte effect is attributable to it on this corpus.

Functions that none of the changes apply to are unchanged: 144 of the 258 functions
the program objects define are instruction-for-instruction identical between the two
backends once alignment NOPs are dropped and addresses are normalized (the user
`main` of 11 programs among them); every other difference is one of the items above.

## 3. Runtime and compile time

The table (rendered from `data/` by `commands/tables.py`): emitted bytes, the ratio
to LLVM `-O3` before, after and after with the loop-alignment opt-in, runtime as the
median of 11 interleaved runs per lane after one warmup (`commands/ab_measure.py run`,
wall from the parent's monotonic clock), program instructions retired, and compile
instructions retired (median of 3 after one warmup, `commands/ab_measure.py compile`).

| program | LLVM -O3 B | before B | after B | before x | after x | +loop-align x | runtime ms LLVM / before / after | after/before | run instr after/before | compile Ginstr before / after | after/before | load |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| b1_mispredict | 564 | 1128 | 784 | 2.000 | 1.390 | 1.532 | 203.02 / 206.84 / 206.63 | 0.999 | 1.00001 | 4.8138 / 4.8036 | 0.99790 | 15.9-17.4 |
| h1_vec_push_sum | 936 | 860 | 728 | 0.919 | 0.778 | 0.829 | 13.15 / 13.28 / 13.10 | 0.987 | 1.00018 | 4.8135 / 4.8102 | 0.99932 | 15.9-15.9 |
| h2_vec_grow | 940 | 884 | 732 | 0.940 | 0.779 | 0.817 | 17.10 / 17.20 / 16.90 | 0.983 | 0.99967 | 4.8147 / 4.8152 | 1.00010 | 15.9-15.9 |
| h3_box_leak | 956 | 788 | 648 | 0.824 | 0.678 | 0.736 | 21.34 / 23.03 / 22.89 | 0.994 | 0.99987 | 4.8050 / 4.8044 | 0.99988 | 15.9-15.9 |
| h4_vec_dropper | 1412 | 844 | 740 | 0.598 | 0.524 | 0.538 | 20.25 / 17.09 / 17.41 | 1.019 | 1.00326 | 4.8107 / 4.8101 | 0.99987 | 15.9-15.9 |
| m1_call_chain | 396 | 560 | 460 | 1.414 | 1.162 | 1.202 | 104.64 / 97.67 / 97.79 | 1.001 | 1.00008 | 4.7622 / 4.7617 | 0.99989 | 15.2-15.9 |
| m2_call_heavy | 424 | 564 | 444 | 1.330 | 1.047 | 1.132 | 69.68 / 67.96 / 68.31 | 1.005 | 1.00008 | 4.7681 / 4.7663 | 0.99962 | 14.9-15.2 |
| p1_xorshift | 488 | 540 | 436 | 1.107 | 0.893 | 0.934 | 627.67 / 632.73 / 631.51 | 0.998 | 0.99984 | 4.7256 / 4.7274 | 1.00039 | 14.9-19.5 |
| p2_collatz | 384 | 556 | 456 | 1.448 | 1.188 | 1.229 | 243.76 / 240.52 / 240.58 | 1.000 | 1.00029 | 4.7346 / 4.7390 | 1.00093 | 17.7-17.9 |
| p3_gcd | 436 | 648 | 536 | 1.486 | 1.229 | 1.294 | 403.83 / 403.63 / 401.96 | 0.996 | 1.00187 | 4.7551 / 4.7516 | 0.99927 | 17.1-17.8 |
| p4_matmul | 984 | 1748 | 1576 | 1.776 | 1.602 | 1.691 | 32.18 / 32.49 / 32.39 | 0.997 | 0.99644 | 4.8973 / 4.8895 | 0.99841 | 17.7-17.7 |
| p5_struct_acc | 400 | 560 | 448 | 1.400 | 1.120 | 1.190 | 691.70 / 693.36 / 692.65 | 0.999 | 0.99997 | 4.7419 / 4.7381 | 0.99921 | 14.6-17.7 |
| p6_branch_match | 524 | 716 | 628 | 1.366 | 1.198 | 1.206 | 1677.63 / 1746.19 / 1715.31 | 0.982 | 0.99990 | 4.8042 / 4.8038 | 0.99992 | 11.2-14.6 |
| p7_sieve | 9248 | 1160 | 1032 | 0.125 | 0.112 | 0.116 | 24.53 / 20.29 / 20.30 | 1.001 | 0.99890 | 4.8091 / 4.8101 | 1.00020 | 11.2-11.2 |
| p8_closure_nest | 396 | 576 | 452 | 1.455 | 1.141 | 1.242 | 211.41 / 211.05 / 211.31 | 1.001 | 0.99996 | 4.7452 / 4.7397 | 0.99883 | 10.7-11.2 |
| v1_saxpy | 656 | 1012 | 844 | 1.543 | 1.287 | 1.415 | 56.51 / 45.64 / 45.22 | 0.991 | 0.99978 | 4.8397 / 4.8278 | 0.99755 | 10.7-10.7 |
| v2_memfill | 420 | 780 | 664 | 1.857 | 1.581 | 1.657 | 10.11 / 10.11 / 10.27 | 1.016 | 0.99897 | 4.7969 / 4.7955 | 0.99971 | 10.7-10.7 |
| v3_popcount | 568 | 996 | 876 | 1.754 | 1.542 | 1.606 | 7.71 / 6.15 / 6.11 | 0.993 | 1.00033 | 4.8516 / 4.8530 | 1.00028 | 10.7-10.7 |
| **geomean** | | | | **1.1474** | **0.9514** | 1.0052 | before 0.9599x, after 0.9578x LLVM | 0.9978 | 0.99996 | | 0.99951 | |

Runtime is not worse: program instructions retired are equal within 0.4% on every
program (geomean 0.99996), and the wall-time ratios scatter on both sides of 1.0 by
up to 2% under this load. An earlier N=5 pass read `p6_branch_match` 22% slower
(2.37 s against 1.94 s) during a load spike to 19; a dedicated re-run with 11 samples
per lane (`data/runtime-ab.json`'s numbers come from the full N=11 pass) reads
after 1.735 s, before 1.762 s, LLVM 1.686 s, with equal instructions retired, so that
reading was load. The removal of loop-head padding is the change most able to move
runtime by itself; its own history (`crates/trust-cg-codegen/src/loop_align.rs`,
"Measured") never showed a benefit, and nothing here shows one either. Compile time
moves by less than its noise: compile instructions retired after / before 0.99951
(-0.05%), compiler peak RSS 0.999.

The harness records (`benchmarks/beat-llvm/run.py --retain-dir`, `before/` and
`after/`, the same command line with `--bridge-cg-arg no-proof-certs --allow-loaded`;
`before` also `--allow-stale-dylib`, because its backend was built from `main`'s
sources) carry the official readings: 18 of 18 MATCH in both runs, and emitted-code
size 1.1474x before and 0.9514x after, byte for byte the attribution tool's numbers,
each map link checked against the timed binary's image digest. Both runs are stamped
LOADED (1-minute load 29.4 -> 10.7 during `after`, 10.7 -> 8.6 during `before`) and
are not evidence. Their wall-clock aggregates (runtime 0.889x after against 1.040x
before, warm compile 1.438x against 1.328x LLVM `-O2`) moved with the load, not the
code: the `after` run's LLVM `h2_vec_grow` median alone is 0.0739 s against 0.0171 s
in the interleaved A/B, and the instruction counts above show neither a runtime nor a
compile-time change. Their compiler peak-RSS geomeans agree (1.111x LLVM `-O2` in
both).

## 4. Correctness evidence

- Every change has unit tests with negative controls, listed in its commit message:
  regalloc (both allocators and the always-on translation validator accept a dying
  `BLR` target in `X0`, and a target live after the call stays out of every clobbered
  register; the W/X span test with an incoming-read control), SROA (argument-load
  promotion and its refusals, the live-in read admission with non-argument controls,
  both admissions refused and retirement withheld for a debug variable's home slot,
  a pipeline pin that a promoted described alloca keeps its frame slot, and the
  parameter-store alloca keeping its frame location with a plain and a volatile
  load), TCO (the narrow-return rule fires for `i32` and is refused for `i8`,
  `bool`, an `i64` signature, an `X0` sink, two sinks, no sink and two results; the
  deleted-root rule with a live-root control), constant folding (both widths, a
  replay of the rewritten block, an unknown-source control), the vector drain (two
  positive shapes and five negative controls, including NZCV live into the exit and
  into its successor), loop alignment (default off, `=0` off, opt-in equals the
  pass), and the final-layout cross-check of both the default and the opt-in layouts
  on Mach-O and ELF.
- The vector-drain proof of NZCV deadness uses `cmp_branch_fusion`'s fail-closed
  successor walk (`nzcv_dead_at_block_entry`), not `effects::reads_flags`, which does
  not list `B.cond`.
- The runtime differential against LLVM is the corpus itself: all 18 programs exit
  with LLVM `-O3`'s code in both lanes (`data/attrib.json`, `data/runtime-ab.json`).
- Gates at `2b60e23c0` (the branch after its merges of `main` up to `9bd719584`,
  which moved the trust-ir pin to `85e5c2d6`), clean tree:
  - the full Darwin AArch64 floor: 280 targets, 1,953 executed passes, failing
    seven of the nine targets that fail on the `main` baseline
    (`aarch64_instruction_word_binding`, `e2e_aarch64_elf_relocation_model`,
    `jit_fail_closed_proof_policy`, `jit_source_bound_arithmetic`,
    `e2e_cegis_superopt`, `local_function_address_jit`, llvm-import
    `intmm_o2_e2e`) and nothing else. A full run at `79702bc0c` failed exactly
    the nine; an earlier one, before the debug-home restriction of section 2
    item 3, also failed `aarch64_elf_dwarf` and `o3_debug_lldb_line_200loc`,
    which pass now.
  - `trust-cg-codegen --lib` 4,520 passed and three failures that fail
    identically on `main` `9bd719584`
    (`x86_trap_only_body_certifies_and_argument_shims_are_judged_by_their_body_theorem`,
    `test_aarch64_parallel_and_serial_multi_function_byte_identical`,
    `test_compile_module_to_jit_rejects_unproved_calling_frame`); `trust-cg-opt`
    `--lib` 3,908 and its seven test targets; `trust-cg-regalloc` `--lib` 733 and
    its two test targets; `must_refuse_corpus` (codegen 2, cli 1);
    `aarch64_final_layout_crosscheck` 6, `aarch64_elf_dwarf` 13,
    `o3_debug_lldb_line_200loc` 2, all passing.
  - the rustc bridge `--lib` (release, at `79702bc0c`): 475 passed, 21 failed,
    all among the 23 the L14-P10 record lists for `main` (the `mem_refine`
    solver rows).
  - `check_fmt`, `check_tippy` (4 packages clean), `check_documentation --check`,
    `native_test_host_matrix --check`, and the three gate unit-test modules (149
    tests, 4 skipped).
- The bridge built at `2b60e23c0` (sha256 `66c1846bce12…`) gives the same
  per-function attribution and exit codes on all 18 programs as the `after`
  backend measured above: neither the trust-ir pin move nor the later merges
  changed an emitted byte of the corpus.

## What remains (measured, not done here)

The after state is still larger than LLVM `-O3` on 12 of 18 programs. In bytes over
the corpus:

- **The runtime entry chain**, 80 bytes per program (220 against LLVM's 140):
  `lang_start` (76 bytes) stays out of line where LLVM inlines it into `_main`, and
  the closure's `call_once`, vtable shim and body take 84 bytes where LLVM has 56. The remaining
  waste is argument shuffling (seven register moves in `lang_start`) and the
  `ldr x1, [x0]; mov x0, x1` pairs. `FnOnce::call_once<fn()>` could be `br x0`
  (4 bytes) if TCO admitted indirect calls whose ABI facts are known; it refuses
  every `BLR` today (`TailCallRefusal::IndirectCall`).
- **Register-to-register moves**: 431 against LLVM's 82 over the corpus (about 96
  bytes per program), mostly call-argument shuffles; the regalloc's copy coalescing
  around calls is the next target.
- **`__trustcg_array_fill_*`** (680 bytes in 6 programs, 96-136 each): every one
  is a `[0iN; N]` zero repeat (`b1` and `p4` `i64`, `v1` `i32`, `p7`, `v2`, `v3`
  `i8`) that the bridge's `Rvalue::Repeat` arm sends to the helper loop because
  `N >= ARRAY_FILL_MIN_COUNT` (16 elements). LLVM stores a 128-byte zero array
  inline (`movi` + four `stp q0, q0`) and calls libSystem `memset`/`bzero`, which
  the size measure does not count, for larger ones. The bridge already lowers
  `write_bytes` to the libc `memset` symbol as a faithful lowering with no new
  proof obligation (`lower_write_bytes_intrinsic`), so the next step is the same
  lowering for a repeat whose constant element has all bytes equal, after
  measuring on `p4_matmul`, which zeroes `c` once per repetition, what replacing a
  helper this backend compiles itself (and vectorizes with `neon_fill`) by an
  opaque external call costs the optimizer around it.
- **`brk #1` after a call to a `-> !` function** (45 instructions, 2.5 per program):
  LLVM omits the trap; removing it is a policy decision about the unreachable trap,
  not a size optimization.
- **`done`**: 60 bytes against LLVM's 48. Its `exit(code % 126)` remainder is a
  64-bit `umulh` sequence where LLVM halves the dividend first and finishes in 32
  bits, plus the trailing `brk #1`.

Arithmetic on `data/attrib.json` (a projection, not a measurement): without the
helper's bytes the after geomean would read 0.910x, without the traps 0.937x, and
without both 0.896x.

None of the work-in-progress salvaged on this branch was removed: every piece was
completed, tested and measured as described above.

## Files

- `commands/size_attrib.py`: the per-function attribution (lanes, map attribution,
  disassembly classes); `commands/ab_measure.py`: the interleaved runtime and compile
  A/B under `/usr/bin/time -l`; `commands/tables.py`: renders section 3 from `data/`.
- `data/attrib.json` (out of tree, see the banner): per program, per lane
  (`llvm_o3`, `before`, `after`, `after_with_loop_head_align`), per function:
  bytes, instruction count, classes, and the run's exit code.
  `data/runtime-ab.json`, `data/compile-ab.json` (out of tree): every sample with
  its load average. `commands/tables.py` reads them from `git show d4e3a331a:...`
  restored into `data/`.
- `before/`, `after/`: the harness's retained records (their Markdown; the JSON
  is out of tree, see the banner).
