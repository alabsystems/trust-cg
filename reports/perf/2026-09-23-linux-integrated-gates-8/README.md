# Integrated Linux gates before the ninth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `58ff4aecf314a624e5d660705811f997924b8bb0`:
origin/main `f4c94bfb2` plus two increments. Each increment was reviewed
adversarially, and the one that needed a repair was then checked by an
independent verifier.

**X-OPCODES-P11: NEON `LD1`/`ST1` post-index with live writebacks.** The new
floor target `neon_butterfly_writeback_execution` compiles three trust-ir
butterfly kernels that the `neon_butterfly` matcher admits. At O2 and O3 the
final objects contain `LD1`/`ST1 {Vt.4S}, [Xn], #16` on four walking
pointers.

The decoded stream shows that every writeback is read as the next
iteration's base. A C oracle, with each scalar operation written as a single
A64 instruction, matches bit for bit at O0 through O3. At O2 and O3, every
writeback-only mutant fails that oracle in multi-pair calls: both the
no-writeback `[Xn]` form and a register post-index whose register holds a
different stride. `neon_fmap`'s dead writebacks could not give this control.

**L11-P4, Linux half: fail-closed instruction-cache coherence rows.** These
are in-place rewrite rows in `jit_icache_coherence` that pin the `ic ivau`
walk and its stride. After the review repair, a structural row also
requires every publication to record its maintenance walk. The Darwin half
of L11-P4 cannot run on this host.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **148 required target families
and 894 Rust tests**. Source fingerprint
`6a41d9410852bb4ad9e57b6c3ad8d90b9213f796d173e6e9b6bcae64ba531190` was
identical before and after. The run took 686 seconds of target wall time
(10:51:16Z to 11:02:52Z), with a highest sampled resident set of 171 MiB.
All four controls were on, and the AY/Clean and dependency identities did
not change.

| Target | Passed |
| --- | --- |
| `neon_butterfly_writeback_execution` | 4/4 |
| `jit_icache_coherence` | 7/7 |
| `neon_ld1_st1_post_execution` | 4/4 |

## Library and CLI suites

On the same checkout, `cargo test -p trust-cg-codegen -p trust-cg-lower --lib`
passed:

- codegen: 4,113 passed, 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`);
- lower: 1,879 passed.

`cargo test -p trust-cg-cli` passed its binary tests 29/29, `--test
link_options` 16/16 and `--test output_paths` 8/8. The bridge lane was not
run; neither increment touches the rustc backend's object-emission path.

## Still open at this source

- **`.eh_frame_entry<x>`:** the prefix miss recorded in
  [the eighth push's gate record](../2026-09-23-linux-integrated-gates-7/README.md)
  is fixed on a branch that is not yet merged.
- **Integration-sweep failures:** the failing tests the Linux sweep found
  are fixed on verified branches, also not yet merged. Among them is the
  trust-cg-cli `trust_ir_binary_container` pair.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.

`records/run12/` holds the complete floor output. `records/lib-i9.log.gz`
and `records/cli-i9.log.gz` hold the library and CLI transcripts.
