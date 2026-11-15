# Integrated Linux gates before the eighteenth main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `47b08253bb90b1e3adddf8e97bd9d0a6360fc0c5`.
It is origin/main `43de0bebe` (the
[gates-17](../2026-09-24-linux-integrated-gates-17/README.md) record) with
the TV-3 hardening branch merged. That branch settles the item gates-17
listed as in progress. The raw dataflow-integrity check (TV-3) changes in
two ways:

- **Fusion edges (`275ba7cd6`).** On every architecture, TV-3 now follows
  a fusion edge only from a plain LIR `Store`. A call, atomic, fence,
  bulk-memory operation or volatile store must be witnessed by an
  instruction stamped from itself. The AArch64 `MachFunction` view returns
  a recorded edge only for a folded stack-slot store into its `RBIT` root.
  An independent probe had passed a dropped store and call through the
  edge's shape alone.
- **Volatile loads (`1479db244`).** TV-3 now requires a stamped machine
  instruction for every `VolatileLoad`, used or not. Before, its
  must-witness set came from `classify_lir_opcode`. That function puts a
  volatile load with plain loads, which may be removed, so a dropped
  volatile read passed TV-3 on AArch64 and x86-64.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,003 Rust tests**. The source fingerprint
`3b63e993d91e46d05a4db4a0973eabc8e706c8b68dfc5320c706b3833bb6ac64` was the
same before and after the run. The run took 730 seconds of target wall time
(02:12:45Z to 02:25:13Z). The highest sampled resident set was 188 MiB, in
`e2e_aarch64_link_runtime`. All four controls were on, and the AY/Clean and
dependency identities did not change.

## Library, CLI and extra suites

- **Library tests:** codegen passed 4,147 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`). That is two more
  than gates-17: the hardening's selector rows in `pipeline.rs` and
  `x86_64/pipeline.rs`. Lower passed 1,894.
- **TV-3 (`trust-cg-verify --lib dataflow_integrity`):** 29 passed.
- **CLI:** the binary's tests passed 30, `link_options` 28, `output_paths` 8
  and `trust_ir_binary_container` 4.
- **trust-cg-llvm-import (`--features driver`):** `bitreverse_intrinsics`
  passed 6 and `intmm_arrays` 3.
- **trust-cg-codegen:** `e2e_aarch64_bit_intrinsics_bulk_memory` passed 2.
  It is the end-to-end `RBIT` fold whose edge the hardening narrows.
- **Other targets:** the trust-cg-verify CEGIS and proof-suite targets (69
  tests) and the race targets (13) passed.

The first run of the extra lane named a test target that does not exist
(`x86_volatile_trace_gate`), so Cargo refused it before anything ran
(`extra-i24.log`). The lane was rerun with the target that does exist
(`extra-i24b.log`). The floor already requires the volatile-access target
`aarch64_volatile_access_preservation`, and it passed there.

## Known and in progress

The seventh closure audit of L02-P10, at `43de0bebe`, kept the gap
PARTIAL. Linked through LLD 22.1.6 or gold 2.42, a `.eh_frame`
`R_AARCH64_PREL32` value in `[2^31, 2^32)` is written truncated. When the
truncated value lands in other executable or allocated memory, the link
driver's plausibility check accepts the image. In the audit's C++
reproducer, an LSDA pointer truncated this way makes the program abort at
its throw. A fix is in progress. The bridge lane was not run: these
changes are in TV-3 and its selector callers, not in the bridge.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
