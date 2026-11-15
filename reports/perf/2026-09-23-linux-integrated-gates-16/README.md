# Integrated Linux gates before the seventeenth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `13e3d898c5d89c4ec4fa220fc2f9316fecad81b4`:
origin/main `5ddb13664` plus two branches.

- **L02-P10 `.eh_frame` window check** (`9ca3a684b`). trust-cg emits
  `R_AARCH64_PREL32` for `.eh_frame` pointers. LLD 22.1.6 and gold 2.42
  write a value in `[2^31, 2^32)`, which unwinders read as negative.
  - `run_link` now stages every Linux link and decodes the linked image's
    `.eh_frame` the way an unwinder does. Each FDE's
    `pc_begin..+range` must lie in executable memory. Personality and LSDA
    pointers must land in allocated memory. The `.eh_frame_hdr` table must
    agree with the FDEs.
  - A violation is refused as `[TCG-LINK-EH-FRAME-WINDOW]`, and an
    incomplete check as `[TCG-LINK-EH-FRAME-UNPROVEN]`.
  - The closure auditor's far placement is now refused through LLD and
    gold. GNU ld still refuses it on its own.
  - A survey of the host's 5,770 ELF images refused none of them. On a
    410-image sample, 1.28 million FDEs decoded the same as GNU readelf
    decodes them.
- **Explicit-target host independence** (`3fe853c25`, `4e38cf83b`). An
  explicit `x86_64-unknown-unknown` target used to take its object format
  from the host. It is now refused on every host, as `aarch64-unknown-unknown`
  already was. Two trust-cg-llvm-import tests that assumed Apple behaviour
  from a host-derived target now use explicit targets.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **154 required target families
and 963 Rust tests**, including:

- `link_options` 28/28;
- `e2e_aarch64_eh_catch` 8/8;
- `e2e_aarch64_link_runtime` 32/32.

The source fingerprint
`78b86d9d2784579b613eee0d2ef1d16d036fb1cc204374544067f2b5e6f4ffc6` was
identical before and after the run. The run took 726 seconds of target
wall time (01:02:18Z to 01:14:41Z), and the highest sampled resident set
was 265 MiB. All four controls were on. The AY/Clean and dependency
identities did not change.

## Library, CLI and extra suites

- **Library tests:** codegen passed 4,142 with 1 ignored, the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`. Lower passed 1,889.
- **CLI:** the binary's tests passed 30. `link_options` passed 28,
  `output_paths` 8 and `trust_ir_binary_container` 4.
- **trust-cg-llvm-import with `--features driver`:** `fp_e2e` passed 9 and
  `ws2_stack_protector_target` 4.
- **trust-cg-codegen:** `e2e_aarch64_eh_catch` passed 8 and
  `e2e_x86_64_dispatcher` 10.
- **Other targets:** the trust-cg-verify CEGIS and proof-suite targets
  passed, and so did the race targets.

The bridge lane was not run. The changes are in the CLI link driver and the
x86-64 output-format selection, and the rustc backend uses neither.

A separate record,
[2026-09-23-linux-integration-sweep](../2026-09-23-linux-integration-sweep/README.md),
runs every root-workspace integration test target at `977de52ca`.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN. L02-P10 stays PARTIAL until a closure audit.
