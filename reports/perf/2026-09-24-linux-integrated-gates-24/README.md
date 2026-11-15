# Integrated Linux gates before the twenty-third main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `296e8cecff103a8970e987c1fc4a3a65179b27de`:
origin/main `f7476fd57` (the owner's fsym commit on top of the
[gates-23](../2026-09-24-linux-integrated-gates-23/README.md) record's
`bba9997f5`) with the linked-image hostile-product bounds merged, and a
Darwin gate pin repaired.

## What changed

- **Hostile-product bounds.** Four image-check costs that grew with a
  product a hostile image controls are bounded:
  - symbol-name scans: a wanted name is compared at its own length;
  - the `.eh_frame` pointer search: a window fast path, with every step
    counted;
  - same-start FDE groups: a map built once;
  - the `.eh_frame_hdr` placeholder scan: at most 16,777,216 zeros.

  The repair and each of its follow-ups had an independent verifier, and
  its qualification is
  [2026-09-24-linux-image-check-hostile-products](../2026-09-24-linux-image-check-hostile-products/README.md).
- **Darwin gate pin.** `test_darwin_aarch64_gate` had failed on main since
  `75a577d3b`. The L02-P6 repair raised `e2e_aarch64_elf_relocation_model`'s
  Darwin minimum from 17 to 18, and a merge combined it with the sum pin
  without updating it. The table sums to 1,420, and the pin now says so.
  The script gate unit tests (Linux and Darwin gates, evidence archives,
  host matrix, closure ledger, fmt) pass: 113 tests, 1 skipped.
  - **Still failing, unchanged.** Three tests of the full `scripts/tests`
    suite fail identically at `bba9997f5`:
    `test_bridge_build_probe` (no `BRIDGE_PROBE_TARGO` tool file),
    `test_benchmark_prerequisites`' Trust-compiler dylib set, and
    `test_soundness_capture`'s expectation of `--release` for the encoding
    gate.

## Linux regression floor (`records/run31/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,012 Rust tests**. The source fingerprint
`028dc92fcd165f9912bb45ef736be8c931cb57158f65fb77177f429bf1097da8` was the
same before and after the run. The run took 09:40:17Z to 09:52:58Z. The
highest sampled resident set was 342 MiB, in `link_options`. All four
controls were on.

## Library, CLI, native and fsym suites

- **Library tests:** codegen passed 4,175 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`), including the new
  bound tests. Lower passed 1,896.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `link_options` 34, `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  `aarch64_elf_cfi_differential` passed 3, `e2e_aarch64_eh_catch` 9,
  `e2e_aarch64_eh_linux` 10, `e2e_aarch64_elf_link` 11,
  `e2e_aarch64_elf_tlsie` 13 and `e2e_aarch64_link_runtime` 32.
- **The owner's fsym commit on this host:** `fsym_ub_map` passed 6,
  `fsym_interpreter_oracle` 4, and the CLI's `fsym_flag` 19.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
