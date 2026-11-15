# Integrated Linux gates before the twenty-second main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `30fb05ef37159f7fbacf081e674907ada95120d9`:
origin/main `75a577d3b` (the
[gates-22](../2026-09-24-linux-integrated-gates-22/README.md) record) with
the bounded image read-back merged.

## The read-back change

- **Before.** The Linux link driver read every staged image back whole
  for its image checks. The seventh L02-P10 closure audit found that a
  valid LLD link with a section at `0x2000000000` writes a 128 GiB sparse
  image, which got the CLI OOM-killed and left a `.tcg-link-*` staging
  directory.
- **Now.** Images over 1 GiB are read piecewise at their real file
  offsets. The checks re-run until a run misses nothing, and only that
  run's verdict counts (speculative runs may read zeros). Past its per-check
  bounds, an image is refused by name. An unreadable GOT layout is refused
  whatever the inputs.
- **Verification.** Two independent verifiers found the install direction
  sound. They ran more than 325,000 whole-versus-piecewise fuzz cases and
  real binaries padded past 1.25 GiB, and found no image the piecewise path
  installs that a whole read refuses. Their robustness findings are
  repaired: hostile-count pre-allocation, overflow panics, unbounded work
  over duplicated tables and `PT_DYNAMIC` headers, a cap that skipped the
  linker-written-PLT check, quadratic PLT diagnostics, and a staging drop
  guard.
- **Merge resolution.** On main, the `.eh_frame` refusals keep their
  file-backed spans next to the new record counter, and read the
  placeholder `.eh_frame_hdr` through the image accessor.

## Linux regression floor (`records/run30/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,012 Rust tests**. The source fingerprint
`042244b62a2d3d6f9514d5d9c8ab744b74aaf9ed8bf72270a12940a102729194` was the
same before and after the run. The run took 805 seconds of target wall time
(06:40:03Z to 06:53:33Z). The highest sampled resident set was 346 MiB, in
`link_options`. All four controls were on.

## Library, CLI and native suites

- **Library tests:** codegen passed 4,171 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`), including the
  read-back tests. Lower passed 1,896.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `link_options` 34 (among them the 128 GiB sparse-image control
  under a 16 GiB address-space limit), `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  `aarch64_elf_cfi_differential` passed 3, `e2e_aarch64_eh_catch` 9,
  `e2e_aarch64_eh_linux` 10, `e2e_aarch64_elf_link` 11,
  `e2e_aarch64_elf_tlsie` 13 and `e2e_aarch64_link_runtime` 32.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
