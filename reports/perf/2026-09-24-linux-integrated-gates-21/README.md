# Integrated Linux gates before the twenty-first main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `24632e79d0502073df9ef82b102277c50e7f634e`:
origin/main `aceeb3bb6` (the
[gates-20](../2026-09-24-linux-integrated-gates-20/README.md) record) with
the third and fourth `.eh_frame` repairs merged. Both are qualified in
[2026-09-24-linux-eh-frame-third-repair](../2026-09-24-linux-eh-frame-third-repair/README.md)
and
[2026-09-24-linux-eh-frame-fourth-repair](../2026-09-24-linux-eh-frame-fourth-repair/README.md).
Without section headers, the walk ends at the first record that is not
`.eh_frame`'s when there is a table, and must reach a terminator when there
is not. The table decides zero-range ties. In a static executable, a
narrower FDE with a range is undecided. LLD's placeholder `.eh_frame_hdr`
is ignored. These repairs settle the three false refusals that gates-20
recorded as in progress.

## Linux regression floor (`records/run28b/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,011 Rust tests**. The source fingerprint
`e12da8aa236f370a65868402a4e6c5b16bd910e34cbdd20128f19c60068ed451` was the
same before and after the run. The run took 782 seconds of target wall time
(05:44:51Z to 05:57:58Z). The highest sampled resident set was 353 MiB, in
`link_options`. All four controls were on.

A first floor run on the same source (not retained) also passed every
target. It is not the record because `--require-clean` refused it: "source
changed while required targets were running". A subagent's shell, which
starts in the main checkout, had briefly written an untracked `fuzz-a.log`
there. The floor was rerun on the clean checkout.

## Library, CLI and native suites

- **Library tests:** codegen passed 4,154 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`). Lower passed 1,896.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `link_options` 33, `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  `aarch64_elf_cfi_differential` passed 3, `e2e_aarch64_eh_catch` 9,
  `e2e_aarch64_eh_linux` 10, `e2e_aarch64_elf_link` 11,
  `e2e_aarch64_elf_tlsie` 13 and `e2e_aarch64_link_runtime` 32.

## Known and in progress

- **The read-back branch.** It reads images over 1 GiB piecewise, so a
  128 GiB sparse image no longer gets the CLI killed. Its second
  independent verifier found the zero-fill mechanism sound, and R1–R4
  fixed. It found three gaps:
  - a cap overflow skips the linker-written-PLT check;
  - repeated `PT_DYNAMIC` headers still allocate without bound;
  - two hostile slow paths.

  They are being fixed, and the branch is not in these gates.
- **Branches under independent verification:** the L02-P1 lift (direct
  calls to and addresses of Internal/Private functions on AArch64 ELF,
  backed by a post-emission binding check), and L04-P11 (Linux switch and
  indirect-call matrices; register copies bound to decoded-word
  obligations instead of exempted).

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
