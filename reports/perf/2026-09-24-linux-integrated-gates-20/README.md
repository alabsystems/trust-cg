# Integrated Linux gates before the twentieth main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `5011a7de4244dd3360f80691dae4705185b0f5d1`.
It is origin/main `0ecdc18a8` (the
[gates-19](../2026-09-24-linux-integrated-gates-19/README.md) record) with
two merges:

- **The second `.eh_frame` repair.** It is qualified in
  [2026-09-24-linux-eh-frame-second-repair](../2026-09-24-linux-eh-frame-second-repair/README.md):
  - without section headers, every record from `eh_frame_ptr` is read;
  - static Linux links pass `--eh-frame-hdr`;
  - a tie that no table entry decides is unproven.
- **L02-P6.** Under `pic`, a module's references to its own hidden and
  protected functions and data bind locally, with no GOT slot and no PLT
  entry. Five copies of the addressing decision now read one preemption
  predicate, and weak and link-once replacement one predicate, with drift
  tests. A new native interposition control runs through GNU ld, gold and
  LLD at O0–O3. An independent verifier found no wrong code or binding. It
  found three low items: untested purity visibility, the weak rule
  implemented twice, and an Internal/Private overclaim. They were repaired
  in `5a72f5718` and `bfec08572`.

The merge commit is followed by a ledger note for L02-P6 (`149f08c32`).

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,009 Rust tests**. The source fingerprint
`fcc5096b7bea7acba79f79f35aaac52550be56ddb8d74d2830d6c800277f4c02` was the
same before and after the run. The run took 765 seconds of target wall time
(04:26:36Z to 04:39:27Z). The highest sampled resident set was 362 MiB, in
`link_options`. All four controls were on, and the AY/Clean and dependency
identities did not change.

## Library, CLI and L02-P6 suites

- **Library tests:** codegen passed 4,154 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`). Lower passed 1,896.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `link_options` 31, `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **L02-P6 native suites, with LLD and gold required and no `SKIP:` line:**
  `aarch64_elf_symbol_binding` passed 20, `e2e_aarch64_elf_relocation_model`
  20, `e2e_aarch64_link_runtime` 32, `e2e_aarch64_elf_link` 11 and
  `e2e_aarch64_elf_tlsie` 13.

## Known and in progress

A third independent verifier of the `.eh_frame` refusals found no soundness
break. Its 42 executable cells and 10 shared-library cells through three
linkers all installed and behaved correctly. It found three false refusals
introduced by the second repair, all narrow and fail-closed:

- **`-z nosectionheader` with an LSDA.** GNU ld's default script puts
  `.gcc_except_table` or `.sframe` right after `.eh_frame` in its segment.
  A `-nostdlib` image with an LSDA, linked with `-z nosectionheader`, is
  refused.
- **Static tie.** A static tie whose table names the function's own FDE is
  refused, although libgcc's registered search never takes a zero-range FDE
  and falls back to the table on a miss.
- **Discarded `.eh_frame`.** When a linker script discards `.eh_frame`, LLD
  writes a zero-filled `.eh_frame_hdr` placeholder, and the image is
  refused.

It also found some documentation overclaims. The third repair is in
progress, and these gates do not include it.

The bridge lane was not rerun. The bridge crate is unchanged since the
gates-19 record's bridge run; L02-P6 changes the adapter and codegen
addressing, which the bridge uses through the same crates.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
