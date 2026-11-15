# Integrated Linux gates before the seventh main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `0aaebea37a9fb9a5de5d34a882c2eb2e9f88adf5`.
That is origin/main `57f35f51d` plus two merged branches and follow-ups.

**L02-P7: SHT_NOBITS zero fill for COMDAT definitions and explicit
zero-fill sections.**
- Zero link-once globals and thread-locals get grouped `.bss.<sym>` and
  `.tbss.<sym>` NOBITS sections.
- All-zero explicit `.bss*`, `.tbss*`, `.sbss` and `.lbss` requests are
  honoured as NOBITS.
- A nonzero initializer there is still refused (`[TCG-SECTION-NOBITS]`).
- The review repair refuses a mutable global in explicit `.bss.rel.ro[.*]`
  (`[TCG-SECTION-READONLY]`), because LLD places that section in RELRO.

**L02-P10: a pinned limit and disposition for every relocation kind the
AArch64 ELF writer can serialize.**
- New named refusals where the object fixes the bound:
  `[TCG-RELOC-WINDOW-TLSLE]` and `[TCG-RELOC-WINDOW-ABS32]`.
- A staged image check refuses a GOT the linker placed out of `ADRP` reach
  (`[TCG-LINK-GOT-PAGE-WINDOW]`). GNU ld 2.42 does not check that window and
  truncates the page delta.
- Every link with a GOT-page input (pic, initial-exec, TLSDESC) is now
  staged. So `-o /dev/null` with such an input is refused.

**Integration follow-ups:**
- `9d01e264d` models `PREL32` with the signed window of aaelf64 2026Q2
  (`-2^31 <= X < 2^31`). trust-cg emits it only for `.eh_frame`, which
  unwinders read as signed.
- `1956dc489` records the L02-P9 closure audit, which kept L02-P9 PARTIAL.
- The plan's L02-P9 repair subsections move back under their own section.

Each branch was reviewed adversarially and repaired, and each repair was
independently verified.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **147 required target families
and 878 Rust tests**. Source fingerprint
`c60f8b189b4d716b880dce19827ceb4e7c809c6a538c274cb2ac91d638cd0424` was
identical before and after. The run took 591 seconds of target wall time
(08:46:10Z to 08:56:06Z), with a highest sampled resident set of 353 MiB.
All four controls were on, and the AY/Clean and dependency identities did
not change.

The changed targets passed:

| Target | Passed |
| --- | ---: |
| `e2e_aarch64_link_runtime` | 28/28 |
| `e2e_aarch64_elf_sections` | 21/21 |
| `e2e_aarch64_elf_stack_zero_fill` | 12/12 |
| `e2e_aarch64_elf_tlsie` | 11/11 |
| `e2e_aarch64_globals_linux` | 15/15 |
| `aarch64_elf_dwarf` | 12/12 |
| `link_options` | 16/16 |

## Library and CLI suites

On the same checkout:

- `cargo test -p trust-cg-codegen -p trust-cg-lower --lib` passed. Codegen
  passed 4,104 with 1 ignored, the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`. Lower passed 1,879.
- In `cargo test -p trust-cg-cli`, the binary's tests passed 29/29 and
  `--test output_paths` passed 8/8.
- `--test trust_ir_binary_container` failed 2 of 4. No gate runs it, and the
  failures predate this source. Neither the CLI sources, `trust-cg-lower`,
  the lockfile, the fixtures nor the test changed between origin/main and
  this commit. Both failures come from the trust-ir pin moving to `7b9146ba`
  after the fixtures were vendored at `d41fa3f8`:
  - A version-44 blob is no longer outside the reader window. It now fails
    as `invalid string id: 20` rather than `unsupported version`.
  - `func_param_abi` is refused by the adapter's `AlwaysMemory`
    struct-passing rule instead of the pinned `[TCG-BYVAL-ABI]`.

## Known findings at this source (fixes in progress)

- The GOT-page image check picks its GOT region by section name (`.got*`).
  A linker script that moves `.got` under another name, while `.got.plt`
  stays near the code, escapes it: the library installs with a truncated
  `ADRP` and its user segfaults. So the documents' claim that a renamed GOT
  "stays covered" is false at this source. A conservative refusal (a far
  code section with no GOT references) is also reported as an observed
  overflow.
- The explicit-section catch-all admits a mutable global in some linker
  special names that land in read-only or RELRO output. Under GNU ld 2.42
  these are `.tcommon`, `.gnu_extab`, `.gcc_except_table.x`,
  `.exception_ranges`, `.sframe` and `.eh_frame.x`; `.jcr` does so under
  both linkers. A store to such a global faults. This predates the batch.
- The implicit COMDAT name of a symbol literally named `rel.ro` collides
  with `.bss.rel.ro` (disclosed in the L02-P7 note).

## Not run

The bridge lane was not run. The rustc backend links `trust-cg-codegen`, but
this batch changes only the ELF object writer's relocation-limit model and
checks, section classification, zero-fill planning and the CLI link driver.
The bridge's C-aggregate target fails for an unrelated known reason
(L06-P1). The last bridge run is in
[the fourth push's gate record](../2026-09-23-linux-integrated-gates-3/README.md).

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.

`records/run10/` holds the complete floor output. `records/lib-i7.log.gz`
and `records/cli-i7.log.gz` hold the library and CLI transcripts.
