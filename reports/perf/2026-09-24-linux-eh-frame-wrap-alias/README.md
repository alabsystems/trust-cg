# L02-P10: `.eh_frame` pointers whose bits give two targets — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record qualifies `53d51970097d8fdcd6fa9b82ce90aded8b8d811f`
(branch `fix/aarch64-eh-frame-wrap-alias`, based on `47b08253b`). Every
leg below ran on that clean source on the Linux AArch64 host, with GNU ld
2.42, LLD 22.1.6 and gold 2.42.

## What the closure audit found

The seventh closure audit of L02-P10, at `43de0bebe`, kept the gap PARTIAL.
The linked-image `.eh_frame` check refused a `PREL32` pointer only when the
value it reads fell outside every executable span (`pc_begin`) or outside
allocated memory (personality, LSDA). LLD and gold write
`2^31 <= X < 2^32` truncated. If the truncated value landed in other code
or data, the image was installed.

## The change

`link_driver::eh_wrap_alias` covers 4-byte and 2-byte fields. A pointer the
existing rules accept is also refused when its bits give another address, a
multiple of 2^32 (2^16) away, where the pointer must lie:

| Pointer | Where the other address must lie |
| --- | --- |
| `pc_begin` | another `pc_range` in executable memory |
| personality, LSDA | another allocated address (the 8-byte slot when indirect) |
| `eh_frame_ptr` | another allocated section start (another allocated address without section headers) |

Such a pointer is refused as `unclassified`, with one
`[TCG-LINK-EH-FRAME-UNPROVEN]` line.

The same commit fixes two side findings from the audit:

- **Classification.** gold's `relocation overflow in R_AARCH64_*` and LLD's
  `improper alignment for relocation R_AARCH64_*` are now classified as
  `relocation-out-of-range`.
- **Veneer control.** The `CALL26` veneer control now links through all
  three linkers, with `.text` pinned.

## Tests (`records/tests/`)

| Target | Result |
| --- | --- |
| `trust-cg-codegen --lib` | 4,150 passed, 1 ignored (the pre-existing `raw_machir_request_cache_real_exhaustive_campaign`), run without `TCG_*` controls |
| CLI binary / `link_options` / `output_paths` | 30 / 29 / 8 |
| `e2e_aarch64_link_runtime` | 32 |
| `e2e_aarch64_elf_tlsie` | 13 |
| `e2e_aarch64_eh_linux` | 10 |
| `e2e_aarch64_eh_catch` | 9 |
| `aarch64_elf_cfi_differential` | 3 |
| `e2e_aarch64_elf_link` | 11 |

The native targets ran with `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1` and
`--nocapture`, and no log has a `SKIP:` line. The codegen library runs
without those variables: the compiler's identity-Core admission refuses
unkeyed ambient `TCG_*` controls, so exporting them fails 51 library tests.

## Direct reproducers (`records/direct/`)

`reproducers.txt` runs two CLIs on the audit's shapes: `trust-cg-prior`,
built from `47b08253b`, and `trust-cg-fix`, built from this source.
`clis.sha256` identifies both.

- **FDE shape.** A `-nostdlib --no-pie` program: `pad.s` gives a 256 KiB
  `tcg_pad` at `0x10000000`, `start2.s` gives a `_start` that calls
  `isize_add_one(41)` and exits 0 when the result is 42, and `.eh_frame` is
  at `0x90000000`. The b1 fixture's `.text` goes to `0x110010000` (far) or
  `0x50010000` (near): an `INSERT AFTER .eh_frame` script for LLD and GNU
  ld, a full `SECTIONS` script for gold.
  - **Prior CLI.** It installs both far programs, through LLD and through
    gold. They run, but readelf decodes their three FDEs as
    `pc=0x10010000..0x10010038`, inside `tcg_pad`.
  - **Fixed CLI.** It refuses both far links with
    `[TCG-LINK-EH-FRAME-UNPROVEN]`, and nothing is written.
  - **GNU ld.** Under both CLIs, it refuses the far link itself (classified
    `relocation-out-of-range`, `R_AARCH64_PREL32`).
  - **Near twins.** They link and run through every linker, under both CLIs.
- **LSDA shape.** `tc_try_elf.o` (trust-cg's `zPLR` object) and
  `driver.o`, with `-lstdc++`. For the far link, `.gcc_except_table` is
  moved alone to `0x100200100`.
  - **Prior CLI.** It installs the LLD program, which dies with SIGSEGV
    (exit 139) at the throw.
  - **Fixed CLI.** It refuses the link with one `[TCG-LINK-EH-FRAME-UNPROVEN]`
    line. The LSDA pointer gives `0x200100`, and the same bits would give
    `0x100200100`.
  - **GNU ld.** It refuses the far link itself.
  - **Near twins.** They print `tc_try returned 42`.

In `reproducers.txt`, bash's `Segmentation fault` line names the harness.
That name has been rewritten to its archived file name
(`harnesses/qualify-eh-frame-wrap-alias-20260924.sh`, the harness with its
local paths replaced by required variables); nothing else was edited.

## Source mutants (`records/mutation/`)

Each mutant was applied and its killing tests were run, then the mutant was
reverted. `summary.txt` has the exit codes, `*.patch` the mutant and
`*.log` the runs. Every one failed at a test assertion; none failed to
compile.

| Mutant | Killed by |
| --- | --- |
| `no-wrap-alias` (the search returns nothing) | the two unit tests, the `link_options` native row, the `e2e_aarch64_eh_catch` native row |
| `self-alias` (a pointer's own address counts) | the unit tests, the `link_options` row (its near twins are refused) |
| `extent-off-by-one` | `eh_wrap_alias_finds_the_other_address_a_narrow_field_gives` |
| `fde-only` (no check for personality/LSDA) | the unit test, the `e2e_aarch64_eh_catch` row |
| `no-gold-lld-classes` | `classifies_gold_overflow_and_lld_misalignment_as_out_of_range` |
| `unpinned-text` (the veneer control without the `.text` pin) | the veneer control's LLD leg: its caller is within 128 MiB |

## Host survey (`records/survey/`)

`survey_test.rs` is a temporary, ignored unit test. It was added to the
source for this run only and is not committed. It ran the check over the
6,368 ELF executables and shared objects that `images.txt` lists (every
`ET_EXEC`/`ET_DYN` ELF64 file under `/usr/bin`, `/usr/sbin`, `/usr/lib`,
`/usr/libexec`, `/usr/local` and `/opt`).

- **Aliasing.** None of the images' 5,091,400 FDEs has a pointer with a
  second address.
- **Verdicts.** 6,095 images pass. The 273 separate debug files, whose
  sections have no contents, are unproven as before.

`verdicts.tsv` gives each image's line; `summary.txt` has the totals.

## Boundaries

This is execution, object and decoder evidence on one host's three
linkers, not a proof.

- **Conservative refusal.** The refusal reads the image, not the input
  relocation. An image whose allocated memory spans 4 GiB so that some
  pointer has such a second address is refused even when its linker was
  given the right one.
- **Earlier blind spots.** The limits in the gap's previous record remain:
  an `.eh_frame` that no header locates, LSDA tables, `-Wl,--no-eh-frame-hdr`,
  Darwin's `__eh_frame` and links for other operating systems.
- **Read-back.** The staged image is still read back whole. A valid LLD
  link with a section at `0x2000000000` writes a 128 GiB sparse image, and
  the CLI is killed reading it. That fix is tracked separately.

L02-P10 stays PARTIAL; a separate closure audit decides.
