# L02-P10: hidden FDEs and file-backed alias regions — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record qualifies `9e0f7321603be25948acf7753dd900bf63ef388e`, which
repairs the `.eh_frame` wrap-alias refusal of `53d519700`. That refusal is
qualified in
[2026-09-24-linux-eh-frame-wrap-alias](../2026-09-24-linux-eh-frame-wrap-alias/README.md).
Every leg ran on clean source on the Linux AArch64 host, with GNU ld 2.42,
LLD 22.1.6 and gold 2.42.

## What the independent verifier found

- **A hidden zero-range FDE (soundness).** GCC emits a zero-range FDE for
  an empty function (`__builtin_unreachable()`). Such an FDE has no code at
  its true address, so no second address was found. In the verifier's
  program, an empty function sits 2^32 + 0x10 above `middle`. LLD wrote the
  empty function's `pc_begin` truncated into `middle`, and its table entry
  hid `middle`'s FDE. The CLI installed the program, and it terminated at
  its throw.
- **A false refusal.** A correct C++ program with a 5 GiB `.bss` was
  refused through GNU ld, LLD and gold, PIE and not. Its personality slot's
  second address, 2^32 away, lay in the `.bss`.

## The repair

- **`eh_fde_overlaps`.** libgcc and LLVM libunwind look an FDE up by its
  start. They take the entry with the greatest start at or below the pc,
  and the last one among entries that begin together. A live FDE that a
  lookup would miss is now an observed failure (`relocation-out-of-range`,
  `[TCG-LINK-EH-FRAME-WINDOW]`). A lookup misses an FDE in two cases:
  - another FDE begins inside its range;
  - the entry taken at its start is narrower (without a table, any narrower
    FDE that begins with it).
- **File-backed alias regions.** `eh_wrap_alias` now looks only in
  file-backed memory: sections with contents and each `PT_LOAD`'s file
  bytes, and for a `pc_begin` only the executable ones.

## Tests (`records/tests/`)

| Target | Result |
| --- | --- |
| `trust-cg-codegen --lib` | 4,152 passed, 1 ignored, run without `TCG_*` controls |
| CLI binary / `link_options` / `output_paths` | 30 / 30 / 8 |
| `e2e_aarch64_link_runtime` | 32 |
| `e2e_aarch64_elf_tlsie` | 13 |
| `e2e_aarch64_eh_linux` | 10 |
| `e2e_aarch64_eh_catch` | 9 |
| `aarch64_elf_cfi_differential` | 3 |
| `e2e_aarch64_elf_link` | 11 |

The native targets ran with `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1` and
`--nocapture`, and no log has a `SKIP:` line. The new native row is
`link_options`
`linux_got_page::a_hidden_zero_range_fde_is_refused_and_a_5_gib_bss_program_links`:
- **The verifier's program.** Placed 2^32 + 0x10 above `middle` (located by
  its near twin's `nm`), it is refused through LLD with the hidden-FDE
  line, and nothing is written.
- **LLD outside the driver.** It installs the program, which dies at the
  throw.
- **GNU ld.** It drops the empty section's FDE, and its program exits 42.
- **Near twin.** Without the empty function, the program exits 42.
- **5 GiB `.bss`.** A program with a throw links and prints
  `caught 7 big=2` through GNU ld, LLD and gold, PIE and not.

## Source mutants (`records/mutation/`)

| Mutant | Killed by |
| --- | --- |
| `no-overlap-rule` | `fdes_a_lookup_by_start_hides_are_refused` and the native row's LLD refusal |
| `data-alias-counts-zero-fill` (personality/LSDA aliases in `.bss` again) | `a_nobits_region_is_no_alias_of_a_pointer_with_contents` and the native row's 5 GiB legs |
| `code-alias-counts-zero-fill` (NOBITS executable sections count for `pc_begin`) | `a_nobits_region_is_no_alias_of_a_pointer_with_contents` |
| `ties-ignore-the-table` (the narrowest FDE is always taken at a tie) | `fdes_a_lookup_by_start_hides_are_refused` (the tie whose table names the wider FDE) |
| `ties-only` (no check across different starts) | the unit test and the native row's LLD refusal |

Each failed at a test assertion. The harness's first form of
`code-alias-counts-zero-fill` (`*.first-attempt*`) left a field unread, so
the build failed on a warning and the test never ran. The mutant was
rerun: the rerun counts NOBITS executable sections in the code region.
`summary.txt` records the rerun.

## Host survey (`records/survey/`)

The same 6,368 ELF executables and shared objects (5,091,400 FDEs) as the
first record were checked by the temporary, ignored unit test
`survey_test.rs`, which is not committed.

- **Aliasing.** No image has an aliasing pointer.
- **Verdicts.** 6,081 images pass. The 273 separate debug files are
  unproven, as before.
- **Hidden FDEs.** 14 images have one (`hidden_fdes.tsv`): the Qt6
  libraries bundled with NVIDIA Nsight Systems and Nsight Compute, linked by
  LLD 17 (their `.comment` names `Ubuntu LLD 17.0.6`). LLD keeps one table
  entry per start, the first in `.eh_frame` order, and here it names a
  zero-range FDE ahead of the function's real one.
  - `libQt6Core.so.6`: the entry for `0x512d20` names the zero-range FDE at
    `0x27a318`, not the 0x20-byte FDE of `QProcess::setupChildProcess`.
  - `libQt6Qml.so.6`: 14 zero-range FDEs precede a 0x73c-byte function's.
  - In both, an unwinder finds no unwind information for those functions.

A first version of the rule refused every zero-range FDE that begins
together with a wider one. The survey showed that whether such a tie is
harmless depends on which FDE the table's last entry for the start names,
so the rule now follows that entry.

## Boundaries

This is execution, object and decoder evidence on one host's three
linkers, not a proof.

- **Conservative refusals.** The wrap-alias rule reads the image, not the
  input relocation. An image with 4 GiB of file-backed memory in which some
  pointer has a second address is refused even when its linker was given
  the right address.
- **The hidden-FDE rule.** It models libgcc's and LLVM libunwind's lookup
  by start, and would refuse an image such as the Qt libraries above even
  when trust-cg's own objects are not involved.
- **Read-back.** The staged image is still read back whole; the fix is on
  a separate branch.

L02-P10 stays PARTIAL; a separate closure audit decides.
