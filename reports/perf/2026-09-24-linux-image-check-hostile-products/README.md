# Linked-image checks: hostile-product costs bounded — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record qualifies `912e8e3a1` on origin/main `bba9997f5`:
- `e3acdf73c`: the repair;
- `d50ee5574`: its tests and record;
- `6b6c3c083`: timings in the documents set to the ones in `records/ab.txt`;
- `fed65f2f2`: the fourth bound, found by the repair's own verifier, and
  that verifier's doc fixes;
- `912e8e3a1`: the off-by-one the fourth bound's verifier found, and tests
  for the scan's choices.

`53c1cee17` after it corrects one test's rustdoc, and the commit that adds
this record updates the completion record's section; neither changes
code. A last verifier checked `912e8e3a1`'s scan against a reference
implementation on 2,418,749 exhaustive and 2,000,000 random cases, with no
disagreement.

Every leg ran on that clean source on the Linux AArch64 host, with GNU ld
2.42, LLD 22.1.6 and gold 2.42.

## What the read-back's third verifier found (on `30fb05ef3`)

No soundness defect. It did find three costs that grew with a product a
hostile image controls, outside every step bound, and an overstated
headroom claim:
- **Symbol names.** `elf_defined_symbols` and `elf_function_at` read each
  symbol's name to its NUL.
- **The `.eh_frame` pointer search.** `eh_wrap_alias` visited every span
  for each pointer.
- **Same-start FDE groups.** `eh_fde_overlaps` scanned the whole
  `.eh_frame_hdr` table for each group.
- **Headroom.** The `CHECK_ITEM_BOUND` rustdoc and LIMITATIONS said the
  largest host library holds about 11 times fewer targets than the bound.
  An Electron executable names 595,711, about 7 times fewer.

## The repair

- **Symbol names.** A wanted name is compared at its own length and the
  byte after it (a NUL or the table's end): the old comparison, without
  reading the rest of the name. A diagnostic's function name is read to at
  most 4 KiB.
- **The pointer search.** A pointer whose address and searched spans lie
  within one window of its field has no alias and takes no step. Otherwise
  the search takes the fewer of one step per span and one per candidate
  address, counted toward `CHECK_WORK_BOUND` (16,777,216) for the whole
  walk; past it the image is an unproven `.eh_frame`.
- **Same-start groups.** The table's last entry for each start is looked
  up in a map built once.
- **Placeholder scan.** Without a `PT_GNU_EH_FRAME`, the zeros scanned in
  `.eh_frame_hdr` sections for LLD's zero-filled placeholder are counted on
  their own, at most `CHECK_WORK_BOUND` of them before a non-zero byte.

## The repair's verifier (on `e3acdf73c`)

It found the repair sound. Its differential tests against the old code
agreed on every input: 400,000 random and 300,000 window-edge alias
searches, 1,440 near 2^64, 300,000 overlap cases and 2,000,000 name
comparisons. In an instrumented build, all 10.08 million alias searches
over the 6,626 host images took the fast path, with no mismatch. It found:
- **A fourth cost**, predating the repair: without a `PT_GNU_EH_FRAME`,
  each section named `.eh_frame_hdr` was scanned whole for LLD's
  placeholder, so 1,000 headers naming the same 64 MiB of zeros installed
  after 17.5 s. `fed65f2f2` bounds it.
- **Doc nits**: the `alias_work` rustdoc left out the pointer's own
  address, and the survey's largest extent is 685 MiB, not 684. Both are
  fixed.
- **A diagnostic difference**: `elf_function_at` now names the first
  covering function where it gave no name when a later covering
  candidate's `st_name` lay past the string table. This changes only a
  diagnostic's subject.

## The fourth bound's verifier (on `fed65f2f2`)

It found the bound sound. On images over 1 GiB read back piecewise, the
verdict matched the whole-file read in 148 differential cases (78 at three
block sizes and two paddings, 70 under tight bounds). It found:
- **An off-by-one** (fail-closed): the scan window stopped one byte short.
  Exactly 16,777,216 zeros followed by a real table were refused, with a
  message saying there were more. `912e8e3a1` looks at the zeros still
  allowed and the byte after them.
- **Four surviving mutants**: a wider window, a section with a non-zero
  byte never chosen, an unreadable section skipped, and only the first
  byte tested. The unit test now pins each (see the mutants below).
- **Doc nits**: the zeros have their own count, not the pointer search's,
  and the test rustdoc credited the wrong verifier. Both are fixed.

## Hostile images (`records/ab.txt`)

Release CLIs built from `bba9997f5` (before) and `e3acdf73c` (after; the
tests and documents after it do not change the binary's code). A stand-in
linker (`harnesses/cc`) copies each image to the staging path. The image
generators are `harnesses/generators/gen3.py` (the verifier's) and
`harnesses/generators/gen_spread.py`; `ab.txt` lists each image's size and
SHA-256.

| Image | Before | After |
| --- | --- | --- |
| 1,000 symbols over a 64 MiB string table without NULs | 17.63 s, installed | 0.06 s, installed |
| 100,000 FDEs over as many sections | 11.80 s, installed | 0.09 s, installed |
| 200,000 same-start groups | 5.40 s, installed | 0.15 s, installed |
| 3,000 sections 4 GiB + 4 KiB apart | 0.01 s, installed | 0.01 s, installed |
| 100,000 sections 4 GiB + 4 KiB apart | 11.85 s, installed | 0.09 s, `[TCG-LINK-EH-FRAME-UNPROVEN]` (past the step bound) |

`records/ab-hdrzeros.txt` is the same A/B for the fourth cost, with the
after CLI rebuilt from `912e8e3a1`'s source (generators
`harnesses/generators/gen_hdrzeros.py` and `gen_vh.py`, both the
verifiers'):

| Image | Before | After |
| --- | --- | --- |
| 1,000 `.eh_frame_hdr` headers naming the same 64 MiB of zeros | 17.58 s, installed | 0.06 s, `[TCG-LINK-EH-FRAME-UNPROVEN]` (past the bound) |
| one 16 MiB zero-filled `.eh_frame_hdr` | installed | installed |
| 8 MiB + 8 MiB of zeros, then a real table (the exact bound) | installed | installed |
| the same, placed past 1 GiB (read back piecewise) | installed | installed |
| 16 MiB of zeros in one section, then a real table | installed | installed |
| 8 MiB + 8 MiB + 1 zeros, then a real table | installed | `[TCG-LINK-EH-FRAME-UNPROVEN]` (one zero past the bound) |

## Tests (`records/tests/`)

| Target | Result |
| --- | --- |
| `trust-cg-codegen --lib` | 4,175 passed, 1 ignored, run without `TCG_*` controls |
| CLI binary / `link_options` / `output_paths` | 30 / 34 / 8 |
| `e2e_aarch64_link_runtime` | 32 |
| `e2e_aarch64_elf_tlsie` | 13 |
| `e2e_aarch64_eh_linux` | 10 |
| `e2e_aarch64_eh_catch` | 9 |
| `aarch64_elf_cfi_differential` | 3 |
| `e2e_aarch64_elf_link` | 11 |

The native targets ran with `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1` and
`--nocapture`, and no log has a `SKIP:` line. The new unit rows:
- `eh_wrap_alias_agrees_with_a_full_search_and_is_bounded`: 4,000 random
  2-byte cases against a search of every address with the field's bits,
  each search mode over 100 times; no step within one window; the bound.
- `an_alias_search_past_the_step_bound_leaves_the_image_unproven`: 5,000
  spread sections whose `pc_begin` and LSDA searches pass the bound only
  together (2,000 FDEs) are unproven; the 1,500-FDE twin is accepted.
- `symbol_names_are_compared_at_the_wanted_length`: longer and shorter
  names, a name that ends at the table's end, a 1 MiB function name.
- `zero_filled_eh_frame_hdr_sections_are_scanned_within_the_step_bound`:
  two 8 MiB placeholders (the bound exactly) are skipped, and a real table
  after them is read; one more zero leaves the image unproven; a section
  with a non-zero byte after 256 zeros, and one whose `sh_size` runs past
  the file's end, are read as the table.

## Source mutants (`records/mutation/`)

All sixteen are killed at test assertions, and none failed to compile:
- the pointer search: `no-window-fast-path`, `no-step-bound`,
  `candidates-miss-the-last`, `candidates-skip-the-first`,
  `bound-per-pointer` (the LSDA and personality search's counter reset per
  pointer) and `fde-bound-per-pointer` (the `pc_begin` search's);
- symbol names: `name-needs-a-nul`, `name-prefix-matches`,
  `function-name-unbounded`;
- same-start groups: `overlaps-first-entry`;
- the placeholder scan: `placeholder-window-one-short` (the verifier's
  off-by-one), `placeholder-scan-unbounded`, `placeholder-scan-not-counted`,
  `placeholder-nonzero-not-chosen`, `placeholder-first-byte-only` and
  `placeholder-unreadable-skipped`.

## Host surveys (`records/survey/`)

- **Verdicts.** The same 6,368 images (5,091,400 FDEs) as the fourth
  `.eh_frame` repair give the same result: 6,081 pass, the 273 debug files
  are unproven, 14 hidden-FDE shared objects, no aliasing pointer.
- **Spread.** `spread.txt` (`harnesses/spread.py` over the 6,626 images of
  the read-back's survey): every image keeps its allocated memory within
  4 GiB, the largest (`libcublasLt.so.13.1.1.3`) within 684 MiB, so none
  of its 4-byte pointers takes a search step.

## Boundaries

This bounds costs. It changes no verdict of an image within the bounds,
and an image past the step bound is refused by name. Other products named
in LIMITATIONS stay proportional (relocation targets × `SHT_NOBITS`
sections and `PT_LOAD` tails, input uses × targets, linker-written slots ×
executable regions).
