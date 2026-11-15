# L02-P10: the `.eh_frame` refusals, third repair — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record qualifies `811fda1af7acbcc3b7409e4f0b037bed46760cdc`: the third
repair (`fb4722a41`) and its test fixes (`811fda1af`), on origin/main
`aceeb3bb6`. Every leg ran on that clean source on the Linux AArch64 host,
with GNU ld 2.42, LLD 22.1.6 and gold 2.42.

A first run, on `fb4722a41`, had two problems:
- **An ETXTBSY flake.** `e2e_aarch64_eh_linux` failed once with "Text file
  busy": a mutated binary written by the test process was executed while
  another test thread's fork held the write descriptor.
- **A surviving mutant.** `no-foreign-fde-stop` survived because the unit
  row's foreign record named a real CIE and read as a removed FDE.

`811fda1af` fixes both. The mutated binaries are written from a child
shell, and the CIE pointer now points outside the loaded bytes.
`e2e_aarch64_eh_linux` then passed six consecutive runs at 16 threads, and
everything below was rerun.

## What the third verifier found (on `02abd45dc`)

It found no soundness break. The walk could not be made to stop early and
miss an FDE, and the earlier reproducers were still refused. 42 executable
and 10 shared-library false-refusal cells installed and ran correctly. It
did find three false refusals from the second repair, a mislabelled
refusal, and overclaims:

- **`.gcc_except_table` after `.eh_frame`.** GNU ld puts
  `.gcc_except_table` or `.sframe` right after `.eh_frame` in its segment
  and writes no terminator for `-nostdlib`. A `-z nosectionheader` program
  with an LSDA was refused.
- **A static tie the table decides.** libgcc's registered search checks
  each range, never takes a zero-range FDE, and falls back to the table on
  a miss. A static tie whose table names the function's own FDE was
  refused.
- **The "static executable" test.** It was the wrong test for
  registration: a `--static --nostdlib` link has no `crtbeginT.o`, and
  gold's registers address 0.
- **LLD's placeholder.** LLD's zero-filled `.eh_frame_hdr` placeholder,
  written when a script discards `.eh_frame`, was refused.

## The repair

- **Where the walk ends.** Without section headers, the walk ends at a
  terminator or at the first record that is not `.eh_frame`'s: one that
  runs past the segment's file bytes or into a following `.eh_frame_hdr`,
  one with a 64-bit length, or an FDE whose CIE pointer names no CIE the
  walk read. A table entry that names an FDE at or past where such a walk
  ended leaves the image unproven.
- **Ties.** The table decides ties in every image. In a static executable
  (no `PT_INTERP`) a hidden FDE is `unclassified`
  (`[TCG-LINK-EH-FRAME-UNPROVEN]`), since a registered search may run first
  and find it. Elsewhere it stays `[TCG-LINK-EH-FRAME-WINDOW]`.
- **The placeholder.** A zero-filled `.eh_frame_hdr` that no
  `PT_GNU_EH_FRAME` locates is ignored.
- **Documents.** The walk-bound, tie, static-flag and gold wording is
  corrected.

## Tests (`records/tests/`)

| Target | Result |
| --- | --- |
| `trust-cg-codegen --lib` | 4,154 passed, 1 ignored, run without `TCG_*` controls |
| CLI binary / `link_options` / `output_paths` | 30 / 32 / 8 |
| `e2e_aarch64_link_runtime` | 32 |
| `e2e_aarch64_elf_tlsie` | 13 |
| `e2e_aarch64_eh_linux` | 10 |
| `e2e_aarch64_eh_catch` | 9 |
| `aarch64_elf_cfi_differential` | 3 |
| `e2e_aarch64_elf_link` | 11 |

The native targets ran with `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1` and
`--nocapture`, and no log has a `SKIP:` line.

The new native row is `link_options`
`linux_got_page::eh_frame_layouts_the_second_repair_refused_link_and_run`:
- GNU ld's `-nostdlib` LSDA program without section headers exits 42.
- LLD's static tie, whose table names `g_mid`'s own FDE, catches.
- LLD's bare-metal static program with a discarded `.eh_frame` exits 42.

## Source mutants (`records/mutation/`)

| Mutant | Killed by |
| --- | --- |
| `foreign-record-is-an-error` (the walk refuses at a foreign record) | the unit test and the native row's GNU ld LSDA program |
| `no-foreign-fde-stop` | `eh_frame_hdr_table_must_agree_with_the_fdes` (the foreign-FDE row) |
| `no-entry-past-the-walk` | the unit test's table entry past the walk |
| `static-hidden-observed` (a static hidden FDE labelled WINDOW) | the unit test's static label and the native static tie |
| `placeholder-hdr-read` | the unit tests and the native row's bare-metal program |
| `static-ignores-the-table` | the unit tests and the native row's table-decided static tie |

Each failed at test assertions; none failed to compile.

## Host survey (`records/survey/`)

The same 6,368 images (5,091,400 FDEs) give the same result: no aliasing
pointer, no undecided tie, and 14 hidden-FDE shared objects (the LLD-17
Qt6 libraries). 6,081 images pass, and the 273 debug files are unproven.

## Boundaries

This is execution, object and decoder evidence on one host's three
linkers, not a proof.
- A static executable's hidden FDE is refused as unproven, whether or not
  its registered search would find it.
- Without section headers, junk that parses as a record of this
  `.eh_frame` after it is read as one, so the result can only be a
  refusal.
- The earlier records' limits remain. The read-back fix is on a separate
  branch.

L02-P10 stays PARTIAL; a separate closure audit decides.
