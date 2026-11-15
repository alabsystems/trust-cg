# L02-P10: the `.eh_frame` refusals, fourth repair — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record qualifies `8120f3bdb576bfc090706de0194cf2394fa25b26`, the
fourth repair, on top of the third repair (`fb4722a41`, `811fda1af`) and
origin/main `aceeb3bb6`. Every leg ran on that clean source on the Linux
AArch64 host, with GNU ld 2.42, LLD 22.1.6 and gold 2.42.

## What the fourth verifier found (on `fb4722a41`)

It found no false refusal. All the round-3 shapes install, and header-less
`-nostdlib` libraries with an LSDA or `.sframe` install through GNU ld and
LLD, 8 of 8. The labels it checked by execution are right: LLD's hidden-FDE
programs and libraries terminate.

It found two soundness regressions introduced by the third repair. The
second repair had refused both:
- **No table.** Without section headers and without a table, a walk that
  stopped at a record it took as foreign was accepted. libgcc, with no
  table, reads on to a zero length. GNU ld writes no table when it cannot
  parse an input `.eh_frame`. Its `-nostdlib -z nosectionheader` libraries
  were installed, one holding a 64-bit record and one an FDE placed before
  its CIE, and their throws aborted or terminated.
- **Static narrow FDEs.** libgcc's registered search (static executables)
  returns any FDE that covers the pc. A narrower FDE with a range
  (`y_mid`, 0x18 of 0x34, return address undefined), which begins together
  with the function's own, was taken whatever the table named. An LLD
  static program was installed and terminated; 19 of 41 padding layouts
  terminate.

## The repair

- **The no-table walk.** Without section headers and without a table, the
  walk must end at a zero length; otherwise the image is unproven. With a
  table, the third repair's stop points still apply.
- **Static narrow FDEs.** In a static executable a narrower FDE with a
  range that begins together with a wider one is undecided (`unclassified`,
  `[TCG-LINK-EH-FRAME-UNPROVEN]`) whatever the table names. Zero-range ties
  still follow the table.
- **Wording.** The undecided message and the quoted LIMITATIONS,
  CHANGELOG and completion-record sentences are corrected.

## Tests (`records/tests/`)

| Target | Result |
| --- | --- |
| `trust-cg-codegen --lib` | 4,154 passed, 1 ignored, run without `TCG_*` controls |
| CLI binary / `link_options` / `output_paths` | 30 / 33 / 8 |
| `e2e_aarch64_link_runtime` | 32 |
| `e2e_aarch64_elf_tlsie` | 13 |
| `e2e_aarch64_eh_linux` | 10 |
| `e2e_aarch64_eh_catch` | 9 |
| `aarch64_elf_cfi_differential` | 3 |
| `e2e_aarch64_elf_link` | 11 |

The native targets ran with `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1` and
`--nocapture`, and no log has a `SKIP:` line.

The new native row is `link_options`
`linux_got_page::eh_frame_walks_without_a_table_and_static_narrow_fdes_are_refused`:
- **The 64-bit-record library.** GNU ld's library with the 64-bit record
  is refused with and without section headers.
- **Swapped in at run time.** GNU ld's own header-less library, in place
  of a normal `libcb.so`, aborts at the throw; the normal one catches.
- **LLD static.** LLD's static narrow-FDE program is refused as undecided,
  and its raw static link terminates.
- **Dynamic twin.** The same objects linked `--no-pie` catch.

## Source mutants (`records/mutation/`)

The third repair's six mutants and two new ones are all killed at test
assertions, and none failed to compile.

| New mutant | Killed by |
| --- | --- |
| `no-table-accepts-an-early-stop` | the unit test's no-table rows and the native row's 64-bit-record library |
| `static-narrow-follows-the-table` | the unit test's static narrow row and the native row's LLD static program |

## Host survey (`records/survey/`)

Unchanged:
- no aliasing pointer;
- no undecided tie;
- 14 hidden-FDE shared objects;
- 6,081 images pass, and the 273 debug files are unproven.

## Boundaries

This is execution, object and decoder evidence on one host's three
linkers, not a proof.
- **Static labels.** A static executable that registers nothing (gold's
  `crtbeginT.o`, or a `-nostdlib` link without it) is labelled unproven
  where the table alone decides; the image is refused either way.
- **CIE pointers.** The check reads an FDE's CIE pointer as unsigned, where
  libgcc reads it signed. A CIE placed after its FDE is refused
  conservatively.
- **Read-back.** The read-back fix is on a separate branch.

L02-P10 stays PARTIAL; a separate closure audit decides.
