# L02-P10: the `.eh_frame` refusals, second repair — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record qualifies `3438c9a693ec6fb109e6135ccd2c12b87c448f98`: the
second repair (`02abd45dc`) and its CLI test pin (`3438c9a69`), on
origin/main `0ecdc18a8`. Every leg ran on that clean source on the Linux
AArch64 host, with GNU ld 2.42, LLD 22.1.6 and gold 2.42.

The first run, on `02abd45dc`, failed one CLI unit test. That test pins a
static link's exact driver arguments, and they now include
`-Wl,--eh-frame-hdr`. Its temporary survey test also still used the old
result type. Both were fixed in `3438c9a69`, and everything below was
rerun on it.

## What the second verifier found (on `aa4b7c48c`)

1. **Bypass (medium).** With `-z nosectionheader`, only the FDEs the table
   names were read. The FDE that LLD's table drops was never seen, so an
   LLD library with an empty function before `read_data` was installed. A
   throw through `read_data` then terminated.
2. **gold `--static` (medium, pre-existing).** gold resolves `crtbeginT.o`'s
   `__EH_FRAME_BEGIN__` to 0. Its static C++ programs register no unwind
   information, and every throw aborts.
3. **Mislabelled tie (low).** A tie with no table was refused as an
   observed failure. In a static executable libgcc's own sort of the
   registered FDEs decides it: the natural order catches, and the reverse
   aborts.
4. **Wrong claim (low).** LLVM libunwind falls back to a linear scan, so the
   lookup model is libgcc's alone.
5. **Wrong example (low).** The Qt example named the empty
   `QProcess::setupChildProcess` instead of the hidden leaf
   `QProcess::readData`.

## The repair

- **Without section headers.** Every record from `eh_frame_ptr` is read,
  even with a table. The walk ends at a terminator, at the end of the file
  bytes of `.eh_frame`'s `PT_LOAD`, or at `.eh_frame_hdr` when that follows
  it. A record across that bound, or bytes after it that are not records,
  leave the image unproven. The missing-entry check now runs without
  section headers too.
- **Static links.** A static Linux link passes `-Wl,--eh-frame-hdr`, which
  the C driver passes for every other link.
- **Undecided ties.** A tie no table entry decides is `unclassified`
  (`[TCG-LINK-EH-FRAME-UNPROVEN]`). That means a start the table does not
  locate, or any tie in a static executable (`ET_EXEC`, no `PT_INTERP`).
- **Documents.** They now state libgcc's lookup and the correct Qt example,
  and the LIMITATIONS `.eh_frame` prose is one paragraph again.

## Tests (`records/tests/`)

| Target | Result |
| --- | --- |
| `trust-cg-codegen --lib` | 4,153 passed, 1 ignored, run without `TCG_*` controls |
| CLI binary / `link_options` / `output_paths` | 30 / 31 / 8 |
| `e2e_aarch64_link_runtime` | 32 |
| `e2e_aarch64_elf_tlsie` | 13 |
| `e2e_aarch64_eh_linux` | 10 |
| `e2e_aarch64_eh_catch` | 9 |
| `aarch64_elf_cfi_differential` | 3 |
| `e2e_aarch64_elf_link` | 11 |

The native targets ran with `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1` and
`--nocapture`, and no log has a `SKIP:` line.

The new native row is `link_options`
`linux_got_page::a_table_that_drops_an_fde_is_refused_without_section_headers_and_static_throws_run`:
- **LLD library.** It is refused with and without section headers, and
  LLD's own libraries terminate at the throw.
- **GNU ld library.** With and without section headers, it is installed
  and catches.
- **Static throw program.** It catches through GNU ld, LLD and gold, while
  gold's own static link without the flag aborts.
- **Static tie.** It is refused as unproven through LLD, and catches
  through GNU ld and gold.

## Source mutants (`records/mutation/`)

| Mutant | Killed by |
| --- | --- |
| `no-static-eh-frame-hdr` | `a_static_linux_link_asks_for_the_eh_frame_hdr` and the native row's gold static leg |
| `static-ties-follow-the-table` | the unit test's static-executable tie and the native row's LLD static tie |
| `undecided-ties-observed` | the unit tests' undecided rows and the native row's LLD static tie |
| `no-segment-bound` (walk to a terminator only) | the unit test's unterminated `.eh_frame` and the native row's GNU ld library without section headers |
| `table-only-without-headers` | the unit test's dropped-entry table without section headers and the native row's LLD library without section headers |

Each failed at test assertions (two tests each); none failed to compile.

## Host survey (`records/survey/`)

The temporary, ignored `survey_test.rs` checked the same 6,368 ELF
executables and shared objects (5,091,400 FDEs). It is not committed.
- No image has an aliasing pointer.
- No image has an undecided tie.
- 14 images have a hidden FDE: the LLD-17-linked Qt6 libraries bundled
  with NVIDIA Nsight. They are shared objects, so the table decides.
- 6,081 images pass, and the 273 separate debug files are unproven, as
  before.

## Boundaries

This is execution, object and decoder evidence on one host's three
linkers, not a proof. A static tie is refused conservatively, as are
bytes after `.eh_frame` in its segment in an image without section
headers. The earlier records' limits remain. The staged image is still
read back whole; that fix is on a separate branch. L02-P10 stays PARTIAL;
a separate closure audit decides.
