# L02-P10: the eighth closure audit's residuals — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record qualifies `228c788bd82e7bf30bb49c9f9ef4c85691078516`, the
branch `fix/l02p10-audit8-residuals` on origin/main `9a9eda112`. The final
run (`records/final/`) used a clean detached checkout of that commit on
the Linux AArch64 host, with GNU ld 2.42, LLD 22.1.6 and gold 2.42.

## What the eighth closure audit found (at `9a9eda112`)

It kept L02-P10 PARTIAL. The blocking finding was a static executable linked
through LLD whose linker script renames the output `.eh_frame`. With
`-Wl,--no-eh-frame-hdr` and `.text` 0xc0000000 above it, the program was
installed with all 916 FDEs truncated and aborted in `_Unwind_Backtrace`.
The check chose sections by the name `.eh_frame`, but `crtbeginT.o`
registers its frames whatever the section is called. It also found six
smaller residuals, all repaired here:
- a false `--no-eh-frame-hdr` statement;
- GNU-ld-only overflow controls;
- GNU ld's silent truncation of its own IE/TLSDESC-to-LE relaxation;
- gold's unclassified TLS message;
- a silently skipped RSS assertion;
- two stale statements.

## The repair, as four independent verifiers shaped it

- **`8cc1e33bb`, `758f4d866`, `84ceb2eb7`.**
  - Every staged Linux link writes a link map. The check decodes every
    `.eh_frame` input piece it places, whatever the output section is
    called. A static executable whose map is missing or cannot place its
    input is refused by name.
  - The native overflow controls run through the three linkers, and a
    JUMP26 veneer control is added.
  - An executable whose `PT_TLS` reaches 2^32 is refused as
    `[TCG-LINK-TLS-TPREL-UNPROVEN]`.
  - gold's "too far from TP" is classified, and the RSS is measured with
    `wait4`.
- **First verifier (soundness).** An ET_EXEC with `crtbeginT.o` and a
  `PT_INTERP` (`--static` then `-Wl,-Bdynamic`) was installed with every
  registered FDE truncated. It also found a TPREL off-by-one at the exact
  edge and an unrecognised map spelling. **Repair `c3079bfd7`, `54310b3af`,
  `824fb7980`:** the map requirement is keyed on whether an input
  registers frames (it imports a libgcc registration function, or takes
  its own `.eh_frame` address), whatever the image kind.
- **Second verifier (robustness).** Shared-object and LTO/bitcode inputs
  were taken to register nothing. **Repair `f885aed47`, `82e7fb941`:**
  shared objects are read for registration imports; unread formats fail
  closed; a global symbol inside an object's own `.eh_frame` counts.
- **Third verifier (low).** A malformed `.dynsym` read as "imports nothing",
  the native control never loaded its library, and a count was wrong.
  **Repair `d9475df93`, `228c788bd`:** a shared object's imports are read
  through `PT_DYNAMIC` as the loader binds them, failing closed on anything
  it would read differently. The control links `--no-as-needed` and proves
  the registration at run time.
- **Fourth verifier.** Accepted. It fuzzed the new reader with about a
  million inputs and got no panic, reproduced the host scan exactly
  (4,249 ET_DYN files, 2 importers, 273 unreadable debug files), and found
  no false refusal among the ordinary libraries.

## Final run (`records/final/`)

| Target | Result |
| --- | --- |
| `trust-cg-codegen --lib` | 4,189 passed, 1 ignored, run without `TCG_*` controls |
| CLI binary / `link_options` / `output_paths` | 30 / 37 / 8 |
| `e2e_aarch64_link_runtime` | 34 |
| `e2e_aarch64_elf_tlsie` | 13 |
| `e2e_aarch64_eh_linux` | 10 |
| `e2e_aarch64_eh_catch` | 9 |
| `aarch64_elf_cfi_differential` | 3 |
| `e2e_aarch64_elf_link` | 11 |

- **Native targets:** they ran with `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1`,
  and no log has a `SKIP` line.
- **Ordinary-link matrix (`matrix.log`):** 66 of 66 links through the CLI
  built from this source (sha256 in `matrix-cli.sha256`) install and run.
  They cover GNU ld, LLD and gold × default/pie/no-pie/static, `-s`,
  `--gc-sections`, user maps, `--static -Wl,-Bdynamic`, `-Wl,-M` and
  `-z nosectionheader`. No staging directory was left behind.
- **Host `.eh_frame` survey (`survey/`):** 6,368 images and 5,091,400 FDEs
  give the same verdict image by image as the hostile-products record
  (`verdict-diff.txt` is empty): 6,081 pass, 273 debug files unproven, 14
  hidden-FDE libraries, no aliasing pointer.

## Mutants and reproducers (`records/rounds/`)

Each round's semantic source mutants ran on that round's commit
(`source.txt` in each directory names it). They total 54, and each was
killed at test assertions:

| Round | Commit | Mutants |
| --- | --- | --- |
| the map check, TPREL, gold's message | `8cc1e33bb` | 16 |
| registration by behaviour | `c3079bfd7` | 13; one first failed to compile under `-D warnings` and was rewritten (`mutation2b`) |
| shared objects, LTO and bitcode | `f885aed47` | 10 |
| the loader-level dynamic reader | `d9475df93` | 15 |

`repro1`–`repro4` hold the audit's and the verifiers' reproducers as each
repair ran them (logs and `summary.txt`; the linked binaries are not kept).
`scripts/` holds the mutant and reproducer drivers.

## Boundaries

This is execution, decoder and reader evidence on one host's three
linkers, not a proof.
- **Registration not seen:**
  - a program that reaches a registration function without a symbol
    reference (`dlsym`), or through a library reached only as another
    library's `DT_NEEDED` dependency, and registers an address no input
    exports or takes from its `.eh_frame`;
  - an input replaced between the link and the driver's read.
- **Conservative refusals:**
  - LLD static links whose `.eh_frame` shares an output section;
  - `-Wl,-M` through GNU ld and LLD;
  - an `--as-needed` library that may register but is dropped;
  - any executable with a 4 GiB thread-local block.

L02-P10 stays PARTIAL; a ninth closure audit decides.
