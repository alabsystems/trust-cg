# Integrated Linux gates before the eighth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `27a7d598b199c5f396b612a65bb05fbb3a255ec1`.
It is origin/main `7cacebb13` plus two repairs, each checked by an
independent verifier.

**The L02-P10 GOT-page slot-region repair** (`c07ffabca`, `06a52ef2c`)
changes how the staged image check finds GOT slots. It used to go by
section name; it now derives them from the image itself:

- file-backed allocated memory;
- every `DT_RELA`/`DT_REL`/`DT_JMPREL`/`DT_RELR` target;
- the `DT_PLTGOT` and `DT_TLSDESC_GOT` words;
- non-allocated sections placed at an address, which covers a linker
  script's `INFO`, `COPY`, `DSECT` and `OVERLAY` outputs.

A linker script that renamed `.got`, or moved it into a non-allocated
section, used to escape the check and install a library or executable with
a truncated `ADRP` that segfaulted. Both cases are now refused.

A refusal that the image cannot show to be an overflow is now its own
code, `[TCG-LINK-GOT-PAGE-UNPROVEN]` (kind `unclassified`). An image
without section headers that has a GOT-page input is refused that way.

**The explicit-section placement repair** (`de03ef846`) decides every
explicit ELF section name from one table, `ELF_NAME_RULES`. The GNU ld 2.42
column is derived from its default scripts, and a unit test re-derives it.
The LLD 22.1.6 column comes from probing: 350 shapes, each linked as PIE,
`-no-pie`, `-z norelro` and `-shared`.

A mutable global used to be admitted into names that fault on store, land
in TLS, RELRO or unwind outputs, or make a segment RWX. That class is now
refused by name. It includes `.tcommon`, `.jcr`, `.gcc_except_table.x`,
`.eh_frame.x`, `.sframe`, `.gnu_extab`, `.exception_ranges`, `.igot` and
`.tm_clone_table`, plus about 30 further names.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **147 required target families
and 886 Rust tests**. Source fingerprint
`2350270eb5a46e2eab05dcec5886d199a6a722d8633c168a291f2122673f35e9` was
identical before and after. The run took 647 seconds of target wall time
(10:35:20Z to 10:46:18Z), with a highest sampled resident set of 166 MiB.
All four controls were on, and the AY/Clean and dependency identities did
not change.

Changed targets:

| Target | Passed |
| --- | --- |
| `e2e_aarch64_link_runtime` | 32/32 |
| `e2e_aarch64_elf_sections` | 25/25 |
| `e2e_aarch64_elf_stack_zero_fill` | 12/12 |
| `e2e_aarch64_globals_linux` | 15/15 |
| `e2e_aarch64_elf_tlsie` | 11/11 |
| `link_options` | 16/16 |

## Library and CLI suites

On the same checkout, `cargo test -p trust-cg-codegen -p trust-cg-lower --lib`
passed:

- codegen 4,113 passed and 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`);
- lower 1,879 passed.

In `cargo test -p trust-cg-cli`:

- the binary's tests passed 29/29;
- `--test link_options` passed 16/16;
- `--test output_paths` passed 8/8.

## Known finding at this source (fix in progress)

The independent check of the placement table swept 3,427 names in about
25,000 links and found one family the table misses. GNU ld treats every
name that begins with `.eh_frame_entry` as compact unwind data, but the
table refuses only `.eh_frame_entry` and `.eh_frame_entry.*`. So trust-cg
accepts `.eh_frame_entryx` and similar names, and every GNU ld link of such
an object then fails with "compact frame descriptions incompatible with
DWARF2 .eh_frame". That is a loud link error, not wrong code; LLD links
and runs it. The documents at this source list `.eh_frame_*` as refused.

The trust-cg-cli `trust_ir_binary_container` failures recorded in
[the seventh push's gate record](../2026-09-23-linux-integrated-gates-6/README.md)
still stand. Their fix is in progress with the integration-sweep triage.

## Not run

The bridge lane was not run. These changes are in the CLI link driver's
image check and the ELF section classifier, and the bridge still refuses
`#[link_section]` (L06-P1).

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.

`records/run11/` holds the complete floor output, and `records/lib-i8.log.gz`
and `records/cli-i8.log.gz` hold the library and CLI transcripts.
