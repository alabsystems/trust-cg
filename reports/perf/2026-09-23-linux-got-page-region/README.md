# L02-P10 GOT-page slot-region repair (Linux AArch64) — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the repair of the staged GOT-page image check in
`link_driver::run_link`, commit `c07ffabca`
(`c07ffabca9bca08cc8823bc8f3d86bfd6dbca8c8`, tree
`11ea6c86088573db75c125ae487a16c9e9b73933`). The check had chosen the GOT
by section name. The run used the Linux AArch64 host (NVIDIA Grace,
`CPU part 0xd87`, Ubuntu 24.04, glibc 2.39, GCC 13.3, GNU ld 2.42, gold
2.42, LLD 22.1.6, stock Rust 1.97.1). `git status --porcelain
--untracked-files=all` was empty before and after the qualifying run and
after every mutant. `records/results.json` holds the provenance, tool
identities and every gate and probe exit.

L02-P10 stays **PARTIAL**. A separate adversarial audit decides closure.

A second independent verifier later found a slot this repair could not
see: a GOT in a non-allocated section. The second repair, `06a52ef2c`, and
its qualifying run are in [Second repair](#second-repair-non-allocated-sections-recordsrepair)
below (`records/repair/`). The first-run records above that section are
unchanged.

## The defect

An independent verifier found the check unsound. It compared the farthest
code byte with the farthest byte of the sections named `.got`/`.got.*`. It
fell back to all allocated sections only when no such section existed. A
`-Wl,-T` script, `SECTIONS { .slots 0x200000000 : { *(.got) *(.igot) } }
INSERT BEFORE .got;` with `--section-start=.got.plt=0x80000000`, moves the
real GOT slots to 8 GiB under another name while `.got.plt` stays at 2 GiB.
Under that script `trust-cg -shared` installed a library whose
`ADR_GOT_PAGE` site is `adrp x1, 0` for a `GLOB_DAT` slot at
`0x200000008`, and an executable using it exited 139. The verifier also
found a misleading diagnostic. A conservative refusal, an executable
section 8 GiB away with no GOT reference, was reported as
`relocation-out-of-range`. Its text asserted a truncated page delta that
does not exist.

## The repair

`got_page_layout` derives both regions from the image:

- Possible sites are every executable byte: `SHF_EXECINSTR` sections and
  `PF_X` `PT_LOAD` segments.
- Possible slots are:
  - all file-backed allocated memory: every allocated section that is not
    `SHT_NOBITS`, and every `PT_LOAD` segment's file contents;
  - every target of the relocation tables the dynamic section names
    (`DT_RELA`, `DT_REL`, `DT_JMPREL`, `DT_RELR`), which are read through
    the program headers;
  - every target of the allocated relocation sections;
  - the GOT words `DT_PLTGOT` and `DT_TLSDESC_GOT` name;
  - every zero-fill region that holds such a target.

The image is admitted only when the page delta between the farthest
possible site and the farthest possible slot fits the window.

Diagnostics:

- A refused use is `relocation-out-of-range` with
  `[TCG-LINK-GOT-PAGE-WINDOW]` only when a dynamic relocation names its own
  slot and every code byte is out of that slot's window. The relocation is
  `GLOB_DAT`, `TLS_TPREL64` or `TLSDESC` against the use's non-local
  symbol.
- Every other use is `unclassified` with `[TCG-LINK-GOT-PAGE-UNPROVEN]`.
  Its text says the refusal is conservative, not an observed overflow.

## Gates (records/logs)

| gate | result |
| --- | --- |
| `cargo test -p trust-cg-codegen --lib` | `test result: ok. 4108 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` |
| same, filtered to `link_driver` | `test result: ok. 31 passed; 0 failed; 0 ignored; 0 measured; 4078 filtered out` |
| `--test e2e_aarch64_link_runtime` (`--nocapture`) | `test result: ok. 31 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `--test e2e_aarch64_elf_tlsie` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `--test e2e_aarch64_elf_relocation_model` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `--test e2e_aarch64_globals_linux` | `test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `--test aarch64_elf_symbol_binding` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo test -p trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo test -p trust-cg-cli --test link_options` | `test result: ok. 16 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo test -p trust-cg-cli --test output_paths` | `test result: ok. 8 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo check -p trust-cg-codegen --features verify`, `cargo build -p trust-cg-cli` | exit 0 |
| `scripts/check_fmt.sh`; the three gate script tests (`Ran 94 tests`, `OK (skipped=1)`); `check_documentation.py --write` then `--check`; `generate_diagnostics_inventory.py --check`; `check_evidence_archive.py --plan` and on the two earlier L02-P10 archives, whose README corrections this change makes; `native_test_host_matrix.py --check` | exit 0 |

The new code is a string literal in `link_driver.rs`, which the
diagnostic census does not scan, so the census is unchanged and its
`--check` passes.

In the `e2e_aarch64_link_runtime` log, every refused row prints `the linker
accepted it; the link driver refused the image`. The refusals come from
the staged image check after GNU ld 2.42 linked the image:

- The GOT at `0x200000000` and at `0x100010000` gets two
  `[TCG-LINK-GOT-PAGE-WINDOW]` lines each.
- The `INSERT` rename (`libslots.so`, and `libslots-nosh.so` under `-z
  nosectionheader`) gets `WINDOW` for `tcg_desc_word` and `UNPROVEN` for
  `tcg_desc_tls`.
- The static slot (`static-far`) gets two `UNPROVEN` lines.
- The far executable section (`far code`) gets two `UNPROVEN` lines.

The same log shows what GNU ld produces without the driver's check.
`libslots-raw.so` and `static-far-raw` make their executables exit 139.
`libfarcode-raw.so` runs, exit 0.

## Direct probes (records/direct)

`records/inputs/got_page.tmbc` is the `pic` probe module of the earlier
runs and the verifier (identical SHA-256, `2c3c6605…b1df`). `tcg_desc_bump`
reaches `tcg_desc_tls` through a TLS descriptor and `tcg_desc_word` through
the GOT. The linker scripts are in `cg/slots-far.ld` and
`cg/slots-near.ld`. In `cg/`, `libslots.so` and `libfar.so` held `precious\n`
before the probes.

- `cli-insert-rename`: the verifier's command exits 1.
  `tcg_desc_word` gets `error[link:relocation-out-of-range]`
  `[TCG-LINK-GOT-PAGE-WINDOW]`: its `R_AARCH64_GLOB_DAT` slot at
  `0x200000008` is at page delta `8589934592` from the nearest code byte.
  `tcg_desc_tls` gets `error[link:unclassified]`
  `[TCG-LINK-GOT-PAGE-UNPROVEN]`, because its `TLSDESC` slot at
  `0x80000018` is in reach. `libslots.so` still reads `precious`, and no
  `.tcg-link-*` directory is left (`ls-after`).
- `cli-insert-rename-nosectionheader`: the same link with `-z
  nosectionheader` gets the same verdicts, read through the segments and
  dynamic tags.
- `raw-gnu-ld-insert-rename`: GNU ld links the same library without the
  driver. `readelf-rW` shows `GLOB_DAT` at `0x200000008`, and `objdump-d`
  shows `adrp x1, 0 <tcg_desc_tls>` then `ldr x1, [x1, #8]`. The executable
  linked against it is killed by SIGSEGV (`run-desc-slotsraw`, exit -11).
- `cli-insert-near`: the same script with `.slots` at 1 GiB is installed,
  and its executable exits 0 (`run-desc-slotsnear`).
- `cli-far-got-shared` and `cli-edge-got-shared`: the GOT at 8 GiB, and at
  `0x100010000` (64 KiB past the upper edge), each exit 1 with two
  `[TCG-LINK-GOT-PAGE-WINDOW]` lines. `libfar.so` still reads `precious`.
  `cli-near-got-shared` (2 GiB) is installed and runs (`run-desc-near`,
  exit 0).
- `cli-far-code`: an executable `.farcode` section at 8 GiB with no GOT
  reference, passed as `-Wl,<dir>/far.o`, exits 1 with two
  `error[link:unclassified]` `[TCG-LINK-GOT-PAGE-UNPROVEN]` lines that say
  the refusal is conservative. `raw-gnu-ld-far-code` links the same library
  without the driver, and its executable exits 0 (`run-desc-farcoderaw`).
  This refusal is conservative, not a defect avoided.
- `cli-static-slot-far`: a `-no-pie -nostdlib` executable
  (`cg/start.c` calls libc's `_exit`) under the same `INSERT` script exits
  1 with two `UNPROVEN` lines. `raw-gnu-ld-static-slot-far` shows why
  dynamic relocations alone do not suffice. The executable has a dynamic
  section (`NEEDED libc.so.6`, `PLTGOT 0x80000000`), and its only dynamic
  relocation is `_exit`'s `JUMP_SLOT` at `0x80000018`. `.slots` at
  `0x200000000` holds the linker-filled slot, and no relocation names it.
  It is killed by SIGSEGV (`run-static-far-raw`, exit -11). Without the
  script, `cli-static-slot-near` is installed and exits 0.

## Mutation leg (records/mutation)

`harnesses/mutation-got-page-region-20260923.py` applied each mutant to the
clean head, ran the named tests and restored the file byte for byte. The
harness ran once with S1 alone and once with S2 through S6. All six mutants
were killed. Each expected test is named `FAILED`, and `status_after` is
empty:

- S1 restores the name-only region: the `.got`/`.got.*` span, with every
  section only when no such section exists. The unit test
  `a_got_renamed_by_a_linker_script_is_a_possible_slot_region` fails. Both
  e2e rows (`a_got_moved_by_a_linker_script_is_refused_whatever_its_name`,
  `a_got_slot_without_a_dynamic_relocation_is_still_found`) panic
  `must not link silently: Ok(LinkSuccess { .. })`.
- S2 uses the region the review suggested: `.got*` names and the sections
  holding a dynamic relocation target, with every section only for an
  image without dynamic targets. The unit row for a dynamic image whose far
  slots have no relocation fails. The e2e static-slot row panics `static-far:
  must not link silently`.
- S3 does not read the dynamic section. The stripped-header and certainty
  unit tests fail. The e2e 8 GiB and rename rows lose the observed overflow
  (`unclassified` where `relocation-out-of-range` was expected).
- S4 reports an unproven refusal as `relocation-out-of-range`. Both
  refusal unit tests fail, and so do the e2e far-code and rename rows.
- S5 lets the certainty rule ignore the window. The certainty unit test
  fails, and the e2e rename row reports `tcg_desc_tls`, whose slot is in
  reach, as an overflow.
- S6 attributes a same-named dynamic slot to a local symbol. The certainty
  unit test fails.

## Boundaries

This is unit, linker and execution evidence on one host, not proof.

The check cannot see:

- a slot the linker fills but places in zero fill that no relocation or
  tag names. Its linked value is not in the file. GNU ld 2.42 refuses to
  link a GOT into a `NOLOAD` section ("final link failed: section has no
  contents"), which was observed on this host during the investigation and
  is not archived. Correction (2026-09-23): this item was incomplete. GNU
  ld refuses only `NOLOAD`. It links a GOT into an `INFO`, `COPY`, `DSECT`
  or `OVERLAY` section. That section is not allocated, so this repair did
  not see it, and over zero fill its undefined-weak slot reads zero, which
  is its right value. See the second repair below.
- a zero-fill slot filled through Android's packed `DT_ANDROID_RELA`
  relocations.
- code that is not executable where it is loaded.

The refusal is conservative. An image whose possible sites and possible
slots span more than the window is refused, even when every real site is in
reach. The far executable section is one such case. A large `.bss` is not,
because zero fill without a target does not count.

An observed overflow assumes that a symbol's GOT slot of a given kind is the
one its dynamic relocation names. It is only a label on a refusal: no image
is admitted on that basis.

The check covers only links through `run_link` (the CLI's link step) and
only positional AArch64 ELF relocatable inputs. It does not cover archive
members, shared libraries or links made outside the driver. Only GNU ld was
driven. LLD refuses these placements itself, and gold gave no GOT-page
evidence in the earlier run.

## Reproduce

```sh
python3 -B harnesses/qualify-got-page-region-20260923.py <worktree> <run-dir>
python3 -B harnesses/mutation-got-page-region-20260923.py <worktree> <run-dir> [MUTANT ...]
python3 -B harnesses/archive-got-page-region-20260923.py <run-dir> <this directory>
```

`<run-dir>/inputs/got_page.tmbc` is `records/inputs/got_page.tmbc.gz`
decompressed.

## Second repair: non-allocated sections (records/repair)

The verifier's reproducer is a static `-nostdlib` executable. A `-fPIC`
`_start` (`records/repair/direct/cg/weakst.c`) exits 0 when the undefined
weak `tcg_weak_missing` is null. It is linked with the `pic` probe and a
script that lays `.slots (INFO) : { *(.got) *(.igot) }` over
`.farbss (NOLOAD)` zero fill at the same address
(`cg/info-0x200000000.ld`). GNU ld 2.42 makes `.slots` non-allocated
(flags `W`, no `A`) at `0x200000000`. The first repair read only allocated
sections, and a static image has no relocation or tag naming the slot, so
`trust-cg --static --nostdlib --relocation-model pic` installed the image.
It died with SIGSEGV, while the `0x40000000` twin runs.

Commit `06a52ef2c` (`06a52ef2c5dae458c30a4b0ec1569cbb51ff6b06`, tree
`89c53d726d6de9724696af8ef249594e7bdc6aac`) counts every non-allocated
section at a nonzero address or with `SHF_WRITE` as a possible slot region,
whatever its type (`elf_placed_sections`). A placed executable one also
counts as possible code. An image without a section header table cannot
show such a section: program headers describe only loaded memory. It is
therefore never shown in reach and is refused as
`[TCG-LINK-GOT-PAGE-UNPROVEN]` ("it has no section header table ..."). Its
dynamic tables are still read to label an observed overflow.

Why ordinary images are unaffected: the gABI gives a section outside the
memory image the address 0. A GOT input is writable, and GNU ld keeps
`SHF_WRITE` on an `INFO` output even at address 0; `(INFO READONLY)` is a
syntax error. These two GNU ld behaviours were observed during the
investigation and are not archived.
`harnesses/scan-non-allocated-sections-20260923.py` read the section
headers of 4,684 ELF64 executables and shared objects on the host
(`records/repair/scan/non-allocated-sections.txt`). The roots were
`/usr/bin`, `/usr/sbin`, `/usr/lib/aarch64-linux-gnu`, `/usr/libexec`, the
Cargo and local binaries, and the workspace's test binaries. All of them
have section headers, and none has a non-allocated section at a nonzero
address or with `SHF_WRITE`.

The run used clean `06a52ef2c`; `git status` was empty before, after and
after every mutant. `records/repair/results.json` holds the provenance
(trust-cg binary SHA-256 `b227f656…3e6`).

### Gates (records/repair/logs)

| gate | result |
| --- | --- |
| `cargo test -p trust-cg-codegen --lib` | `test result: ok. 4109 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` |
| same, filtered to `link_driver` | `test result: ok. 32 passed; 0 failed; 0 ignored; 0 measured; 4078 filtered out` |
| `--test e2e_aarch64_link_runtime` (`--nocapture`) | `test result: ok. 32 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `--test e2e_aarch64_elf_tlsie` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `--test e2e_aarch64_elf_relocation_model` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `--test e2e_aarch64_globals_linux` | `test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `--test aarch64_elf_symbol_binding` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo test -p trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo test -p trust-cg-cli --test link_options` | `test result: ok. 16 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo test -p trust-cg-cli --test output_paths` | `test result: ok. 8 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo check -p trust-cg-codegen --features verify`, `cargo build -p trust-cg-cli`, `scripts/check_fmt.sh`, the three gate script tests, `check_documentation.py --write` then `--check`, `generate_diagnostics_inventory.py --check`, `check_evidence_archive.py --plan` and on the three L02-P10 archives, `native_test_host_matrix.py --check` | exit 0 |

The new row `a_got_in_a_non_allocated_section_is_found` prints `the linker
accepted it; the link driver refused the image` for:

- `INFO`, `COPY`, `DSECT` and `OVERLAY` at 8 GiB, with three `UNPROVEN`
  lines each (`tcg_weak_missing`, `tcg_desc_tls`, `tcg_desc_word`);
- `INFO-far-nosh` and `INFO-near-nosh`.

GNU ld's images without the driver exit 139 for the four 8 GiB placements
and `INFO-far-nosh-raw`, and 0 for `INFO-near-nosh-raw`. The four 1 GiB
twins link through the driver and exit 0. The first repair's rows are
unchanged.

### Direct probes (records/repair/direct)

- `cli-info-far`: the verifier's command, `trust-cg --static --nostdlib
  --relocation-model pic -Wl,-T,<dir>/info-0x200000000.ld,<dir>/weakst.o
  -o cli-weakst-0x200000000 got_page.tmbc`, exits 1. It prints two
  `error[link:unclassified]` `[TCG-LINK-GOT-PAGE-UNPROVEN]` lines, for the
  positional probe's `tcg_desc_tls` and `tcg_desc_word`. `weakst.o` is
  passed inside `-Wl` and is not scanned. The output still reads `precious`
  (`cat-cli-weakst-after-refusal`). `cli-copy-far` does the same with
  `COPY`.
- `raw-gnu-ld-info-far`: GNU ld links it without the driver.
  `readelf-SW` shows `.slots PROGBITS 0x200000000 ... W` over
  `.farbss NOBITS 0x200000000 ... WA`, and `readelf-rW` shows no
  relocations. `objdump-d` shows `adrp x0, 0` then `ldr x0, [x0, #8]` in
  `probe`. `run-raw-info-far` is killed by SIGSEGV (-11), and so is
  `run-raw-copy-far`.
- `cli-info-near` and `cli-copy-near`: the 1 GiB twins are installed and
  exit 0.
- `cli-info-far-nosh` and `cli-info-near-nosh`: with `-z nosectionheader`
  both exit 1, with the reason starting "it has no section header table".
  `readelf-lW-raw-info-far-nosh` shows no section headers, and the only
  8 GiB program header is a zero-fill `PT_LOAD`. GNU ld's stripped images
  die at 8 GiB (`run-raw-info-far-nosh`, -11) and run at 1 GiB
  (`run-raw-info-near-nosh`, 0). The 1 GiB refusal is therefore
  conservative.
- `cli-insert-rename`: the first repair's `INSERT` rename is still refused,
  and `libslots.so` still reads `precious`.

### Mutation leg (records/repair/mutation)

`harnesses/mutation-got-page-region-repair-20260923.py` ran on clean
`06a52ef2c`. All nine mutants were killed, each expected test named
`FAILED`, and `status_after` is empty:

- R1 drops the non-allocated sections again. The unit row
  `a_placed_non_allocated_section_is_a_possible_slot_region` fails
  (`0x200000000: None`), and the e2e row panics `INFO-far: must not link
  silently: Ok(LinkSuccess { .. })`.
- R2 lets a stripped image be shown in reach by its segments. Both
  stripped unit tests fail, and the e2e row panics `INFO-far-nosh: must
  not link silently`.
- R3 ignores a writable non-allocated section at address 0. The unit row's
  address-0 case fails.
- S1 to S6 are the first repair's mutants, re-run on this head, and all are
  killed.

R1 and R3 were first written as `if flags & SHF_ALLOC == 0 {` and `... &&
address == 0 {`. Those did not compile, because the crate denies the
now-unused `SHF_WRITE`, so the harness reported them as surviving. They
were rewritten to keep the constant referenced (`true || ...`) and re-run.
The logs of the non-compiling attempt were overwritten.

### Boundaries of the second repair

The check still cannot see:

- a slot the linker fills but places in allocated zero fill (`SHT_NOBITS`)
  that no relocation or tag names. It reads zero, which is right only for
  an undefined weak symbol. GNU ld refuses that for `NOLOAD`, and LLD
  checks the window itself.
- a non-allocated section at address 0 that is not writable. GNU ld does
  not make one from GOT input.
- a zero-fill slot filled through Android's packed relocations.
- code that is not executable where it is loaded.

Every `-z nosectionheader` link with a GOT-page input is now refused, even
when it is in reach. This is unit, linker and execution evidence on one
host with GNU ld 2.42, not proof.

```sh
python3 -B harnesses/qualify-got-page-region-repair-20260923.py <worktree> <run-dir>
python3 -B harnesses/mutation-got-page-region-repair-20260923.py <worktree> <run-dir> [MUTANT ...]
python3 -B harnesses/scan-non-allocated-sections-20260923.py <root> [<root> ...]
python3 -B harnesses/archive-got-page-region-repair-20260923.py <run-dir> <this directory>
```
