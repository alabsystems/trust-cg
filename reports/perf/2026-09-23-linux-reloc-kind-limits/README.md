# Per-kind AArch64 relocation limits (L02-P10) on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the relocation-limit model and controls for ledger gap
L02-P10. It runs on clean source `76ead5025f292892b81756faf33de8c615c192f6`
(tree `00a5acd7311385a5246add64ac19d6b28c2d315d`) on the Linux AArch64 host
(NVIDIA Grace, `CPU part 0xd87`, Ubuntu 24.04, glibc 2.39). `git status
--porcelain --untracked-files=all` was empty before and after the qualifying
run and after the mutation leg. `records/results.json` holds the provenance,
tool identities and every gate and probe exit.

L02-P10 stays **PARTIAL**. A separate adversarial audit decides closure.

## What the change does

- `AArch64RelocType::relocation_limit`
  ([`elf/reloc.rs`](../../../crates/trust-cg-codegen/src/elf/reloc.rs)) is an
  exhaustive disposition for every kind the checked ELF writer decodes: a
  psABI window and who refuses an out-of-window value, the checked page
  relocation that an unchecked low-12 form pairs with, full width, or no
  value. `displacement_window` now also returns the windows of
  `TLSDESC_ADR_PAGE21`, `ABS32`, `TLSLE_ADD_TPREL_HI12` and the never-emitted
  `TLSLE_ADD_TPREL_LO12`. Existing windows are unchanged.
- trust-cg refuses by name when its own object fixes a bound:
  `[TCG-RELOC-WINDOW-TLSLE]` for a local-exec `TPREL` of at least `2^24`
  (16-byte TCB + the thread-local's offset in its TLS section + addend), and
  `[TCG-RELOC-WINDOW-ABS32]` for a DWARF32 addend above `2^32 - 1`.
- `link_driver::run_link` reads back the output of a link whose AArch64 ELF
  inputs carry a GOT-page `ADRP` (`ADR_GOT_PAGE`,
  `TLSIE_ADR_GOTTPREL_PAGE21`, `TLSDESC_ADR_PAGE21`). It removes and refuses
  an image whose GOT lies outside the page window of its code, as
  `relocation-out-of-range` with `[TCG-LINK-GOT-PAGE-WINDOW]`. (That is the
  behaviour on `76ead5025`. After the merge with the L02-P9 second repair,
  the check runs on the staged image and never touches the requested
  output; see
  [2026-09-23-linux-reloc-kind-limits-staged](../2026-09-23-linux-reloc-kind-limits-staged/README.md).)

## psABI premises (records/psabi-aaelf64-excerpt.txt)

The windows were re-read from the aaelf64 source on the Arm `abi-aa` main
branch, fetched on 2026-09-23 (SHA-256 `1bf9c709…2e9d`). Its `|release|`
macro still reads 2025Q4, but its change history runs to 2026Q3. The excerpt
keeps every row this change relies on:

- `TLSDESC_ADR_PAGE21` (562): `Page(G(GTLSDESC(S))) - Page(P)`, check
  `-2^32 <= X < 2^32`, the same as the other `ADRP` page kinds.
- `ABS32` (258): `S + A`, check `-2^31 <= X < 2^32`.
- `TLSLE_ADD_TPREL_HI12` (549): `TPREL(S+A)`, check `0 <= X < 2^24`;
  `TLSLE_ADD_TPREL_LO12` (550): `0 <= X < 2^12`.
- `PREL32` (261): `-2^31 <= X < 2^31` in this source. The 2026Q2
  change-history entry ("make pc-relative relocaions signed") narrowed it.
  trust-cg keeps the pre-2026Q2 upper bound `2^32` in its model, as the task
  required; nothing in trust-cg refuses from that window.

## Finding: GNU ld 2.42 does not check the GOT-page ADRP windows

`records/direct/cg/got_page.o` is the `pic` object for `got_page.tmbc`. Its
`tcg_desc_bump` reaches the thread-local `tcg_desc_tls` through a TLS
descriptor and the preemptible `tcg_desc_word` through the GOT
(`readelf-rW-got_page.o`). Linked `-shared -nostdlib` with `.got` at 8 GiB and
`.got.plt` at 8 GiB + 64 KiB:

- GNU ld 2.42 exits 0 with no diagnostic (`gnu-far-got-shared`). In the
  library (`gnu-far-got-objdump-d`, `gnu-far-got-readelf-SW`, `-rW`), the
  TLSDESC `ADRP` at `0x358` addresses page `0x10000`, but its slot is at
  `0x200010018`. The `ADR_GOT_PAGE` `ADRP` at `0x374` addresses page `0`,
  but its slot is at `0x200000008`. Both page deltas were truncated to 33
  bits: silent wrong code.
- LLD 22.1.6 refuses both relocations with `out of range`
  (`lld-far-got-shared`; it also refuses its own `.eh_frame` `PREL32`, which
  it lays out after the placed GOT).
- The assembler probe below shows the same GNU ld behaviour for
  `TLSIE_ADR_GOTTPREL_PAGE21`.

Through the CLI (`cli-far-got-shared`), `trust-cg -shared -nostdlib
--relocation-model pic` with the same placement prints one
``error[link:relocation-out-of-range] `tcg_desc_tls`
(R_AARCH64_TLSDESC_ADR_PAGE21): [TCG-LINK-GOT-PAGE-WINDOW] …`` line and one
for `tcg_desc_word` (`R_AARCH64_ADR_GOT_PAGE`). It then prints `the linked
output libfar.so was refused and removed` and exits 1. `libfar.so` is absent
(`cli-far-got-output-absent`). As the positive twin, the GOT at 2 GiB links
(`cli-near-got-shared`), and an executable linked against that library runs
and checks `42` then `44` (`run-desc`, exit 0).

## Native probes through the CLI (records/direct)

- `TLSLE_ADD_TPREL_HI12`: `cli-compile-le_over` refuses `le_over.tmbc`, whose
  `tcg_le_edge` sits at offset `0xfffff0` of `.tbss`, with
  `[TCG-RELOC-WINDOW-TLSLE] … TPREL(S + A) is at least 16777216 …`.
  `le_edge.tmbc` (offset `0xffffe0`) compiles. Its object keeps the 16 MiB
  pad as `.tbss` zero-fill (`readelf-sSW-le_edge.o`). The linked program adds
  `0xfff000` and `0xff0` to the thread pointer, a TPREL of `2^24 - 16`
  (`objdump-d-edge`), and exits 0 (`run-edge`). A small trust-cg thread-local
  linked behind a 16 MiB thread-local from an assembler object is refused by
  GNU ld (`relocation truncated to fit: R_AARCH64_TLSLE_ADD_TPREL_HI12 against
  symbol `tcg_le_edge'`, `gnu-le-behind-pad`) and by LLD
  (`lld-le-behind-pad`: `16777232 is not in [0, 16777215]`). The same objects
  in the other order run (`run-ahead`).
- `ABS32`: the `-g` object has 17 `R_AARCH64_ABS32` records
  (`readelf-rW-debug_probe.o`). With `.debug_str` placed at 4 GiB, GNU ld
  refuses them (`relocation truncated to fit: R_AARCH64_ABS32 against
  `.debug_str'`, `gnu-debug-str-far`). Placed at `0x7fff0000` the program
  links and runs (`run-debug_near`). LLD ignores `--section-start` for the
  non-allocated `.debug_str` (address 0, `lld-debug-str-far-readelf-SW`), so
  its link is an in-window image, not a missed overflow.
- `LDST128`: `lo12_q.o` at `-O2` reads and writes its 16-byte-aligned `v4i32`
  globals with `ldr q0` / `str q1` carrying
  `R_AARCH64_LDST128_ABS_LO12_NC` (`objdump-dr-lo12_q.o`). The linked
  program checks all four lanes twice and exits 0 (`run-lo12_q`).

## Linker window probe (records/linker-windows)

`harnesses/probe-linker-windows-20260923.py` links small assembler inputs
with GNU ld 2.42, gold 2.42 and LLD 22.1.6 (`results.json` lists every
command and exit). For `ABS32`, `PREL32` and `ADR_PREL_PG_HI21` it probes
both edges of the window, and for `TLSLE_ADD_TPREL_HI12` the upper edge
(`2^24 - 1` / `2^24`); there it fixes `X` exactly with `--defsym`,
`--section-start` or a `.tbss` pad. The GOT-page kinds are not probed at a
window edge: the probe places the GOT at 2 GiB and at 8 GiB (the `x` values
`2147483648` and `8589934592` in `results.json` are those GOT addresses,
not page deltas), which is inside and far outside the `+-4 GiB` window, and
gold gives no evidence for them (internal error on both placements):

| relocation | GNU ld 2.42 | gold 2.42 | LLD 22.1.6 |
| --- | --- | --- | --- |
| `ABS32` at `2^32 - 1` / `2^32` | links / refuses | links / refuses | links / refuses |
| `ABS32` at `-2^31` / `-2^31 - 1` | refuses / refuses | links / refuses | links / refuses |
| `PREL32` at `2^31 - 1` / `2^31` / `2^32 - 1` | links / refuses / refuses | links / links / links | links / links / links |
| `PREL32` at `-2^31` / `-2^31 - 1` | links / refuses | links / refuses | links / refuses |
| `ADR_PREL_PG_HI21` at `2^32 - 4096` / `2^32` and `-2^32` / `-2^32 - 4096` | links / refuses, links / refuses | same | same |
| `TLSLE_ADD_TPREL_HI12` at `2^24 - 1` / `2^24` | links / refuses | links / refuses | links / refuses |
| `ADR_GOT_PAGE`, `TLSIE_ADR_GOTTPREL_PAGE21`, `TLSDESC_ADR_PAGE21` with the GOT at 2 GiB / 8 GiB | links / **links (truncated)** | internal error / internal error | links / refuses |

gold 2.42 aborts (`internal error in set_offset`) on every `-shared` link
with a placed `.got`, in or out of the window. `.text` is pinned in the
placed cases, because otherwise gold aborts in `set_segment_offsets` and LLD
lays `.text` out after a placed `.got`.

## Test targets and gates (records/logs)

| target / gate | result |
| --- | --- |
| `trust-cg-codegen --lib` (whole library suite) | `test result: ok. 4095 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --lib -- elf::reloc elf::dwarf link_driver pipeline::tests::local_exec pipeline::tests::intra_object` | `test result: ok. 50 passed; 0 failed; 0 ignored; 0 measured; 4046 filtered out` |
| `e2e_aarch64_link_runtime` (`--nocapture`) | `test result: ok. 28 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `aarch64_elf_dwarf` | `test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `e2e_aarch64_elf_tlsie` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `e2e_aarch64_elf_relocation_model` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-cli --test link_options` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-verify --lib -- aarch64_elf_reloc_proofs aarch64_elf_tls_reloc_proofs object_inventory` | `test result: ok. 40 passed; 0 failed; 0 ignored; 0 measured; 4139 filtered out` |
| `cargo check -p trust-cg-codegen` and `--features verify` | exit 0 |
| `bash scripts/check_fmt.sh` | exit 0 |
| `python3 -B -m unittest` of the three gate script tests | exit 0 |
| `python3 scripts/native_test_host_matrix.py --check` | exit 0 |
| `python3 scripts/check_documentation.py --check` | exit 0 |
| `python3 scripts/generate_diagnostics_inventory.py --check` | exit 0 |
| `python3 scripts/check_evidence_archive.py --plan` | exit 0 |

In `logs/e2e_aarch64_link_runtime.log`, the GOT-page control reports
`far GOT: the linker accepted it; the link driver refused the image`, with
both `[TCG-LINK-GOT-PAGE-WINDOW]` lines.

## Mutation leg (records/mutation)

`harnesses/mutation-reloc-limits-20260923.py` applies seven one-line mutants
to 76ead5025, runs the tests that should catch each one, and restores the
file. Every mutant was killed, with each expected test reported `FAILED`:

| mutant | killed by |
| --- | --- |
| M1 image check disabled | `got_page_window_output_refusal_names_each_use`, e2e `got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver` |
| M2 image window one page wider | `got_page_reach_is_decided_from_the_linked_section_layout` |
| M3 TLSLE refusal disabled | `local_exec_tls_lower_bound_above_the_hi12_window_is_refused`, e2e `local_exec_tls_past_the_hi12_window_is_refused_by_name_at_the_edge` |
| M4 TLSLE bound without the 16-byte TCB | the same two tests |
| M5 ABS32 addend edge off by one | `abs32_section_offset_addend_is_refused_above_the_psabi_window` |
| M6 `TLSDESC_ADR_PAGE21` discharged by the linker only | `every_serializable_aarch64_relocation_kind_has_a_pinned_limit`, `got_page_relocations_are_the_linked_image_discharged_kinds` |
| M7 TLSLE window one wider | `every_serializable_aarch64_relocation_kind_has_a_pinned_limit` |

## Inputs

The `.tmbc` inputs in `records/inputs` were written by the committed test
builders (`got_page_module`, `local_exec_tls_module`, `debug_probe_module`,
`lo12_q_probe`) through a temporary test
(`records/inputs/dump-probe-modules.patch`). The patch was applied, run and
reverted before the qualifying run. Their SHA-256 values are in
`results.json` (`inputs`). `le_edge.tmbc` and `le_over.tmbc` carry their
16 MiB zero pads as byte constants.

Two earlier qualifying attempts ran on commits that were amended before this
one. The first failed only `check_documentation` (an `INVENTORY.md` line
count that was stale after two doc-comment edits). The second passed, but it
came before the psABI citation wording was corrected. Their records were
discarded. This archive holds only the run on 76ead5025.

## Evidence boundaries

- This is linker, execution and unit-test evidence on one host, not proof.
  The windows are psABI text, and the linker behaviour was observed with
  these three linker versions.
- The trust-cg refusals see only what one object fixes: a lower bound, or a
  target in its own text. The image check compares the farthest code byte
  with the farthest `.got`/`.got.*` byte, falling back to all allocated
  non-TLS sections, or to the writable `PT_LOAD` segments when there is no
  section header table. This README first called that conservative. It was
  not: a linker script could move the GOT's slots into a section of another
  name, 8 GiB away, while `.got.plt` stayed near. The check then admitted an
  image whose `ADR_GOT_PAGE` delta GNU ld had truncated. The 2026-09-23
  slot-region repair (plan,
  "GOT-page slot region repair") derives the region from the image instead.
  An image spanning more than 4 GiB can be refused even if every site is in
  reach. It runs only for
  links through `run_link` and reads only AArch64 ELF relocatable inputs,
  not archive members, shared libraries or links made outside the driver.
- `PREL32` values in `[2^31, 2^32)` are refused by GNU ld but not by gold or
  LLD, and nothing in trust-cg re-checks them.
- The native controls use `--section-start`, not images larger than 4 GiB.
  The Darwin floor has not run the added tests.

## Reproduce

On the Linux AArch64 host, with a clean checkout of 76ead5025 and `RUN`
outside the tree:

1. Apply `records/inputs/dump-probe-modules.patch`, run
   `TCG_DUMP_PROBE_MODULES=RUN/inputs cargo test -p trust-cg-codegen --test
   e2e_aarch64_link_runtime -- dump_reloc_limit_probe_modules`, and revert
   the patch.
2. Copy `harnesses/*.py` to `RUN/harnesses/`.
3. Run `python3 RUN/harnesses/qualify-reloc-limits-20260923.py WORKTREE RUN
   aaelf64.rst`, where `aaelf64.rst` is the fetched psABI source. Then run
   `mutation-reloc-limits-20260923.py WORKTREE RUN` and
   `archive-reloc-limits-20260923.py RUN DEST`.

Logs, probe records, objects and sources are stored as `*.gz`. Linked
binaries and shared objects are not stored; their `readelf` and `objdump`
records are.
