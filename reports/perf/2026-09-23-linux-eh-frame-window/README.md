# `.eh_frame` pointers outside the `PREL32` window (L02-P10 closure audit) on Linux AArch64, 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the change that answers the 2026-09-23 closure audit of
ledger gap L02-P10 at `5ddb13664`. The change is `9ca3a684b`. The run used
clean source `9ca3a684bbd6b3fedea74dcd88e29d34f4196550` (tree
`0f48990ee0a1e8dc6b1e0677c5bf2b269d8142ef`) on the Linux AArch64 host
(`aarch64-unknown-linux-gnu`, Ubuntu 24.04, gcc 13.3, GNU ld, gold,
readelf and nm 2.42, LLD 22.1.6, stock Rust 1.97.1). `git status
--porcelain --untracked-files=all` was empty before and after every phase;
the phases that edit the source (the prior-driver build, the survey test and
the mutants) restore it byte for byte. `records/results.json` holds the
run's full record: provenance, tool versions and SHA-256s, every gate's
`test result:` lines, every probe's command, exit code, stderr, directory
listing and program output, the survey's verdict counts and readelf
comparison, each mutant's failing tests with each panic's location and
message, and the timing samples.

L02-P10 stays **PARTIAL**. A separate adversarial audit decides closure.
This is execution, object and decoder evidence on one host, not a proof.

## What the audit found

The audit kept L02-P10 PARTIAL on one residual; everything else it checked
was met. trust-cg writes each FDE's `pc_begin`, and a module's personality
and LSDA pointers, as `DW_EH_PE_pcrel|sdata4` fields through
`R_AARCH64_PREL32` (aaelf64 2026Q2: `-2^31 <= X < 2^31`) and left the window
to the linker (`WindowDischarge::Linker` in `elf/reloc.rs`). GNU ld 2.42
refuses a value outside it, but LLD 22.1.6 and gold 2.42 apply the earlier
bound `X < 2^32` and write `[2^31, 2^32)`, which unwinders read as negative.
The auditor's probe, `trust-cg -o btfar b1_scalars.tmbc -Wl,bt.o
-Wl,--section-start=.eh_frame=0x10000000,--section-start=.eh_frame_hdr=0x0fff0000,--section-start=.text=0xd0000000`
with an LLD `cc` wrapper first on `PATH`, exited 0 and installed a program
whose FDEs readelf decodes as `pc=ffffffffd0000118..` although
`isize_add_one` is at `0xd0000118`; its `backtrace()` found one frame
against six in the near twin, and gold gave the same.

## The change

`run_link` stages every Linux link (a plain `-nostdlib` executable link too,
without the input trace), and every staged Linux image's `.eh_frame` is
decoded as an unwinder reads it (`link_driver::eh_frame_check`): every
allocated `.eh_frame` and the section the `.eh_frame_hdr` `eh_frame_ptr`
names (without section headers, the FDEs `PT_GNU_EH_FRAME`'s table names,
or every record to the terminator), CIE by CIE and FDE by FDE. Each
`pc_begin` is decoded with its CIE's `R` encoding and `pc_begin..pc_begin +
pc_range` must lie in executable memory; the personality and LSDA pointers
must resolve into allocated memory; the `.eh_frame_hdr` binary search table
must agree with the FDEs. A failure is `relocation-out-of-range`
(`[TCG-LINK-EH-FRAME-WINDOW]`); a check that cannot complete is
`unclassified` (`[TCG-LINK-EH-FRAME-UNPROVEN]`). The image never reaches
the requested output. `R_AARCH64_PREL32`'s disposition is now
`WindowDischarge::LinkerThenEhFrameImage`. The plan section "L02-P10
`.eh_frame` pointers" of `docs/linux-aarch64-completion.md` and
`LIMITATIONS.md` describe the check and its boundaries.

## Gates (records/logs)

Run by `harnesses/qualify-eh-frame-window-20260923.py ... gates` on the
clean checkout. The CLI tests ran with `TCG_REQUIRE_LLD=1` and
`TCG_REQUIRE_GOLD=1`, so no linker leg could skip; the library and `e2e`
targets ran without them (trust-cg-codegen's admission refuses any ambient
`TCG_*` control, so a first gates attempt that exported them to every
target failed 51 unrelated library tests and was discarded).

| log | result |
| --- | --- |
| `test-cli` (`cargo test -p trust-cg-cli --test link_options --test output_paths --bin trust-cg`) | CLI bin 30 passed; `link_options` 28 passed (27 plus the new native control); `output_paths` 8 passed |
| `test-native-eh-frame` (the new `link_options` control alone, `--nocapture`) | 1 passed, no `SKIP:` line |
| `test-eh-catch-eh-frame` (the new `e2e_aarch64_eh_catch` control alone, `--nocapture`) | 1 passed, no `SKIP:` line |
| `test-codegen-lib` (`cargo test -p trust-cg-codegen --lib`) | 4140 passed, 1 ignored (4135 at `5ddb13664`'s source, plus the five new unit tests) |
| `test-codegen-e2e` | `aarch64_elf_cfi_differential` 3, `e2e_aarch64_eh_catch` 8 (7 plus the new control), `e2e_aarch64_eh_linux` 10, `e2e_aarch64_elf_link` 11, `e2e_aarch64_elf_tlsie` 13, `e2e_aarch64_link_runtime` 32; all passed |
| `check-codegen-verify`, `check-codegen` (`cargo check -p trust-cg-codegen` with and without `--features verify`) | exit 0 |
| `check-fmt` (`scripts/check_fmt.sh`) | exit 0 |
| `check-documentation-write`, `check-documentation` (`--write`, then `--check`) | exit 0; the write changed nothing |
| `diagnostics-inventory` (`--check`) | exit 0 (`link_driver.rs` is not a scanned file) |
| `script-gate-tests` (the three Linux/Darwin/bridge gate test files) | Ran 94 tests, OK (skipped=1) |

The CLI the gates built (`target/debug/trust-cg`, SHA-256
`3a1fba0af1b92ac62f84b93a0c676c89d5e72112521cc90c642d8e571fc2227a`) is the
one the direct probes used, and the CLI rebuilt after the mutants has the
same hash.

## Direct probes (records/direct, records/inputs)

The probes ran in a scratch directory (`$WORK`) with two CLIs: PRIOR, this
source with `5ddb13664`'s `link_driver.rs` and `elf/reloc.rs` (SHA-256
`3af4386b1776ff5d3452425041e047efafac701aed1aa9d28857cacff97322ff`), and
CURRENT, this source. `lld-cc.sh` runs the host `cc` with `-fuse-ld=lld
-B<dir>` (the directory holds only `ld.lld`), `gold-cc.sh` with
`-fuse-ld=gold`; each is put first on `PATH` for its rows. `bt.c` is the
auditor's `bt.o` reconstructed: `main` calls `isize_add_one(41)` and
`mid()`, which calls `depth()`, which returns `backtrace()`'s count. FAR is
the audit's placement (`.eh_frame` at `0x10000000`, `.eh_frame_hdr` at
`0x0fff0000`, `.text` at `0xd0000000`); EDGE moves `.text` to `0x8ffe0000`,
so every FDE's `PREL32` value is about 128 KiB below `2^31`.

| row | LLD 22.1.6 | gold 2.42 | GNU ld 2.42 |
| --- | --- | --- | --- |
| PRIOR, FAR (`trust-cg -o btfar b1_scalars.tmbc -Wl,bt.o <FAR>`) | exit 0, installed; readelf: all 11 FDEs at `pc=ffffffffd00000..` (`isize_add_one`'s at `ffffffffd0000118`); runs `frames=1 v=42` | exit 0, installed; FDEs at `ffffffffd00000..`; runs `frames=1 v=42` | exit 1: GNU ld's own `relocation truncated to fit: R_AARCH64_PREL32` (classified `relocation-out-of-range`), nothing written |
| CURRENT, FAR | exit 1, exactly one `error[link:` line, `relocation-out-of-range` naming `_start` and `R_AARCH64_PREL32`: `[TCG-LINK-EH-FRAME-WINDOW] ... 11 of its 11 FDEs describe code outside executable memory ...; the same 32 bits read as unsigned would give 0xd0000000, the function _start ...`; directory listing unchanged | the same (11 of 11 FDEs), listing unchanged | as PRIOR (the linker refuses first) |
| CURRENT, FAR with `precious\n` already at the output | refused, the file keeps its bytes | the same | the same |
| the same objects linked by the linker outside the driver (`btraw_*`) | links; `frames=1 v=42` | links; `frames=1 v=42` | (refuses) |
| CURRENT, EDGE | links, `frames=6 v=42`, FDEs at `pc=000000008ffe0000..` | the same | the same |
| PRIOR and CURRENT, near (default placement) | links, `frames=6 v=42` | the same | the same |
| trust-cg's own `zPLR` object (`tc_try_elf.o` from `e2e_aarch64_elf_eh_catch_object_emit`, with the C++ `driver.o`, `-Wl,tc_try_elf.o,driver.o,-lstdc++`), `.gcc_except_table` at `0xd0000000` (and `.eh_frame`, `.text` near `0x10000000`), PRIOR | exit 0, installed; the program dies with SIGSEGV at the throw | the same | exit 1: GNU ld refuses both `PREL32` fields (`DW.ref.__gxx_personality_v0` and `.gcc_except_table`), two classified lines |
| the same, CURRENT | exit 1, one line: `[TCG-LINK-EH-FRAME-WINDOW] ... 2 personality or LSDA pointers in its .eh_frame resolve outside allocated memory; the first, the personality pointer of the CIE at 0x10000140, is the DW_EH_PE_indirect\|pcrel\|sdata4 field at 0x10000153, which holds 0xc003075d and so gives 0xffffffffd00308b0 (the address of the 8-byte slot ...)`; listing unchanged | the same (2 pointers) | as PRIOR |
| the same object, default placement, PRIOR and CURRENT | `tc_try returned 42` | the same | the same |
| `--shared --nostdlib --relocation-model pic -Wl,-z,nosectionheader,<FAR>` (the section-header-less path through `PT_GNU_EH_FRAME`) | PRIOR installs the library; CURRENT refuses it: `3 of its 3 FDEs describe code outside executable memory ... would give 0xd0000000, in executable memory` (no symbol table to name it) | not run | not run |

The linker matrix before and after, for the audit's placement:

| linker | before (`5ddb13664`) | after (`9ca3a684b`) |
| --- | --- | --- |
| GNU ld 2.42 | refused by the linker, classified | unchanged |
| LLD 22.1.6 | installed, `backtrace()` 1 frame | refused, `[TCG-LINK-EH-FRAME-WINDOW]`, nothing written |
| gold 2.42 | installed, `backtrace()` 1 frame | refused, `[TCG-LINK-EH-FRAME-WINDOW]`, nothing written |
| any, near or window edge | links, 6 frames | links, 6 frames |

## Host survey (records/survey)

`harnesses/survey_test.rs` is a temporary, ignored unit test the harness
appends to `link_driver.rs` for one run and then removes (the file is
restored byte for byte). It runs `eh_frame_check` and
`eh_frame_diagnostics` over every ELF64 little-endian `ET_EXEC` or `ET_DYN`
regular file under `/usr/bin`, `/usr/sbin`, `/usr/lib`, `/usr/libexec` and
`/usr/local/bin` (6,043 files, symlinks and duplicates skipped), and lists
every FDE its own walk of each `.eh_frame` section decodes.
`survey/verdicts.txt` keeps each image's verdict and diagnostics; the full
FDE listing (3,486,499 FDEs) stays in `$WORK`.

- All 5,770 images that are not separate debug files pass: no FDE outside
  executable memory, no stray personality or LSDA pointer, and every
  `.eh_frame_hdr` table (5,287 images have one) agrees with the FDEs. None
  is unproven.
- The 273 separate debug files under `/usr/lib/debug/.build-id/` are
  unproven (`the .eh_frame_hdr at ... ends before its header`): their
  sections have no file contents, so `PT_GNU_EH_FRAME` points at nothing
  loaded. The driver never links such a file.
- `survey/readelf-comparison.json`: for 410 images (a seeded sample of 400
  of the 5,332 non-debug images with FDEs, plus the 10 with the most FDEs),
  the decoded FDEs (section offset, `pc_begin` and `pc_begin + pc_range`, in
  order) equal GNU readelf 2.42's `--debug-dump=frames` `.eh_frame` lines
  exactly: 1,279,346 FDEs, 0 mismatches.

The survey shows that the check refuses none of the host's linked images
and that its decoder agrees with an independent one on real `.eh_frame`
contents. It does not exercise the refusal paths (the probes, the native
controls and the unit tests do).

## Mutation legs (records/mutation)

Each mutant edits `link_driver.rs` once (`mutant.diff`), runs three legs
(the `link_driver` unit tests, the native `link_options` control with
`TCG_REQUIRE_LLD`/`TCG_REQUIRE_GOLD`, and the native `e2e_aarch64_eh_catch`
control) and restores the file. A mutant counts as killed only when a test
failed, not when a build failed; every leg of every mutant built.

| mutant | killed by |
| --- | --- |
| `skip-eh-frame-check` (`staged_image_refusals` never runs the `.eh_frame` check) | `every_linux_link_is_staged_for_the_eh_frame_check`, `a_traced_got_page_input_refuses_an_image_not_shown_in_reach` (its non-ELF image loses the unproven line), the native LLD/gold control and the native EH control |
| `plain-link-unstaged` (a plain `-nostdlib` Linux link is linked directly again) | `every_linux_link_is_staged_for_the_eh_frame_check`, `traced_links_pass_the_trace_before_every_passthrough`; no native control makes a plain link |
| `sdata4-unsigned` (`DW_EH_PE_sdata4` zero-extended, the reading gold and LLD assume) | all five new unit tests, the native LLD/gold control and the native EH control |
| `begin-only` (only `pc_begin`, not `pc_begin + pc_range`, must be executable) | `eh_frame_decoder_reads_each_pc_begin_encoding` (the one-byte-past rows) only |
| `pointers-always-allocated` (personality and LSDA pointers never checked) | `eh_frame_decoder_reads_zr_and_zplr_cies` and the native EH control |
| `unknown-augmentation-ignored` (the letter `X` skipped) | `eh_frame_decoder_reads_zr_and_zplr_cies` only |
| `no-table-check` (the `.eh_frame_hdr` table never compared) | `eh_frame_hdr_table_must_agree_with_the_fdes` only; every native table agrees with its FDEs |
| `no-table-coverage` (a live FDE may be missing from the table) | `eh_frame_hdr_table_must_agree_with_the_fdes` only |
| `table-sort-ignored` | `eh_frame_hdr_table_must_agree_with_the_fdes` only |
| `no-dynamic-relocation-check` | `eh_frame_decoder_refuses_a_truncated_record` only |

All 10 mutants are killed. The skipped check is killed by the native LLD
row, as required. A first mutation attempt stopped at `sdata4-unsigned`,
whose anchor text rustfmt had wrapped (the harness requires exactly one
match); after the anchor was corrected all ten mutants were run afresh in
two batches, and only those runs are archived.

## Timing (records/timing)

Each case ran 21 rounds, interleaved, with the order of three debug CLIs
rotated each round: PRIOR, this source's CLI and an identical copy of it
(the scatter control). Times in ms:

| case | PRIOR median (IQR, min) | current median (IQR, min) | current copy median (IQR, min) |
| --- | --- | --- | --- |
| plain `--nostdlib` executable of `b1_scalars.tmbc` (newly staged and checked) | 14.67 (13.93-18.91, 12.86) | 15.76 (14.75-19.09, 14.43) | 16.06 (14.65-19.10, 13.67) |
| default executable of `b1_scalars.tmbc` with `-Wl,bt.o` (already staged) | 25.24 (24.91-26.89, 21.22) | 24.84 (22.49-29.88, 20.65) | 25.42 (24.71-26.43, 21.09) |

The plain link's medians are about 1 ms higher with this source, which the
added staging directory, rename and read-back plausibly explain; the
identical copy differs from the current binary by 0.3 ms. The default link,
which was staged before, shows no difference above the copy's scatter.
With 21 samples on one host, this bounds the cost roughly; it is not a
precise measurement.

## Boundaries

- One host, three linker versions; not a proof. The decoder's agreement
  with readelf is on a sample of well-formed host images.
- Not seen: an `.eh_frame` that neither a section header nor
  `PT_GNU_EH_FRAME` locates (a runtime that registers frames itself with
  `__register_frame`). Not refused: an image whose FDEs no program header
  makes reachable (`-Wl,--no-eh-frame-hdr`): its pointers are checked, but
  glibc's unwinder does not find the FDEs, and `backtrace()` stopped at the
  first frame through all three linkers when this was tried during
  development (not part of this archive).
- Not read: LSDA call-site tables, the slot an indirect personality pointer
  names, `.debug_frame`; Darwin's `__eh_frame` and links for other operating
  systems are not checked.
- Every Linux link is now staged: a plain `-nostdlib` link refuses `-o
  /dev/null` and needs a writable output directory, and its image is read
  back into memory after the link (the far LLD images here are 268 MB
  sparse files).
- Conservative refusals: `DW_EH_PE_datarel`, `textrel`, `funcrel` and
  `aligned` pointers, augmentation letters other than `R`, `P`, `L`, `S`,
  `B`, `G`, an absolute pointer in a position-independent image and any
  dynamic relocation into `.eh_frame` refuse an image that an unwinder
  might read correctly. None of the host's 5,770 images needs one of them.

## Reproduce

From a clean checkout of `9ca3a684b` on an AArch64 Linux host with GNU
binutils 2.42 (`ld.bfd`, `ld.gold`, `readelf`, `nm`), gcc/g++ and an
`ld.lld`, with `$RUN` a new directory outside the tree:

```sh
for phase in gates direct survey mutation timing finish; do
  python3 -B reports/perf/2026-09-23-linux-eh-frame-window/harnesses/qualify-eh-frame-window-20260923.py "$PWD" "$RUN" "$phase"
done
python3 -B reports/perf/2026-09-23-linux-eh-frame-window/harnesses/archive-eh-frame-window-20260923.py "$RUN" <archive> <harnesses...>
```

The harness expects `survey_test.rs` next to itself and LLD at
`$HOME/.local/bin/ld.lld`. This run ran `mutation` in two batches of five
(the mutant names as extra arguments), each phase under 20 minutes.
`python3 scripts/check_evidence_archive.py
reports/perf/2026-09-23-linux-eh-frame-window` checks this archive.
