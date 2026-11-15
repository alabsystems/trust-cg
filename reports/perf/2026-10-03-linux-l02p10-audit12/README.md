# L02-P10: the twelfth closure audit's findings — 2026-10-03

This record qualifies the branch `fix/l02p10-audit12-tls-permissions-bitcode`
on `23ee1104a` (origin/main at the audit), built with the Trust package
`ae9c2c1d` (`targo --unverified`, debug) on the Linux AArch64 host: kernel
6.17, 4 KiB pages, glibc 2.39, GNU ld 2.42, gold 2.42, LLD 22.1.6, GCC 13.3.
It is execution and object evidence on one host, not a proof.

## What the audit found (at `23ee1104a`)

The auditor and two skeptics kept L02-P10 PARTIAL on five in-scope findings:

1. **High: the thread-local template was never checked.** No rule related
   `PT_TLS` to the thread-local sections. GNU ld given a `PHDRS` script whose
   `PT_TLS` held `.tbss` alone, LLD given an `INSERT` script with
   `-z norelro`, and LLD given `-Wl,--section-start=.tbss=0x700000` (no
   script) installed programs and a library whose trust-cg thread-locals read
   0 or other bytes, with exit status 1 and no crash.
2. **Low: only `PF_W` was checked** for trust-cg's sections: `.rodata` in a
   `FLAGS(0)` segment and `.text` in a `FLAGS(4)` one were installed and died
   with SIGSEGV.
3. **Medium, fail-open: LLVM bitcode inputs were not read.** A static LLD
   image whose bitcode archive member defined libgcc's outline-atomics
   helpers was installed and hung in `__register_frame_info`; its ELF twin
   was refused.
4. **Low, false refusal:** every static LLD link with a direct bitcode input
   was refused on the claim that the linker reads it as a linker script.
5. **Low, docs:** LIMITATIONS still said the page-granular rule was not
   implemented.

## The repair

`crates/trust-cg-codegen/src/link_driver.rs`; LIMITATIONS (the 2026-10-03
correction under `[TCG-LINK-WRITE-PROTECTED]`), CHANGELOG and decision
LD-07 state the rules and their bounds.

- `[TCG-LINK-TLS-TEMPLATE]`: `tls_template` and `tls_template_disagreement`
  (one `PT_TLS` with memory holding every allocated thread-local section,
  starting at the first; `p_align` a power of two dividing `p_vaddr`; its
  file part in one `PT_LOAD`'s, holding `.tdata` and no other section, zero
  bytes under a `.tbss` there; no overlapping thread-local sections), and
  `own_tls_disagreement` (trust-cg's own thread-local input sections, as the
  map places them, inside `PT_TLS`; each local-exec `ADD` and relaxed
  `MOVZ`/`MOVK` field of trust-cg's code in an executable holding
  `align_up(16, p_align) + (S + A - p_vaddr)`; each global thread-local's
  symbol value its offset from `p_vaddr`).
- `[TCG-LINK-SEGMENT-PERMISSIONS]`: `segment_permission_disagreement` over
  `own_section_lacking`, the predicate the `PF_W` rule now shares; gold's map
  prints trust-cg's `.text` at `0xffffffffffffffff` (the last code input of
  an output section), placed by the symbols listed under it
  (`own_sections_located`).
- LLVM bitcode: `is_llvm_bitcode_prefix` (raw and wrapped magic), never a
  script; `trace_names_bitcode`; the link runs again through LLD with
  `--lto-obj-path` after every argument and that link is checked and
  installed; `examine_lto_objects` reads the objects LLD kept as loaded
  inputs, and the C-runtime stand-in rule names bitcode whose objects are not
  shown.
- The Linux floor pins `link_options` at 68.

## Evidence

Logs are host-local, under the session's scratch directory
`.../scratchpad/l02p10-a/` (not committed); the reproducer and harness
sources are in `inputs/`, `harnesses/` and `sweep/`.

- **Reproducers** (`inputs/repro_all.sh`, with `TCG`, `LLVM` and `LLD`
  set): at `23ee1104a` every audit row is installed (and misbehaves); with
  the repair the GNU ld `PHDRS` rows (no-PIE, PIE), LLD's `INSERT` PIE and
  shared object and `--section-start` rows (no-PIE, PIE) are refused as
  `[TCG-LINK-TLS-TEMPLATE]`; `.rodata` without permissions (GNU ld, LLD,
  gold) and `.text` read-only (GNU ld, gold; LLD also by the `.eh_frame`
  check) as `[TCG-LINK-SEGMENT-PERMISSIONS]`; the bitcode outline-atomics
  member as `[TCG-LINK-IRELATIVE-UNAPPLIED]`, naming the object LLD
  compiled; each with the output's sentinel bytes kept. The raw links run
  outside the driver: wrong thread-local values (exit 1), SIGSEGV (139), a
  hang (124). Ordinary thread-local links (PIE, no-PIE, static,
  `-z relro -z now`, a shared object) through all three linkers, the
  linkers' own `PHDRS` layouts, `.rodata` in an `R` segment, and static,
  PIE and no-PIE LLD links with full, ThinLTO and archived bitcode are
  installed and run.
- **Native rows** (`link_options`, `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1`,
  no SKIP): 68/68, the three new ones
  `tls_templates_that_do_not_hold_trust_cgs_thread_locals_are_never_installed`,
  `segments_without_the_permissions_trust_cgs_sections_need_are_never_installed`
  and `llvm_bitcode_inputs_are_read_through_the_objects_lld_compiles`;
  `output_paths` 8/8.
- **Unit rows** (`link_driver::tests`): 129/129 (123 before), six new.
- **Mutants** (`harnesses/mutants.py`, `harnesses/run_mutants.sh`): one
  build with each new check behind a guard; all 24 mutants (each template
  rule, the own-placement, `TPREL` and symbol rules, the read and execute
  rules, the `.tbss` exemption, bitcode magic, LTO object reading, the
  re-link, the empty-object rule, the stand-in reason, gold's symbol
  placement and its unplaced-input record) are killed, and the unmutated
  build passes every row.
- **Host survey** (`harnesses/survey_test.rs`, a temporary ignored test):
  over the 6,494 ELF executables and shared objects under `/usr/lib`,
  `/usr/bin`, `/usr/sbin`, `/usr/libexec`, `/usr/local`, `/opt` and the Trust
  package (465 with `PT_TLS`), the template rule refuses none; the read and
  execute rule, with each image's allocated sections taken as trust-cg's,
  flags none.
- **Ordinary-link sweep** (`sweep/`: the second skeptic's matrix of
  `gen.sh` plus `extra_rows.sh`, 4,959 links through GNU ld, gold and LLD,
  each paired with the same link outside the driver and every program
  run): see the summary below.
- **Floor targets** of the link driver re-run green with the linkers
  required: `e2e_aarch64_link_runtime`, `e2e_aarch64_elf_tlsie`,
  `e2e_aarch64_eh_catch`, `aarch64_elf_symbol_binding`,
  `e2e_aarch64_globals_linux`, `e2e_aarch64_elf_link`,
  `e2e_aarch64_eh_linux`, `aarch64_elf_cfi_differential`,
  `e2e_aarch64_elf_relocation_model`, `aarch64_elf_eh_relocation_inventory`,
  `e2e_aarch64_elf_sections`.

### Sweep summary

Of 4,959 links: 4,816 installed and ran (`v=OK`), and no installed program
failed to run. 112 failed in the linker itself, the same link failing
outside the driver (an option a linker does not accept, the `evil` inputs'
duplicate definitions). 21 refusals are true: LLD's `--pack-dyn-relocs=relr`
(seven; the raw program fails with `DT_RELR without GLIBC_ABI_DT_RELR`) and
the outline-atomics replacements through bitcode (eight, LLD), ELF (four)
and GCC LTO (two), whose raw programs hang. 10 are refused although the raw
link runs: LLD's `--print-gc-sections` in static and shared links (six,
`[TCG-LINK-INPUT-TRACE]`, the documented class) and gold's static links
with the `evil2` ELF archive or GCC LTO object (four, the documented
conservative refusal of a libgcc support routine defined outside libgcc;
the base CLI at `23ee1104a` refuses the same four the same way).

Against the second skeptic's run of the same matrix at `23ee1104a`, no link
that passed there is refused or fails here, and 85 of its false refusals
(every LLD static link with a direct bitcode input) now install and run;
the intermediate build's run of the whole matrix gave the same verdict for
every link.

## Residuals

Stated in LIMITATIONS: accesses left in GOT or descriptor form and a
shared object's code are not decoded (the template rules carry them); the
rules model glibc 2.39 and the three linkers measured; an execute-only
segment is refused although such hardware could run trust-cg's code
(trust-cg reads its jump tables from `.text`); a static LLD link with a
ThinLTO cache, with its own `obj-path`, or with bitcode through another
linker is refused conservatively; an LLD bitcode link is linked twice; and
the LLD `--print-gc-sections` refusal of earlier rounds is unchanged.

## First verifier round (on `be368f243`)

The verifier refuted the repair on two holes and a test gap, with one
informational item; the repair of those found a third class.

1. **Medium: images without a section header table skipped the thread-local
   section rules.** GNU ld 2.42 given `-z nosectionheader` and a `PHDRS`
   script that put `.tbss` before `.tdata` wrote a `--nostdlib` PIE whose two
   sections shared their bytes (trust-cg's zero-fill `tcg_tz` read 42, exit
   42); a twin whose `PT_TLS` began at `.data` had a C reader of trust-cg's
   `tcg_t` read `.data`'s bytes (exit 4). Both were installed.
   `tls_template_disagreement` now refuses an image without section headers
   that has a `PT_TLS` with memory: where its thread-local sections lie is not
   shown. LLD 22.1.6 also accepts `-z nosectionheader`; the linkers' own
   layouts written that way are refused too, conservatively.
2. **Low: trust-cg's `.eh_frame` was not seen through LLD and gold.** A
   dynamic no-PIE `PHDRS` script that gave `.eh_frame` a `PT_LOAD` without
   permissions was refused through GNU ld and installed through LLD 22.1.6
   (whose map prints `.eh_frame` input as pieces, which never became own
   input sections) and gold 2.42 (whose map prints merged `** eh_frame` data
   with no file); each program died with SIGSEGV in `_Unwind_Find_FDE` at its
   first `backtrace`. LLD's own pieces are own input sections now (their
   output section's span where it holds other input,
   `EhFrameMap::own_unplaced`), and gold's merged spans are taken as holding
   each own object's allocated `.eh_frame` its map does not list
   (`own_merged_eh_frame`, read after the own inputs by
   `segment_permission_disagreement`).
3. **Low, tests: the refusal of a gold input placed neither by symbols nor
   by an output section could be mutated off with every test green.** The
   gold unit row now runs `segment_permission_diagnostics` on such a map and
   requires the refusal.
4. **Info: two conservative refusals gave untrue reasons.** LLD and gold
   measure thread-local offsets from `p_vaddr`, so their `PHDRS` layouts with
   `.data` inside `PT_TLS` ran correctly outside the driver (GNU ld's twin
   read wrong values, exit 1; measured again here). The first-section rule
   now gives two reasons: a section before `PT_TLS` is not initialized; a
   block that begins with other bytes is refused because the check does not
   show which base the linker used. The one-`PT_LOAD` file-part rule now says
   the template's bytes are not shown to be in memory, rather than that they
   are not.
5. **Found by the repair: trust-cg's sections not loaded where the map places
   them.** The loaded-bytes section rules also read the section headers, and
   the output section's type. With `-z nosectionheader`, GNU ld and LLD
   placed trust-cg's `.data` in no segment (`:NONE`), and the driver installed
   static programs whose global read 0 (exit 50). A script marking trust-cg's
   `.rodata` `(NOLOAD)` made GNU ld and LLD write a zero-fill output section
   (which the image rule admits), and the driver installed programs whose
   constant read 0 (exit 50); gold loads the bytes (exit 0).
   `own_loaded_disagreement` (`[TCG-LINK-LOADED-BYTES]`, after the image rule)
   now requires each own allocated input section the map places to lie in a
   `PT_LOAD`'s memory. A section with contents in its object must lie in the
   file part, and a zero-fill one there must lie over zero bytes.

### Evidence (round 1)

Logs are host-local under the session's scratch directory
`.../scratchpad/r1-l02p10/` (not committed). The reproducer sources are in
`inputs/v1/`. Linker scripts are not committed under `reports/`, so
`inputs/v1/make_scripts.py` writes them, two from GNU ld's default PIE
script and the patches beside it. The mutant harness is
`harnesses/mutants_v1.py` and `harnesses/run_mutants_v1.sh`.

- **Reproducers** (`inputs/v1/repro_v1.sh`): with the base build
  (`be368f243`), the two header-less TLS rows are installed (exit 42, exit 4).
  So are the LLD and gold `.eh_frame` rows (SIGSEGV), the GNU ld and LLD
  `(NOLOAD)` rows (exit 50) and the GNU ld and LLD header-less `:NONE` rows
  (exit 50). With the repair, each is refused by name with the sentinel
  output kept: `[TCG-LINK-TLS-TEMPLATE]`, `[TCG-LINK-SEGMENT-PERMISSIONS]` and
  `[TCG-LINK-LOADED-BYTES]`. The controls are installed and run: the
  script-free `--nostdlib` TLS links, the `FLAGS(4)` `.eh_frame` twins
  through all three linkers (`v=42 frames=4`) and gold's `(NOLOAD)` link.
  The raw links outside the driver show each defect (exit 42, SIGSEGV 139,
  exit 50). `inputs/repro_all.sh`, the twelfth audit's reproducers, gives
  the same verdicts as before.
- **Native rows** (`link_options`, `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1`):
  68/68. The extended rows are
  `tls_templates_that_do_not_hold_trust_cgs_thread_locals_are_never_installed`
  (GNU ld header-less `.tbss`-first and plain links, the headed overlap, and
  the LLD header-less link) and
  `segments_without_the_permissions_trust_cgs_sections_need_are_never_installed`
  (`.eh_frame` without permissions through the three linkers, `(NOLOAD)`
  `.rodata`, header-less `:NONE` `.data`). `output_paths` passes 8/8.
- **Unit rows** (`link_driver::tests`): 131/131 (129 before). The new rows are
  `trust_cg_eh_frame_through_lld_and_gold_maps_needs_read_permission` and
  `trust_cg_sections_the_map_places_must_be_loaded_with_their_bytes`. The
  extended rows cover the TLS template (header-less, before/after reasons),
  gold placement (the refusal of an input placed neither way) and the map
  read (gold's merged data).
- **Ordinary-link sweep** (the same 4,959-link matrix, `sweep/`): every link
  has the same verdict and the same refusal tags as the repair's final run.
  That is 4,816 installed and run, 112 linker failures, 21 true refusals and
  the 10 documented conservative refusals. None carries
  `[TCG-LINK-TLS-TEMPLATE]`, `[TCG-LINK-SEGMENT-PERMISSIONS]` or
  `[TCG-LINK-LOADED-BYTES]`.
- **Mutants** (`harnesses/mutants_v1.py`, `harnesses/run_mutants_v1.sh`):
  one build carries each new check behind a guard. All 16 mutants are killed
  by the unit rows, and 9 also by the native rows. They cover the
  header-less refusal, the before-`PT_TLS` reason, LLD's own pieces and their
  unplaced form, gold's merged data (inline and wrapped), its attribution
  (object without `.eh_frame`, object whose `.eh_frame` the map lists), the
  rule reading it, the own-section map path, the unloaded, zero-fill and
  zero-byte rules, the object's section type, and the gold input placed
  neither way. The unmutated build passes every row. `harnesses/mutants.py`
  (the repair's own 24) had one anchor that no longer matched the formatted
  source (`bc-empty`); it is corrected and applies again.
- **Floor targets** of the link driver re-run green with the floor's linker
  requirements and no SKIP: `e2e_aarch64_link_runtime` 35,
  `e2e_aarch64_eh_catch` 9, `aarch64_elf_symbol_binding` 81,
  `e2e_aarch64_elf_tlsie` 13, `e2e_aarch64_elf_sections` 26,
  `e2e_aarch64_elf_relocation_model` 21, `e2e_aarch64_globals_linux` 15,
  `e2e_aarch64_elf_link` 11, `e2e_aarch64_eh_linux` 12,
  `aarch64_elf_cfi_differential` 3 and `aarch64_elf_eh_relocation_inventory`
  13. `link_options` keeps its pinned 68 (no row was added; two were
  extended).
- **Gates**: `scripts/check_fmt.sh`, `scripts/check_documentation.py --check`
  and the diagnostics census are clean (no new code). `targo tippy` on
  `trust-cg-codegen` (`--lib`, and `--lib --profile test` for the unit rows)
  is clean apart from the two `wasm/opt.rs` collapsible-`if` findings it
  reports on the base too. On `link_options` it reports only the 20 findings
  of lines this change does not touch (3174-3192 and 8834).

### Residuals (round 1)

Stated in LIMITATIONS. A thread-local link written without section headers is
refused even in the linker's own layout. gold's merged `.eh_frame` span is
taken to hold each own object's `.eh_frame`, whichever span holds it. A
`PT_TLS` that begins with other bytes is refused for LLD and gold too, though
they measure from `p_vaddr`. A `PT_TLS` file part past its `PT_LOAD`'s file
part is refused even where a page mapping holds the bytes. trust-cg's own
sections are held to the loaded-bytes rules through the map; another input's
sections in an image without section headers are read by the segments alone,
as before.
