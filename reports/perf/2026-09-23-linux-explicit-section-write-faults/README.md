# Explicit-section default-link placement (L02-P3, touches L02-P7) on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the repair of a wrong-code class in the AArch64 ELF
explicit data-section classifier. An independent verifier found the class
after the L02-P7 `.bss.rel.ro` repair. It ran on clean source
`d088a4e07ce522bec17902019708d27a7e87713d` (tree
`284d6790dd15fed9aecf2e699e48392438612f95`). That is the change
`de03ef846` plus a test-only commit that makes the native placement
control list every escaped name instead of stopping at the first. `git
status --porcelain --untracked-files=all` was empty before and after the
qualifying run (`records/results.json`, `source_before` equal to
`source_after`) and after each mutation batch restored its file
(`records/mutation/results.json`).

L02-P3 and L02-P7 stay **PARTIAL**. A separate adversarial audit decides
closure.

## Premises at base `0aaebea37`

- `object_sections.rs:482-488`: after the zero-fill, constructor-table,
  `.tdata`, `.rodata`, `.data.rel.ro` and `.data` arms,
  `classify_elf_section` gave every other valid name `SHF_ALLOC`, plus
  `SHF_WRITE` when the global was mutable or relocated. The only other
  refusals were the writer-owned list (`elf_reserved_reason`), `.text*`,
  `.init`, `.fini` and `.ctors`/`.dtors`.
- `pipeline.rs:11829-11840`: a COMDAT definition without an explicit name
  got `format!("{}.{}", implicit.base(), global.name)` with the implicit
  class's type and flags, unclassified.
- `LIMITATIONS.md:794-796` described the catch-all as admitting `.jcr`,
  `.stab` or `.eh_frame.x` "as plain allocated data".

## The change (`de03ef846`)

`object_sections::ELF_NAME_RULES` records, per input-section name family,
where GNU ld 2.42's default AArch64 script and LLD 22.1.6's built-in rules
put it. The mapping table is in the `object_sections` module doc. The
classifier derives every refusal from those two columns. A mutable global
in a read-only or `PT_GNU_RELRO` output of either linker is
`[TCG-SECTION-READONLY]`. `.tcommon` (GNU ld's `.tbss`) is
`[TCG-SECTION-TLS]`. `.stub` and `.iplt` are `[TCG-SECTION-EXEC]`. Names a
linker parses, synthesizes, types by name, drops or discards, or that
crtbegin/crtend walk, are `[TCG-SECTION-RESERVED]` for every data global.
Names no row matches are orphans under both linkers and keep the global's
flags. `ElfImplicitSection::comdat_section` classifies a COMDAT
definition's `<base>.<symbol>` with the same table and refuses a symbol
that moves it out of `<base>`'s row. The function-section allowlist
refuses `COMMON`.

### Dispositions that changed (data globals unless stated)

| name | base `0aaebea37` | now |
| --- | --- | --- |
| `.tcommon` (non-TLS) | honoured, writable PROGBITS | `[TCG-SECTION-TLS]` |
| `.gnu_extab*`, `.gcc_except_table.*`, `.exception_ranges*`, `.sframe`, `.sframe.*`, `.eh_frame.*`, `.eh_frame_entry`, `.eh_frame_entry.*` | honoured | `[TCG-SECTION-RESERVED]` |
| `.jcr`, `.tm_clone_table` | honoured | `[TCG-SECTION-RESERVED]` |
| `.igot`, `.igot.plt`, `.relro_padding`, `COMMON` | honoured | `[TCG-SECTION-RESERVED]` |
| `.rela*` beyond `.rela`/`.rela.*` (`.rela_x`, `.relative`), `.relr.dyn` | honoured | `[TCG-SECTION-RESERVED]` |
| `.stab`, `.stabstr`, `.stab.excl`, `.stab.exclstr`, `.stab.index`, `.stab.indexstr`, `.stab*str`, `.line` | honoured | `[TCG-SECTION-RESERVED]` |
| `.gnu_debuglink` | honoured | `[TCG-SECTION-RESERVED]` |
| `.stub`, `.iplt` | honoured | `[TCG-SECTION-EXEC]` |
| `.rodata1`, mutable or relocated | honoured (`SHF_WRITE`) | `[TCG-SECTION-READONLY]`; an immutable relocation-free one stays `SHF_ALLOC` |
| `.toc`, mutable | honoured | `[TCG-SECTION-READONLY]`; immutable stays honoured |
| `.init_array[.N]`, `.fini_array[.N]`, `.preinit_array`, mutable table | honoured | `[TCG-SECTION-READONLY]` |
| implicit COMDAT of a mutable symbol `rel.ro`/`rel.ro.*` | `.data.rel.ro...`/`.bss.rel.ro...` | `[TCG-SECTION-READONLY]` (implicit ELF COMDAT section) |
| function section `COMMON` | honoured (undotted) | `[TCG-SECTION-DATA]` |

The table was re-derived without loosening any honoured, verified name.
`.data*`, `.data1`, `.bss*` zero fill, `.sbss*`, `.lbss*`, `.tdata*`/`.tbss*`
for thread-locals, immutable `.rodata*`/`.data.rel.ro*`, the constructor
tables for immutable pointer tables, and orphans keep their placement.
The orphans include the names one character past a family, such as
`.data.rel.rox`, `.bss.rel.rox`, `.tcommon.x`, `.jcrx`, `.eh_framex`,
`.rodata1.x`, `.stabx`, `.relro` and `tcg_custom_rw`. That is not true of
every such name. A name BFD matches by a raw prefix outside the script is
refused, and `.eh_frame_entryx` was admitted by mistake. See
[the repair](#repair-after-the-verifiers-sweep--2026-09-23).

## Derivation (`records/probe/`)

Harness: `harnesses/linker-placement-probe-20260923.py`.

- `records/probe/scripts/ld-verbose-*.x` are `ld --verbose` for exe, PIE
  and `-shared`, each with `-z relro`, `-z norelro` and `-z now -z relro`.
  `results.json.gz` records which ldscripts variant each selects: gcc's
  default link (`-pie -z now -z relro`) is `aarch64linux.xdw`, `-no-pie` is
  `.xw`, and `-shared` is `.xsw`. `-z norelro` prints the same script as `-z
  relro`. The input patterns are the same across the three, apart from
  `.interp` (absent in `.xsw`) and `.got.plt`, which is outside
  `PT_GNU_RELRO` without `-z now`. The parsed statements of the default
  script and their regions are in `results.json.gz`
  (`gnu_default_statements`). The `.xdw` text is also retained in the
  source tree as the unit-test fixture, byte-identical to the installed
  `/usr/lib/aarch64-linux-gnu/ldscripts/aarch64linux.xdw` (SHA-256
  `bae2974d8be53aeef8af71e75cefb7fc7a8e5b705dc9a69ecc384c97c356c8be`).
- 120 data-section names and three function-section names, 350 shapes in
  all. Each probe object is assembled under a
  same-length placeholder and renamed in `.shstrtab`, because GNU as gives
  `.stab*`, `.rel*` and `.tdata*` names types or flags of its own. That
  leaves the section type and flags trust-cg's pre-repair classifier
  emitted: mutable all-zero, mutable nonzero, immutable, constructor-table
  and function shapes. Each is linked with GNU ld and LLD as a PIE, with
  `-no-pie`, with `-z norelro` and as a `-shared` library, and run.
  `summary.txt` has one line per name and shape: the output section, the
  segments that cover the global (`RELRO`, `TLS`, `LOAD` flags), whether it
  sits in crtstuff's TM clone list, and the exit status.
- `tcommon_beside_tls` places `.tcommon` next to a real `__thread`. GNU ld
  then prints `section '.tbss' type changed to PROGBITS`, the output
  becomes `WAT` inside `PT_TLS` and `PT_GNU_RELRO`, and the non-TLS store
  still faults.

Findings the rules encode (PIE unless stated):

| input name | GNU ld 2.42 | LLD 22.1.6 |
| --- | --- | --- |
| `.tcommon` | `.tbss`, RELRO: store SIGSEGV | orphan, runs |
| `.gnu_extab`, `.gcc_except_table[.x]`, `.exception_ranges[.x]`, `.sframe[.x]`, `.eh_frame.x`, `.igot`, `.igot.plt` | RW member forces the ONLY_IF_RW statement (or `.got`) inside RELRO: SIGSEGV | orphan or by flags, runs |
| `.gnu_extab.x` | writable: orphan, runs; read-only: `.gnu_extab` unwind output | orphan |
| `.eh_frame_entry[.x]` | link error ("compact frame descriptions incompatible") | orphan |
| `.jcr`, `.data.rel.ro*`, constructor tables | RELRO: SIGSEGV | RELRO: SIGSEGV |
| `.bss.rel.ro*`, `.toc` | `.bss` / orphan, runs | RELRO: SIGSEGV |
| `.stub` | `.text`: SIGSEGV | orphan |
| `.iplt` | `.plt`, segment RWX | `.iplt`, segment RWX |
| `.rodata1`, `.rodata*` (mutable) | text segment turns RWX | by flags, RW |
| `.stab`, `.stabstr`, `.stab.excl[str]`, `.stab.index[str]`, `.line` | link error ("PHDR segment not covered by LOAD segment"); `-shared` links an RWX segment | orphan |
| `.stab*str` | orphan typed `SHT_STRTAB` | orphan |
| `.rela_x`, `.relative`, `.rela` | typed `SHT_RELA`; `-shared`: SIGSEGV | orphan |
| `.rel`, `.rel.*`, `.relr.dyn` | `-shared`: unusable library ("file format not recognized") | orphan |
| `.gnu_debuglink` | `/DISCARD/`: link error | orphan |
| `.relro_padding` | orphan | link error (overlaps `.dynamic`) |
| `.tm_clone_table` | orphan between `__TMC_LIST__` and `__TMC_END__` | same |
| `COMMON` | `.bss` | `.bss` |
| `COMMON` (function) | `.bss`, segment RWX | `.bss`, segment RWX |
| `.gnu_debugaltlink`, `.noinit`, `.persistent*`, `.ctf`, `.ldata*`, `.lrodata*`, `.sdata*`, `.srodata*`, `.sdata2`, `.sbss2`, `.relx`, `.relro`, `.relr`, `.tdata1`, `.openbsd.randomdata`, `.gdb_index` | orphan, runs | orphan or by flags, runs |

## Qualifying run (`records/results.json`, `records/logs/`)

Harness: `harnesses/qualify-explicit-section-write-faults-20260923.py`,
2026-09-23T09:50:08Z to 09:53:10Z. `e2e_aarch64_elf_sections` ran with a
private `TMPDIR`, `TCG_RETAIN_TEST_EVIDENCE=1` and `TCG_REQUIRE_LLD=1`, so
the LLD legs could not be skipped (`ld.lld` from `~/.local/bin`, LLD
22.1.6).

| target | result |
| --- | --- |
| `e2e_aarch64_elf_sections` | `test result: ok. 25 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 28.38s` |
| `e2e_aarch64_elf_stack_zero_fill` | `test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 6.51s` |
| `e2e_aarch64_globals_linux` | `test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.36s` |
| `e2e_aarch64_elf_tlsie` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.29s` |
| `v41_global_linkage` | `test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.11s` |
| `aarch64_elf_symbol_binding` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 2.37s` |
| `e2e_aarch64_elf_relocation_model` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.07s` |
| `e2e_aarch64_elf_link` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.47s` |
| `trust-cg-codegen --lib` | `test result: ok. 4108 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 5.71s` |

`cargo check -p trust-cg-codegen --features verify` passed. The script
gates passed too: the Linux, Darwin and bridge gate unit tests (`OK
(skipped=1)`; the skip is the non-Linux `/proc` control, and the `Linux
AArch64 bridge gate: FAIL` line in that log is a fixture's output),
`native_test_host_matrix.py --check`, `check_documentation.py --check`,
`generate_diagnostics_inventory.py --check`, `check_fmt.sh`, and the
Darwin and Linux floor listings. `e2e_aarch64_elf_sections` has 25 tests,
up from 21 at base: two host-neutral rows (the Darwin minimum rises to 19,
for a total of 1333) and two Linux-native rows. The library suite's 4108
include four new `object_sections` tests (the module had 10 tests at base
and has 14 now).

## Native evidence (`records/native/`)

Relocatable objects are `*.o.gz`. Linked executables and libraries are in
`linked-binaries.json` by SHA-256 and length.

`refused/NN-name/` holds
`linux_native::refused_sections_fault_or_misplace_trust_cg_bytes_under_the_named_linker`,
one directory per case, O2. The control compiles the mutable all-zero victim
(a hidden u64 with trust-cg's own `+= 3` load and store) under a
same-length placeholder trust-cg honours, then renames that section in
`.shstrtab`. Every other byte is the compiler's. The constructor tables use
the honoured immutable table instead, whose object is byte-identical to the
mutable one's. The COMDAT cases use a same-length stand-in symbol. Each
control is linked with `cc` (GNU ld 2.42) and `cc -fuse-ld=lld` (LLD 22.1.6)
as a PIE, or as a `-shared` library for `.relative` and `.relr.dyn`. The
directory keeps `record.txt`, `control-*.run.txt` (output section,
segments, exit or signal) and `control-*.link.txt`, and records the
compiler's refusal of the mutable victim:

| victim | refusal | GNU ld 2.42 | LLD 22.1.6 |
| --- | --- | --- | --- |
| `.tcommon` | `[TCG-SECTION-TLS]` | `.tbss`, RELRO, SIGSEGV | `.tcommon`, exit 0 |
| `.gnu_extab` | `[TCG-SECTION-RESERVED]` | `.gnu_extab`, RELRO, SIGSEGV | exit 0 |
| `.gcc_except_table.x` | `[TCG-SECTION-RESERVED]` | `.gcc_except_table`, RELRO, SIGSEGV | exit 0 |
| `.exception_ranges` | `[TCG-SECTION-RESERVED]` | RELRO, SIGSEGV | exit 0 |
| `.sframe` | `[TCG-SECTION-RESERVED]` | RELRO (and `GNU_SFRAME`), SIGSEGV | exit 0 |
| `.eh_frame.x` | `[TCG-SECTION-RESERVED]` | `.eh_frame`, RELRO, SIGSEGV | exit 0 |
| `.jcr` | `[TCG-SECTION-RESERVED]` | RELRO, SIGSEGV | RELRO, SIGSEGV |
| `.sframe.x` | `[TCG-SECTION-RESERVED]` | `.sframe`, RELRO, SIGSEGV | exit 0 |
| `.exception_ranges.x` | `[TCG-SECTION-RESERVED]` | RELRO, SIGSEGV | exit 0 |
| `.eh_frame_entry` | `[TCG-SECTION-RESERVED]` | link error: compact frame descriptions incompatible | exit 0 |
| `.stub` | `[TCG-SECTION-EXEC]` | `.text`, SIGSEGV | exit 0 |
| `.iplt` | `[TCG-SECTION-EXEC]` | `.plt`, `LOAD` RWE | `.iplt`, `LOAD` RWE |
| `.rodata1` | `[TCG-SECTION-READONLY]` | `LOAD` RWE | exit 0 |
| `.igot` | `[TCG-SECTION-RESERVED]` | `.got`, RELRO, SIGSEGV | exit 0 |
| `.toc` | `[TCG-SECTION-READONLY]` | exit 0 | RELRO, SIGSEGV |
| `.relro_padding` | `[TCG-SECTION-RESERVED]` | exit 0 | link error: overlaps `.dynamic` |
| `COMMON` | `[TCG-SECTION-RESERVED]` | `.bss` | `.bss` |
| `.tm_clone_table` | `[TCG-SECTION-RESERVED]` | in `__TMC_LIST__`..`__TMC_END__` | same |
| `.stab` | `[TCG-SECTION-RESERVED]` | link error: PHDR segment not covered | exit 0 |
| `.line` | `[TCG-SECTION-RESERVED]` | link error: PHDR segment not covered | exit 0 |
| `.gnu_debuglink` | `[TCG-SECTION-RESERVED]` | link error: defined in discarded section | exit 0 |
| `.relative` (`-shared`) | `[TCG-SECTION-RESERVED]` | SIGSEGV | exit 0 |
| `.relr.dyn` (`-shared`) | `[TCG-SECTION-RESERVED]` | driver link: file format not recognized | exit 0 |
| `.init_array` (table) | `[TCG-SECTION-READONLY]` | RELRO, SIGSEGV | RELRO, SIGSEGV |
| `.fini_array` (table) | `[TCG-SECTION-READONLY]` | RELRO, SIGSEGV | RELRO, SIGSEGV |
| COMDAT `rel.ro`, nonzero (`.data.rel.ro`) | `[TCG-SECTION-READONLY]` | RELRO, SIGSEGV | RELRO, SIGSEGV |
| COMDAT `rel.ro`, zero (`.bss.rel.ro`) | `[TCG-SECTION-READONLY]` | `.bss`, exit 0 | RELRO, SIGSEGV |
| `.bss.rel.ro` | `[TCG-SECTION-READONLY]` | `.bss`, exit 0 | RELRO, SIGSEGV |
| `.data.rel.ro` | `[TCG-SECTION-READONLY]` | RELRO, SIGSEGV | RELRO, SIGSEGV |

`honoured/O0` and `honoured/O2` hold
`linux_native::honoured_writable_sections_survive_a_store_under_gnu_ld_and_lld`.
Fourteen mutable globals are placed in honoured writable names:
`.data.tcg`, `.data1`, NOBITS `.bss.tcg`, `.sbss.tcg` and `.lbss.tcg`,
`.bss.rel.rox`, `.data.rel.rox`, `.tcommon.x`, `.jcrx`, `.eh_framex`,
`.rodata1.x`, `.stabx`, `.relro` and `tcg_custom_rw`. Three immutable
globals are placed in `.rodata1`, `.toc` and `.data.rel.ro.tcg`. Each
object is linked as a PIE and as a `-shared` library under GNU ld and under
LLD. Every writable global sits in an `SHF_WRITE` output under an RW `LOAD`
outside `PT_GNU_RELRO`, and every program exits 0 with `honoured sections
survived every store` (`record.txt`).

## Mutation controls (`records/mutation/`)

Harness: `harnesses/mutation-explicit-section-write-faults-20260923.py`,
three batches on `d088a4e07`. Each mutation is a single-occurrence edit of
`object_sections.rs` (`*.diff`). The harness runs the `object_sections`
unit tests and `e2e_aarch64_elf_sections` with retention and
`TCG_REQUIRE_LLD=1`, then restores the file with `git checkout --`. All
eight are caught, and the tree was clean after each. A first attempt at
`executable-outputs-narrowed` did not compile (the edit left
`executable_reason` unused under `-D warnings`) and was discarded. The
recorded batch uses the corrected edit in the retained harness.

| mutation | unit | e2e | escaped objects (retained under `records/mutation/<mutation>/`) |
| --- | --- | --- | --- |
| `special-names-admitted` | `FAILED. 13 passed; 1 failed` | `FAILED. 23 passed; 2 failed` | 17 names escape; GNU ld SIGSEGV for `.gnu_extab`, `.gcc_except_table.x`, `.exception_ranges`, `.sframe`, `.eh_frame.x`, `.sframe.x`, `.exception_ranges.x`, `.igot`, `.relative`; link errors for `.eh_frame_entry`, `.stab`, `.line`, `.gnu_debuglink`, `.relr.dyn`; LLD link error for `.relro_padding`; `COMMON` in `.bss`; `.tm_clone_table` in the TM list. `.jcr` falls through to `[TCG-SECTION-READONLY]` (wrong code, still refused) |
| `write-protected-admitted` | `FAILED. 11 passed; 3 failed` | `FAILED. 22 passed; 3 failed` | `.toc` SIGSEGV under LLD; `.data.rel.ro` SIGSEGV under both; `.rodata1` is emitted `SHF_ALLOC` for the mutable global and faults under both; COMDAT `rel.ro` refused with the wrong code |
| `mutable-tables-admitted` | `FAILED. 13 passed; 1 failed` | `FAILED. 23 passed; 2 failed` | `.init_array`, `.fini_array`: SIGSEGV under both |
| `tcommon-admitted` | `FAILED. 13 passed; 1 failed` | `FAILED. 23 passed; 2 failed` | `.tcommon`: `.tbss`, SIGSEGV under GNU ld |
| `executable-outputs-narrowed` | `FAILED. 13 passed; 1 failed` | `FAILED. 23 passed; 2 failed` | `.stub`: `.text`, SIGSEGV under GNU ld; `.iplt`: RWX under both |
| `comdat-collision-admitted` | `FAILED. 13 passed; 1 failed` | `FAILED. 23 passed; 2 failed` | COMDAT `rel.ro`: `.data.rel.ro` SIGSEGV under both; `.bss.rel.ro` SIGSEGV under LLD |
| `function-common-admitted` | `FAILED. 13 passed; 1 failed` | `FAILED. 24 passed; 1 failed` | (object rows only) |
| `gnu-column-drift` | `FAILED. 12 passed; 2 failed` | `FAILED. 23 passed; 2 failed` | the script cross-check fails; `.tcommon` escapes and faults under GNU ld |

For every escaped explicit-section name, the escaped object is
byte-identical to the renamed control object (`record.txt`), so the
controls above are the bytes the pre-repair compiler emitted. The
exception is `.rodata1` under `write-protected-admitted`, whose mutant
emits different flags. The COMDAT objects differ only in the stand-in
symbol name.

## Evidence boundaries and residuals

- This is object and execution evidence for GNU ld 2.42 (Ubuntu binutils
  2.42), LLD 22.1.6, gcc 13.3 (crtbegin/crtend) and glibc 2.39 on one Linux
  AArch64 host (`records/results.json` records identities and hashes). It
  is not a linker or loader proof. The GNU column is tied to the default
  scripts and BFD's name typing of this binutils. The LLD column is
  probed, not derived from LLD's source. A custom `-T` script, `-z
  separate-code`, LLD's `-z pack-relative-relocs` (a synthetic `.relr.dyn`),
  other linkers (gold, mold) and other binutils/LLD versions may place
  names differently.
- Refusals are conservative where one linker treats a name specially. A
  name refused because GNU ld misplaces it (`.gnu_extab*`,
  `.gcc_except_table.*`, `.sframe*`, `.stab*`, `.line`, ...) is refused even
  when linking with LLD, and `.toc` and `.bss.rel.ro*` are immutable-only
  even under GNU ld. A writable `.gnu_extab.x` is an orphan under both
  linkers and ran in the probe, but it is still refused, because the same
  name in a read-only object joins GNU ld's `.gnu_extab` unwind output.
- The implicit COMDAT check refuses a colliding symbol. It does not rename
  it. Only hand-written trust-ir symbols can collide: Rust and C++ mangled
  names and C identifiers contain no `.`. The check compares table rows,
  not explicit-name syntax, so long or unusual symbols are unaffected.
- The function-section allowlist was already derived from the same
  scripts. This run only adds `COMMON`, covered by object rows and the
  probe, with no trust-cg native function run.
- Mach-O placement is unchanged. x86-64, RISC-V, the JIT and Wasm refuse
  explicit sections, and the rustc bridge still refuses `#[link_section]`
  (L06-P1).
- The 145-target Linux floor was not re-run. Only the targets above ran.

## Repair after the verifier's sweep — 2026-09-23

An independent verifier checked tip `5713bd236` with a 3,427-name sweep:
about 25,000 links under GNU ld and LLD with PIE, `-no-pie`, `-z norelro`,
`-shared`, `-static`, `-s`, strip and `--gc-sections`. It found no store
faults, no `PT_GNU_RELRO` or TLS landings and no RWX segments, and it found
one admitted class. `ELF_NAME_RULES` matched only `.eh_frame_entry` and
`.eh_frame_entry.*`, the patterns the default script names. But BFD
(`bfd/elflink.c` `_bfd_elf_parse_eh_frame_entries`) parses every input
section whose name STARTS with `.eh_frame_entry` as compact unwind entries.
It does this by name and outside the script. Beside the C runtime's DWARF
`.eh_frame`, every GNU ld 2.42 link then fails with "compact frame
descriptions incompatible with DWARF2 .eh_frame". trust-cg admitted
`.eh_frame_entryx`, `.eh_frame_entry1`, `.eh_frame_entry_x`,
`.eh_frame_entry-x` and `.eh_frame_entry$x` for mutable zero, mutable
nonzero and immutable globals, and LLD links and runs them. The derivation
test could not catch this, because its GNU model had no category for a rule
BFD applies by name. Functions were already refused, because the function
allowlist refuses dot-prefixed names.

### The change (`a3f73e83d`)

- The row is the prefix `.eh_frame_entry*`, with a new GNU placement
  `ElfPlacement::ParsedByName`. Every spelling is `[TCG-SECTION-RESERVED]`,
  and `.eh_frame_entq` (one character short) stays an orphan.
- `crates/trust-cg-codegen/tests/fixtures/gnu-ld-2.42-bfd-by-name.txt` is
  a retained list of the rules BFD applies by name, each with its binutils
  2.42 source:
  - parsed: `.eh_frame_entry*`;
  - typed: `.rela*` (`SHT_RELA`), `.relr.dyn` (`SHT_RELR`) and `.stab*str`
    (`SHT_STRTAB`);
  - owned, meaning already writer-owned: `.eh_frame`, `.rel`, `.rel.*`,
    `.gnu.warning*`, `.gnu.linkonce*`, `.gnu.lto_*`, `.note*`, `.debug*`,
    `.zdebug*` and `.comment`;
  - inert for allocated data: `.line*`, `.stab*`, `.gdb_index`, `.noinit*`,
    `.persistent*`, `.gnu_object_only*` and `.ctf*`.
- `elf_name_rules_match_the_gnu_ld_2_42_default_script` now models GNU
  ld's disposition of a name in this order: writer-owned; parsed by name;
  first script statement; typed-by-name orphan; plain orphan. It checks
  every script pattern, every list row and every table row against the
  table. A by-name placement in the table must therefore come from the
  list, and an owned row must be covered by the writer's reserved names.
- Rows: the five spellings are pinned to `[TCG-SECTION-RESERVED]` in the
  unit matrix and in `unhonorable_elf_sections_are_refused_by_name`, and
  `.eh_frame_entq` is added to the boundary lists. The native placement
  control adds `.eh_frame_entryx`, so it now has 30 cases. The new Linux
  row `c_globals_under_the_eh_frame_entry_prefix_fail_the_gnu_link` covers
  the C spellings. `e2e_aarch64_elf_sections` has 26 tests. The new test is
  Linux-only, and the Darwin minimum stays 19.
- LIMITATIONS, the module doc, the plan and the CHANGELOG no longer say that
  every name one character past a family keeps the global's flags.

### By-name probe (`records/repair/probe/`)

`linker-placement-probe-20260923.py` (the copy under
`records/repair/harnesses/`, with the added names) ran with `--only` for 42
names in 126 shapes, under both linkers in four modes. `summary.txt` has
one line per name and shape:

- `.eh_frame_entry`, `.eh_frame_entry.x`, `.eh_frame_entryx`,
  `.eh_frame_entry1`, `.eh_frame_entry_x`, `.eh_frame_entry-x` and
  `.eh_frame_entry$x`: every GNU link fails ("compact frame descriptions
  incompatible with DWARF2 .eh_frame from .../Scrt1.o" or crtbeginS.o for
  `-shared`), for every shape and mode. LLD links each as an orphan and
  runs it.
- `.eh_frame_entq`, `.eh_frame_hdrx`, `.eh_frame_hdr.x`, `.eh_framex`,
  `.eh_frameq`, `.gcc_except_tablex`, `.tm_clone_tablex`, `.sframex`,
  `.relr.dynx`, `.gnu_debuglinkx`, `.lto_x`, `.gnu_lto_x`, `.gnu_warning`,
  `.note_gnu`, `.debug_`, `.linex`, `.stabx`, `.gdb_index`, `.noinit`,
  `.noinit.x`, `.noinitx`, `.persistent`, `.persistent.x`, `.persistentx`,
  `.persistent.bss`, `.gnu_object_only`, `.gnu_object_onlyx`, `.ctf` and
  `.ctfx`: PROGBITS orphans under both linkers, and every program runs.
  `.debug_` is writer-owned anyway.
- `.relax`, `.rela_x` and `.relative` are typed `SHT_RELA`, and the `-shared`
  store faults. `.relr.dyn` is typed `SHT_RELR`, and the `-shared` library is
  unusable. `.stabqstr` and `.stabxstr` are typed `SHT_STRTAB`.

### Re-qualifying run (`records/repair/results.json`, `records/repair/logs/`)

The run was on clean `a3f73e83d2a35925882355c0df6d7bb3c948d101` (tree
`52602225c8e6921ffdee2a076de10504f5d26d3b`), from 2026-09-23T10:47:33Z to
10:51:11Z, using the same harness. `source_before` equals `source_after`,
and the tree was clean. `e2e_aarch64_elf_sections` ran with
`TCG_REQUIRE_LLD=1`.

| target | result |
| --- | --- |
| `e2e_aarch64_elf_sections` | `test result: ok. 26 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 27.87s` |
| `e2e_aarch64_elf_stack_zero_fill` | `test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 6.48s` |
| `e2e_aarch64_globals_linux` | `test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.38s` |
| `e2e_aarch64_elf_tlsie` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.41s` |
| `v41_global_linkage` | `test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.17s` |
| `aarch64_elf_symbol_binding` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 3.85s` |
| `e2e_aarch64_elf_relocation_model` | `test result: ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.70s` |
| `e2e_aarch64_elf_link` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 2.24s` |
| `trust-cg-codegen --lib` | `test result: ok. 4108 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 5.08s` |

`cargo check -p trust-cg-codegen --features verify`, the gate unit tests,
`native_test_host_matrix.py --check`, `check_documentation.py --check`,
`generate_diagnostics_inventory.py --check`, `check_fmt.sh` and both floor
listings passed.

Native records are under `records/repair/native/`:

- `refused/`: the 30 placement controls. `10-eh_frame_entryx` has trust-cg's
  bytes under `.eh_frame_entryx`. The GNU link fails with the compact-frame
  error, and LLD runs it.
- `eh-frame-entry-c/`: the C control, with its six sources and
  `record.txt`. GNU ld fails the link for each of the five spellings, LLD
  links and runs each (`10`), and trust-cg refuses each name as
  `[TCG-SECTION-RESERVED]`. `.eh_frame_entq` links and runs under both and
  is honoured.
- `honoured/`: the honoured-name rows again.

### Repair mutations (`records/repair/mutation/`)

`mutation-explicit-section-write-faults-20260923.py` (the copy under
`records/repair/harnesses/`) ran on `a3f73e83d`, and the tree was clean
after it.

| mutation | unit | e2e | result |
| --- | --- | --- | --- |
| `eh-frame-entry-prefix-narrowed`: the table row back to `.eh_frame_entry`/`.eh_frame_entry.*` | `FAILED. 12 passed; 2 failed` | `FAILED. 23 passed; 3 failed` | caught. The derivation test fails with "BFD parses every input named `.eh_frame_entryq` as compact unwind entries ... but the table says Orphan", the unit matrix and the e2e refusal rows fail, and the C control fails because trust-cg compiles the spellings. The escaped `.eh_frame_entryx` object is retained. It is byte-identical to the control, and its GNU link fails with the compact-frame error. |
| `bfd-by-name-list-narrowed`: the retained list's row narrowed to `.eh_frame_entry` | `FAILED. 13 passed; 1 failed` | not run (the list is read only by the unit test) | caught. The derivation test fails with "GNU ld places `.eh_frame_entry.` in `.eh_frame_hdr` (ReadOnly) but the table says ParsedByName(...)", so the table's prefix row is no longer backed by the list. |

### Boundaries

- The by-name list comes from binutils 2.42 behaviour and source knowledge
  for an allocated data section on AArch64. It is not a proof that BFD has
  no other by-name rule. The verifier's 3,427-name sweep and the 42-name
  repair probe found no other. Refusals stay conservative.
- The first qualifying run, the mutation controls and the evidence above
  are unchanged. The earlier claim that every name one character past a
  family keeps the global's flags is corrected here, and the ledger note
  for L02-P3 is corrected too. `.tm_clone_table` and `COMMON` were
  misplaced rather than faulting, and `.eh_frame_entry` failed the link.
