# COMDAT and explicit zero fill (L02-P7) on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the two items the 2026-09-23 closure audit left open on
ledger gap L02-P7, together with the repair of the `.bss.rel.ro` hole the
first review found. It ran on clean source
`a2466f346948c86b0f774122577a4127cb379806` (tree
`c53dc7167641d5b327ac24ca04f111243b53d554`), which is the first change
`cbacfbbcd` plus the repair. `git status --porcelain --untracked-files=all`
was empty before and after the qualifying run (`records/results.json`,
`source_before` equal to `source_after`), and again after the mutation leg
restored each file (`records/mutation/results.json`). This archive replaces
the first one, which was recorded on `cbacfbbcd` before the repair.

L02-P7 stays **PARTIAL**. A separate adversarial audit decides closure.

## Premises at base `722e7611f`

- `pipeline.rs:11596`: the shared-section planner's filter was
  `global.section.is_none() && !global.comdat`, so COMDAT definitions never
  reached the zero-fill `.bss`/`.tbss` partition.
- `pipeline.rs:11917-11931`: the COMDAT arm named
  `elf_implicit_section_base`, which returned only `.tdata`, `.data`,
  `.rodata` or `.data.rel.ro` (`object_sections.rs:536-546`), and hard-coded
  `sh_type: SHT_PROGBITS`.
- `object_sections.rs:324-331`: every `.bss*`, `.tbss*`, `.sbss*` and
  `.lbss*` request was refused as `[TCG-SECTION-NOBITS]`, pinned by
  `e2e_aarch64_elf_sections.rs:804-806` on the all-zero `tcg_state`.

## The change (`cbacfbbcd`, repaired in `a2466f346`)

- `object_sections::ElfImplicitSection` is the one class decision for the
  shared implicit sections and for a COMDAT definition's own
  `<base>.<symbol>` section. Zero fill needs every byte zero and no pointer
  slot (`is_elf_zero_fill`). Non-TLS zero fill also needs mutability, and
  every thread-local zero template is `.tbss`. The shared sections' output is
  unchanged.
- A zero-initialized `LinkOnce`, `LinkOnceOdr` or `WeakOdr` mutable global is
  an SHT_NOBITS `.bss.<sym>` member (`SHF_ALLOC|SHF_WRITE|SHF_GROUP`) of its
  own `GRP_COMDAT` group. An all-zero COMDAT thread-local template is a
  `.tbss.<sym>` member with `SHF_TLS` added.
- An explicit zero-fill name is SHT_NOBITS (`SHF_ALLOC|SHF_WRITE`, plus
  `SHF_TLS` on `.tbss*`) when its global is all zero with no pointer slot. A
  relocated pointer slot or a nonzero byte there is refused as
  `[TCG-SECTION-NOBITS]`, checked before the TLS kind. An all-zero global of
  the wrong TLS kind is `[TCG-SECTION-TLS]`.
- Repair (`a2466f346`): a mutable global in `.bss.rel.ro` or `.bss.rel.ro.*`
  is refused as `[TCG-SECTION-READONLY]`, the `.data.rel.ro` rule. The first
  change admitted it as writable NOBITS because the name matches the `.bss`
  family, although base `722e7611f` refused it. lld places that input inside
  `PT_GNU_RELRO`, so the first store faults (see the linker control below).
  An immutable all-zero global there stays SHT_NOBITS, and `.bss.rel.rox`
  (no `.` boundary) is ordinary `.bss` zero fill.
- `add_placed_elf_section` refuses nonzero NOBITS bytes ahead of the reparse
  gate. Classification never produces them.

## Qualifying run (`records/results.json`, `records/logs/`)

Harness: `harnesses/qualify-comdat-explicit-zero-fill-20260923.py`, run with
`~/.local/bin` on `PATH` so the object rows cross-check with `llvm-readelf`.
The two
native targets ran with a private `TMPDIR` and `TCG_RETAIN_TEST_EVIDENCE=1`,
so their scratch directories were kept for `records/native/`.

| target | libtest result |
| --- | --- |
| `e2e_aarch64_elf_stack_zero_fill` | `ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `e2e_aarch64_elf_sections` | `ok. 21 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `e2e_aarch64_globals_linux` | `ok. 15 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `e2e_aarch64_elf_tlsie` | `ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `v41_global_linkage` | `ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `aarch64_elf_symbol_binding` | `ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `e2e_aarch64_elf_relocation_model` | `ok. 19 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `v41_abi_residue_objects` | `ok. 17 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `e2e_aarch64_elf_link` | `ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `weak_linkage_x86` | `ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --lib` | `ok. 4094 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` |

At base the two extended targets had 9 and 19 tests. The script gates also
passed:

- The Linux, Darwin and bridge gate unit tests: `OK (skipped=1)`. The skip
  is the non-Linux `/proc` control. The `Linux AArch64 bridge gate: FAIL`
  line in that log is a fixture's output.
- `native_test_host_matrix.py --check`, `check_documentation.py --check`
  and `generate_diagnostics_inventory.py --check` passed, as did
  `check_fmt.sh`.
- The floor listings show 147 Linux targets and 193 Darwin rows. The Darwin
  minimums rise to 7 for `e2e_aarch64_elf_stack_zero_fill` and 17 for
  `e2e_aarch64_elf_sections`, for a total of 1331.

The new library tests are:

- `elf::reparse` `grouped_nobits_members_pass_and_bind_type_size_flags_and_membership`,
  `refutation_nonzero_grouped_nobits_content_fails_closed` and
  `refutation_relocation_against_grouped_nobits_member_fails_closed`;
- `pipeline` `elf_zero_fill_comdat_and_explicit_sections_are_grouped_or_shared_nobits`;
- `object_sections` `elf_zero_fill_names_are_nobits_only_for_all_zero_relocation_free_globals`
  and `elf_implicit_section_class_matrix`.

The repair adds rows to existing tests, so the counts do not change. The
zero-fill matrix gains the immutable `.bss.rel.ro`/`.bss.rel.ro.x`
admissions, the `.bss.rel.rox` boundary, a nonzero `.bss.rel.ro` NOBITS
refusal and the mutable `[TCG-SECTION-READONLY]` refusals (`.bss.rel.ro`,
`.bss.rel.ro.x`, `.bss.rel.ro.tcg.hot`, zero-sized).
`unhonorable_elf_sections_are_refused_by_name` pins the mutable `tcg_state`
in `.bss.rel.ro` and `.bss.rel.ro.tcg` to `TCG-SECTION-READONLY`.

## Native evidence (`records/native/`)

All links use the host `cc` (gcc 13.3), GNU ld 2.42 and glibc 2.39, without
`-z noexecstack`. Relocatable objects are stored as `*.o.gz`. Linked
executables are recorded by SHA-256 and length in `linked-binaries.json`,
not copied.

- `link-once/`: 12 links, covering each pairing of the three COMDAT linkages
  (`LinkOnce`+`LinkOnceOdr`, `LinkOnceOdr`+`WeakOdr`, `WeakOdr`+`LinkOnce`)
  at O0-O3. Unit `a` and unit `b` both define `lo_big` (4 MiB of zeros,
  align 4096), `lo_counter` (u64 zero) and `lo_tls` (thread-local
  `[u64; 4]` zeros, align 64). They also define the nonzero twins `lo_seed`
  and `lo_tls_seed`.
  - `a-*.readelf.txt` and `b-*.readelf.txt` (GNU `readelf -S -g -s -W`) show
    `.bss.lo_big`, `.bss.lo_counter` (`NOBITS WAG`) and `.tbss.lo_tls`
    (`NOBITS WAGT`), each alone in a COMDAT group signed by its weak symbol.
    `.data.lo_seed` and `.tdata.lo_tls_seed` are `PROGBITS` with their
    bytes. Every zero-unit object is 2,960 bytes.
  - `link-once-*.map.gz` (GNU ld `-Map`) lists all five of `b`'s sections
    under "Discarded input sections".
  - `link-once-*.readelf.txt` (`readelf -S -W` and `-l -W`) shows a `.bss`
    `NOBITS` of 0x401008 bytes and `PT_TLS` with FileSiz 0x10 and MemSiz
    0x60 (align 0x40).
  - `link-once-*.run.txt` records each executable at 71,832 bytes. Each exits
    0 with `link-once zero-fill data and TLS shared one instance in three
    threads`. Both units see one instance of each global, and writes through
    either unit are seen by the other. The thread-local is one zero-filled
    instance per thread, shared by both units, in three live threads.
  - `strong-O0.link.txt` and `strong-O2.link.txt` are the control. The same
    units with `External` linkage fail to link with `multiple definition of`
    `lo_seed`, `lo_big`, `lo_counter`, `lo_tls_seed` and `lo_tls`.
- `explicit/O0`-`O3`: `zero_fill.o` places all-zero globals in
  `.bss.tcg_big` (2 MiB, align 256), `.bss.tcg_shared` (three members,
  including an immutable and an internal one), `.sbss`, `.lbss.tcg`,
  `.tbss.tcg` (thread-local, `WAT`) and a link-once-ODR `.bss.tcg_comdat`
  (`WAG`, in its group). All are `NOBITS` (`readelf.txt`). The executable
  (71,928 bytes) puts them in `.bss`, `.tbss`, and the orphan `.sbss` and
  `.lbss.tcg` `NOBITS` output sections. It exits 0 with `explicit zero-fill
  sections matched in three threads` (`run.txt`).
- `ctor-bss-tcg/O0`-`O3`: the constructor module with its all-zero
  `tcg_state` in `.bss.tcg`, which was the refusal pin's input. Now `NOBITS
  WA` size 8, it prints `main-done` and `fini-after-main`.

## Mutation controls (`records/mutation/`)

Harness: `harnesses/mutation-comdat-explicit-zero-fill-20260923.py`. Each
mutation is a single-occurrence source edit (`*.diff`) that the harness
applies, tests, and reverts with `git checkout --`. Every mutation was
caught, and the tree was clean after each one.

| mutation | re-introduces | target result | failed tests |
| --- | --- | --- | --- |
| `comdat-arm-progbits` | the base COMDAT arm (zero COMDAT data back in PROGBITS `.data.X`/`.tdata.X`) | `FAILED. 9 passed; 3 failed` | the COMDAT object row, the oracle mutation control and the native link-once row |
| `tbss-type-progbits` | a flipped section type (`.tbss` class typed PROGBITS) | `FAILED. 7 passed; 5 failed` | the above three, plus the implicit `.tbss` object row and the native O0-O3 zero-TLS row (PT_TLS tail) |
| `explicit-zero-fill-refused` | the base refusal of every explicit zero-fill name | `FAILED. 18 passed; 3 failed` | the explicit object row, the native explicit row and the TLS-mismatch and `.bss.rel.ro` rows of the refusal test |
| `explicit-nonzero-admitted` | NOBITS admission of a nonzero initializer | `FAILED. 20 passed; 1 failed` | `unhonorable_elf_sections_are_refused_by_name` (the updated pin) |
| `bss-rel-ro-mutable-admitted` | the first change's writable NOBITS admission of a mutable global in `.bss.rel.ro[.*]` | `FAILED. 20 passed; 1 failed` | `unhonorable_elf_sections_are_refused_by_name` (the `.bss.rel.ro` pin) |

The unit tests hold the byte-level group, flag and type mutations of the
reparse gate and of the test's own oracle
(`link_once_oracle_catches_type_group_flag_and_membership_mutations`).

## Linker control for the repair (`records/lld-relro-control/`)

Harness: `harnesses/lld-relro-control-20260923.py`. It compiles a C global
`unsigned long counter` with a section attribute. Each program is linked
once with the host `cc` (GNU ld 2.42) and once with `cc -fuse-ld=lld`
(LLD 22.1.6). A `store` program writes the global, and a `load` program only
reads it. `results.json` records each exit status and the output sections
readelf maps into the lld image's `GNU_RELRO` segment (`*-lld.readelf.txt`).

| section | GNU ld store/load | lld store | lld load | `.bss.rel.ro` in lld `GNU_RELRO` |
| --- | --- | --- | --- | --- |
| `.bss.rel.ro` | 0 / 0 | SIGSEGV | 0 | yes |
| `.bss.rel.ro.tcg` | 0 / 0 | SIGSEGV | 0 | yes |
| `.bss.rel.rox` | 0 / 0 | 0 | 0 | no |
| `.bss.tcg` | 0 / 0 | 0 | 0 | no |

This is evidence about where the two linkers put the input name. It is why
trust-cg refuses a mutable global there and still admits an immutable one.
It does not run trust-cg output. The review reproduced the fault with a
trust-cg object built before the repair. That probe is not retained, and the
repaired compiler refuses the request.

## Evidence boundaries

- This is object and execution evidence for GNU ld 2.42, gcc 13.3 and glibc
  2.39 on one Linux AArch64 host (`records/results.json` records the
  identities). It is not a linker, loader or TLS-runtime proof.
- lld and other ELF linkers have no native run of trust-cg output. The
  object-level readelf cross-check uses `llvm-readelf` 18.1.3. The lld
  linker control above covers C objects only.
- The implicit COMDAT name `<base>.<symbol>` is not screened for
  linker-special suffixes. A COMDAT symbol literally named `rel.ro` would
  become `.bss.rel.ro` (or `.data.rel.ro`, as at base). Rust mangled names
  cannot take that form. This pre-existing class is not changed here.
- AArch64 has no counterpart of `SHF_X86_64_LARGE`, so `.lbss` carries no
  large-data flag. GNU ld places `.sbss*`/`.lbss*` as orphans by their flags.
- Mach-O still stores zero definitions in `__DATA,__data`. x86-64, RISC-V,
  the JIT and Wasm refuse explicit sections.
- The 147-target Linux floor was not re-run. Only the targets above ran.
