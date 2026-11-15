# AArch64 ELF function sections allowlist and parallel emitter rows on Linux — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run re-qualifies audit rows L02-P1 and L02-P3 at commit
`14fa1eb695f033dc4110974ab467f4d8bb18335d`. That commit repairs three defects that review found in
the [first qualifying run](../2026-09-23-linux-elf-function-attrs/README.md)
(`b68b16269`):

1. **Classifier.** The function-section classifier was a deny-list that
   missed several GNU ld default-script families. `.jcr` and
   `.tm_clone_table` were linked into an RWX segment, and `.jcr` crashed
   with SIGSEGV. `.stab` broke the link. `.rodata1` and `.eh_frame.x` were
   merged into data and unwind output.
2. **Parallel rows.** The `parallel=true` visibility rows compiled a
   24-function module. That is below the 32-item threshold of
   `resource_limits::worker_count_for_items`, so the rows never reached the
   parallel emitter.
3. **Archive.** The first archive's relocatable objects were git-ignored,
   so its archive check failed on a clean checkout.

The run used a clean checkout, and the source identity was the same before
and after (`records/results.json`). The host is Linux AArch64 (NVIDIA Grace,
Ubuntu 24.04). The toolchain was gcc 13.3.0, GNU ld and readelf 2.42, glibc
2.39, and stock Rust 1.97.1 selected by `rust-toolchain.toml`. The pinned
trust-ir is `7b9146ba` (wire v45). `records/results.json` records every
tool's path and SHA-256.

## Result

Verdict **PASS**. Every command exited 0. Each libtest `test result:` line is
in `records/logs/`:

| Target | Result |
| --- | --- |
| `trust-cg-codegen --test aarch64_elf_symbol_binding` | 19 passed |
| `trust-cg-codegen --test e2e_aarch64_elf_sections` | 19 passed |
| `trust-cg-codegen --test aarch64_elf_dwarf` | 12 passed |
| `trust-cg-codegen --test e2e_aarch64_elf_relocation_model` | 19 passed |
| `trust-cg-codegen --test v41_abi_residue_objects` | 17 passed |
| `trust-cg-lower --test pin_move_floor` | 8 passed |
| `trust-cg-lower --test v41_contract_surface` | 21 passed |
| `trust-cg-codegen --lib` | 4,067 passed, 1 ignored |
| `trust-cg-lower --lib` | 1,879 passed |

`e2e_aarch64_elf_sections` had 18 tests at `b68b16269` and 13 at
`be25d1ba6`; the new parallel row makes 19. `aarch64_elf_symbol_binding`
keeps 19 tests, but its visibility row now compiles 48 definitions.

## What changed and what the new rows check

- **Allowlist.** `classify_elf_function_section` now honours only a
  `.text`-prefixed name or a name without a leading `.`. GNU ld 2.42's
  default AArch64 script (`ld --verbose`) folds `.text` and `.text.*` into
  `.text` and has no pattern for any other such name, so the linker places
  those as executable orphans. lld folds the same set. The classifier
  refuses `.jcr`, `.tm_clone_table`, `.rodata1`, `.tcommon`, `.sdata*`,
  `.ldata` and `.lrodata` as `[TCG-SECTION-DATA]`. It refuses `.eh_frame*`,
  `.gcc_except_table*`, `.gnu_extab*`, `.exception_ranges*`, `.sframe*`,
  `.stab*` and `.line*`, and every other dot-prefixed name (`.stub`,
  `.igot`, `.custom_code`, `.`), as `[TCG-SECTION-RESERVED]`. The
  `unhonorable_function_sections_are_refused_by_name` row sends `.jcr`,
  `.tm_clone_table`, `.rodata1`, `.stab`, `.eh_frame.x`,
  `.gcc_except_table.f`, `.sframe` and `.custom_code` through
  `Compiler::compile` and matches each refusal by name. Run against the old
  classifier, that row fails at `.jcr`, which compiles
  (`controls/old-classifier.txt`).
- **Parallel path observable.** The `compile_module` trace entry of
  `Compiler::compile` now names the preparation and emission path, for
  example `48 functions, parallel preparation and emission, N workers`,
  `... sequential preparation and emission` or `cached object`.
- **Visibility rows.** `compiler_maps_trust_ir_function_visibility_to_elf_symbols`
  compiles two copies of the 12 linkage and visibility rows (48
  definitions). In each of its 16 configurations (static and `pic`, O0–O3,
  sequential and parallel), both the module and its default-visibility
  control assert from the trace that `parallel=true` took the parallel path
  and `parallel=false` the sequential one. The mutation needles now match the exact symbol
  (`vis_external_hidden: `).
- **Sections through the parallel emitter.**
  `explicit_function_sections_hold_on_the_parallel_emission_path` adds 34
  unsectioned leaves to the sectioned module (40 definitions). At O0–O3,
  with and without `-ffunction-sections`, both the sequential and the
  parallel objects pass the placement, flag, relocation and FDE checker,
  with every function's FDE included. The parallel object is byte-identical
  to the sequential one, and the trace shows each object's path.
- **Negative controls for the parallel assertion** (`controls/`). With
  `TRUST_CG_MAX_PARALLELISM=1`, both rows fail by name: the parallel row ran
  `48 functions, sequential preparation and emission`, or `40 functions`
  for the sections row. With the visibility module cut back to one copy (24
  definitions, the first run's shape), the row fails with
  `24 functions, sequential preparation and emission;
  worker_count_for_items(24) = Ok(None)`. The source mutations were
  reverted before the commit. The controls ran on the uncommitted tree just
  before `14fa1eb69`, so their line numbers can differ from the commit.
- **Native rows (`records/native/visibility-v45/O0`–`O3` and
  `records/native/named-gc/O0`–`O3`).** These repeat the first run's
  hidden/protected `-shared` library with `LD_PRELOAD` interposition and the
  named-section `--gc-sections` link on the new commit.

## Archive layout

The linked shared objects and executables are not archived.
`records/native/linked-binaries.json` records their SHA-256 and length. The
emitted relocatable objects are archived gzip-compressed (`library.o.gz`,
`named.o.gz`), because the root `.gitignore` ignores `*.o`. Each inventory
entry gives the decoded object's SHA-256 and length and the stored `.gz`
digest. `CAPTURED_FROM.txt` names each directory's original host-local
capture path. Before this directory was committed, its archive check was
run on a `git archive` export of the staged tree. It is also run on an
export of the commit itself.

## Reproduce

```sh
python3 -B reports/perf/2026-09-23-linux-elf-function-attrs-2/harnesses/qualify-elf-function-attrs-2-20260923.py \
  --source . --out /path/outside/source/run --jobs 8
python3 -B reports/perf/2026-09-23-linux-elf-function-attrs-2/harnesses/archive-elf-function-attrs-2-20260923.py \
  --run /path/outside/source/run --archive <new archive dir> --harness <each harness>
python3 scripts/check_evidence_archive.py reports/perf/2026-09-23-linux-elf-function-attrs-2
```

The harness prepends the pinned AY/Clean package's `bin` and `~/.cargo/bin`
to `PATH`. It runs `cargo test --locked --offline` per target, and gives the
two native targets a private `TMPDIR`.

## Boundary

This is object and execution evidence for GNU ld 2.42 and the glibc 2.39
loader on this host. It is not a linker, loader or compiler proof. The
allowlist rests on GNU ld 2.42's default script and lld's section-name
folding. A custom linker script can still map any name anywhere. The
data-global rule (`Global.section`) is still a deny-list: its catch-all
admits other dot-prefixed names as plain allocated data. The byte identity
of the parallel and sequential objects is a test on these modules, not a
proof that the two emitters agree. The Darwin gate minima for the two
targets were raised to 14 and 16 from the cfg gates, but have not yet run
on a Darwin host. The 145-family Linux floor was not re-run for this commit;
only the targets listed above ran. L02-P1 and L02-P3 remain PARTIAL, and no
L01–L14 row closes.
