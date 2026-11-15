# AArch64 ELF function visibility and sections on Linux — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies commit `b68b16269fef2c1bb0d18f41809b762e4687d82c`, which
addresses audit rows L02-P1 and L02-P3. It ran on a clean checkout, and the
source identity was the same before and after (`records/results.json`). The
host is Linux AArch64 (NVIDIA Grace, Ubuntu 24.04). It used gcc 13.3.0,
GNU ld and readelf 2.42 and glibc 2.39, and stock Rust 1.97.1 selected by
`rust-toolchain.toml`. The pinned trust-ir is `7b9146ba` (wire v45).
`records/results.json` records every tool's path and SHA-256, plus the
SHA-256 of glibc's `libc.so.6` and `ld-linux-aarch64.so.1`.

## Result

Verdict **PASS**. Every command exited 0. Each libtest `test result:` line is
in `records/logs/`:

| Target | Result |
| --- | --- |
| `trust-cg-codegen --test aarch64_elf_symbol_binding` | 19 passed |
| `trust-cg-codegen --test e2e_aarch64_elf_sections` | 18 passed |
| `trust-cg-codegen --test aarch64_elf_dwarf` | 12 passed |
| `trust-cg-codegen --test e2e_aarch64_elf_relocation_model` | 19 passed |
| `trust-cg-codegen --test v41_abi_residue_objects` | 17 passed |
| `trust-cg-lower --test pin_move_floor` | 8 passed |
| `trust-cg-lower --test v41_contract_surface` | 21 passed |
| `trust-cg-codegen --lib` | 4,067 passed, 1 ignored |
| `trust-cg-lower --lib` | 1,879 passed |

The base `be25d1ba6` had 15 tests in `aarch64_elf_symbol_binding` and 13 in
`e2e_aarch64_elf_sections`. Every test that existed there still passes.

## What the new rows check

- **Visibility, object level.** `compiler_maps_trust_ir_function_visibility_to_elf_symbols`
  compiles every (linkage, visibility) a trust-ir v45 definition may state
  with `Compiler::compile`. It covers O0–O3, sequential and parallel, and the
  `static` and `pic` models. The test's own ELF reader finds
  `STB_GLOBAL`/`STB_WEAK` with `STV_HIDDEN`/`STV_PROTECTED`. The same module
  with every visibility reset to default has identical `.text` and
  relocations. Mutating one `st_other` or one `st_info` byte is caught by the
  row checker.
- **Visibility refusals.** An `Internal`/`Private` function with visibility,
  or an import with visibility, is refused by name
  (`[TCG-FUNCTION-VISIBILITY]`). Mach-O, x86-64 and RISC-V refuse the v45
  `visibility` facet, and so does the JIT (aarch64 host).
- **Visibility, native (`records/native/visibility-v45/O0`–`O3`).** A
  `.trust_ir` text module with `; #visibility: hidden|protected` directives
  (`library.tir`) is parsed back and compiled with `Compiler::compile` under
  `pic`. `cc -shared` links it. In the library's `.dynsym` (`dynsym.txt`),
  hidden functions are absent and protected ones are `STV_PROTECTED`. In
  `library-relocs.txt`, of the five leaves only the default one has an
  `R_AARCH64_JUMP_SLOT`. `run-plain.txt` is the run without `LD_PRELOAD`.
  In `run-preload.txt`, an `LD_PRELOAD` interposer (`interposer.c`) rebinds
  the default-visibility call and the executable's own protected reference
  (111, 222). It never rebinds the library's calls to its protected and
  hidden definitions (22, 33, 44, 55). Linking a hidden function from
  outside fails.
- **Sections, object level.** `explicit_function_sections_place_bodies_relocations_and_fdes`
  covers O0–O3 with and without `-ffunction-sections`. Named functions land
  in `SHF_ALLOC|SHF_EXECINSTR`, 4-aligned sections: `.text.hot`, the shared
  `tcg_cold_code` and `.text` itself. Their bodies are byte-identical to the
  unsectioned object's. Every text relocation keeps its function-relative
  offset, type, target and addend. Each FDE is anchored at its function's
  section symbol, with the function's offset as addend. Four mutations are
  caught by the checker: `sh_flags`, `st_shndx`, a `.rela` `sh_info` and an
  FDE addend. A COMDAT function with a named section forms a group of that
  name. Named refusals cover data-class names (`[TCG-SECTION-DATA]`),
  reserved and malformed names, a name shared with a data global, a COMDAT
  function naming `.text`, Mach-O/x86-64/RISC-V/JIT and `-g`.
- **Sections, native (`records/native/named-gc/O0`–`O3`).** `sections.txt`
  is `readelf -S -W` of the object. `.text.keep_me`, `.text.drop_me` and the
  shared `.text.shared` are all `PROGBITS`, `AX`, alignment 4. With
  `--gc-sections --print-gc-sections` (`link-gc-true.txt`), GNU ld removes
  exactly `.text.drop_me` from this object. It keeps the unreferenced
  `tcg_shared_unused` with its referenced section-mate, and the program
  runs. Without `--gc-sections` (`link-gc-false.txt`) nothing is removed and
  every function is linked.
- **Pin-move floor.** `Function.section`, a malformed function section,
  `Function.visibility` and `Function.retained` each get a row. Every
  default entry refuses them under their own name.

The linked shared objects and executables are not archived.
`records/native/linked-binaries.json` records their SHA-256 and length. The
emitted relocatable objects are archived gzip-compressed (`library.o.gz`,
`named.o.gz`). The archive harness in `harnesses/` copied them raw, and the
root `.gitignore` (`*.o`) kept the raw copies out of the first commit, so the
archive failed its check on a clean checkout. On 2026-09-23 they were
compressed in place, byte-for-byte: each inventory entry keeps the object's
original SHA-256 and length as the decoded digest and adds the stored `.gz`
digest. `CAPTURED_FROM.txt` names each directory's original host-local
capture path.

A later review found defects this run did not detect. The function-section
classifier accepted `.jcr`, `.tm_clone_table`, `.stab`, `.rodata1` and
`.eh_frame.x`. The `parallel=true` visibility rows compiled a 24-function
module, which is below the parallel threshold, so they re-ran the sequential
emitter. The "sequential and parallel" claim above is therefore not
supported by this run. The repair and its qualifying run are in
[`../2026-09-23-linux-elf-function-attrs-2/`](../2026-09-23-linux-elf-function-attrs-2/README.md).

## Reproduce

```sh
PKG=$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23
python3 -B reports/perf/2026-09-23-linux-elf-function-attrs/harnesses/qualify-elf-function-attrs-20260923.py \
  --source . --out /path/outside/source/run --jobs 8
python3 -B reports/perf/2026-09-23-linux-elf-function-attrs/harnesses/archive-elf-function-attrs-20260923.py \
  --run /path/outside/source/run --archive <new archive dir> --harness <each harness>
python3 scripts/check_evidence_archive.py reports/perf/2026-09-23-linux-elf-function-attrs
```

The harness prepends `$PKG/bin` and `~/.cargo/bin` to `PATH`. It runs
`cargo test --locked --offline` per target, giving the two native targets a
private `TMPDIR`.

## Boundary

This is object and execution evidence for GNU ld 2.42 and the glibc 2.39
loader on this host. It is not a linker, loader or compiler proof. Hidden and
protected functions stay GOT-addressed and non-inlinable under `pic`, which
is conservative. The rustc bridge still stamps default visibility on
functions and refuses `#[link_section]`, which depends on L06-P1. Function
`retained`, Mach-O function visibility and sections, and `-g` with named or
split text stay refused. The 145-family Linux floor was not re-run for this
commit. Only the targets listed above ran. L02-P1 and L02-P3 remain
PARTIAL; no L01–L14 row closes.
