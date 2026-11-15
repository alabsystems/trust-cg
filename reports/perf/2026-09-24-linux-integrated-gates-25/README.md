# Integrated Linux gates before the twenty-fourth main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `a5dca1f988feea9c20be62632d3a2a4ac63c4bcd`:
origin/main `93e2c1c05` (the owner's fsym commit on top of the
[gates-24](../2026-09-24-linux-integrated-gates-24/README.md) record's
`9a9eda112`) with the L02-P1 module-local function references merged, a
small follow-up to its eighth verifier, and the L02-P10 ledger note.

## What changed

- **L02-P1: module-local function references on AArch64 ELF.** Objects
  admit calls, `FnDef`/closure addresses and `SymbolAddr` constants that
  name Internal/Private functions, bound as local symbols and checked after
  emission. The branch had eight independent verifier rounds; each repair
  is recorded in the L02-P1 section of `docs/linux-aarch64-completion.md`.
  - **Merges:** `merge_modules` renames colliding module-local functions
    apart and checks that undoing the rename restores each input. It
    refuses merges that would change an input's EH personality.
  - **Shadowing:** a module-local function, or any data definition, named
    like one of 29 names the backend or optimizer references by name
    (`trust_cg_lower::RuntimeSymbol`) is refused before lowering. This runs
    in `Compiler::compile` on every target, in the JIT, and in every public
    trust-ir translation entry. Core reaches its strict entry only through
    an `unsafe` token that one private helper constructs, and Core's own
    qualification and address-free compilation checks refuse the backend's
    calls. Wrong code this closes: a module-local `fmod` captured the
    backend's `fmod` call (`my_rem(5,3)` returned 42) in the Linux JIT, in
    Mach-O objects and through the public strict translation entries.
  - **Drift rows:** source scans pin every by-name symbol use in lower, opt
    and frame lowering, and every construction of the Core token. Their
    blind spots are listed in LIMITATIONS.
  - **Integration follow-up (`dfcd73c5a`):** the Core-token row skips only
    Cargo target directories, and LIMITATIONS names the scanners' remaining
    blind spots, from the eighth verifier.
- **L02-P10 ledger note.** The row records the bounded read-back, the
  hostile-product bounds and the eighth closure audit, which kept it
  PARTIAL. It is still PARTIAL; ledger counts 99 open / 92 partial / 36
  closed.

## Linux regression floor (`records/run32/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,035 Rust tests**. The source fingerprint
`fee20bb6cdd1a15b86b99fabb13ff5b75ab37f385aa851844a1677f0523d26da` was the
same before and after the run. The run took 13:10:41Z to 13:24:29Z. The
highest sampled resident set was 270 MiB, in `link_options`. All four
controls were on.

## Library, CLI, native and branch suites

- **Library tests:** codegen passed 4,189 with 1 ignored; lower 1,902; opt
  3,540.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `link_options` 34, `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  `aarch64_elf_cfi_differential` 3, `e2e_aarch64_eh_catch` 9,
  `e2e_aarch64_eh_linux` 10, `e2e_aarch64_elf_link` 11,
  `e2e_aarch64_elf_tlsie` 13 and `e2e_aarch64_link_runtime` 32.
- **L02-P1 lanes:** `aarch64_elf_symbol_binding` 41 and
  `e2e_aarch64_elf_relocation_model` 20 with LLD and gold required;
  `core_jit_planning` 13, `jit_external_symbol_resolution_policy` 6,
  `e2e_x86_64_module_batch_fnptr` 1 and `e2e_x86_64_module_batch_globals` 1.
- **The owner's fsym tests on this host:** `fsym_ub_map` 8,
  `fsym_interpreter_oracle` 4, and the CLI's `fsym_flag` 20.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
