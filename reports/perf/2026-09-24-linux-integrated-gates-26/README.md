# Integrated Linux gates before the twenty-fifth main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `f4b38814eecb025f4daadca4c86385dd91c648a5`:
origin/main `7538ff147` (the owner's fsym commit on top of the
[gates-25](../2026-09-24-linux-integrated-gates-25/README.md) record's
`8cf9583e9`) with the L02-P10 eighth-audit residuals merged, and the
L02-P1 and L02-P10 ledger notes.

## What changed

- **L02-P10: eighth-audit residuals.** Every staged Linux link now writes a
  link map. The check decodes every `.eh_frame` input piece the map places,
  whatever the output section is called; the audit's renamed-section LLD
  static program is refused.
  - **Registration.** An image needs a readable map when any input
    registers frames. That covers:
    - an input that imports a libgcc registration function, or takes or
      exports an address in its own `.eh_frame`;
    - shared objects, read through `PT_DYNAMIC` as the loader binds them;
    - bitcode, GCC LTO objects and formats the driver does not read, which
      count as may-register.
  - **TLS:** an executable whose `PT_TLS` reaches 2^32 is refused (GNU ld
    silently truncates its IE/TLSDESC-to-LE relaxation there).
  - **gold:** its "too far from TP" message is classified.
  - **Overflow controls:** they run through the three linkers, and a JUMP26
    veneer control is added.
  - **Verification:** four independent verifier rounds. The qualification is
    [2026-09-24-linux-l02p10-audit8-residuals](../2026-09-24-linux-l02p10-audit8-residuals/README.md).
- **Ledger notes.** L02-P1 records the module-local function references, and
  L02-P10 the eighth audit and this repair. Both stay PARTIAL, and the
  counts are 99 open / 92 partial / 36 closed.

## Linux regression floor (`records/run33/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,040 Rust tests**. The source fingerprint
`1ec55dacf86fb640d241e86609d7d9d6d411da436d7b5ed30da195d17d441bdd` was the
same before and after the run. The run took 14:08:37Z to 14:23:06Z. The
highest sampled resident set was 443 MiB, in `e2e_aarch64_link_runtime`.
All four controls were on.

## Library, CLI, native and branch suites

- **Library tests:** codegen passed 4,203 with 1 ignored; lower 1,902; opt
  3,540.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `link_options` 37, `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  `aarch64_elf_cfi_differential` 3, `e2e_aarch64_eh_catch` 9,
  `e2e_aarch64_eh_linux` 10, `e2e_aarch64_elf_link` 11,
  `e2e_aarch64_elf_tlsie` 13 and `e2e_aarch64_link_runtime` 34.
- **L02-P1 lanes:**
  - with LLD and gold required: `aarch64_elf_symbol_binding` 41 and
    `e2e_aarch64_elf_relocation_model` 20;
  - `core_jit_planning` 13, `jit_external_symbol_resolution_policy` 6, and
    the two x86-64 module-batch targets 1 each.
- **The owner's fsym tests on this host:** `fsym_ub_map` 10,
  `fsym_interpreter_oracle` 4, and the CLI's `fsym_flag` 20.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
