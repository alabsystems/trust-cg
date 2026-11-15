# Integrated Linux gates before the twenty-seventh main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `5bb260883cc02d28aee54c0f9dc7c40ed53457ce`:
origin/main `fa930ca68` (the
[gates-27](../2026-09-24-linux-integrated-gates-27/README.md) record) with
the L02-P1 hidden and protected function declarations merged, plus the
L02-P1 and L02-P10 ledger notes.

## What changed

- **L02-P1: hidden and protected function declarations on AArch64 ELF.**
  - A bodyless declaration with hidden or protected visibility is emitted
    as an undefined `STB_GLOBAL` (`STB_WEAK`) symbol with `STV_HIDDEN` or
    `STV_PROTECTED`. It used to be refused.
  - **Addressing:** `RelocationModel::symbol_address_is_got_indirect` is
    the one address rule. Every declaration's address comes from the GOT.
    A PC-relative address of a hidden declaration whose definition is a
    GNU IFUNC gave the PLT stub under GNU ld and gold, which differs from
    the C object's address. Calls to hidden and protected declarations are
    direct, with no PLT entry.
  - **Merges:** `merge_modules` keeps the most constraining visibility.
  - **Native rows,** through GNU ld, gold and LLD, cover:
    - binding within a library;
    - protected address equality;
    - missing definitions, which are refused and classified;
    - weak declarations that are absent or defined only in another
      library;
    - IFUNC definitions, with one address in non-PIE, `-static`, PIE,
      static-PIE and shared images.
  - **Verification:** two independent verifier rounds. The second found
    the repair sound: the data-import change is a no-op, 116 execution
    runs passed, and 1,278 corpus objects are byte-identical to the base.
- **Ledger notes.**
  - L02-P1 records this work. What remains is the rustc bridge's default
    function visibility and Mach-O function visibility.
  - L02-P10 records its ninth closure audit, kept PARTIAL. A repair is on
    a branch.
  - Counts stay 99 open, 92 partial, 36 closed.

## Linux regression floor (`records/run35/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,049 Rust tests**. The source fingerprint
`69298dd6e39793a8a9e0f713d5ea2772a9e0ef3d4d77d165c8e758421aad6670` was the
same before and after the run. The run took 15:21:58Z to 15:35:52Z. The
highest sampled resident set was 408 MiB, in `link_options`. All four
controls were on.

## Library, CLI, native, verifier-gate and branch suites

- **Library tests:** codegen passed 4,204 with 1 ignored, lower 1,904 and
  opt 3,540.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:**
  - the binary's tests 30;
  - `link_options` 37;
  - `output_paths` 8;
  - `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  - `aarch64_elf_cfi_differential` 3;
  - `e2e_aarch64_eh_catch` 9;
  - `e2e_aarch64_eh_linux` 10;
  - `e2e_aarch64_elf_link` 11;
  - `e2e_aarch64_elf_tlsie` 13;
  - `e2e_aarch64_link_runtime` 34.
- **Verifier gate targets:**
  - `aarch64_value_decode_gate` 5;
  - `coverage_gate_tests` 51;
  - `meta_theorems` 8;
  - `proof_gate_strict` 32;
  - `soundness_manifest` 11.
- **L02-P1 lanes:**
  - with LLD and gold required, `aarch64_elf_symbol_binding` 48 and
    `e2e_aarch64_elf_relocation_model` 20;
  - `core_jit_planning` 13;
  - `jit_external_symbol_resolution_policy` 6;
  - the two x86-64 module-batch targets, 1 each.
- **The owner's fsym tests:** `fsym_ub_map` 10, `fsym_interpreter_oracle` 4
  and the CLI's `fsym_flag` 20.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
