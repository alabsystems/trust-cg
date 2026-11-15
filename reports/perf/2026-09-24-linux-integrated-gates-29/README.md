# Integrated Linux gates before the twenty-eighth main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `780c8065d764722be62bcf71e89da8af9c4d87a0`:
origin/main `3be0b17c6` (the
[gates-28](../2026-09-24-linux-integrated-gates-28/README.md) record) with L03-P2
merged, plus the L03-P2 and L02-P6 ledger notes.

## What changed

- **L03-P2: the Linux rustc-bridge unwind/cleanup twin and the invoke split.**
  - **Linux bridge twin.** `crates/rustc-codegen-trust-cg/tests/unwind_cleanup_linux.rs`
    runs a Rust panic through two CG frames with Box and user-Drop cleanups at
    O0-O3, each against an LLVM twin, with an exact model of the outcome. It has
    12 landing-pad-zeroing controls and is a required target of the Linux bridge
    runner.
  - **Invoke split.** An invoke that follows another adapter-emitted call in the
    same block now moves into its own block. The result is byte-identical to the
    explicit-branch form the old compiler accepted.
    - `e2e_aarch64_eh_linux` adds C++ and Rust rows where the earlier call throws
      past the frame's pad, with mutants.
    - Calls that instruction selection adds itself stay refused by name.
    - An x86-64 `f16` parameter is refused by name instead of panicking.
  - Two independent verifier rounds; qualification in
    [2026-09-24-linux-bridge-unwind](../2026-09-24-linux-bridge-unwind/README.md).
- **Ledger.** L03-P2 records both residuals. It stays PARTIAL: a catching CG
  frame is refused, and the split has no Darwin or x86-64 native run. L02-P6
  records its closure audit, kept PARTIAL, with a repair on a branch. Counts stay
  99 open / 92 partial / 36 closed.

## Linux regression floor (`records/run36/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families and
1,051 Rust tests**. The source fingerprint
`7f6377b54a4c0425f637407b7047eca657bec5322f0516d6de8a69fb8c9747f2` was the same
before and after the run. The run took 18:00:48Z to 18:15:59Z. The highest sampled
resident set was 407 MiB, in `link_options`. All four controls were on.

## Library, CLI, native, verifier-gate and branch suites

- **Library tests:** codegen passed 4,204 with 1 ignored, lower 1,905 and opt 3,540.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests passed
  30, `link_options` 37, `output_paths` 8 and `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  `aarch64_elf_cfi_differential` 3, `e2e_aarch64_eh_catch` 9,
  `e2e_aarch64_eh_linux` 12, `e2e_aarch64_elf_link` 11, `e2e_aarch64_elf_tlsie` 13
  and `e2e_aarch64_link_runtime` 34.
- **Verifier gate targets:** `aarch64_value_decode_gate` 5, `coverage_gate_tests`
  51, `meta_theorems` 8, `proof_gate_strict` 32 and `soundness_manifest` 11.
- **L02-P1 lanes:**
  - With LLD and gold required: `aarch64_elf_symbol_binding` 48 and
    `e2e_aarch64_elf_relocation_model` 20.
  - `core_jit_planning` 13, `jit_external_symbol_resolution_policy` 6, and the two
    x86-64 module-batch targets 1 each.
- **The owner's fsym tests:** `fsym_ub_map` 10, `fsym_interpreter_oracle` 4 and the
  CLI's `fsym_flag` 20.

## Linux bridge lane (`records/bridge36/`)

`scripts/check_linux_aarch64_bridge.py --require-proof-tools`, with the Trust
toolchain `~/toolchains/trust-a62ae50d` first on PATH:
- `unwind_cleanup_linux` passed 2 of 2;
- `tls_thread_local_linux` passed 2 of 2;
- `aarch64_c_fnabi_aggregate_linux` failed at the known L06-P1 refusal
  (`[TCG-PROOF-465]` proof promotion rejected; `native.log`).

The lane therefore reports FAIL, as before this change. The backend library is
identified by its hash in `report.json` and is not archived.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains OPEN.
