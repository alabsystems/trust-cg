# Integrated Linux gates before the twenty-ninth main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates cover the source for the twenty-ninth main push, `fdaa93f6e`: the
twenty-eighth push `d64dcdeb2` merged with the L02-P6 closure-audit residual branch
(`3b3a53e2e`) plus the ledger note (`fdaa93f6e`). The residual branch covers:

- merged globals keep the most constraining visibility;
- hidden and protected data declarations;
- a WEAK HIDDEN COMDAT `DW.ref` personality slot;
- local TLS descriptor anchors;
- floor pins.

It had two independent verifier rounds before the merge.

## Runs, all on the clean merged source `fdaa93f6e`

- **`records/run39/`: `scripts/check_linux_aarch64.py`**
  - Passed all **166 required target families and 1,063 Rust tests**,
    19:52:24Z to 20:08:10Z.
  - The source fingerprint
    `7cd37a121785bffae69fc1266205be15fac09a3e1b57221f27131bf3df6cf1c1` was the same
    before and after the run.
  - All four controls were on: clean source, a 16 GiB RSS ceiling, offline
    dependencies, and required proof tools.
  - The highest sampled resident set was 412 MiB, in `e2e_aarch64_link_runtime`.
- **Library tests (`lib-i39`):** codegen 4,208 passed with 1 ignored; lower 1,906;
  opt 3,540.
- **CLI, with LLD and gold required (`cli-bin-i39`):** the binary's tests 30,
  `link_options` 37, `output_paths` 8, `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line (`natives-i39`):**
  - `aarch64_elf_cfi_differential` 3;
  - `e2e_aarch64_eh_catch` 9;
  - `e2e_aarch64_eh_linux` 12;
  - `e2e_aarch64_elf_link` 11;
  - `e2e_aarch64_elf_tlsie` 13;
  - `e2e_aarch64_link_runtime` 34.
- **Verifier gate targets (`verify-gates-i39`):** 5 / 51 / 8 / 32 / 11.
- **L02-P1 and L02-P6 lanes:**
  - `binding-i39`, with LLD and gold required: `aarch64_elf_symbol_binding` 59 and
    `e2e_aarch64_elf_relocation_model` 21. These are the new floor minimums.
  - `localcall-i39`: `core_jit_planning` 13,
    `jit_external_symbol_resolution_policy` 6, and the two x86-64 module-batch
    targets 1 each.
- **fsym:** `fsym_interpreter_oracle` 5, `fsym_ub_map` 11, and the CLI's `fsym_flag` 20.
- **Linux bridge lane (`records/bridge39/`), on backend
  `3c8ca4d44b260f343ef4e6834436e119c6377f0c66b84ff76d7d4ba604f8e784`:**
  - `unwind_cleanup_linux` 2 of 2 and `tls_thread_local_linux` 2 of 2.
  - `aarch64_c_fnabi_aggregate_linux` fails at the known L06-P1 `[TCG-PROOF-465]`
    proof-promotion refusal, so the lane reports FAIL, as before.
  - The backend library itself is identified by that hash and not retained.

`records/gates39.status.txt` is the lane-by-lane exit record.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains OPEN.
