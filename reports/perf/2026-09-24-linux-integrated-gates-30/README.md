# Integrated Linux gates before the twenty-eighth main push, after the owner's merge — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates cover the source pushed as the twenty-eighth main push. It is the
[gates-29](../2026-09-24-linux-integrated-gates-29/README.md) source `780c8065d`
(L03-P2) merged with the owner's `98c65ab0c` (the atomic replay cohort and the
trust-ir pin `29744d5f`), plus one test fix.

## Runs

- **`records/run37/` and the `-i37` logs, on the merged source `22781dcf0`.** Every
  lane passed except the floor. The floor failed one row of `e2e_aarch64_eh_catch`,
  `eh_frame_personality_and_lsda_pointers_out_of_window_are_refused_by_run_link`: it
  expected the raw LLD far program to fault (signal 11) and saw it killed by the
  row's 10-second bound (signal 9). This host's `core_pattern` pipes to apport, which
  holds a faulting child until it has read the core. Under the load of concurrent
  builds and a nearly full disk, that took more than 10 seconds. The L02-P6 branch's
  own run had seen the same row time out once and then pass 24 of 24 times on
  repeat.
- **`07dcc8022`.** This commit only raises that file's two run bounds from 10 to 120
  seconds, so a hang is still caught. What the tests assert is unchanged.
- **`records/run38/` and `ehcatch-i38.log`, on `07dcc8022` (the pushed code).**
  - `scripts/check_linux_aarch64.py` passed all **166 required target families and
    1,051 Rust tests**, 19:25:56Z to 19:40:45Z.
  - The source fingerprint
    `b38c45ca2dc2add2a8196017a05d4662de6d08aaa4398f1bec7c01dba9331478` was the same
    before and after the run.
  - The highest sampled resident set was 2,462 MiB, in `aarch64_scalar_cell_bytes`.
  - All four controls were on.
  - `e2e_aarch64_eh_catch` passed 9 of 9 with LLD and gold required.

## Lanes on the merged source (`-i37` logs)

- **Library tests:** codegen 4,207 passed with 1 ignored; lower 1,905; opt 3,540.
- **CLI, with LLD and gold required:** the binary's tests 30, `link_options` 37,
  `output_paths` 8, `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  - `aarch64_elf_cfi_differential` 3;
  - `e2e_aarch64_eh_catch` 9 (this lane's own run passed);
  - `e2e_aarch64_eh_linux` 12;
  - `e2e_aarch64_elf_link` 11;
  - `e2e_aarch64_elf_tlsie` 13;
  - `e2e_aarch64_link_runtime` 34.
- **Verifier gate targets:** 5 / 51 / 8 / 32 / 11.
- **L02-P1 lanes:**
  - `aarch64_elf_symbol_binding` 48;
  - `e2e_aarch64_elf_relocation_model` 20;
  - `core_jit_planning` 13;
  - `jit_external_symbol_resolution_policy` 6;
  - the two x86-64 module-batch targets 1 each.
- **The owner's fsym tests on the new trust-ir pin:** `fsym_interpreter_oracle` 5,
  `fsym_ub_map` 11, and the CLI's `fsym_flag` 20.
- **Linux bridge lane (`records/bridge37/`):**
  - `unwind_cleanup_linux` 2 of 2 and `tls_thread_local_linux` 2 of 2.
  - `aarch64_c_fnabi_aggregate_linux` fails at the known L06-P1 `[TCG-PROOF-465]`
    refusal, so the lane reports FAIL, as before.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains OPEN.
