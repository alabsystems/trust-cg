# Integrated Linux gates in Trust development mode before the thirty-fourth main push — 2026-09-26

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates cover `01b84f0c8`: origin/main `b2b9bba5c` (the thirty-third push) merged with:
- **L02-P6's fourth-audit repair.** A 1,008-case table-driven visibility test, 101 of 101 mutants killed, and `aarch64_elf_symbol_binding` pinned at 77.
- **L02-P10's tenth-audit residuals, after four verifier rounds.**
  - Fail-open linker options refused by measurement:
    - `--noinhibit-exec` and `-w`/`--no-warnings`;
    - GNU ld/gold one-dash option groups;
    - unresolved-symbol, copy-relocation and address-equality switches;
    - `--unique` and `--no-check-sections`.
  - Relocation formats glibc never applies, loaded-byte overlap and the entry point.
  - Fixes for the false refusals of address options, `-fpic` objects and GCC LTO.
- **Ledger updates.** The L02-P6 fourth audit, the L02-P10 tenth audit, and new gap L06-P15.

The runner and environment are those of
[gates-32](../2026-09-26-linux-integrated-gates-32/README.md). The baseline is
gates-35's `run-i48` and `*-i47` lanes, which is the code of origin/main `b2b9bba5c`.

## Result: no failure beyond origin/main's

- **Floor (`records/run-i50/`):** 204 targets and 1,387 tests passed. The same 8 targets and 20 test names fail as on main, and `floor-failed-tests.diff` against `run-i48` is empty. Pass counts include `aarch64_elf_symbol_binding` 77, `link_options` 62 and `e2e_aarch64_link_runtime` 35.
- **Same failures as main:** codegen/lower library 7, CLI 1, native 3 and local-call 1.
- **fsym:** it now passes 11/11. The fsym map mismatch in main's baseline was resolved by the owner's trust-ir pin move in `2597556b4`.
- **Green lanes:**
  - symbol binding 77 and relocation model 21 (LLD and gold required through the runner, no `SKIP:`);
  - verifier gates 5/52/8/32/11;
  - opt 3,622;
  - fsym CLI 20;
  - unwrap ratchet.
- **Linux bridge lane (`records/bridge-i50/`):** the known L06-P1 refusal. TLS and unwind each pass 2/2, and the source fingerprint stayed stable.
- **Before the gate:** the verifiers' reproducers (`repro_v2.sh`, `repro_w.sh`) were re-run against this integration's CLI. Every finding is refused as claimed, and the documented residuals behave as documented.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains OPEN.
