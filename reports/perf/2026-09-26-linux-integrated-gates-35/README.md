# Integrated Linux gates in Trust development mode before the thirty-third main push — 2026-09-26

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates cover `824d77e4f`. That is origin/main `8124ab792` (the thirty-second push) merged with:

- **L02-P6's third-audit coverage rows.** Strong hidden/protected definitions in every implicit section, through both emitters and all three linkers. `v41_abi_residue_objects` joins the floor.
- **L02-P10's audit-9 residual repair.** Nine verifier rounds; the last one was clean.
- **Ledger updates.** L02-P6 and L03-P13 audits, L02-P10, and new rows L03-P14 and L06-P14.
- **One floor-runner fix (`824d77e4f`).** Described in the next section.

The runner and environment are the same as in
[gates-32](../2026-09-26-linux-integrated-gates-32/README.md). The baseline is gates-33's `run-i45`, which is the code of origin/main `2a5373470`.

## A failure the gate caught

`records/run-i47/` failed six native link targets at compile time:
`e2e_aarch64_elf_tlsie`, `e2e_aarch64_elf_sections`, `aarch64_elf_symbol_binding`,
`e2e_aarch64_link_runtime`, `link_options` and `e2e_aarch64_eh_catch`.

- **Cause.** L02-P10's floor sets `TCG_REQUIRE_LLD`/`TCG_REQUIRE_GOLD` on the Cargo process. The Trust compiler refuses `TCG_*` variables as untracked compiler controls.
- **Why neither branch saw it.** L02-P10 was developed with the stock toolchain. L13-P7's Trust-mode runner path routed only the Clean checker selection.
- **Fix.** `824d77e4f` sends a target's `TARGET_ENVIRONMENT` through the same Cargo target runner in Trust mode, and keeps the process environment in stock mode. A unit test covers both lanes.
- **Re-run.** `records/run-i48/` re-runs the whole floor at `824d77e4f`:
  - 204 targets, 1,369 tests passed;
  - the six targets pass (13, 26, 70, 18 for the new `v41_abi_residue_objects`, 35, 51, 9);
  - it fails exactly main's 20 tests by name (`floor-failed-tests.diff` against `run-i45` is empty).

## Other lanes (`*-i47`, on `ce45d43db`; the floor fix touches only the floor script)

- **Same failures as main:** codegen and lower library 7, CLI 1, native 3, fsym 1, local-call 1.
- **Symbol binding:** 70 and 21, with LLD and gold required through the runner and no `SKIP:`.
- **Verifier gates:** 5/52/8/32/11.
- **Opt:** 3,622.
- **fsym CLI:** 20.
- **Unwrap ratchet:** passes.
- **Linux bridge lane (`records/bridge-i47/`):** the known L06-P1 refusal. TLS and unwind each pass 2/2, and the source fingerprint stayed stable.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains OPEN.
