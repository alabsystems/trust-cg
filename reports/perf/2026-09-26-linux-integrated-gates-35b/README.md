# Post-merge re-check for the thirty-third main push — 2026-09-26

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

[gates-35](../2026-09-26-linux-integrated-gates-35/README.md) qualified `89c5367c2`.
Before the push, origin/main moved to `2597556b4`, which contains three owner
commits:

- the trust-ir pin moves from `be401849` to `794227ad`, and trust-ir v47–v49 are
  refused by name in every consumer;
- a Darwin Mach-O globals test fix;
- a pin-bump tooling change.

The integration merged them as `bf458b960`, and the only conflict was the
regenerated INVENTORY. These commits touch the dependency pin and its consumers,
not the integration's changes: link driver, symbol-binding tests, floor runner
and ledger. So the check was proportionate rather than a full gate. It used the
same Trust environment as gates-35.

- **Static checks:** `cargo fetch --locked` (root and bridge);
  `cargo check --workspace --all-features --all-targets` clean; fmt, docs,
  diagnostics census and host matrix current; 172 gate/ledger/lane unit tests OK.
- **`records/lib-i49.log`:** codegen library 4,327 passed. Its 7 failures are
  exactly main's.
- **`records/link-i49.log`:** LLD and gold were required through the Cargo target
  runner, and there was no `SKIP:` line:
  - `aarch64_elf_symbol_binding` 70;
  - `e2e_aarch64_eh_catch` 9;
  - `e2e_aarch64_elf_relocation_model` 21;
  - `e2e_aarch64_elf_sections` 26;
  - `e2e_aarch64_link_runtime` 35.
- **`records/cli-i49.log`:** `link_options` 51 and `output_paths` 8.

Regression evidence only; not qualification. Every L01–L14 row remains OPEN.
