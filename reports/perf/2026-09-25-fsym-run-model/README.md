# Symbolic verifier run-model checks — 2026-09-25

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

On clean source `5bf537467c25c36ee3b62ae988d7b5a8c285bc31`, both the
verifier and CLI passed all-target compilation, and 161 Rust tests passed with
zero failures or ignored tests. The full `fsym_trust_ir::tests::` namespace,
all seven fsym verifier integration targets, and the full CLI flag target ran.
Integration targets had no filters. The maintained formatting gate passed.

The interpreter oracle used its unchanged default of 20,000 generated
functions and seed `0xfa57eed20260923`. It reported 16,951 interpreter UB
outcomes, 989 fsym-clean functions, 924 clean-and-executed functions, zero
unsound classifications, and zero crashes in this finite sample. Its complete
construct and run-placement inventory is retained in the log. This is testing
evidence, not an exhaustive soundness proof or coverage of every Rust program.

The thirteenth command, the documentation check, failed because `INVENTORY.md`
was stale. The original failed result is preserved. A separate follow-up
regenerated the inventory and passed the documentation check. Only that
generated Markdown file changed; no tested code changed. The frozen test
checkout remained clean at the tested revision, and the recorded tool hashes
were rechecked after the run. Commands, logs, hashes, resource records, and
the inventory-only patch are archived in inventory.json.

The run used the pinned stock Rust 1.97.1 toolchain, one Cargo job, one test
thread, and an 8 GiB process-group limit. It does not qualify the private
compiler bridge, native x86 execution, the installed Trust toolchain, or all
L01–L14/G1–G8 gates. The complete required AArch64 floor remains bound to
`443ed769f6` in the [floor report](../2026-09-25-linux-required-floor/README.md).
