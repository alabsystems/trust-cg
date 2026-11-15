# Linux integration of recursive handle diagnostics

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Source `e4e40899bf197b0ffd9bc3cd2811eec0348a523c`, 2026-09-16, Linux AArch64. Compiler/build inputs
match incoming qualified source `e25e8a04`; the merge also includes the latest
memory-source completion documentation.

All **22 selected tests passed**, zero failed or ignored: one recursive handle
census unit test (1,823 filtered) and the complete opaque-handle integration
target (21 passed, zero filtered). Documentation inventory/link checks passed.
The earlier Linux qualification of opaque-handle adoption remains scoped to
its source; this run qualifies the added diagnostic-cycle fix on this host.

The runner records exact commands, durations, source hashes and outcomes. It
held the host resource lease, used two Cargo jobs and enforced a 16 GiB RSS
limit with zero grace. Source/build inputs remained unchanged and no watchdog
fired. Stock Rust 1.97.1 was used. This is development integration, not a
Trust-certified or full-workspace build, generated-code execution, installation
or whole-compiler completion claim.

The inventory binds all 6 retained artifacts by compressed and decoded
SHA-256 hashes and byte counts. The original concurrent push refusal was
resolved by a normal main pull and merge; no remote history was overwritten.
