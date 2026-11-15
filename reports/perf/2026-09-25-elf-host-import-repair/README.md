# x86 ELF EH imports on AArch64 — 2026-09-25

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

PASS on clean source `81f1c2288c6710bae7c8a6280e9dbe735038a921`:
all 17 commands, including codegen all-target compilation, 167 Rust tests
(zero failures or ignored tests), the three maintained Linux gate Python
modules (56 tests reported, with one expected non-/proc-host skip), and the
maintained formatting gate. The 11 integration targets ran without filters;
the three unit namespaces retain their explicit filtered counts.

The incoming native x86 EH rows were correctly compile-time gated, but their
native-only imports remained unconditional. On AArch64, `cargo check --all-targets`
failed with four unused-import errors under `-D warnings`. The repair scopes
those imports to their native consumers in all three affected targets. No
runtime test, host predicate, warning policy or proof refusal was removed.

The passing run includes all three full x86 EH object targets, DWARF CFI,
x86 ELF emission and unsupported-format gate units, and eight complete native
AArch64 EH, CFI, DWARF and NEON post-index targets. It claims no native x86
execution on the AArch64 host. The first failure, successful retry, exact
commands, patch, source/tool identities and process-group resource records
are retained in the hash-checked inventory. The 8 GiB limit and one Cargo job
were unchanged. The archive checker checks integrity, not compiler correctness.

This follows the [full 167-target AArch64 run](../2026-09-25-linux-required-floor/README.md)
at `443ed769f6`. The 167 tests here are a different, overlapping population from
that run's 1,078 tests; do not add them as unique tests or transfer that full
qualification to this revision. The later vectorizer merge at `5366857b0`
requires its own affected checks. Trust frontend, private ABI, release proof
and L01–L14/G1–G8 completion remain outside this report.
