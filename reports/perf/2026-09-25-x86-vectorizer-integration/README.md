# x86 vectorizer merged-source checks — 2026-09-25

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

PASS on clean source `5366857b0894b18bd4bb19bd7f376860b6cf2a06`:
15 commands and 255 Rust tests, zero failed or ignored. Both optimization
and codegen packages passed all-target compilation. The six complete changed
optimization test namespaces cover the shared pure-trap predicate, bounds-check
elimination, branch layout, conditional swaps, vectorization and shared runtime
symbol inventory. The codegen checks cover optimization schedules, branch
layout controls and ELF EH emission. All three x86 EH object integration targets
ran without filters. The maintained formatting gate passed.

This merged source contains the large-fill System V memset route and its ABI
guards, new vector loop shapes, and the single trap-block predicate used by
four machine passes. All actual commands, filtered unit counts, logs, source
and tool identities, and 8 GiB process-group resource records are retained in
the inventory. The source and tools remained unchanged. One Cargo job and one
test thread were used with the recorded locked, offline stock Rust toolchain.

These are AArch64-hosted unit and cross-emission checks. They do not run the
new private-bridge x86 vectorizer native fixtures or establish native x86
execution, comparative performance, general optimization correctness, release
acceptance or complete L01–L14/G1–G8 coverage. The private-bridge tracked knob
forwarding still needs qualification with its matched compiler and native host.

The preceding [ELF host-import qualification](../2026-09-25-elf-host-import-repair/README.md)
applies to `81f1c2288`; its overlap with this run must not be added as unique
tests. The [full AArch64 floor](../2026-09-25-linux-required-floor/README.md)
remains bound to `443ed769f6`. The current Trust rebuild deliberately pins the
qualified `81f1c2288` backend while this later main integration is checked.
